import V185TrunkScan23Chunk0672

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3979356 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3979356 : Nat := 118140960795 + 3979356 * 2 ^ 59
def prefixEnd_3979356 : Nat := 4983230072969 + 3 ^ 40 * 3979356 * 2
def baseEnd_3979356 : Nat := 2043322323353037985049281

theorem tailTrace_3979356 : CollatzResearch.WordTrace tailWord_3979356 prefixEnd_3979356 2043322323353037985049281 := by
  unfold tailWord_3979356
  simp only [CollatzResearch.WordTrace]
  refine ⟨72569518485740153371302961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96759357980986871161737281 72569518485740153371302961)
  ·
    refine ⟨54427138864305115028477221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72569518485740153371302961 54427138864305115028477221)
    ·
      refine ⟨10205088537057209067839479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54427138864305115028477221 10205088537057209067839479)
      ·
        refine ⟨15307632805585813601759219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205088537057209067839479 15307632805585813601759219)
        ·
          refine ⟨22961449208378720402638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307632805585813601759219 22961449208378720402638829)
          ·
            refine ⟨8610543453142020150989561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22961449208378720402638829 8610543453142020150989561)
            ·
              refine ⟨6457907589856515113242171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8610543453142020150989561 6457907589856515113242171)
              ·
                refine ⟨9686861384784772669863257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457907589856515113242171 9686861384784772669863257)
                ·
                  refine ⟨7265146038588579502397443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686861384784772669863257 7265146038588579502397443)
                  ·
                    refine ⟨10897719057882869253596165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265146038588579502397443 10897719057882869253596165)
                    ·
                      refine ⟨2043322323353037985049281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10897719057882869253596165 2043322323353037985049281)
                      ·
                        rfl

theorem cell23_3979356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3979356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979356 prefixEnd_3979356 := by exact prefixLift 3979356
  have htrace : WordTrace (prefixWord ++ tailWord_3979356) baseStart_3979356 baseEnd_3979356 := by
    simpa [prefixWord, tailWord_3979356, baseEnd_3979356] using wordTrace_append hprefix tailTrace_3979356
  have hstable : (prefixWord ++ tailWord_3979356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979356).length < 2 ^ (prefixWord ++ tailWord_3979356).sum := by decide
  have hdescent : baseEnd_3979356 < baseStart_3979356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979383 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 1, 4]
def baseStart_3979383 : Nat := 118140960795 + 3979383 * 2 ^ 59
def prefixEnd_3979383 : Nat := 4983230072969 + 3 ^ 40 * 3979383 * 2
def baseEnd_3979383 : Nat := 681112062443569793137219

theorem tailTrace_3979383 : CollatzResearch.WordTrace tailWord_3979383 prefixEnd_3979383 681112062443569793137219 := by
  unfold tailWord_3979383
  simp only [CollatzResearch.WordTrace]
  refine ⟨145140021742382490353838803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96760014494921660235892535 145140021742382490353838803)
  ·
    refine ⟨217710032613573735530758205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145140021742382490353838803 217710032613573735530758205)
    ·
      refine ⟨81641262230090150824034327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217710032613573735530758205 81641262230090150824034327)
      ·
        refine ⟨122461893345135226236051491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81641262230090150824034327 122461893345135226236051491)
        ·
          refine ⟨183692840017702839354077237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122461893345135226236051491 183692840017702839354077237)
          ·
            refine ⟨17221203751659641189444741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183692840017702839354077237 17221203751659641189444741)
            ·
              refine ⟨3228975703436182723020889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17221203751659641189444741 3228975703436182723020889)
              ·
                refine ⟨2421731777577137042265667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228975703436182723020889 2421731777577137042265667)
                ·
                  refine ⟨3632597666365705563398501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2421731777577137042265667 3632597666365705563398501)
                  ·
                    refine ⟨681112062443569793137219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632597666365705563398501 681112062443569793137219)
                    ·
                      rfl

theorem cell23_3979383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_3979383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979383 prefixEnd_3979383 := by exact prefixLift 3979383
  have htrace : WordTrace (prefixWord ++ tailWord_3979383) baseStart_3979383 baseEnd_3979383 := by
    simpa [prefixWord, tailWord_3979383, baseEnd_3979383] using wordTrace_append hprefix tailTrace_3979383
  have hstable : (prefixWord ++ tailWord_3979383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979383).length < 2 ^ (prefixWord ++ tailWord_3979383).sum := by decide
  have hdescent : baseEnd_3979383 < baseStart_3979383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979449 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3979449 : Nat := 118140960795 + 3979449 * 2 ^ 59
def prefixEnd_3979449 : Nat := 4983230072969 + 3 ^ 40 * 3979449 * 2
def baseEnd_3979449 : Nat := 2043370077053906121186353

theorem tailTrace_3979449 : CollatzResearch.WordTrace tailWord_3979449 prefixEnd_3979449 2043370077053906121186353 := by
  unfold tailWord_3979449
  simp only [CollatzResearch.WordTrace]
  refine ⟨145142428960143383625741401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96761619306762255750494267 145142428960143383625741401)
  ·
    refine ⟨108856821720107537719306051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145142428960143383625741401 108856821720107537719306051)
    ·
      refine ⟨163285232580161306578959077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108856821720107537719306051 163285232580161306578959077)
      ·
        refine ⟨30615981108780244983554827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163285232580161306578959077 30615981108780244983554827)
        ·
          refine ⟨45923971663170367475332241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30615981108780244983554827 45923971663170367475332241)
          ·
            refine ⟨34442978747377775606499181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45923971663170367475332241 34442978747377775606499181)
            ·
              refine ⟨12916117030266665852437193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34442978747377775606499181 12916117030266665852437193)
              ·
                refine ⟨9687087772699999389327895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12916117030266665852437193 9687087772699999389327895)
                ·
                  refine ⟨14530631659049999083991843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687087772699999389327895 14530631659049999083991843)
                  ·
                    refine ⟨21795947488574998625987765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14530631659049999083991843 21795947488574998625987765)
                    ·
                      refine ⟨2043370077053906121186353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21795947488574998625987765 2043370077053906121186353)
                      ·
                        rfl

theorem cell23_3979449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3979449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979449 prefixEnd_3979449 := by exact prefixLift 3979449
  have htrace : WordTrace (prefixWord ++ tailWord_3979449) baseStart_3979449 baseEnd_3979449 := by
    simpa [prefixWord, tailWord_3979449, baseEnd_3979449] using wordTrace_append hprefix tailTrace_3979449
  have hstable : (prefixWord ++ tailWord_3979449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979449).length < 2 ^ (prefixWord ++ tailWord_3979449).sum := by decide
  have hdescent : baseEnd_3979449 < baseStart_3979449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979456 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_3979456 : Nat := 118140960795 + 3979456 * 2 ^ 59
def prefixEnd_3979456 : Nat := 4983230072969 + 3 ^ 40 * 3979456 * 2
def baseEnd_3979456 : Nat := 681124557139495864599607

theorem tailTrace_3979456 : CollatzResearch.WordTrace tailWord_3979456 prefixEnd_3979456 681124557139495864599607 := by
  unfold tailWord_3979456
  simp only [CollatzResearch.WordTrace]
  refine ⟨72571342135559011910623111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96761789514078682547497481 72571342135559011910623111)
  ·
    refine ⟨108857013203338517865934667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72571342135559011910623111 108857013203338517865934667)
    ·
      refine ⟨163285519805007776798902001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108857013203338517865934667 163285519805007776798902001)
      ·
        refine ⟨122464139853755832599176501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163285519805007776798902001 122464139853755832599176501)
        ·
          refine ⟨11481013111289609306172797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122464139853755832599176501 11481013111289609306172797)
          ·
            refine ⟨4305379916733603489814799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11481013111289609306172797 4305379916733603489814799)
            ·
              refine ⟨6458069875100405234722199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305379916733603489814799 6458069875100405234722199)
              ·
                refine ⟨9687104812650607852083299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458069875100405234722199 9687104812650607852083299)
                ·
                  refine ⟨14530657218975911778124949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687104812650607852083299 14530657218975911778124949)
                  ·
                    refine ⟨681124557139495864599607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14530657218975911778124949 681124557139495864599607)
                    ·
                      rfl

theorem cell23_3979456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_3979456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979456 prefixEnd_3979456 := by exact prefixLift 3979456
  have htrace : WordTrace (prefixWord ++ tailWord_3979456) baseStart_3979456 baseEnd_3979456 := by
    simpa [prefixWord, tailWord_3979456, baseEnd_3979456] using wordTrace_append hprefix tailTrace_3979456
  have hstable : (prefixWord ++ tailWord_3979456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979456).length < 2 ^ (prefixWord ++ tailWord_3979456).sum := by decide
  have hdescent : baseEnd_3979456 < baseStart_3979456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_3979472 : Nat := 118140960795 + 3979472 * 2 ^ 59
def prefixEnd_3979472 : Nat := 4983230072969 + 3 ^ 40 * 3979472 * 2
def baseEnd_3979472 : Nat := 2043381887108959531198747

theorem tailTrace_3979472 : CollatzResearch.WordTrace tailWord_3979472 prefixEnd_3979472 2043381887108959531198747 := by
  unfold tailWord_3979472
  simp only [CollatzResearch.WordTrace]
  refine ⟨72571633919530029276914335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96762178559373372369219113 72571633919530029276914335)
  ·
    refine ⟨108857450879295043915371503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72571633919530029276914335 108857450879295043915371503)
    ·
      refine ⟨163286176318942565873057255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108857450879295043915371503 163286176318942565873057255)
      ·
        refine ⟨244929264478413848809585883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163286176318942565873057255 244929264478413848809585883)
        ·
          refine ⟨367393896717620773214378825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244929264478413848809585883 367393896717620773214378825)
          ·
            refine ⟨275545422538215579910784119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367393896717620773214378825 275545422538215579910784119)
            ·
              refine ⟨413318133807323369866176179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275545422538215579910784119 413318133807323369866176179)
              ·
                refine ⟨619977200710985054799264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413318133807323369866176179 619977200710985054799264269)
                ·
                  refine ⟨232491450266619395549724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619977200710985054799264269 232491450266619395549724101)
                  ·
                    refine ⟨43592146924991136665573269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232491450266619395549724101 43592146924991136665573269)
                    ·
                      refine ⟨2043381887108959531198747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43592146924991136665573269 2043381887108959531198747)
                      ·
                        rfl

theorem cell23_3979472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_3979472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979472 prefixEnd_3979472 := by exact prefixLift 3979472
  have htrace : WordTrace (prefixWord ++ tailWord_3979472) baseStart_3979472 baseEnd_3979472 := by
    simpa [prefixWord, tailWord_3979472, baseEnd_3979472] using wordTrace_append hprefix tailTrace_3979472
  have hstable : (prefixWord ++ tailWord_3979472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979472).length < 2 ^ (prefixWord ++ tailWord_3979472).sum := by decide
  have hdescent : baseEnd_3979472 < baseStart_3979472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979479 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_3979479 : Nat := 118140960795 + 3979479 * 2 ^ 59
def prefixEnd_3979479 : Nat := 4983230072969 + 3 ^ 40 * 3979479 * 2
def baseEnd_3979479 : Nat := 2043385481473541003811215

theorem tailTrace_3979479 : CollatzResearch.WordTrace tailWord_3979479 prefixEnd_3979479 2043385481473541003811215 := by
  unfold tailWord_3979479
  simp only [CollatzResearch.WordTrace]
  refine ⟨145143523150034698749333491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96762348766689799166222327 145143523150034698749333491)
  ·
    refine ⟨217715284725052048124000237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145143523150034698749333491 217715284725052048124000237)
    ·
      refine ⟨81643231771894518046500089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217715284725052048124000237 81643231771894518046500089)
      ·
        refine ⟨61232423828920888534875067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81643231771894518046500089 61232423828920888534875067)
        ·
          refine ⟨91848635743381332802312601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61232423828920888534875067 91848635743381332802312601)
          ·
            refine ⟨68886476807535999601734451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91848635743381332802312601 68886476807535999601734451)
            ·
              refine ⟨103329715211303999402601677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68886476807535999601734451 103329715211303999402601677)
              ·
                refine ⟨38748643204238999775975629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103329715211303999402601677 38748643204238999775975629)
                ·
                  refine ⟨14530741201589624915990861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38748643204238999775975629 14530741201589624915990861)
                  ·
                    refine ⟨5449027950596109343496573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14530741201589624915990861 5449027950596109343496573)
                    ·
                      refine ⟨2043385481473541003811215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449027950596109343496573 2043385481473541003811215)
                      ·
                        rfl

theorem cell23_3979479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_3979479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979479 prefixEnd_3979479 := by exact prefixLift 3979479
  have htrace : WordTrace (prefixWord ++ tailWord_3979479) baseStart_3979479 baseEnd_3979479 := by
    simpa [prefixWord, tailWord_3979479, baseEnd_3979479] using wordTrace_append hprefix tailTrace_3979479
  have hstable : (prefixWord ++ tailWord_3979479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979479).length < 2 ^ (prefixWord ++ tailWord_3979479).sum := by decide
  have hdescent : baseEnd_3979479 < baseStart_3979479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3]
def baseStart_3979539 : Nat := 118140960795 + 3979539 * 2 ^ 59
def prefixEnd_3979539 : Nat := 4983230072969 + 3 ^ 40 * 3979539 * 2
def baseEnd_3979539 : Nat := 2043416290312810769060939

theorem tailTrace_3979539 : CollatzResearch.WordTrace tailWord_3979539 prefixEnd_3979539 2043416290312810769060939 := by
  unfold tailWord_3979539
  simp only [CollatzResearch.WordTrace]
  refine ⟨145145711529817328996517671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96763807686544885997678447 145145711529817328996517671)
  ·
    refine ⟨217718567294725993494776507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145145711529817328996517671 217718567294725993494776507)
    ·
      refine ⟨326577850942088990242164761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217718567294725993494776507 326577850942088990242164761)
      ·
        refine ⟨244933388206566742681623571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326577850942088990242164761 244933388206566742681623571)
        ·
          refine ⟨367400082309850114022435357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244933388206566742681623571 367400082309850114022435357)
          ·
            refine ⟨137775030866193792758413259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367400082309850114022435357 137775030866193792758413259)
            ·
              refine ⟨206662546299290689137619889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137775030866193792758413259 206662546299290689137619889)
              ·
                refine ⟨154996909724468016853214917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206662546299290689137619889 154996909724468016853214917)
                ·
                  refine ⟨29061920573337753159977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154996909724468016853214917 29061920573337753159977797)
                  ·
                    refine ⟨5449110107500828717495837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29061920573337753159977797 5449110107500828717495837)
                    ·
                      refine ⟨2043416290312810769060939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449110107500828717495837 2043416290312810769060939)
                      ·
                        rfl

theorem cell23_3979539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_3979539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979539 prefixEnd_3979539 := by exact prefixLift 3979539
  have htrace : WordTrace (prefixWord ++ tailWord_3979539) baseStart_3979539 baseEnd_3979539 := by
    simpa [prefixWord, tailWord_3979539, baseEnd_3979539] using wordTrace_append hprefix tailTrace_3979539
  have hstable : (prefixWord ++ tailWord_3979539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979539).length < 2 ^ (prefixWord ++ tailWord_3979539).sum := by decide
  have hdescent : baseEnd_3979539 < baseStart_3979539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979553 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3979553 : Nat := 118140960795 + 3979553 * 2 ^ 59
def prefixEnd_3979553 : Nat := 4983230072969 + 3 ^ 40 * 3979553 * 2
def baseEnd_3979553 : Nat := 2043423479041973714285875

theorem tailTrace_3979553 : CollatzResearch.WordTrace tailWord_3979553 prefixEnd_3979553 2043423479041973714285875 := by
  unfold tailWord_3979553
  simp only [CollatzResearch.WordTrace]
  refine ⟨145146222151766609387527313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96764148101177739591684875 145146222151766609387527313)
  ·
    refine ⟨108859666613824957040645485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145146222151766609387527313 108859666613824957040645485)
    ·
      refine ⟨40822374980184358890242057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108859666613824957040645485 40822374980184358890242057)
      ·
        refine ⟨30616781235138269167681543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40822374980184358890242057 30616781235138269167681543)
        ·
          refine ⟨45925171852707403751522315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30616781235138269167681543 45925171852707403751522315)
          ·
            refine ⟨68887757779061105627283473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45925171852707403751522315 68887757779061105627283473)
            ·
              refine ⟨51665818334295829220462605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68887757779061105627283473 51665818334295829220462605)
              ·
                refine ⟨19374681875360935957673477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51665818334295829220462605 19374681875360935957673477)
                ·
                  refine ⟨3632752851630175492063777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19374681875360935957673477 3632752851630175492063777)
                  ·
                    refine ⟨2724564638722631619047833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3632752851630175492063777 2724564638722631619047833)
                    ·
                      refine ⟨2043423479041973714285875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724564638722631619047833 2043423479041973714285875)
                      ·
                        rfl

theorem cell23_3979553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3979553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979553 prefixEnd_3979553 := by exact prefixLift 3979553
  have htrace : WordTrace (prefixWord ++ tailWord_3979553) baseStart_3979553 baseEnd_3979553 := by
    simpa [prefixWord, tailWord_3979553, baseEnd_3979553] using wordTrace_append hprefix tailTrace_3979553
  have hstable : (prefixWord ++ tailWord_3979553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979553).length < 2 ^ (prefixWord ++ tailWord_3979553).sum := by decide
  have hdescent : baseEnd_3979553 < baseStart_3979553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979556 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3979556 : Nat := 118140960795 + 3979556 * 2 ^ 59
def prefixEnd_3979556 : Nat := 4983230072969 + 3 ^ 40 * 3979556 * 2
def baseEnd_3979556 : Nat := 2043425019483937202548361

theorem tailTrace_3979556 : CollatzResearch.WordTrace tailWord_3979556 prefixEnd_3979556 2043425019483937202548361 := by
  unfold tailWord_3979556
  simp only [CollatzResearch.WordTrace]
  refine ⟨72573165785377870449943261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96764221047170493933257681 72573165785377870449943261)
  ·
    refine ⟨27214937169516701418728723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72573165785377870449943261 27214937169516701418728723)
    ·
      refine ⟨40822405754275052128093085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27214937169516701418728723 40822405754275052128093085)
      ·
        refine ⟨15308402157853144548034907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40822405754275052128093085 15308402157853144548034907)
        ·
          refine ⟨22962603236779716822052361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308402157853144548034907 22962603236779716822052361)
          ·
            refine ⟨17221952427584787616539271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22962603236779716822052361 17221952427584787616539271)
            ·
              refine ⟨25832928641377181424808907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221952427584787616539271 25832928641377181424808907)
              ·
                refine ⟨38749392962065772137213361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25832928641377181424808907 38749392962065772137213361)
                ·
                  refine ⟨29062044721549329102910021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38749392962065772137213361 29062044721549329102910021)
                  ·
                    refine ⟨5449133385290499206795629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29062044721549329102910021 5449133385290499206795629)
                    ·
                      refine ⟨2043425019483937202548361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449133385290499206795629 2043425019483937202548361)
                      ·
                        rfl

theorem cell23_3979556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3979556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979556 prefixEnd_3979556 := by exact prefixLift 3979556
  have htrace : WordTrace (prefixWord ++ tailWord_3979556) baseStart_3979556 baseEnd_3979556 := by
    simpa [prefixWord, tailWord_3979556, baseEnd_3979556] using wordTrace_append hprefix tailTrace_3979556
  have hstable : (prefixWord ++ tailWord_3979556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979556).length < 2 ^ (prefixWord ++ tailWord_3979556).sum := by decide
  have hdescent : baseEnd_3979556 < baseStart_3979556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979570 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_3979570 : Nat := 118140960795 + 3979570 * 2 ^ 59
def prefixEnd_3979570 : Nat := 4983230072969 + 3 ^ 40 * 3979570 * 2
def baseEnd_3979570 : Nat := 2043432208213100147773297

theorem tailTrace_3979570 : CollatzResearch.WordTrace tailWord_3979570 prefixEnd_3979570 2043432208213100147773297 := by
  unfold tailWord_3979570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36286710548176255322724041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96764561461803347527264109 36286710548176255322724041)
  ·
    refine ⟨27215032911132191492043031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36286710548176255322724041 27215032911132191492043031)
    ·
      refine ⟨40822549366698287238064547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27215032911132191492043031 40822549366698287238064547)
      ·
        refine ⟨61233824050047430857096821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40822549366698287238064547 61233824050047430857096821)
        ·
          refine ⟨5740671004691946642852827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61233824050047430857096821 5740671004691946642852827)
          ·
            refine ⟨8611006507037919964279241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740671004691946642852827 8611006507037919964279241)
            ·
              refine ⟨6458254880278439973209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8611006507037919964279241 6458254880278439973209431)
              ·
                refine ⟨9687382320417659959814147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458254880278439973209431 9687382320417659959814147)
                ·
                  refine ⟨14531073480626489939721221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687382320417659959814147 14531073480626489939721221)
                  ·
                    refine ⟨2724576277617466863697729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14531073480626489939721221 2724576277617466863697729)
                    ·
                      refine ⟨2043432208213100147773297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724576277617466863697729 2043432208213100147773297)
                      ·
                        rfl

theorem cell23_3979570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_3979570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979570 prefixEnd_3979570 := by exact prefixLift 3979570
  have htrace : WordTrace (prefixWord ++ tailWord_3979570) baseStart_3979570 baseEnd_3979570 := by
    simpa [prefixWord, tailWord_3979570, baseEnd_3979570] using wordTrace_append hprefix tailTrace_3979570
  have hstable : (prefixWord ++ tailWord_3979570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979570).length < 2 ^ (prefixWord ++ tailWord_3979570).sum := by decide
  have hdescent : baseEnd_3979570 < baseStart_3979570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979599 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_3979599 : Nat := 118140960795 + 3979599 * 2 ^ 59
def prefixEnd_3979599 : Nat := 4983230072969 + 3 ^ 40 * 3979599 * 2
def baseEnd_3979599 : Nat := 2043447099152080534310663

theorem tailTrace_3979599 : CollatzResearch.WordTrace tailWord_3979599 prefixEnd_3979599 2043447099152080534310663 := by
  unfold tailWord_3979599
  simp only [CollatzResearch.WordTrace]
  refine ⟨145147899909599959243701851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96765266606399972829134567 145147899909599959243701851)
  ·
    refine ⟨217721849864399938865552777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145147899909599959243701851 217721849864399938865552777)
    ·
      refine ⟨163291387398299954149164583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217721849864399938865552777 163291387398299954149164583)
      ·
        refine ⟨244937081097449931223746875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163291387398299954149164583 244937081097449931223746875)
        ·
          refine ⟨367405621646174896835620313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244937081097449931223746875 367405621646174896835620313)
          ·
            refine ⟨275554216234631172626715235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367405621646174896835620313 275554216234631172626715235)
            ·
              refine ⟨413331324351946758940072853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275554216234631172626715235 413331324351946758940072853)
              ·
                refine ⟨19374905828997504325315915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413331324351946758940072853 19374905828997504325315915)
                ·
                  refine ⟨29062358743496256487973873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19374905828997504325315915 29062358743496256487973873)
                  ·
                    refine ⟨21796769057622192365980405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29062358743496256487973873 21796769057622192365980405)
                    ·
                      refine ⟨2043447099152080534310663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21796769057622192365980405 2043447099152080534310663)
                      ·
                        rfl

theorem cell23_3979599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_3979599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979599 prefixEnd_3979599 := by exact prefixLift 3979599
  have htrace : WordTrace (prefixWord ++ tailWord_3979599) baseStart_3979599 baseEnd_3979599 := by
    simpa [prefixWord, tailWord_3979599, baseEnd_3979599] using wordTrace_append hprefix tailTrace_3979599
  have hstable : (prefixWord ++ tailWord_3979599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979599).length < 2 ^ (prefixWord ++ tailWord_3979599).sum := by decide
  have hdescent : baseEnd_3979599 < baseStart_3979599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979639 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3979639 : Nat := 118140960795 + 3979639 * 2 ^ 59
def prefixEnd_3979639 : Nat := 4983230072969 + 3 ^ 40 * 3979639 * 2
def baseEnd_3979639 : Nat := 2043467638378260377810479

theorem tailTrace_3979639 : CollatzResearch.WordTrace tailWord_3979639 prefixEnd_3979639 2043467638378260377810479 := by
  unfold tailWord_3979639
  simp only [CollatzResearch.WordTrace]
  refine ⟨145149358829455046075157971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96766239219636697383438647 145149358829455046075157971)
  ·
    refine ⟨217724038244182569112736957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145149358829455046075157971 217724038244182569112736957)
    ·
      refine ⟨81646514341568463417276359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217724038244182569112736957 81646514341568463417276359)
      ·
        refine ⟨122469771512352695125914539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81646514341568463417276359 122469771512352695125914539)
        ·
          refine ⟨183704657268529042688871809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122469771512352695125914539 183704657268529042688871809)
          ·
            refine ⟨137778492951396782016653857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183704657268529042688871809 137778492951396782016653857)
            ·
              refine ⟨103333869713547586512490393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137778492951396782016653857 103333869713547586512490393)
              ·
                refine ⟨77500402285160689884367795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103333869713547586512490393 77500402285160689884367795)
                ·
                  refine ⟨116250603427741034826551693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77500402285160689884367795 116250603427741034826551693)
                  ·
                    refine ⟨43593976285402888059956885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116250603427741034826551693 43593976285402888059956885)
                    ·
                      refine ⟨2043467638378260377810479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43593976285402888059956885 2043467638378260377810479)
                      ·
                        rfl

theorem cell23_3979639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3979639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979639 prefixEnd_3979639 := by exact prefixLift 3979639
  have htrace : WordTrace (prefixWord ++ tailWord_3979639) baseStart_3979639 baseEnd_3979639 := by
    simpa [prefixWord, tailWord_3979639, baseEnd_3979639] using wordTrace_append hprefix tailTrace_3979639
  have hstable : (prefixWord ++ tailWord_3979639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979639).length < 2 ^ (prefixWord ++ tailWord_3979639).sum := by decide
  have hdescent : baseEnd_3979639 < baseStart_3979639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979683 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 6]
def baseStart_3979683 : Nat := 118140960795 + 3979683 * 2 ^ 59
def prefixEnd_3979683 : Nat := 4983230072969 + 3 ^ 40 * 3979683 * 2
def baseEnd_3979683 : Nat := 227054470169673133962253

theorem tailTrace_3979683 : CollatzResearch.WordTrace tailWord_3979683 prefixEnd_3979683 227054470169673133962253 := by
  unfold tailWord_3979683
  simp only [CollatzResearch.WordTrace]
  refine ⟨145150963641295641589759703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96767309094197094393173135 145150963641295641589759703)
  ·
    refine ⟨217726445461943462384639555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145150963641295641589759703 217726445461943462384639555)
    ·
      refine ⟨326589668192915193576959333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217726445461943462384639555 326589668192915193576959333)
      ·
        refine ⟨61235562786171598795679875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326589668192915193576959333 61235562786171598795679875)
        ·
          refine ⟨91853344179257398193519813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61235562786171598795679875 91853344179257398193519813)
          ·
            refine ⟨17222502033610762161284965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91853344179257398193519813 17222502033610762161284965)
            ·
              refine ⟨3229219131302017905240931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17222502033610762161284965 3229219131302017905240931)
              ·
                refine ⟨4843828696953026857861397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229219131302017905240931 4843828696953026857861397)
                ·
                  refine ⟨227054470169673133962253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4843828696953026857861397 227054470169673133962253)
                  ·
                    rfl

theorem cell23_3979683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 6].length) (baseStart_3979683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979683 prefixEnd_3979683 := by exact prefixLift 3979683
  have htrace : WordTrace (prefixWord ++ tailWord_3979683) baseStart_3979683 baseEnd_3979683 := by
    simpa [prefixWord, tailWord_3979683, baseEnd_3979683] using wordTrace_append hprefix tailTrace_3979683
  have hstable : (prefixWord ++ tailWord_3979683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979683).length < 2 ^ (prefixWord ++ tailWord_3979683).sum := by decide
  have hdescent : baseEnd_3979683 < baseStart_3979683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979720 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_3979720 : Nat := 118140960795 + 3979720 * 2 ^ 59
def prefixEnd_3979720 : Nat := 4983230072969 + 3 ^ 40 * 3979720 * 2
def baseEnd_3979720 : Nat := 2043509230311274560897607

theorem tailTrace_3979720 : CollatzResearch.WordTrace tailWord_3979720 prefixEnd_3979720 2043509230311274560897607 := by
  unfold tailWord_3979720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72576156571080798454428307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96768208761441064605904409 72576156571080798454428307)
  ·
    refine ⟨108864234856621197681642461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72576156571080798454428307 108864234856621197681642461)
    ·
      refine ⟨40824088071232949130615923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108864234856621197681642461 40824088071232949130615923)
      ·
        refine ⟨61236132106849423695923885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40824088071232949130615923 61236132106849423695923885)
        ·
          refine ⟨22963549540068533885971457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61236132106849423695923885 22963549540068533885971457)
          ·
            refine ⟨17222662155051400414478593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22963549540068533885971457 17222662155051400414478593)
            ·
              refine ⟨12916996616288550310858945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17222662155051400414478593 12916996616288550310858945)
              ·
                refine ⟨9687747462216412733144209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12916996616288550310858945 9687747462216412733144209)
                ·
                  refine ⟨7265810596662309549858157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9687747462216412733144209 7265810596662309549858157)
                  ·
                    refine ⟨2724678973748366081196809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7265810596662309549858157 2724678973748366081196809)
                    ·
                      refine ⟨2043509230311274560897607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724678973748366081196809 2043509230311274560897607)
                      ·
                        rfl

theorem cell23_3979720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_3979720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979720 prefixEnd_3979720 := by exact prefixLift 3979720
  have htrace : WordTrace (prefixWord ++ tailWord_3979720) baseStart_3979720 baseEnd_3979720 := by
    simpa [prefixWord, tailWord_3979720, baseEnd_3979720] using wordTrace_append hprefix tailTrace_3979720
  have hstable : (prefixWord ++ tailWord_3979720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979720).length < 2 ^ (prefixWord ++ tailWord_3979720).sum := by decide
  have hdescent : baseEnd_3979720 < baseStart_3979720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979726 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3979726 : Nat := 118140960795 + 3979726 * 2 ^ 59
def prefixEnd_3979726 : Nat := 4983230072969 + 3 ^ 40 * 3979726 * 2
def baseEnd_3979726 : Nat := 681170770398400512474193

theorem tailTrace_3979726 : CollatzResearch.WordTrace tailWord_3979726 prefixEnd_3979726 681170770398400512474193 := by
  unfold tailWord_3979726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144066497517482491696879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96768354653426573289050021 18144066497517482491696879)
  ·
    refine ⟨27216099746276223737545319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18144066497517482491696879 27216099746276223737545319)
    ·
      refine ⟨40824149619414335606317979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27216099746276223737545319 40824149619414335606317979)
      ·
        refine ⟨61236224429121503409476969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40824149619414335606317979 61236224429121503409476969)
        ·
          refine ⟨45927168321841127557107727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61236224429121503409476969 45927168321841127557107727)
          ·
            refine ⟨68890752482761691335661591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45927168321841127557107727 68890752482761691335661591)
            ·
              refine ⟨103336128724142537003492387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68890752482761691335661591 103336128724142537003492387)
              ·
                refine ⟨155004193086213805505238581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103336128724142537003492387 155004193086213805505238581)
                ·
                  refine ⟨14531643101832544266116117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155004193086213805505238581 14531643101832544266116117)
                  ·
                    refine ⟨681170770398400512474193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14531643101832544266116117 681170770398400512474193)
                    ·
                      rfl

theorem cell23_3979726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3979726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979726 prefixEnd_3979726 := by exact prefixLift 3979726
  have htrace : WordTrace (prefixWord ++ tailWord_3979726) baseStart_3979726 baseEnd_3979726 := by
    simpa [prefixWord, tailWord_3979726, baseEnd_3979726] using wordTrace_append hprefix tailTrace_3979726
  have hstable : (prefixWord ++ tailWord_3979726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979726).length < 2 ^ (prefixWord ++ tailWord_3979726).sum := by decide
  have hdescent : baseEnd_3979726 < baseStart_3979726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979733 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3979733 : Nat := 118140960795 + 3979733 * 2 ^ 59
def prefixEnd_3979733 : Nat := 4983230072969 + 3 ^ 40 * 3979733 * 2
def baseEnd_3979733 : Nat := 2043515905559783010035047

theorem tailTrace_3979733 : CollatzResearch.WordTrace tailWord_3979733 prefixEnd_3979733 2043515905559783010035047 := by
  unfold tailWord_3979733
  simp only [CollatzResearch.WordTrace]
  refine ⟨145152787291114500129079853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96768524860743000086053235 145152787291114500129079853)
  ·
    refine ⟨54432295234167937548404945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145152787291114500129079853 54432295234167937548404945)
    ·
      refine ⟨40824221425625953161303709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54432295234167937548404945 40824221425625953161303709)
      ·
        refine ⟨15309083034609732435488891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40824221425625953161303709 15309083034609732435488891)
        ·
          refine ⟨22963624551914598653233337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309083034609732435488891 22963624551914598653233337)
          ·
            refine ⟨17222718413935948989925003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22963624551914598653233337 17222718413935948989925003)
            ·
              refine ⟨25834077620903923484887505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222718413935948989925003 25834077620903923484887505)
              ·
                refine ⟨19375558215677942613665629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25834077620903923484887505 19375558215677942613665629)
                ·
                  refine ⟨7265834330879228480124611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19375558215677942613665629 7265834330879228480124611)
                  ·
                    refine ⟨10898751496318842720186917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265834330879228480124611 10898751496318842720186917)
                    ·
                      refine ⟨2043515905559783010035047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10898751496318842720186917 2043515905559783010035047)
                      ·
                        rfl

theorem cell23_3979733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3979733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979733 prefixEnd_3979733 := by exact prefixLift 3979733
  have htrace : WordTrace (prefixWord ++ tailWord_3979733) baseStart_3979733 baseEnd_3979733 := by
    simpa [prefixWord, tailWord_3979733, baseEnd_3979733] using wordTrace_append hprefix tailTrace_3979733
  have hstable : (prefixWord ++ tailWord_3979733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979733).length < 2 ^ (prefixWord ++ tailWord_3979733).sum := by decide
  have hdescent : baseEnd_3979733 < baseStart_3979733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979736 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3979736 : Nat := 118140960795 + 3979736 * 2 ^ 59
def prefixEnd_3979736 : Nat := 4983230072969 + 3 ^ 40 * 3979736 * 2
def baseEnd_3979736 : Nat := 2043517446001746498297533

theorem tailTrace_3979736 : CollatzResearch.WordTrace tailWord_3979736 prefixEnd_3979736 2043517446001746498297533 := by
  unfold tailWord_3979736
  simp only [CollatzResearch.WordTrace]
  refine ⟨72576448355051815820719531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96768597806735754427626041 72576448355051815820719531)
  ·
    refine ⟨108864672532577723731079297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72576448355051815820719531 108864672532577723731079297)
    ·
      refine ⟨81648504399433292798309473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108864672532577723731079297 81648504399433292798309473)
      ·
        refine ⟨61236378299574969598732105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81648504399433292798309473 61236378299574969598732105)
        ·
          refine ⟨45927283724681227199049079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61236378299574969598732105 45927283724681227199049079)
          ·
            refine ⟨68890925587021840798573619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45927283724681227199049079 68890925587021840798573619)
            ·
              refine ⟨103336388380532761197860429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68890925587021840798573619 103336388380532761197860429)
              ·
                refine ⟨38751145642699785449197661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103336388380532761197860429 38751145642699785449197661)
                ·
                  refine ⟨14531679616012419543449123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38751145642699785449197661 14531679616012419543449123)
                  ·
                    refine ⟨21797519424018629315173685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14531679616012419543449123 21797519424018629315173685)
                    ·
                      refine ⟨2043517446001746498297533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21797519424018629315173685 2043517446001746498297533)
                      ·
                        rfl

theorem cell23_3979736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3979736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979736 prefixEnd_3979736 := by exact prefixLift 3979736
  have htrace : WordTrace (prefixWord ++ tailWord_3979736) baseStart_3979736 baseEnd_3979736 := by
    simpa [prefixWord, tailWord_3979736, baseEnd_3979736] using wordTrace_append hprefix tailTrace_3979736
  have hstable : (prefixWord ++ tailWord_3979736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979736).length < 2 ^ (prefixWord ++ tailWord_3979736).sum := by decide
  have hdescent : baseEnd_3979736 < baseStart_3979736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979743 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 6]
def baseStart_3979743 : Nat := 118140960795 + 3979743 * 2 ^ 59
def prefixEnd_3979743 : Nat := 4983230072969 + 3 ^ 40 * 3979743 * 2
def baseEnd_3979743 : Nat := 681173680122109323636667

theorem tailTrace_3979743 : CollatzResearch.WordTrace tailWord_3979743 prefixEnd_3979743 681173680122109323636667 := by
  unfold tailWord_3979743
  simp only [CollatzResearch.WordTrace]
  refine ⟨145153152021078271836943883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96768768014052181224629255 145153152021078271836943883)
  ·
    refine ⟨217729728031617407755415825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145153152021078271836943883 217729728031617407755415825)
    ·
      refine ⟨163297296023713055816561869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217729728031617407755415825 163297296023713055816561869)
      ·
        refine ⟨61236486008892395931210701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163297296023713055816561869 61236486008892395931210701)
        ·
          refine ⟨22963682253334648474204013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61236486008892395931210701 22963682253334648474204013)
          ·
            refine ⟨8611380845000493177826505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22963682253334648474204013 8611380845000493177826505)
            ·
              refine ⟨6458535633750369883369879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8611380845000493177826505 6458535633750369883369879)
              ·
                refine ⟨9687803450625554825054819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458535633750369883369879 9687803450625554825054819)
                ·
                  refine ⟨14531705175938332237582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687803450625554825054819 14531705175938332237582229)
                  ·
                    refine ⟨681173680122109323636667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14531705175938332237582229 681173680122109323636667)
                    ·
                      rfl

theorem cell23_3979743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_3979743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979743 prefixEnd_3979743 := by exact prefixLift 3979743
  have htrace : WordTrace (prefixWord ++ tailWord_3979743) baseStart_3979743 baseEnd_3979743 := by
    simpa [prefixWord, tailWord_3979743, baseEnd_3979743] using wordTrace_append hprefix tailTrace_3979743
  have hstable : (prefixWord ++ tailWord_3979743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979743).length < 2 ^ (prefixWord ++ tailWord_3979743).sum := by decide
  have hdescent : baseEnd_3979743 < baseStart_3979743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979777 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3979777 : Nat := 118140960795 + 3979777 * 2 ^ 59
def prefixEnd_3979777 : Nat := 4983230072969 + 3 ^ 40 * 3979777 * 2
def baseEnd_3979777 : Nat := 681179499569526945961615

theorem tailTrace_3979777 : CollatzResearch.WordTrace tailWord_3979777 prefixEnd_3979777 681179499569526945961615 := by
  unfold tailWord_3979777
  simp only [CollatzResearch.WordTrace]
  refine ⟨145154392102955095643681585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96769594735303397095787723 145154392102955095643681585)
  ·
    refine ⟨108865794077216321732761189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145154392102955095643681585 108865794077216321732761189)
    ·
      refine ⟨20412336389478060324892723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108865794077216321732761189 20412336389478060324892723)
      ·
        refine ⟨30618504584217090487339085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20412336389478060324892723 30618504584217090487339085)
        ·
          refine ⟨11481939219081408932752157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30618504584217090487339085 11481939219081408932752157)
          ·
            refine ⟨4305727207155528349782059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11481939219081408932752157 4305727207155528349782059)
            ·
              refine ⟨6458590810733292524673089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305727207155528349782059 6458590810733292524673089)
              ·
                refine ⟨4843943108049969393504817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458590810733292524673089 4843943108049969393504817)
                ·
                  refine ⟨3632957331037477045128613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4843943108049969393504817 3632957331037477045128613)
                  ·
                    refine ⟨681179499569526945961615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632957331037477045128613 681179499569526945961615)
                    ·
                      rfl

theorem cell23_3979777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3979777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979777 prefixEnd_3979777 := by exact prefixLift 3979777
  have htrace : WordTrace (prefixWord ++ tailWord_3979777) baseStart_3979777 baseEnd_3979777 := by
    simpa [prefixWord, tailWord_3979777, baseEnd_3979777] using wordTrace_append hprefix tailTrace_3979777
  have hstable : (prefixWord ++ tailWord_3979777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979777).length < 2 ^ (prefixWord ++ tailWord_3979777).sum := by decide
  have hdescent : baseEnd_3979777 < baseStart_3979777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979793 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_3979793 : Nat := 118140960795 + 3979793 * 2 ^ 59
def prefixEnd_3979793 : Nat := 4983230072969 + 3 ^ 40 * 3979793 * 2
def baseEnd_3979793 : Nat := 2043546714399052775284771

theorem tailTrace_3979793 : CollatzResearch.WordTrace tailWord_3979793 prefixEnd_3979793 2043546714399052775284771 := by
  unfold tailWord_3979793
  simp only [CollatzResearch.WordTrace]
  refine ⟨145154975670897130376264033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96769983780598086917509355 145154975670897130376264033)
  ·
    refine ⟨108866231753172847782198025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145154975670897130376264033 108866231753172847782198025)
    ·
      refine ⟨81649673814879635836648519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108866231753172847782198025 81649673814879635836648519)
      ·
        refine ⟨122474510722319453754972779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81649673814879635836648519 122474510722319453754972779)
        ·
          refine ⟨183711766083479180632459169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122474510722319453754972779 183711766083479180632459169)
          ·
            refine ⟨137783824562609385474344377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183711766083479180632459169 137783824562609385474344377)
            ·
              refine ⟨103337868421957039105758283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137783824562609385474344377 103337868421957039105758283)
              ·
                refine ⟨155006802632935558658637425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103337868421957039105758283 155006802632935558658637425)
                ·
                  refine ⟨116255101974701668993978069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155006802632935558658637425 116255101974701668993978069)
                  ·
                    refine ⟨2724728952532070367046361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116255101974701668993978069 2724728952532070367046361)
                    ·
                      refine ⟨2043546714399052775284771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724728952532070367046361 2043546714399052775284771)
                      ·
                        rfl

theorem cell23_3979793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_3979793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979793 prefixEnd_3979793 := by exact prefixLift 3979793
  have htrace : WordTrace (prefixWord ++ tailWord_3979793) baseStart_3979793 baseEnd_3979793 := by
    simpa [prefixWord, tailWord_3979793, baseEnd_3979793] using wordTrace_append hprefix tailTrace_3979793
  have hstable : (prefixWord ++ tailWord_3979793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979793).length < 2 ^ (prefixWord ++ tailWord_3979793).sum := by decide
  have hdescent : baseEnd_3979793 < baseStart_3979793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979800 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3979800 : Nat := 118140960795 + 3979800 * 2 ^ 59
def prefixEnd_3979800 : Nat := 4983230072969 + 3 ^ 40 * 3979800 * 2
def baseEnd_3979800 : Nat := 2043550308763634247897239

theorem tailTrace_3979800 : CollatzResearch.WordTrace tailWord_3979800 prefixEnd_3979800 2043550308763634247897239 := by
  unfold tailWord_3979800
  simp only [CollatzResearch.WordTrace]
  refine ⟨72577615490935885285884427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96770153987914513714512569 72577615490935885285884427)
  ·
    refine ⟨108866423236403827928826641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72577615490935885285884427 108866423236403827928826641)
    ·
      refine ⟨81649817427302870946619981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108866423236403827928826641 81649817427302870946619981)
      ·
        refine ⟨30618681535238576604982493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81649817427302870946619981 30618681535238576604982493)
        ·
          refine ⟨11482005575714466226868435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30618681535238576604982493 11482005575714466226868435)
          ·
            refine ⟨17223008363571699340302653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482005575714466226868435 17223008363571699340302653)
            ·
              refine ⟨6458628136339387252613495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17223008363571699340302653 6458628136339387252613495)
              ·
                refine ⟨9687942204509080878920243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458628136339387252613495 9687942204509080878920243)
                ·
                  refine ⟨14531913306763621318380365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687942204509080878920243 14531913306763621318380365)
                  ·
                    refine ⟨5449467490036357994392637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14531913306763621318380365 5449467490036357994392637)
                    ·
                      refine ⟨2043550308763634247897239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449467490036357994392637 2043550308763634247897239)
                      ·
                        rfl

theorem cell23_3979800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3979800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979800 prefixEnd_3979800 := by exact prefixLift 3979800
  have htrace : WordTrace (prefixWord ++ tailWord_3979800) baseStart_3979800 baseEnd_3979800 := by
    simpa [prefixWord, tailWord_3979800, baseEnd_3979800] using wordTrace_append hprefix tailTrace_3979800
  have hstable : (prefixWord ++ tailWord_3979800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979800).length < 2 ^ (prefixWord ++ tailWord_3979800).sum := by decide
  have hdescent : baseEnd_3979800 < baseStart_3979800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979897 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 5]
def baseStart_3979897 : Nat := 118140960795 + 3979897 * 2 ^ 59
def prefixEnd_3979897 : Nat := 4983230072969 + 3 ^ 40 * 3979897 * 2
def baseEnd_3979897 : Nat := 227066679598568929820477

theorem tailTrace_3979897 : CollatzResearch.WordTrace tailWord_3979897 prefixEnd_3979897 227066679598568929820477 := by
  unfold tailWord_3979897
  simp only [CollatzResearch.WordTrace]
  refine ⟨145158768862520356138049945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96772512575013570758699963 145158768862520356138049945)
  ·
    refine ⟨108869076646890267103537459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145158768862520356138049945 108869076646890267103537459)
    ·
      refine ⟨163303614970335400655306189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108869076646890267103537459 163303614970335400655306189)
      ·
        refine ⟨61238855613875775245739821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163303614970335400655306189 61238855613875775245739821)
        ·
          refine ⟨22964570855203415717152433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61238855613875775245739821 22964570855203415717152433)
          ·
            refine ⟨17223428141402561787864325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22964570855203415717152433 17223428141402561787864325)
            ·
              refine ⟨3229392776512980335224561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17223428141402561787864325 3229392776512980335224561)
              ·
                refine ⟨2422044582384735251418421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229392776512980335224561 2422044582384735251418421)
                ·
                  refine ⟨227066679598568929820477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422044582384735251418421 227066679598568929820477)
                  ·
                    rfl

theorem cell23_3979897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 5].length) (baseStart_3979897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979897 prefixEnd_3979897 := by exact prefixLift 3979897
  have htrace : WordTrace (prefixWord ++ tailWord_3979897) baseStart_3979897 baseEnd_3979897 := by
    simpa [prefixWord, tailWord_3979897, baseEnd_3979897] using wordTrace_append hprefix tailTrace_3979897
  have hstable : (prefixWord ++ tailWord_3979897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979897).length < 2 ^ (prefixWord ++ tailWord_3979897).sum := by decide
  have hdescent : baseEnd_3979897 < baseStart_3979897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979900 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_3979900 : Nat := 118140960795 + 3979900 * 2 ^ 59
def prefixEnd_3979900 : Nat := 4983230072969 + 3 ^ 40 * 3979900 * 2
def baseEnd_3979900 : Nat := 2043601656829083856646779

theorem tailTrace_3979900 : CollatzResearch.WordTrace tailWord_3979900 prefixEnd_3979900 2043601656829083856646779 := by
  unfold tailWord_3979900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72579439140754743825204577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96772585521006325100272769 72579439140754743825204577)
  ·
    refine ⟨54434579355566057868903433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72579439140754743825204577 54434579355566057868903433)
    ·
      refine ⟨40825934516674543401677575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54434579355566057868903433 40825934516674543401677575)
      ·
        refine ⟨61238901775011815102516363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40825934516674543401677575 61238901775011815102516363)
        ·
          refine ⟨91858352662517722653774545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61238901775011815102516363 91858352662517722653774545)
          ·
            refine ⟨68893764496888291990330909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91858352662517722653774545 68893764496888291990330909)
            ·
              refine ⟨25835161686333109496374091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68893764496888291990330909 25835161686333109496374091)
              ·
                refine ⟨38752742529499664244561137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25835161686333109496374091 38752742529499664244561137)
                ·
                  refine ⟨29064556897124748183420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38752742529499664244561137 29064556897124748183420853)
                  ·
                    refine ⟨2724802209105445142195705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29064556897124748183420853 2724802209105445142195705)
                    ·
                      refine ⟨2043601656829083856646779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724802209105445142195705 2043601656829083856646779)
                      ·
                        rfl

theorem cell23_3979900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_3979900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979900 prefixEnd_3979900 := by exact prefixLift 3979900
  have htrace : WordTrace (prefixWord ++ tailWord_3979900) baseStart_3979900 baseEnd_3979900 := by
    simpa [prefixWord, tailWord_3979900, baseEnd_3979900] using wordTrace_append hprefix tailTrace_3979900
  have hstable : (prefixWord ++ tailWord_3979900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979900).length < 2 ^ (prefixWord ++ tailWord_3979900).sum := by decide
  have hdescent : baseEnd_3979900 < baseStart_3979900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979913 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_3979913 : Nat := 118140960795 + 3979913 * 2 ^ 59
def prefixEnd_3979913 : Nat := 4983230072969 + 3 ^ 40 * 3979913 * 2
def baseEnd_3979913 : Nat := 2043608332077592305784219

theorem tailTrace_3979913 : CollatzResearch.WordTrace tailWord_3979913 prefixEnd_3979913 2043608332077592305784219 := by
  unfold tailWord_3979913
  simp only [CollatzResearch.WordTrace]
  refine ⟨145159352430462390870632393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96772901620308260580421595 145159352430462390870632393)
  ·
    refine ⟨108869514322846793152974295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145159352430462390870632393 108869514322846793152974295)
    ·
      refine ⟨163304271484270189729461443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108869514322846793152974295 163304271484270189729461443)
      ·
        refine ⟨244956407226405284594192165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163304271484270189729461443 244956407226405284594192165)
        ·
          refine ⟨45929326354950990861411031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244956407226405284594192165 45929326354950990861411031)
          ·
            refine ⟨68893989532426486292116547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45929326354950990861411031 68893989532426486292116547)
            ·
              refine ⟨103340984298639729438174821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68893989532426486292116547 103340984298639729438174821)
              ·
                refine ⟨19376434555994949269657779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103340984298639729438174821 19376434555994949269657779)
                ·
                  refine ⟨29064651833992423904486669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19376434555994949269657779 29064651833992423904486669)
                  ·
                    refine ⟨10899244437747158964182501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29064651833992423904486669 10899244437747158964182501)
                    ·
                      refine ⟨2043608332077592305784219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10899244437747158964182501 2043608332077592305784219)
                      ·
                        rfl

theorem cell23_3979913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_3979913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979913 prefixEnd_3979913 := by exact prefixLift 3979913
  have htrace : WordTrace (prefixWord ++ tailWord_3979913) baseStart_3979913 baseEnd_3979913 := by
    simpa [prefixWord, tailWord_3979913, baseEnd_3979913] using wordTrace_append hprefix tailTrace_3979913
  have hstable : (prefixWord ++ tailWord_3979913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979913).length < 2 ^ (prefixWord ++ tailWord_3979913).sum := by decide
  have hdescent : baseEnd_3979913 < baseStart_3979913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979940 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_3979940 : Nat := 118140960795 + 3979940 * 2 ^ 59
def prefixEnd_3979940 : Nat := 4983230072969 + 3 ^ 40 * 3979940 * 2
def baseEnd_3979940 : Nat := 681207398685087900048865

theorem tailTrace_3979940 : CollatzResearch.WordTrace tailWord_3979940 prefixEnd_3979940 681207398685087900048865 := by
  unfold tailWord_3979940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72580168600682287240932637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96773558134243049654576849 72580168600682287240932637)
  ·
    refine ⟨27217563225255857715349739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72580168600682287240932637 27217563225255857715349739)
    ·
      refine ⟨40826344837883786573024609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27217563225255857715349739 40826344837883786573024609)
      ·
        refine ⟨30619758628412839929768457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40826344837883786573024609 30619758628412839929768457)
        ·
          refine ⟨22964818971309629947326343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30619758628412839929768457 22964818971309629947326343)
          ·
            refine ⟨34447228456964444920989515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964818971309629947326343 34447228456964444920989515)
            ·
              refine ⟨51670842685446667381484273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34447228456964444920989515 51670842685446667381484273)
              ·
                refine ⟨38753132014085000536113205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51670842685446667381484273 38753132014085000536113205)
                ·
                  refine ⟨3633106126320468800260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38753132014085000536113205 3633106126320468800260613)
                  ·
                    refine ⟨681207398685087900048865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633106126320468800260613 681207398685087900048865)
                    ·
                      rfl

theorem cell23_3979940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_3979940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979940 prefixEnd_3979940 := by exact prefixLift 3979940
  have htrace : WordTrace (prefixWord ++ tailWord_3979940) baseStart_3979940 baseEnd_3979940 := by
    simpa [prefixWord, tailWord_3979940, baseEnd_3979940] using wordTrace_append hprefix tailTrace_3979940
  have hstable : (prefixWord ++ tailWord_3979940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979940).length < 2 ^ (prefixWord ++ tailWord_3979940).sum := by decide
  have hdescent : baseEnd_3979940 < baseStart_3979940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3979957 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3979957 : Nat := 118140960795 + 3979957 * 2 ^ 59
def prefixEnd_3979957 : Nat := 4983230072969 + 3 ^ 40 * 3979957 * 2
def baseEnd_3979957 : Nat := 681210308408796711211339

theorem tailTrace_3979957 : CollatzResearch.WordTrace tailWord_3979957 prefixEnd_3979957 681210308408796711211339 := by
  unfold tailWord_3979957
  simp only [CollatzResearch.WordTrace]
  refine ⟨145160957242302986385234125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96773971494868657590156083 145160957242302986385234125)
  ·
    refine ⟨54435358965863619894462797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145160957242302986385234125 54435358965863619894462797)
    ·
      refine ⟨20413259612198857460423549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54435358965863619894462797 20413259612198857460423549)
      ·
        refine ⟨7654972354574571547658831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20413259612198857460423549 7654972354574571547658831)
        ·
          refine ⟨11482458531861857321488247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654972354574571547658831 11482458531861857321488247)
          ·
            refine ⟨17223687797792785982232371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482458531861857321488247 17223687797792785982232371)
            ·
              refine ⟨25835531696689178973348557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17223687797792785982232371 25835531696689178973348557)
              ·
                refine ⟨9688324386258442115005709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25835531696689178973348557 9688324386258442115005709)
                ·
                  refine ⟨3633121644846915793127141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9688324386258442115005709 3633121644846915793127141)
                  ·
                    refine ⟨681210308408796711211339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633121644846915793127141 681210308408796711211339)
                    ·
                      rfl

theorem cell23_3979957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3979957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3979957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3979957 prefixEnd_3979957 := by exact prefixLift 3979957
  have htrace : WordTrace (prefixWord ++ tailWord_3979957) baseStart_3979957 baseEnd_3979957 := by
    simpa [prefixWord, tailWord_3979957, baseEnd_3979957] using wordTrace_append hprefix tailTrace_3979957
  have hstable : (prefixWord ++ tailWord_3979957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3979957).length < 2 ^ (prefixWord ++ tailWord_3979957).sum := by decide
  have hdescent : baseEnd_3979957 < baseStart_3979957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3979957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980014 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3980014 : Nat := 118140960795 + 3980014 * 2 ^ 59
def prefixEnd_3980014 : Nat := 4983230072969 + 3 ^ 40 * 3980014 * 2
def baseEnd_3980014 : Nat := 2043660193623696410621255

theorem tailTrace_3980014 : CollatzResearch.WordTrace tailWord_3980014 prefixEnd_3980014 2043660193623696410621255 := by
  unfold tailWord_3980014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145379525387060640007387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96775357468730990080039397 18145379525387060640007387)
  ·
    refine ⟨27218069288080590960011081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18145379525387060640007387 27218069288080590960011081)
    ·
      refine ⟨20413551966060443220008311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27218069288080590960011081 20413551966060443220008311)
      ·
        refine ⟨30620327949090664830012467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20413551966060443220008311 30620327949090664830012467)
        ·
          refine ⟨45930491923635997245018701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30620327949090664830012467 45930491923635997245018701)
          ·
            refine ⟨17223934471363498966882013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45930491923635997245018701 17223934471363498966882013)
            ·
              refine ⟨6458975426761312112580755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17223934471363498966882013 6458975426761312112580755)
              ·
                refine ⟨9688463140141968168871133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458975426761312112580755 9688463140141968168871133)
                ·
                  refine ⟨3633173677553238063326675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9688463140141968168871133 3633173677553238063326675)
                  ·
                    refine ⟨5449760516329857094990013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633173677553238063326675 5449760516329857094990013)
                    ·
                      refine ⟨2043660193623696410621255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449760516329857094990013 2043660193623696410621255)
                      ·
                        rfl

theorem cell23_3980014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3980014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980014 prefixEnd_3980014 := by exact prefixLift 3980014
  have htrace : WordTrace (prefixWord ++ tailWord_3980014) baseStart_3980014 baseEnd_3980014 := by
    simpa [prefixWord, tailWord_3980014, baseEnd_3980014] using wordTrace_append hprefix tailTrace_3980014
  have hstable : (prefixWord ++ tailWord_3980014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980014).length < 2 ^ (prefixWord ++ tailWord_3980014).sum := by decide
  have hdescent : baseEnd_3980014 < baseStart_3980014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980021 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 6]
def baseStart_3980021 : Nat := 118140960795 + 3980021 * 2 ^ 59
def prefixEnd_3980021 : Nat := 4983230072969 + 3 ^ 40 * 3980021 * 2
def baseEnd_3980021 : Nat := 227073754220919764803747

theorem tailTrace_3980021 : CollatzResearch.WordTrace tailWord_3980021 prefixEnd_3980021 227073754220919764803747 := by
  unfold tailWord_3980021
  simp only [CollatzResearch.WordTrace]
  refine ⟨145163291514071125315563917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96775527676047416877042611 145163291514071125315563917)
  ·
    refine ⟨54436234317776671993336469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145163291514071125315563917 54436234317776671993336469)
    ·
      refine ⟨2551698483645781499687647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54436234317776671993336469 2551698483645781499687647)
      ·
        refine ⟨3827547725468672249531471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551698483645781499687647 3827547725468672249531471)
        ·
          refine ⟨5741321588203008374297207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827547725468672249531471 5741321588203008374297207)
          ·
            refine ⟨8611982382304512561445811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741321588203008374297207 8611982382304512561445811)
            ·
              refine ⟨12917973573456768842168717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611982382304512561445811 12917973573456768842168717)
              ·
                refine ⟨4844240090046288315813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12917973573456768842168717 4844240090046288315813269)
                ·
                  refine ⟨227073754220919764803747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4844240090046288315813269 227073754220919764803747)
                  ·
                    rfl

theorem cell23_3980021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_3980021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980021 prefixEnd_3980021 := by exact prefixLift 3980021
  have htrace : WordTrace (prefixWord ++ tailWord_3980021) baseStart_3980021 baseEnd_3980021 := by
    simpa [prefixWord, tailWord_3980021, baseEnd_3980021] using wordTrace_append hprefix tailTrace_3980021
  have hstable : (prefixWord ++ tailWord_3980021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980021).length < 2 ^ (prefixWord ++ tailWord_3980021).sum := by decide
  have hdescent : baseEnd_3980021 < baseStart_3980021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980034 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3980034 : Nat := 118140960795 + 3980034 * 2 ^ 59
def prefixEnd_3980034 : Nat := 4983230072969 + 3 ^ 40 * 3980034 * 2
def baseEnd_3980034 : Nat := 681223487745595444123721

theorem tailTrace_3980034 : CollatzResearch.WordTrace tailWord_3980034 prefixEnd_3980034 681223487745595444123721 := by
  unfold tailWord_3980034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36290941415756007133946789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96775843775349352357191437 36290941415756007133946789)
  ·
    refine ⟨6804551515454251337615023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36290941415756007133946789 6804551515454251337615023)
    ·
      refine ⟨10206827273181377006422535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804551515454251337615023 10206827273181377006422535)
      ·
        refine ⟨15310240909772065509633803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206827273181377006422535 15310240909772065509633803)
        ·
          refine ⟨22965361364658098264450705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15310240909772065509633803 22965361364658098264450705)
          ·
            refine ⟨17224021023493573698338029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22965361364658098264450705 17224021023493573698338029)
            ·
              refine ⟨6459007883810090136876761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17224021023493573698338029 6459007883810090136876761)
              ·
                refine ⟨4844255912857567602657571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459007883810090136876761 4844255912857567602657571)
                ·
                  refine ⟨7266383869286351403986357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844255912857567602657571 7266383869286351403986357)
                  ·
                    refine ⟨681223487745595444123721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7266383869286351403986357 681223487745595444123721)
                    ·
                      rfl

theorem cell23_3980034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3980034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980034 prefixEnd_3980034 := by exact prefixLift 3980034
  have htrace : WordTrace (prefixWord ++ tailWord_3980034) baseStart_3980034 baseEnd_3980034 := by
    simpa [prefixWord, tailWord_3980034, baseEnd_3980034] using wordTrace_append hprefix tailTrace_3980034
  have hstable : (prefixWord ++ tailWord_3980034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980034).length < 2 ^ (prefixWord ++ tailWord_3980034).sum := by decide
  have hdescent : baseEnd_3980034 < baseStart_3980034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980064 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_3980064 : Nat := 118140960795 + 3980064 * 2 ^ 59
def prefixEnd_3980064 : Nat := 4983230072969 + 3 ^ 40 * 3980064 * 2
def baseEnd_3980064 : Nat := 681228622552140404998675

theorem tailTrace_3980064 : CollatzResearch.WordTrace tailWord_3980064 prefixEnd_3980064 681228622552140404998675 := by
  unfold tailWord_3980064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72582429926457671829689623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96776573235276895772919497 72582429926457671829689623)
  ·
    refine ⟨108873644889686507744534435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72582429926457671829689623 108873644889686507744534435)
    ·
      refine ⟨163310467334529761616801653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108873644889686507744534435 163310467334529761616801653)
      ·
        refine ⟨15310356312612165151575155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163310467334529761616801653 15310356312612165151575155)
        ·
          refine ⟨22965534468918247727362733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15310356312612165151575155 22965534468918247727362733)
          ·
            refine ⟨8612075425844342897761025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22965534468918247727362733 8612075425844342897761025)
            ·
              refine ⟨6459056569383257173320769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8612075425844342897761025 6459056569383257173320769)
              ·
                refine ⟨4844292427037442879990577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459056569383257173320769 4844292427037442879990577)
                ·
                  refine ⟨3633219320278082159992933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844292427037442879990577 3633219320278082159992933)
                  ·
                    refine ⟨681228622552140404998675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633219320278082159992933 681228622552140404998675)
                    ·
                      rfl

theorem cell23_3980064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_3980064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980064 prefixEnd_3980064 := by exact prefixLift 3980064
  have htrace : WordTrace (prefixWord ++ tailWord_3980064) baseStart_3980064 baseEnd_3980064 := by
    simpa [prefixWord, tailWord_3980064, baseEnd_3980064] using wordTrace_append hprefix tailTrace_3980064
  have hstable : (prefixWord ++ tailWord_3980064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980064).length < 2 ^ (prefixWord ++ tailWord_3980064).sum := by decide
  have hdescent : baseEnd_3980064 < baseStart_3980064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980087 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_3980087 : Nat := 118140960795 + 3980087 * 2 ^ 59
def prefixEnd_3980087 : Nat := 4983230072969 + 3 ^ 40 * 3980087 * 2
def baseEnd_3980087 : Nat := 2043697677711474625008419

theorem tailTrace_3980087 : CollatzResearch.WordTrace tailWord_3980087 prefixEnd_3980087 2043697677711474625008419 := by
  unfold tailWord_3980087
  simp only [CollatzResearch.WordTrace]
  refine ⟨145165698731832018587466515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96777132487888012391644343 145165698731832018587466515)
  ·
    refine ⟨217748548097748027881199773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145165698731832018587466515 217748548097748027881199773)
    ·
      refine ⟨81655705536655510455449915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217748548097748027881199773 81655705536655510455449915)
      ·
        refine ⟨122483558304983265683174873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81655705536655510455449915 122483558304983265683174873)
        ·
          refine ⟨91862668728737449262381155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122483558304983265683174873 91862668728737449262381155)
          ·
            refine ⟨137794003093106173893571733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91862668728737449262381155 137794003093106173893571733)
            ·
              refine ⟨6459093894989351901261175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137794003093106173893571733 6459093894989351901261175)
              ·
                refine ⟨9688640842484027851891763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459093894989351901261175 9688640842484027851891763)
                ·
                  refine ⟨14532961263726041777837645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688640842484027851891763 14532961263726041777837645)
                  ·
                    refine ⟨5449860473897265666689117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14532961263726041777837645 5449860473897265666689117)
                    ·
                      refine ⟨2043697677711474625008419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449860473897265666689117 2043697677711474625008419)
                      ·
                        rfl

theorem cell23_3980087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_3980087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980087 prefixEnd_3980087 := by exact prefixLift 3980087
  have htrace : WordTrace (prefixWord ++ tailWord_3980087) baseStart_3980087 baseEnd_3980087 := by
    simpa [prefixWord, tailWord_3980087, baseEnd_3980087] using wordTrace_append hprefix tailTrace_3980087
  have hstable : (prefixWord ++ tailWord_3980087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980087).length < 2 ^ (prefixWord ++ tailWord_3980087).sum := by decide
  have hdescent : baseEnd_3980087 < baseStart_3980087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980094 : List Nat := [4, 2, 1, 2, 3, 1, 3, 7]
def baseStart_3980094 : Nat := 118140960795 + 3980094 * 2 ^ 59
def prefixEnd_3980094 : Nat := 4983230072969 + 3 ^ 40 * 3980094 * 2
def baseEnd_3980094 : Nat := 75692639706520596208181

theorem tailTrace_3980094 : CollatzResearch.WordTrace tailWord_3980094 prefixEnd_3980094 75692639706520596208181 := by
  unfold tailWord_3980094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145744255350832347871417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96777302695204439188647557 18145744255350832347871417)
  ·
    refine ⟨13609308191513124260903563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18145744255350832347871417 13609308191513124260903563)
    ·
      refine ⟨20413962287269686391355345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13609308191513124260903563 20413962287269686391355345)
      ·
        refine ⟨15310471715452264793516509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20413962287269686391355345 15310471715452264793516509)
        ·
          refine ⟨5741426893294599297568691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15310471715452264793516509 5741426893294599297568691)
          ·
            refine ⟨8612140339941898946353037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741426893294599297568691 8612140339941898946353037)
            ·
              refine ⟨3229552627478212104882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8612140339941898946353037 3229552627478212104882389)
              ·
                refine ⟨75692639706520596208181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3229552627478212104882389 75692639706520596208181)
                ·
                  rfl

theorem cell23_3980094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_3980094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980094 prefixEnd_3980094 := by exact prefixLift 3980094
  have htrace : WordTrace (prefixWord ++ tailWord_3980094) baseStart_3980094 baseEnd_3980094 := by
    simpa [prefixWord, tailWord_3980094, baseEnd_3980094] using wordTrace_append hprefix tailTrace_3980094
  have hstable : (prefixWord ++ tailWord_3980094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980094).length < 2 ^ (prefixWord ++ tailWord_3980094).sum := by decide
  have hdescent : baseEnd_3980094 < baseStart_3980094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980121 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_3980121 : Nat := 118140960795 + 3980121 * 2 ^ 59
def prefixEnd_3980121 : Nat := 4983230072969 + 3 ^ 40 * 3980121 * 2
def baseEnd_3980121 : Nat := 2043715136053727491983263

theorem tailTrace_3980121 : CollatzResearch.WordTrace tailWord_3980121 prefixEnd_3980121 2043715136053727491983263 := by
  unfold tailWord_3980121
  simp only [CollatzResearch.WordTrace]
  refine ⟨145166938813708842394204217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96777959209139228262802811 145166938813708842394204217)
  ·
    refine ⟨108875204110281631795653163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145166938813708842394204217 108875204110281631795653163)
    ·
      refine ⟨163312806165422447693479745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108875204110281631795653163 163312806165422447693479745)
      ·
        refine ⟨122484604624066835770109809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163312806165422447693479745 122484604624066835770109809)
        ·
          refine ⟨91863453468050126827582357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122484604624066835770109809 91863453468050126827582357)
          ·
            refine ⟨4306099381314849695042923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91863453468050126827582357 4306099381314849695042923)
            ·
              refine ⟨6459149071972274542564385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306099381314849695042923 6459149071972274542564385)
              ·
                refine ⟨4844361803979205906923289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459149071972274542564385 4844361803979205906923289)
                ·
                  refine ⟨3633271352984404430192467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4844361803979205906923289 3633271352984404430192467)
                  ·
                    refine ⟨5449907029476606645288701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633271352984404430192467 5449907029476606645288701)
                    ·
                      refine ⟨2043715136053727491983263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5449907029476606645288701 2043715136053727491983263)
                      ·
                        rfl

theorem cell23_3980121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_3980121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980121 prefixEnd_3980121 := by exact prefixLift 3980121
  have htrace : WordTrace (prefixWord ++ tailWord_3980121) baseStart_3980121 baseEnd_3980121 := by
    simpa [prefixWord, tailWord_3980121, baseEnd_3980121] using wordTrace_append hprefix tailTrace_3980121
  have hstable : (prefixWord ++ tailWord_3980121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980121).length < 2 ^ (prefixWord ++ tailWord_3980121).sum := by decide
  have hdescent : baseEnd_3980121 < baseStart_3980121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980144 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2]
def baseStart_3980144 : Nat := 118140960795 + 3980144 * 2 ^ 59
def prefixEnd_3980144 : Nat := 4983230072969 + 3 ^ 40 * 3980144 * 2
def baseEnd_3980144 : Nat := 2043726946108780901995657

theorem tailTrace_3980144 : CollatzResearch.WordTrace tailWord_3980144 prefixEnd_3980144 2043726946108780901995657 := by
  unfold tailWord_3980144
  simp only [CollatzResearch.WordTrace]
  refine ⟨72583888846312758661145743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96778518461750344881527657 72583888846312758661145743)
  ·
    refine ⟨108875833269469137991718615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72583888846312758661145743 108875833269469137991718615)
    ·
      refine ⟨163313749904203706987577923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108875833269469137991718615 163313749904203706987577923)
      ·
        refine ⟨244970624856305560481366885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163313749904203706987577923 244970624856305560481366885)
        ·
          refine ⟨45931992160557292590256291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244970624856305560481366885 45931992160557292590256291)
          ·
            refine ⟨68897988240835938885384437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45931992160557292590256291 68897988240835938885384437)
            ·
              refine ⟨6459186397578369270504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68897988240835938885384437 6459186397578369270504791)
              ·
                refine ⟨9688779596367553905757187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459186397578369270504791 9688779596367553905757187)
                ·
                  refine ⟨14533169394551330858635781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688779596367553905757187 14533169394551330858635781)
                  ·
                    refine ⟨2724969261478374535994209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14533169394551330858635781 2724969261478374535994209)
                    ·
                      refine ⟨2043726946108780901995657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2724969261478374535994209 2043726946108780901995657)
                      ·
                        rfl

theorem cell23_3980144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2].length) (baseStart_3980144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980144 prefixEnd_3980144 := by exact prefixLift 3980144
  have htrace : WordTrace (prefixWord ++ tailWord_3980144) baseStart_3980144 baseEnd_3980144 := by
    simpa [prefixWord, tailWord_3980144, baseEnd_3980144] using wordTrace_append hprefix tailTrace_3980144
  have hstable : (prefixWord ++ tailWord_3980144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980144).length < 2 ^ (prefixWord ++ tailWord_3980144).sum := by decide
  have hdescent : baseEnd_3980144 < baseStart_3980144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980227 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 5, 4]
def baseStart_3980227 : Nat := 118140960795 + 3980227 * 2 ^ 59
def prefixEnd_3980227 : Nat := 4983230072969 + 3 ^ 40 * 3980227 * 2
def baseEnd_3980227 : Nat := 681256521667701359085925

theorem tailTrace_3980227 : CollatzResearch.WordTrace tailWord_3980227 prefixEnd_3980227 681256521667701359085925 := by
  unfold tailWord_3980227
  simp only [CollatzResearch.WordTrace]
  refine ⟨145170804951324822497562935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96780536634216548331708623 145170804951324822497562935)
  ·
    refine ⟨217756207426987233746344403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145170804951324822497562935 217756207426987233746344403)
    ·
      refine ⟨326634311140480850619516605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217756207426987233746344403 326634311140480850619516605)
      ·
        refine ⟨122487866677680318982318727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326634311140480850619516605 122487866677680318982318727)
        ·
          refine ⟨183731800016520478473478091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122487866677680318982318727 183731800016520478473478091)
          ·
            refine ⟨275597700024780717710217137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183731800016520478473478091 275597700024780717710217137)
            ·
              refine ⟨206698275018585538282662853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275597700024780717710217137 206698275018585538282662853)
              ·
                refine ⟨38755926565984788427999285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206698275018585538282662853 38755926565984788427999285)
                ·
                  refine ⟨3633368115561073915124933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38755926565984788427999285 3633368115561073915124933)
                  ·
                    refine ⟨681256521667701359085925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633368115561073915124933 681256521667701359085925)
                    ·
                      rfl

theorem cell23_3980227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 4].length) (baseStart_3980227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980227 prefixEnd_3980227 := by exact prefixLift 3980227
  have htrace : WordTrace (prefixWord ++ tailWord_3980227) baseStart_3980227 baseEnd_3980227 := by
    simpa [prefixWord, tailWord_3980227, baseEnd_3980227] using wordTrace_append hprefix tailTrace_3980227
  have hstable : (prefixWord ++ tailWord_3980227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980227).length < 2 ^ (prefixWord ++ tailWord_3980227).sum := by decide
  have hdescent : baseEnd_3980227 < baseStart_3980227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980234 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_3980234 : Nat := 118140960795 + 3980234 * 2 ^ 59
def prefixEnd_3980234 : Nat := 4983230072969 + 3 ^ 40 * 3980234 * 2
def baseEnd_3980234 : Nat := 2043773159367685549870243

theorem tailTrace_3980234 : CollatzResearch.WordTrace tailWord_3980234 prefixEnd_3980234 2043773159367685549870243 := by
  unfold tailWord_3980234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36292765065574865673266939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96780706841532975128711837 36292765065574865673266939)
  ·
    refine ⟨54439147598362298509900409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36292765065574865673266939 54439147598362298509900409)
    ·
      refine ⟨40829360698771723882425307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54439147598362298509900409 40829360698771723882425307)
      ·
        refine ⟨61244041048157585823637961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40829360698771723882425307 61244041048157585823637961)
        ·
          refine ⟨45933030786118189367728471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61244041048157585823637961 45933030786118189367728471)
          ·
            refine ⟨68899546179177284051592707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45933030786118189367728471 68899546179177284051592707)
            ·
              refine ⟨103349319268765926077389061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68899546179177284051592707 103349319268765926077389061)
              ·
                refine ⟨19377997362893611139510449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103349319268765926077389061 19377997362893611139510449)
                ·
                  refine ⟨14533498022170208354632837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19377997362893611139510449 14533498022170208354632837)
                  ·
                    refine ⟨2725030879156914066493657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14533498022170208354632837 2725030879156914066493657)
                    ·
                      refine ⟨2043773159367685549870243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725030879156914066493657 2043773159367685549870243)
                      ·
                        rfl

theorem cell23_3980234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_3980234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980234 prefixEnd_3980234 := by exact prefixLift 3980234
  have htrace : WordTrace (prefixWord ++ tailWord_3980234) baseStart_3980234 baseEnd_3980234 := by
    simpa [prefixWord, tailWord_3980234, baseEnd_3980234] using wordTrace_append hprefix tailTrace_3980234
  have hstable : (prefixWord ++ tailWord_3980234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980234).length < 2 ^ (prefixWord ++ tailWord_3980234).sum := by decide
  have hdescent : baseEnd_3980234 < baseStart_3980234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980271 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_3980271 : Nat := 118140960795 + 3980271 * 2 ^ 59
def prefixEnd_3980271 : Nat := 4983230072969 + 3 ^ 40 * 3980271 * 2
def baseEnd_3980271 : Nat := 2043792158151901905107573

theorem tailTrace_3980271 : CollatzResearch.WordTrace tailWord_3980271 prefixEnd_3980271 2043792158151901905107573 := by
  unfold tailWord_3980271
  simp only [CollatzResearch.WordTrace]
  refine ⟨145172409763165418012164667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96781606508776945341443111 145172409763165418012164667)
  ·
    refine ⟨217758614644748127018247001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145172409763165418012164667 217758614644748127018247001)
    ·
      refine ⟨163318960983561095263685251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217758614644748127018247001 163318960983561095263685251)
      ·
        refine ⟨244978441475341642895527877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163318960983561095263685251 244978441475341642895527877)
        ·
          refine ⟨45933457776626558042911477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244978441475341642895527877 45933457776626558042911477)
          ·
            refine ⟨4306261666558739816522951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45933457776626558042911477 4306261666558739816522951)
            ·
              refine ⟨6459392499838109724784427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306261666558739816522951 6459392499838109724784427)
              ·
                refine ⟨9689088749757164587176641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459392499838109724784427 9689088749757164587176641)
                ·
                  refine ⟨7266816562317873440382481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689088749757164587176641 7266816562317873440382481)
                  ·
                    refine ⟨5450112421738405080286861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7266816562317873440382481 5450112421738405080286861)
                    ·
                      refine ⟨2043792158151901905107573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450112421738405080286861 2043792158151901905107573)
                      ·
                        rfl

theorem cell23_3980271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_3980271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980271 prefixEnd_3980271 := by exact prefixLift 3980271
  have htrace : WordTrace (prefixWord ++ tailWord_3980271) baseStart_3980271 baseEnd_3980271 := by
    simpa [prefixWord, tailWord_3980271, baseEnd_3980271] using wordTrace_append hprefix tailTrace_3980271
  have hstable : (prefixWord ++ tailWord_3980271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980271).length < 2 ^ (prefixWord ++ tailWord_3980271).sum := by decide
  have hdescent : baseEnd_3980271 < baseStart_3980271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980278 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3980278 : Nat := 118140960795 + 3980278 * 2 ^ 59
def prefixEnd_3980278 : Nat := 4983230072969 + 3 ^ 40 * 3980278 * 2
def baseEnd_3980278 : Nat := 681265250838827792573347

theorem tailTrace_3980278 : CollatzResearch.WordTrace tailWord_3980278 prefixEnd_3980278 681265250838827792573347 := by
  unfold tailWord_3980278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073291567133753637979343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96781776716093372138446325 9073291567133753637979343)
  ·
    refine ⟨13609937350700630456969015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9073291567133753637979343 13609937350700630456969015)
    ·
      refine ⟨20414906026050945685453523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13609937350700630456969015 20414906026050945685453523)
      ·
        refine ⟨30622359039076418528180285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20414906026050945685453523 30622359039076418528180285)
        ·
          refine ⟨11483384639653656948067607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30622359039076418528180285 11483384639653656948067607)
          ·
            refine ⟨17225076959480485422101411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483384639653656948067607 17225076959480485422101411)
            ·
              refine ⟨25837615439220728133152117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225076959480485422101411 25837615439220728133152117)
              ·
                refine ⟨2422276447426943262483011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25837615439220728133152117 2422276447426943262483011)
                ·
                  refine ⟨3633414671140414893724517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422276447426943262483011 3633414671140414893724517)
                  ·
                    refine ⟨681265250838827792573347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633414671140414893724517 681265250838827792573347)
                    ·
                      rfl

theorem cell23_3980278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3980278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980278 prefixEnd_3980278 := by exact prefixLift 3980278
  have htrace : WordTrace (prefixWord ++ tailWord_3980278) baseStart_3980278 baseEnd_3980278 := by
    simpa [prefixWord, tailWord_3980278, baseEnd_3980278] using wordTrace_append hprefix tailTrace_3980278
  have hstable : (prefixWord ++ tailWord_3980278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980278).length < 2 ^ (prefixWord ++ tailWord_3980278).sum := by decide
  have hdescent : baseEnd_3980278 < baseStart_3980278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980311 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3980311 : Nat := 118140960795 + 3980311 * 2 ^ 59
def prefixEnd_3980311 : Nat := 4983230072969 + 3 ^ 40 * 3980311 * 2
def baseEnd_3980311 : Nat := 2043812697378081748607389

theorem tailTrace_3980311 : CollatzResearch.WordTrace tailWord_3980311 prefixEnd_3980311 2043812697378081748607389 := by
  unfold tailWord_3980311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145173868683020504843620787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96782579122013669895747191 145173868683020504843620787)
  ·
    refine ⟨217760803024530757265431181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145173868683020504843620787 217760803024530757265431181)
    ·
      refine ⟨81660301134199033974536693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217760803024530757265431181 81660301134199033974536693)
      ·
        refine ⟨7655653231331159435112815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81660301134199033974536693 7655653231331159435112815)
        ·
          refine ⟨11483479846996739152669223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655653231331159435112815 11483479846996739152669223)
          ·
            refine ⟨17225219770495108729003835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483479846996739152669223 17225219770495108729003835)
            ·
              refine ⟨25837829655742663093505753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225219770495108729003835 25837829655742663093505753)
              ·
                refine ⟨19378372241806997320129315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25837829655742663093505753 19378372241806997320129315)
                ·
                  refine ⟨29067558362710495980193973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19378372241806997320129315 29067558362710495980193973)
                  ·
                    refine ⟨2725083596504108998143185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29067558362710495980193973 2725083596504108998143185)
                    ·
                      refine ⟨2043812697378081748607389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725083596504108998143185 2043812697378081748607389)
                      ·
                        rfl

theorem cell23_3980311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3980311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980311 prefixEnd_3980311 := by exact prefixLift 3980311
  have htrace : WordTrace (prefixWord ++ tailWord_3980311) baseStart_3980311 baseEnd_3980311 := by
    simpa [prefixWord, tailWord_3980311, baseEnd_3980311] using wordTrace_append hprefix tailTrace_3980311
  have hstable : (prefixWord ++ tailWord_3980311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980311).length < 2 ^ (prefixWord ++ tailWord_3980311).sum := by decide
  have hdescent : baseEnd_3980311 < baseStart_3980311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980321 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3980321 : Nat := 118140960795 + 3980321 * 2 ^ 59
def prefixEnd_3980321 : Nat := 4983230072969 + 3 ^ 40 * 3980321 * 2
def baseEnd_3980321 : Nat := 681272610728208903160781

theorem tailTrace_3980321 : CollatzResearch.WordTrace tailWord_3980321 prefixEnd_3980321 681272610728208903160781 := by
  unfold tailWord_3980321
  simp only [CollatzResearch.WordTrace]
  refine ⟨145174233412984276551484817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96782822275322851034323211 145174233412984276551484817)
  ·
    refine ⟨108880675059738207413613613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145174233412984276551484817 108880675059738207413613613)
    ·
      refine ⟨40830253147401827780105105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108880675059738207413613613 40830253147401827780105105)
      ·
        refine ⟨30622689860551370835078829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40830253147401827780105105 30622689860551370835078829)
        ·
          refine ⟨11483508697706764063154561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30622689860551370835078829 11483508697706764063154561)
          ·
            refine ⟨8612631523280073047365921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483508697706764063154561 8612631523280073047365921)
            ·
              refine ⟨6459473642460054785524441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8612631523280073047365921 6459473642460054785524441)
              ·
                refine ⟨4844605231845041089143331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459473642460054785524441 4844605231845041089143331)
                ·
                  refine ⟨7266907847767561633714997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844605231845041089143331 7266907847767561633714997)
                  ·
                    refine ⟨681272610728208903160781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7266907847767561633714997 681272610728208903160781)
                    ·
                      rfl

theorem cell23_3980321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3980321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980321 prefixEnd_3980321 := by exact prefixLift 3980321
  have htrace : WordTrace (prefixWord ++ tailWord_3980321) baseStart_3980321 baseEnd_3980321 := by
    simpa [prefixWord, tailWord_3980321, baseEnd_3980321] using wordTrace_append hprefix tailTrace_3980321
  have hstable : (prefixWord ++ tailWord_3980321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980321).length < 2 ^ (prefixWord ++ tailWord_3980321).sum := by decide
  have hdescent : baseEnd_3980321 < baseStart_3980321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980334 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3980334 : Nat := 118140960795 + 3980334 * 2 ^ 59
def prefixEnd_3980334 : Nat := 4983230072969 + 3 ^ 40 * 3980334 * 2
def baseEnd_3980334 : Nat := 681274835811045052873261

theorem tailTrace_3980334 : CollatzResearch.WordTrace tailWord_3980334 prefixEnd_3980334 681274835811045052873261 := by
  unfold tailWord_3980334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146838445242147471463507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96783138374624786514472037 18146838445242147471463507)
  ·
    refine ⟨27220257667863221207195261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18146838445242147471463507 27220257667863221207195261)
    ·
      refine ⟨10207596625448707952698223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27220257667863221207195261 10207596625448707952698223)
      ·
        refine ⟨15311394938173061929047335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207596625448707952698223 15311394938173061929047335)
        ·
          refine ⟨22967092407259592893571003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311394938173061929047335 22967092407259592893571003)
          ·
            refine ⟨34450638610889389340356505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967092407259592893571003 34450638610889389340356505)
            ·
              refine ⟨25837978958167042005267379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34450638610889389340356505 25837978958167042005267379)
              ·
                refine ⟨38756968437250563007901069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25837978958167042005267379 38756968437250563007901069)
                ·
                  refine ⟨14533863163968961127962901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38756968437250563007901069 14533863163968961127962901)
                  ·
                    refine ⟨681274835811045052873261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14533863163968961127962901 681274835811045052873261)
                    ·
                      rfl

theorem cell23_3980334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3980334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980334 prefixEnd_3980334 := by exact prefixLift 3980334
  have htrace : WordTrace (prefixWord ++ tailWord_3980334) baseStart_3980334 baseEnd_3980334 := by
    simpa [prefixWord, tailWord_3980334, baseEnd_3980334] using wordTrace_append hprefix tailTrace_3980334
  have hstable : (prefixWord ++ tailWord_3980334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980334).length < 2 ^ (prefixWord ++ tailWord_3980334).sum := by decide
  have hdescent : baseEnd_3980334 < baseStart_3980334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980344 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_3980344 : Nat := 118140960795 + 3980344 * 2 ^ 59
def prefixEnd_3980344 : Nat := 4983230072969 + 3 ^ 40 * 3980344 * 2
def baseEnd_3980344 : Nat := 2043829642239680119494737

theorem tailTrace_3980344 : CollatzResearch.WordTrace tailWord_3980344 prefixEnd_3980344 2043829642239680119494737 := by
  unfold tailWord_3980344
  simp only [CollatzResearch.WordTrace]
  refine ⟨72587536145950475739786043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96783381527933967653048057 72587536145950475739786043)
  ·
    refine ⟨108881304218925713609679065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72587536145950475739786043 108881304218925713609679065)
    ·
      refine ⟨81660978164194285207259299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108881304218925713609679065 81660978164194285207259299)
      ·
        refine ⟨122491467246291427810888949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81660978164194285207259299 122491467246291427810888949)
        ·
          refine ⟨11483575054339821357270839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122491467246291427810888949 11483575054339821357270839)
          ·
            refine ⟨17225362581509732035906259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483575054339821357270839 17225362581509732035906259)
            ·
              refine ⟨25838043872264598053859389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225362581509732035906259 25838043872264598053859389)
              ·
                refine ⟨9689266452099224270197271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25838043872264598053859389 9689266452099224270197271)
                ·
                  refine ⟨14533899678148836405295907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9689266452099224270197271 14533899678148836405295907)
                  ·
                    refine ⟨21800849517223254607943861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14533899678148836405295907 21800849517223254607943861)
                    ·
                      refine ⟨2043829642239680119494737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21800849517223254607943861 2043829642239680119494737)
                      ·
                        rfl

theorem cell23_3980344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_3980344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980344 prefixEnd_3980344 := by exact prefixLift 3980344
  have htrace : WordTrace (prefixWord ++ tailWord_3980344) baseStart_3980344 baseEnd_3980344 := by
    simpa [prefixWord, tailWord_3980344, baseEnd_3980344] using wordTrace_append hprefix tailTrace_3980344
  have hstable : (prefixWord ++ tailWord_3980344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980344).length < 2 ^ (prefixWord ++ tailWord_3980344).sum := by decide
  have hdescent : baseEnd_3980344 < baseStart_3980344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980377 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_3980377 : Nat := 118140960795 + 3980377 * 2 ^ 59
def prefixEnd_3980377 : Nat := 4983230072969 + 3 ^ 40 * 3980377 * 2
def baseEnd_3980377 : Nat := 681282195700426163460695

theorem tailTrace_3980377 : CollatzResearch.WordTrace tailWord_3980377 prefixEnd_3980377 681282195700426163460695 := by
  unfold tailWord_3980377
  simp only [CollatzResearch.WordTrace]
  refine ⟨145176275900781398115523385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96784183933854265410348923 145176275900781398115523385)
  ·
    refine ⟨108882206925586048586642539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145176275900781398115523385 108882206925586048586642539)
    ·
      refine ⟨163323310388379072879963809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108882206925586048586642539 163323310388379072879963809)
      ·
        refine ⟨122492482791284304659972857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163323310388379072879963809 122492482791284304659972857)
        ·
          refine ⟨91869362093463228494979643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122492482791284304659972857 91869362093463228494979643)
          ·
            refine ⟨137804043140194842742469465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91869362093463228494979643 137804043140194842742469465)
            ·
              refine ⟨103353032355146132056852099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137804043140194842742469465 103353032355146132056852099)
              ·
                refine ⟨155029548532719198085278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103353032355146132056852099 155029548532719198085278149)
                ·
                  refine ⟨29068040349884849640989653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155029548532719198085278149 29068040349884849640989653)
                  ·
                    refine ⟨681282195700426163460695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29068040349884849640989653 681282195700426163460695)
                    ·
                      rfl

theorem cell23_3980377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_3980377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980377 prefixEnd_3980377 := by exact prefixLift 3980377
  have htrace : WordTrace (prefixWord ++ tailWord_3980377) baseStart_3980377 baseEnd_3980377 := by
    simpa [prefixWord, tailWord_3980377, baseEnd_3980377] using wordTrace_append hprefix tailTrace_3980377
  have hstable : (prefixWord ++ tailWord_3980377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980377).length < 2 ^ (prefixWord ++ tailWord_3980377).sum := by decide
  have hdescent : baseEnd_3980377 < baseStart_3980377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980391 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3980391 : Nat := 118140960795 + 3980391 * 2 ^ 59
def prefixEnd_3980391 : Nat := 4983230072969 + 3 ^ 40 * 3980391 * 2
def baseEnd_3980391 : Nat := 2043853775830441435607021

theorem tailTrace_3980391 : CollatzResearch.WordTrace tailWord_3980391 prefixEnd_3980391 2043853775830441435607021 := by
  unfold tailWord_3980391
  simp only [CollatzResearch.WordTrace]
  refine ⟨145176786522730678506533027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96784524348487119004355351 145176786522730678506533027)
  ·
    refine ⟨217765179784096017759799541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145176786522730678506533027 217765179784096017759799541)
    ·
      refine ⟨20415485604759001664981207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217765179784096017759799541 20415485604759001664981207)
      ·
        refine ⟨30623228407138502497471811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20415485604759001664981207 30623228407138502497471811)
        ·
          refine ⟨45934842610707753746207717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30623228407138502497471811 45934842610707753746207717)
          ·
            refine ⟨8612782989507703827413947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45934842610707753746207717 8612782989507703827413947)
            ·
              refine ⟨12919174484261555741120921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612782989507703827413947 12919174484261555741120921)
              ·
                refine ⟨9689380863196166805840691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12919174484261555741120921 9689380863196166805840691)
                ·
                  refine ⟨14534071294794250208761037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9689380863196166805840691 14534071294794250208761037)
                  ·
                    refine ⟨5450276735547843828285389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14534071294794250208761037 5450276735547843828285389)
                    ·
                      refine ⟨2043853775830441435607021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450276735547843828285389 2043853775830441435607021)
                      ·
                        rfl

theorem cell23_3980391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3980391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980391 prefixEnd_3980391 := by exact prefixLift 3980391
  have htrace : WordTrace (prefixWord ++ tailWord_3980391) baseStart_3980391 baseEnd_3980391 := by
    simpa [prefixWord, tailWord_3980391, baseEnd_3980391] using wordTrace_append hprefix tailTrace_3980391
  have hstable : (prefixWord ++ tailWord_3980391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980391).length < 2 ^ (prefixWord ++ tailWord_3980391).sum := by decide
  have hdescent : baseEnd_3980391 < baseStart_3980391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980409 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 1, 2, 2]
def baseStart_3980409 : Nat := 118140960795 + 3980409 * 2 ^ 59
def prefixEnd_3980409 : Nat := 4983230072969 + 3 ^ 40 * 3980409 * 2
def baseEnd_3980409 : Nat := 2043863018482222365181939

theorem tailTrace_3980409 : CollatzResearch.WordTrace tailWord_3980409 prefixEnd_3980409 2043863018482222365181939 := by
  unfold tailWord_3980409
  simp only [CollatzResearch.WordTrace]
  refine ⟨145177443036665467580688281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96784962024443645053792187 145177443036665467580688281)
  ·
    refine ⟨108883082277499100685516211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145177443036665467580688281 108883082277499100685516211)
    ·
      refine ⟨163324623416248651028274317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108883082277499100685516211 163324623416248651028274317)
      ·
        refine ⟨61246733781093244135602869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163324623416248651028274317 61246733781093244135602869)
        ·
          refine ⟨5741881291977491637712769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61246733781093244135602869 5741881291977491637712769)
          ·
            refine ⟨4306410968983118728284577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741881291977491637712769 4306410968983118728284577)
            ·
              refine ⟨3229808226737339046213433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306410968983118728284577 3229808226737339046213433)
              ·
                refine ⟨2422356170053004284660075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229808226737339046213433 2422356170053004284660075)
                ·
                  refine ⟨3633534255079506426990113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422356170053004284660075 3633534255079506426990113)
                  ·
                    refine ⟨2725150691309629820242585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633534255079506426990113 2725150691309629820242585)
                    ·
                      refine ⟨2043863018482222365181939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725150691309629820242585 2043863018482222365181939)
                      ·
                        rfl

theorem cell23_3980409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_3980409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980409 prefixEnd_3980409 := by exact prefixLift 3980409
  have htrace : WordTrace (prefixWord ++ tailWord_3980409) baseStart_3980409 baseEnd_3980409 := by
    simpa [prefixWord, tailWord_3980409, baseEnd_3980409] using wordTrace_append hprefix tailTrace_3980409
  have hstable : (prefixWord ++ tailWord_3980409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980409).length < 2 ^ (prefixWord ++ tailWord_3980409).sum := by decide
  have hdescent : baseEnd_3980409 < baseStart_3980409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980448 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2]
def baseStart_3980448 : Nat := 118140960795 + 3980448 * 2 ^ 59
def prefixEnd_3980448 : Nat := 4983230072969 + 3 ^ 40 * 3980448 * 2
def baseEnd_3980448 : Nat := 2043883044227747712594259

theorem tailTrace_3980448 : CollatzResearch.WordTrace tailWord_3980448 prefixEnd_3980448 2043883044227747712594259 := by
  unfold tailWord_3980448
  simp only [CollatzResearch.WordTrace]
  refine ⟨72589432741762088620678999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96785910322349451494238665 72589432741762088620678999)
  ·
    refine ⟨108884149112643132931018499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72589432741762088620678999 108884149112643132931018499)
    ·
      refine ⟨163326223668964699396527749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108884149112643132931018499 163326223668964699396527749)
      ·
        refine ⟨30623666937930881136848953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163326223668964699396527749 30623666937930881136848953)
        ·
          refine ⟨22967750203448160852636715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30623666937930881136848953 22967750203448160852636715)
          ·
            refine ⟨34451625305172241278955073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967750203448160852636715 34451625305172241278955073)
            ·
              refine ⟨25838718978879180959216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34451625305172241278955073 25838718978879180959216305)
              ·
                refine ⟨19379039234159385719412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25838718978879180959216305 19379039234159385719412229)
                ·
                  refine ⟨3633569856404884822389793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19379039234159385719412229 3633569856404884822389793)
                  ·
                    refine ⟨2725177392303663616792345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633569856404884822389793 2725177392303663616792345)
                    ·
                      refine ⟨2043883044227747712594259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725177392303663616792345 2043883044227747712594259)
                      ·
                        rfl

theorem cell23_3980448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_3980448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980448 prefixEnd_3980448 := by exact prefixLift 3980448
  have htrace : WordTrace (prefixWord ++ tailWord_3980448) baseStart_3980448 baseEnd_3980448 := by
    simpa [prefixWord, tailWord_3980448, baseEnd_3980448] using wordTrace_append hprefix tailTrace_3980448
  have hstable : (prefixWord ++ tailWord_3980448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980448).length < 2 ^ (prefixWord ++ tailWord_3980448).sum := by decide
  have hdescent : baseEnd_3980448 < baseStart_3980448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980452 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_3980452 : Nat := 118140960795 + 3980452 * 2 ^ 59
def prefixEnd_3980452 : Nat := 4983230072969 + 3 ^ 40 * 3980452 * 2
def baseEnd_3980452 : Nat := 2043885098150365696944241

theorem tailTrace_3980452 : CollatzResearch.WordTrace tailWord_3980452 prefixEnd_3980452 2043885098150365696944241 := by
  unfold tailWord_3980452
  simp only [CollatzResearch.WordTrace]
  refine ⟨72589505687754842962251805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96786007583673123949669073 72589505687754842962251805)
  ·
    refine ⟨27221064632908066110844427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72589505687754842962251805 27221064632908066110844427)
    ·
      refine ⟨40831596949362099166266641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27221064632908066110844427 40831596949362099166266641)
      ·
        refine ⟨30623697712021574374699981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40831596949362099166266641 30623697712021574374699981)
        ·
          refine ⟨11483886642008090390512493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30623697712021574374699981 11483886642008090390512493)
          ·
            refine ⟨4306457490753033896442185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11483886642008090390512493 4306457490753033896442185)
            ·
              refine ⟨3229843118064775422331639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306457490753033896442185 3229843118064775422331639)
              ·
                refine ⟨4844764677097163133497459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229843118064775422331639 4844764677097163133497459)
                ·
                  refine ⟨7267147015645744700246189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844764677097163133497459 7267147015645744700246189)
                  ·
                    refine ⟨2725180130867154262592321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7267147015645744700246189 2725180130867154262592321)
                    ·
                      refine ⟨2043885098150365696944241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725180130867154262592321 2043885098150365696944241)
                      ·
                        rfl

theorem cell23_3980452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_3980452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980452 prefixEnd_3980452 := by exact prefixLift 3980452
  have htrace : WordTrace (prefixWord ++ tailWord_3980452) baseStart_3980452 baseEnd_3980452 := by
    simpa [prefixWord, tailWord_3980452, baseEnd_3980452] using wordTrace_append hprefix tailTrace_3980452
  have hstable : (prefixWord ++ tailWord_3980452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980452).length < 2 ^ (prefixWord ++ tailWord_3980452).sum := by decide
  have hdescent : baseEnd_3980452 < baseStart_3980452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980464 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_3980464 : Nat := 118140960795 + 3980464 * 2 ^ 59
def prefixEnd_3980464 : Nat := 4983230072969 + 3 ^ 40 * 3980464 * 2
def baseEnd_3980464 : Nat := 2043891259918219649994185

theorem tailTrace_3980464 : CollatzResearch.WordTrace tailWord_3980464 prefixEnd_3980464 2043891259918219649994185 := by
  unfold tailWord_3980464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72589724525733105986970223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96786299367644141315960297 72589724525733105986970223)
  ·
    refine ⟨108884586788599658980455335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72589724525733105986970223 108884586788599658980455335)
    ·
      refine ⟨163326880182899488470683003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108884586788599658980455335 163326880182899488470683003)
      ·
        refine ⟨244990320274349232706024505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163326880182899488470683003 244990320274349232706024505)
        ·
          refine ⟨183742740205761924529518379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244990320274349232706024505 183742740205761924529518379)
          ·
            refine ⟨275614110308642886794277569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183742740205761924529518379 275614110308642886794277569)
            ·
              refine ⟨206710582731482165095708177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275614110308642886794277569 206710582731482165095708177)
              ·
                refine ⟨155032937048611623821781133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206710582731482165095708177 155032937048611623821781133)
                ·
                  refine ⟨58137351393229358933167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155032937048611623821781133 58137351393229358933167925)
                  ·
                    refine ⟨5450376693115252399984493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58137351393229358933167925 5450376693115252399984493)
                    ·
                      refine ⟨2043891259918219649994185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450376693115252399984493 2043891259918219649994185)
                      ·
                        rfl

theorem cell23_3980464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_3980464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980464 prefixEnd_3980464 := by exact prefixLift 3980464
  have htrace : WordTrace (prefixWord ++ tailWord_3980464) baseStart_3980464 baseEnd_3980464 := by
    simpa [prefixWord, tailWord_3980464, baseEnd_3980464] using wordTrace_append hprefix tailTrace_3980464
  have hstable : (prefixWord ++ tailWord_3980464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980464).length < 2 ^ (prefixWord ++ tailWord_3980464).sum := by decide
  have hdescent : baseEnd_3980464 < baseStart_3980464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980465 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3980465 : Nat := 118140960795 + 3980465 * 2 ^ 59
def prefixEnd_3980465 : Nat := 4983230072969 + 3 ^ 40 * 3980465 * 2
def baseEnd_3980465 : Nat := 2043891773398874146081681

theorem tailTrace_3980465 : CollatzResearch.WordTrace tailWord_3980465 prefixEnd_3980465 2043891773398874146081681 := by
  unfold tailWord_3980465
  simp only [CollatzResearch.WordTrace]
  refine ⟨145179485524462589144726849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96786323682975059429817899 145179485524462589144726849)
  ·
    refine ⟨108884614143346941858545137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145179485524462589144726849 108884614143346941858545137)
    ·
      refine ⟨81663460607510206393908853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108884614143346941858545137 81663460607510206393908853)
      ·
        refine ⟨7655949431954081849428955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81663460607510206393908853 7655949431954081849428955)
        ·
          refine ⟨11483924147931122774143433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655949431954081849428955 11483924147931122774143433)
          ·
            refine ⟨8612943110948342080607575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483924147931122774143433 8612943110948342080607575)
            ·
              refine ⟨12919414666422513120911363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612943110948342080607575 12919414666422513120911363)
              ·
                refine ⟨19379121999633769681367045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919414666422513120911363 19379121999633769681367045)
                ·
                  refine ⟨3633585374931331815256321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19379121999633769681367045 3633585374931331815256321)
                  ·
                    refine ⟨2725189031198498861442241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633585374931331815256321 2725189031198498861442241)
                    ·
                      refine ⟨2043891773398874146081681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725189031198498861442241 2043891773398874146081681)
                      ·
                        rfl

theorem cell23_3980465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3980465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980465 prefixEnd_3980465 := by exact prefixLift 3980465
  have htrace : WordTrace (prefixWord ++ tailWord_3980465) baseStart_3980465 baseEnd_3980465 := by
    simpa [prefixWord, tailWord_3980465, baseEnd_3980465] using wordTrace_append hprefix tailTrace_3980465
  have hstable : (prefixWord ++ tailWord_3980465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980465).length < 2 ^ (prefixWord ++ tailWord_3980465).sum := by decide
  have hdescent : baseEnd_3980465 < baseStart_3980465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980471 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 5]
def baseStart_3980471 : Nat := 118140960795 + 3980471 * 2 ^ 59
def prefixEnd_3980471 : Nat := 4983230072969 + 3 ^ 40 * 3980471 * 2
def baseEnd_3980471 : Nat := 227099428253644569178517

theorem tailTrace_3980471 : CollatzResearch.WordTrace tailWord_3980471 prefixEnd_3980471 227099428253644569178517 := by
  unfold tailWord_3980471
  simp only [CollatzResearch.WordTrace]
  refine ⟨145179704362440852169445267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96786469574960568112963511 145179704362440852169445267)
  ·
    refine ⟨217769556543661278254167901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145179704362440852169445267 217769556543661278254167901)
    ·
      refine ⟨81663583703872979345312963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217769556543661278254167901 81663583703872979345312963)
      ·
        refine ⟨122495375555809469017969445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81663583703872979345312963 122495375555809469017969445)
        ·
          refine ⟨22967882916714275440869271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122495375555809469017969445 22967882916714275440869271)
          ·
            refine ⟨34451824375071413161303907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967882916714275440869271 34451824375071413161303907)
            ·
              refine ⟨51677736562607119741955861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34451824375071413161303907 51677736562607119741955861)
              ·
                refine ⟨2422393901372208737904181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51677736562607119741955861 2422393901372208737904181)
                ·
                  refine ⟨227099428253644569178517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422393901372208737904181 227099428253644569178517)
                  ·
                    rfl

theorem cell23_3980471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 5].length) (baseStart_3980471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980471 prefixEnd_3980471 := by exact prefixLift 3980471
  have htrace : WordTrace (prefixWord ++ tailWord_3980471) baseStart_3980471 baseEnd_3980471 := by
    simpa [prefixWord, tailWord_3980471, baseEnd_3980471] using wordTrace_append hprefix tailTrace_3980471
  have hstable : (prefixWord ++ tailWord_3980471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980471).length < 2 ^ (prefixWord ++ tailWord_3980471).sum := by decide
  have hdescent : baseEnd_3980471 < baseStart_3980471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980486 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3980486 : Nat := 118140960795 + 3980486 * 2 ^ 59
def prefixEnd_3980486 : Nat := 4983230072969 + 3 ^ 40 * 3980486 * 2
def baseEnd_3980486 : Nat := 2043902556492618563919085

theorem tailTrace_3980486 : CollatzResearch.WordTrace tailWord_3980486 prefixEnd_3980486 2043902556492618563919085 := by
  unfold tailWord_3980486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536882858043328429101291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96786834304924339820827541 4536882858043328429101291)
  ·
    refine ⟨6805324287064992643651937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536882858043328429101291 6805324287064992643651937)
    ·
      refine ⟨5103993215298744482738953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6805324287064992643651937 5103993215298744482738953)
      ·
        refine ⟨3827994911474058362054215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5103993215298744482738953 3827994911474058362054215)
        ·
          refine ⟨5741992367211087543081323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827994911474058362054215 5741992367211087543081323)
          ·
            refine ⟨8612988550816631314621985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741992367211087543081323 8612988550816631314621985)
            ·
              refine ⟨6459741413112473485966489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8612988550816631314621985 6459741413112473485966489)
              ·
                refine ⟨4844806059834355114474867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459741413112473485966489 4844806059834355114474867)
                ·
                  refine ⟨7267209089751532671712301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844806059834355114474867 7267209089751532671712301)
                  ·
                    refine ⟨2725203408656824751892113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7267209089751532671712301 2725203408656824751892113)
                    ·
                      refine ⟨2043902556492618563919085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725203408656824751892113 2043902556492618563919085)
                      ·
                        rfl

theorem cell23_3980486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3980486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980486 prefixEnd_3980486 := by exact prefixLift 3980486
  have htrace : WordTrace (prefixWord ++ tailWord_3980486) baseStart_3980486 baseEnd_3980486 := by
    simpa [prefixWord, tailWord_3980486, baseEnd_3980486] using wordTrace_append hprefix tailTrace_3980486
  have hstable : (prefixWord ++ tailWord_3980486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980486).length < 2 ^ (prefixWord ++ tailWord_3980486).sum := by decide
  have hdescent : baseEnd_3980486 < baseStart_3980486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980501 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3980501 : Nat := 118140960795 + 3980501 * 2 ^ 59
def prefixEnd_3980501 : Nat := 4983230072969 + 3 ^ 40 * 3980501 * 2
def baseEnd_3980501 : Nat := 681303419567478668410505

theorem tailTrace_3980501 : CollatzResearch.WordTrace tailWord_3980501 prefixEnd_3980501 681303419567478668410505 := by
  unfold tailWord_3980501
  simp only [CollatzResearch.WordTrace]
  refine ⟨145180798552332167293037357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96787199034888111528691571 145180798552332167293037357)
  ·
    refine ⟨54442799457124562734889009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145180798552332167293037357 54442799457124562734889009)
    ·
      refine ⟨40832099592843422051166757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54442799457124562734889009 40832099592843422051166757)
      ·
        refine ⟨7656018673658141634593767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40832099592843422051166757 7656018673658141634593767)
        ·
          refine ⟨11484028010487212451890651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656018673658141634593767 11484028010487212451890651)
          ·
            refine ⟨17226042015730818677835977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11484028010487212451890651 17226042015730818677835977)
            ·
              refine ⟨12919531511798114008376983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17226042015730818677835977 12919531511798114008376983)
              ·
                refine ⟨19379297267697171012565475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919531511798114008376983 19379297267697171012565475)
                ·
                  refine ⟨29068945901545756518848213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19379297267697171012565475 29068945901545756518848213)
                  ·
                    refine ⟨681303419567478668410505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29068945901545756518848213 681303419567478668410505)
                    ·
                      rfl

theorem cell23_3980501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3980501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980501 prefixEnd_3980501 := by exact prefixLift 3980501
  have htrace : WordTrace (prefixWord ++ tailWord_3980501) baseStart_3980501 baseEnd_3980501 := by
    simpa [prefixWord, tailWord_3980501, baseEnd_3980501] using wordTrace_append hprefix tailTrace_3980501
  have hstable : (prefixWord ++ tailWord_3980501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980501).length < 2 ^ (prefixWord ++ tailWord_3980501).sum := by decide
  have hdescent : baseEnd_3980501 < baseStart_3980501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980558 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3980558 : Nat := 118140960795 + 3980558 * 2 ^ 59
def prefixEnd_3980558 : Nat := 4983230072969 + 3 ^ 40 * 3980558 * 2
def baseEnd_3980558 : Nat := 2043939527099742282218753

theorem tailTrace_3980558 : CollatzResearch.WordTrace tailWord_3980558 prefixEnd_3980558 2043939527099742282218753 := by
  unfold tailWord_3980558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147859689140708253482791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96788585008750444018574885 18147859689140708253482791)
  ·
    refine ⟨27221789533711062380224187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147859689140708253482791 27221789533711062380224187)
    ·
      refine ⟨40832684300566593570336281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27221789533711062380224187 40832684300566593570336281)
      ·
        refine ⟨30624513225424945177752211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40832684300566593570336281 30624513225424945177752211)
        ·
          refine ⟨45936769838137417766628317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30624513225424945177752211 45936769838137417766628317)
          ·
            refine ⟨17226288689301531662485619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45936769838137417766628317 17226288689301531662485619)
            ·
              refine ⟨25839433033952297493728429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17226288689301531662485619 25839433033952297493728429)
              ·
                refine ⟨9689787387732111560148161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25839433033952297493728429 9689787387732111560148161)
                ·
                  refine ⟨7267340540799083670111121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689787387732111560148161 7267340540799083670111121)
                  ·
                    refine ⟨5450505405599312752583341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267340540799083670111121 5450505405599312752583341)
                    ·
                      refine ⟨2043939527099742282218753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450505405599312752583341 2043939527099742282218753)
                      ·
                        rfl

theorem cell23_3980558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3980558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980558 prefixEnd_3980558 := by exact prefixLift 3980558
  have htrace : WordTrace (prefixWord ++ tailWord_3980558) baseStart_3980558 baseEnd_3980558 := by
    simpa [prefixWord, tailWord_3980558, baseEnd_3980558] using wordTrace_append hprefix tailTrace_3980558
  have hstable : (prefixWord ++ tailWord_3980558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980558).length < 2 ^ (prefixWord ++ tailWord_3980558).sum := by decide
  have hdescent : baseEnd_3980558 < baseStart_3980558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980588 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_3980588 : Nat := 118140960795 + 3980588 * 2 ^ 59
def prefixEnd_3980588 : Nat := 4983230072969 + 3 ^ 40 * 3980588 * 2
def baseEnd_3980588 : Nat := 2043954931519377164843615

theorem tailTrace_3980588 : CollatzResearch.WordTrace tailWord_3980588 prefixEnd_3980588 2043954931519377164843615 := by
  unfold tailWord_3980588
  simp only [CollatzResearch.WordTrace]
  refine ⟨72591985851508490575727209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96789314468677987434302945 72591985851508490575727209)
  ·
    refine ⟨54443989388631367931795407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72591985851508490575727209 54443989388631367931795407)
    ·
      refine ⟨81665984082947051897693111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54443989388631367931795407 81665984082947051897693111)
      ·
        refine ⟨122498976124420577846539667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81665984082947051897693111 122498976124420577846539667)
        ·
          refine ⟨183748464186630866769809501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122498976124420577846539667 183748464186630866769809501)
          ·
            refine ⟨68905674069986575038678563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183748464186630866769809501 68905674069986575038678563)
            ·
              refine ⟨103358511104979862558017845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68905674069986575038678563 103358511104979862558017845)
              ·
                refine ⟨9689860416091862114814173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103358511104979862558017845 9689860416091862114814173)
                ·
                  refine ⟨3633697656034448293055315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9689860416091862114814173 3633697656034448293055315)
                  ·
                    refine ⟨5450546484051672439582973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633697656034448293055315 5450546484051672439582973)
                    ·
                      refine ⟨2043954931519377164843615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450546484051672439582973 2043954931519377164843615)
                      ·
                        rfl

theorem cell23_3980588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_3980588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980588 prefixEnd_3980588 := by exact prefixLift 3980588
  have htrace : WordTrace (prefixWord ++ tailWord_3980588) baseStart_3980588 baseEnd_3980588 := by
    simpa [prefixWord, tailWord_3980588, baseEnd_3980588] using wordTrace_append hprefix tailTrace_3980588
  have hstable : (prefixWord ++ tailWord_3980588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980588).length < 2 ^ (prefixWord ++ tailWord_3980588).sum := by decide
  have hdescent : baseEnd_3980588 < baseStart_3980588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980615 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_3980615 : Nat := 118140960795 + 3980615 * 2 ^ 59
def prefixEnd_3980615 : Nat := 4983230072969 + 3 ^ 40 * 3980615 * 2
def baseEnd_3980615 : Nat := 2043968795497048559205991

theorem tailTrace_3980615 : CollatzResearch.WordTrace tailWord_3980615 prefixEnd_3980615 2043968795497048559205991 := by
  unfold tailWord_3980615
  simp only [CollatzResearch.WordTrace]
  refine ⟨145184956473919164762687299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96789970982612776508458199 145184956473919164762687299)
  ·
    refine ⟨217777434710878747144030949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145184956473919164762687299 217777434710878747144030949)
    ·
      refine ⟨40833269008289765089505803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217777434710878747144030949 40833269008289765089505803)
      ·
        refine ⟨61249903512434647634258705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40833269008289765089505803 61249903512434647634258705)
        ·
          refine ⟨45937427634325985725694029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61249903512434647634258705 45937427634325985725694029)
          ·
            refine ⟨17226535362872244647135261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45937427634325985725694029 17226535362872244647135261)
            ·
              refine ⟨6459950761077091742675723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17226535362872244647135261 6459950761077091742675723)
              ·
                refine ⟨9689926141615637614013585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459950761077091742675723 9689926141615637614013585)
                ·
                  refine ⟨7267444606211728210510189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689926141615637614013585 7267444606211728210510189)
                  ·
                    refine ⟨2725291727329398078941321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7267444606211728210510189 2725291727329398078941321)
                    ·
                      refine ⟨2043968795497048559205991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725291727329398078941321 2043968795497048559205991)
                      ·
                        rfl

theorem cell23_3980615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_3980615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980615 prefixEnd_3980615 := by exact prefixLift 3980615
  have htrace : WordTrace (prefixWord ++ tailWord_3980615) baseStart_3980615 baseEnd_3980615 := by
    simpa [prefixWord, tailWord_3980615, baseEnd_3980615] using wordTrace_append hprefix tailTrace_3980615
  have hstable : (prefixWord ++ tailWord_3980615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980615).length < 2 ^ (prefixWord ++ tailWord_3980615).sum := by decide
  have hdescent : baseEnd_3980615 < baseStart_3980615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980622 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_3980622 : Nat := 118140960795 + 3980622 * 2 ^ 59
def prefixEnd_3980622 : Nat := 4983230072969 + 3 ^ 40 * 3980622 * 2
def baseEnd_3980622 : Nat := 2043972389861630031818459

theorem tailTrace_3980622 : CollatzResearch.WordTrace tailWord_3980622 prefixEnd_3980622 2043972389861630031818459 := by
  unfold tailWord_3980622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18148151473111725619774015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96790141189929203305461413 18148151473111725619774015)
  ·
    refine ⟨27222227209667588429661023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18148151473111725619774015 27222227209667588429661023)
    ·
      refine ⟨40833340814501382644491535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27222227209667588429661023 40833340814501382644491535)
      ·
        refine ⟨61250011221752073966737303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40833340814501382644491535 61250011221752073966737303)
        ·
          refine ⟨91875016832628110950105955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61250011221752073966737303 91875016832628110950105955)
          ·
            refine ⟨137812525248942166425158933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91875016832628110950105955 137812525248942166425158933)
            ·
              refine ⟨6459962121044164051179325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137812525248942166425158933 6459962121044164051179325)
              ·
                refine ⟨2422485795391561519192247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6459962121044164051179325 2422485795391561519192247)
                ·
                  refine ⟨3633728693087342278788371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422485795391561519192247 3633728693087342278788371)
                  ·
                    refine ⟨5450593039631013418182557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633728693087342278788371 5450593039631013418182557)
                    ·
                      refine ⟨2043972389861630031818459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450593039631013418182557 2043972389861630031818459)
                      ·
                        rfl

theorem cell23_3980622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_3980622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980622 prefixEnd_3980622 := by exact prefixLift 3980622
  have htrace : WordTrace (prefixWord ++ tailWord_3980622) baseStart_3980622 baseEnd_3980622 := by
    simpa [prefixWord, tailWord_3980622, baseEnd_3980622] using wordTrace_append hprefix tailTrace_3980622
  have hstable : (prefixWord ++ tailWord_3980622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980622).length < 2 ^ (prefixWord ++ tailWord_3980622).sum := by decide
  have hdescent : baseEnd_3980622 < baseStart_3980622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980641 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3980641 : Nat := 118140960795 + 3980641 * 2 ^ 59
def prefixEnd_3980641 : Nat := 4983230072969 + 3 ^ 40 * 3980641 * 2
def baseEnd_3980641 : Nat := 2043982145994065457480871

theorem tailTrace_3980641 : CollatzResearch.WordTrace tailWord_3980641 prefixEnd_3980641 2043982145994065457480871 := by
  unfold tailWord_3980641
  simp only [CollatzResearch.WordTrace]
  refine ⟨145185904771824971203133777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96790603181216647468755851 145185904771824971203133777)
  ·
    refine ⟨108889428578868728402350333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145185904771824971203133777 108889428578868728402350333)
    ·
      refine ⟨40833535717075773150881375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108889428578868728402350333 40833535717075773150881375)
      ·
        refine ⟨61250303575613659726322063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40833535717075773150881375 61250303575613659726322063)
        ·
          refine ⟨91875455363420489589483095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61250303575613659726322063 91875455363420489589483095)
          ·
            refine ⟨137813183045130734384224643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91875455363420489589483095 137813183045130734384224643)
            ·
              refine ⟨206719774567696101576336965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137813183045130734384224643 206719774567696101576336965)
              ·
                refine ⟨38759957731443019045563181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206719774567696101576336965 38759957731443019045563181)
                ·
                  refine ⟨14534984149291132142086193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38759957731443019045563181 14534984149291132142086193)
                  ·
                    refine ⟨10901238111968349106564645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14534984149291132142086193 10901238111968349106564645)
                    ·
                      refine ⟨2043982145994065457480871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10901238111968349106564645 2043982145994065457480871)
                      ·
                        rfl

theorem cell23_3980641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3980641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980641 prefixEnd_3980641 := by exact prefixLift 3980641
  have htrace : WordTrace (prefixWord ++ tailWord_3980641) baseStart_3980641 baseEnd_3980641 := by
    simpa [prefixWord, tailWord_3980641, baseEnd_3980641] using wordTrace_append hprefix tailTrace_3980641
  have hstable : (prefixWord ++ tailWord_3980641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980641).length < 2 ^ (prefixWord ++ tailWord_3980641).sum := by decide
  have hdescent : baseEnd_3980641 < baseStart_3980641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980655 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 2, 4]
def baseStart_3980655 : Nat := 118140960795 + 3980655 * 2 ^ 59
def prefixEnd_3980655 : Nat := 4983230072969 + 3 ^ 40 * 3980655 * 2
def baseEnd_3980655 : Nat := 681329778241076134235269

theorem tailTrace_3980655 : CollatzResearch.WordTrace tailWord_3980655 prefixEnd_3980655 681329778241076134235269 := by
  unfold tailWord_3980655
  simp only [CollatzResearch.WordTrace]
  refine ⟨145186415393774251594143419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96790943595849501062762279 145186415393774251594143419)
  ·
    refine ⟨217779623090661377391215129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145186415393774251594143419 217779623090661377391215129)
    ·
      refine ⟨163334717317996033043411347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217779623090661377391215129 163334717317996033043411347)
      ·
        refine ⟨245002075976994049565117021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163334717317996033043411347 245002075976994049565117021)
        ·
          refine ⟨91875778491372768586918883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245002075976994049565117021 91875778491372768586918883)
          ·
            refine ⟨137813667737059152880378325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91875778491372768586918883 137813667737059152880378325)
            ·
              refine ⟨3230007837587323895633867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 137813667737059152880378325 3230007837587323895633867)
              ·
                refine ⟨4845011756380985843450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230007837587323895633867 4845011756380985843450801)
                ·
                  refine ⟨3633758817285739382588101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4845011756380985843450801 3633758817285739382588101)
                  ·
                    refine ⟨681329778241076134235269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633758817285739382588101 681329778241076134235269)
                    ·
                      rfl

theorem cell23_3980655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_3980655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980655 prefixEnd_3980655 := by exact prefixLift 3980655
  have htrace : WordTrace (prefixWord ++ tailWord_3980655) baseStart_3980655 baseEnd_3980655 := by
    simpa [prefixWord, tailWord_3980655, baseEnd_3980655] using wordTrace_append hprefix tailTrace_3980655
  have hstable : (prefixWord ++ tailWord_3980655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980655).length < 2 ^ (prefixWord ++ tailWord_3980655).sum := by decide
  have hdescent : baseEnd_3980655 < baseStart_3980655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980679 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_3980679 : Nat := 118140960795 + 3980679 * 2 ^ 59
def prefixEnd_3980679 : Nat := 4983230072969 + 3 ^ 40 * 3980679 * 2
def baseEnd_3980679 : Nat := 2044001658258936308805697

theorem tailTrace_3980679 : CollatzResearch.WordTrace tailWord_3980679 prefixEnd_3980679 2044001658258936308805697 := by
  unfold tailWord_3980679
  simp only [CollatzResearch.WordTrace]
  refine ⟨145187290745687303693017091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96791527163791535795344727 145187290745687303693017091)
  ·
    refine ⟨217780936118530955539525637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145187290745687303693017091 217780936118530955539525637)
    ·
      refine ⟨40833925522224554163661057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217780936118530955539525637 40833925522224554163661057)
      ·
        refine ⟨30625444141668415622745793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40833925522224554163661057 30625444141668415622745793)
        ·
          refine ⟨22969083106251311717059345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30625444141668415622745793 22969083106251311717059345)
          ·
            refine ⟨17226812329688483787794509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22969083106251311717059345 17226812329688483787794509)
            ·
              refine ⟨6460054623633181420422941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17226812329688483787794509 6460054623633181420422941)
              ·
                refine ⟨2422520483862443032658603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6460054623633181420422941 2422520483862443032658603)
                ·
                  refine ⟨3633780725793664548987905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422520483862443032658603 3633780725793664548987905)
                  ·
                    refine ⟨2725335544345248411740929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633780725793664548987905 2725335544345248411740929)
                    ·
                      refine ⟨2044001658258936308805697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725335544345248411740929 2044001658258936308805697)
                      ·
                        rfl

theorem cell23_3980679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_3980679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980679 prefixEnd_3980679 := by exact prefixLift 3980679
  have htrace : WordTrace (prefixWord ++ tailWord_3980679) baseStart_3980679 baseEnd_3980679 := by
    simpa [prefixWord, tailWord_3980679, baseEnd_3980679] using wordTrace_append hprefix tailTrace_3980679
  have hstable : (prefixWord ++ tailWord_3980679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980679).length < 2 ^ (prefixWord ++ tailWord_3980679).sum := by decide
  have hdescent : baseEnd_3980679 < baseStart_3980679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980695 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3980695 : Nat := 118140960795 + 3980695 * 2 ^ 59
def prefixEnd_3980695 : Nat := 4983230072969 + 3 ^ 40 * 3980695 * 2
def baseEnd_3980695 : Nat := 2044009873949408246205623

theorem tailTrace_3980695 : CollatzResearch.WordTrace tailWord_3980695 prefixEnd_3980695 2044009873949408246205623 := by
  unfold tailWord_3980695
  simp only [CollatzResearch.WordTrace]
  refine ⟨145187874313629338425599539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96791916209086225617066359 145187874313629338425599539)
  ·
    refine ⟨217781811470444007638399309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145187874313629338425599539 217781811470444007638399309)
    ·
      refine ⟨81668179301416502864399741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217781811470444007638399309 81668179301416502864399741)
      ·
        refine ⟨30625567238031188574149903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81668179301416502864399741 30625567238031188574149903)
        ·
          refine ⟨45938350857046782861224855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30625567238031188574149903 45938350857046782861224855)
          ·
            refine ⟨68907526285570174291837283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45938350857046782861224855 68907526285570174291837283)
            ·
              refine ⟨103361289428355261437755925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68907526285570174291837283 103361289428355261437755925)
              ·
                refine ⟨4845060441954152879894809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103361289428355261437755925 4845060441954152879894809)
                ·
                  refine ⟨3633795331465614659921107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4845060441954152879894809 3633795331465614659921107)
                  ·
                    refine ⟨5450692997198421989881661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3633795331465614659921107 5450692997198421989881661)
                    ·
                      refine ⟨2044009873949408246205623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450692997198421989881661 2044009873949408246205623)
                      ·
                        rfl

theorem cell23_3980695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3980695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980695 prefixEnd_3980695 := by exact prefixLift 3980695
  have htrace : WordTrace (prefixWord ++ tailWord_3980695) baseStart_3980695 baseEnd_3980695 := by
    simpa [prefixWord, tailWord_3980695, baseEnd_3980695] using wordTrace_append hprefix tailTrace_3980695
  have hstable : (prefixWord ++ tailWord_3980695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980695).length < 2 ^ (prefixWord ++ tailWord_3980695).sum := by decide
  have hdescent : baseEnd_3980695 < baseStart_3980695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980696 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3980696 : Nat := 118140960795 + 3980696 * 2 ^ 59
def prefixEnd_3980696 : Nat := 4983230072969 + 3 ^ 40 * 3980696 * 2
def baseEnd_3980696 : Nat := 2044010387430062742293119

theorem tailTrace_3980696 : CollatzResearch.WordTrace tailWord_3980696 prefixEnd_3980696 2044010387430062742293119 := by
  unfold tailWord_3980696
  simp only [CollatzResearch.WordTrace]
  refine ⟨72593955393312857798192971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96791940524417143730923961 72593955393312857798192971)
  ·
    refine ⟨108890933089969286697289457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72593955393312857798192971 108890933089969286697289457)
    ·
      refine ⟨81668199817476965022967093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108890933089969286697289457 81668199817476965022967093)
      ·
        refine ⟨7656393732888465470903165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81668199817476965022967093 7656393732888465470903165)
        ·
          refine ⟨2871147649833174551588687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7656393732888465470903165 2871147649833174551588687)
          ·
            refine ⟨4306721474749761827383031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871147649833174551588687 4306721474749761827383031)
            ·
              refine ⟨6460082212124642741074547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306721474749761827383031 6460082212124642741074547)
              ·
                refine ⟨9690123318186964111611821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460082212124642741074547 9690123318186964111611821)
                ·
                  refine ⟨3633796244320111541854433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9690123318186964111611821 3633796244320111541854433)
                  ·
                    refine ⟨2725347183240083656390825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633796244320111541854433 2725347183240083656390825)
                    ·
                      refine ⟨2044010387430062742293119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725347183240083656390825 2044010387430062742293119)
                      ·
                        rfl

theorem cell23_3980696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3980696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980696 prefixEnd_3980696 := by exact prefixLift 3980696
  have htrace : WordTrace (prefixWord ++ tailWord_3980696) baseStart_3980696 baseEnd_3980696 := by
    simpa [prefixWord, tailWord_3980696, baseEnd_3980696] using wordTrace_append hprefix tailTrace_3980696
  have hstable : (prefixWord ++ tailWord_3980696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980696).length < 2 ^ (prefixWord ++ tailWord_3980696).sum := by decide
  have hdescent : baseEnd_3980696 < baseStart_3980696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 6, 2, 2]
def baseStart_3980735 : Nat := 118140960795 + 3980735 * 2 ^ 59
def prefixEnd_3980735 : Nat := 4983230072969 + 3 ^ 40 * 3980735 * 2
def baseEnd_3980735 : Nat := 2044030413175588089705439

theorem tailTrace_3980735 : CollatzResearch.WordTrace tailWord_3980735 prefixEnd_3980735 2044030413175588089705439 := by
  unfold tailWord_3980735
  simp only [CollatzResearch.WordTrace]
  refine ⟨145189333233484425257055659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96792888822322950171370439 145189333233484425257055659)
  ·
    refine ⟨217783999850226637885583489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145189333233484425257055659 217783999850226637885583489)
    ·
      refine ⟨163337999887669978414187617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217783999850226637885583489 163337999887669978414187617)
      ·
        refine ⟨122503499915752483810640713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163337999887669978414187617 122503499915752483810640713)
        ·
          refine ⟨91877624936814362857980535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122503499915752483810640713 91877624936814362857980535)
          ·
            refine ⟨137816437405221544286970803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91877624936814362857980535 137816437405221544286970803)
            ·
              refine ⟨206724656107832316430456205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137816437405221544286970803 206724656107832316430456205)
              ·
                refine ⟨77521746040437118661421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206724656107832316430456205 77521746040437118661421077)
                ·
                  refine ⟨3633831845645489937254113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77521746040437118661421077 3633831845645489937254113)
                  ·
                    refine ⟨2725373884234117452940585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633831845645489937254113 2725373884234117452940585)
                    ·
                      refine ⟨2044030413175588089705439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725373884234117452940585 2044030413175588089705439)
                      ·
                        rfl

theorem cell23_3980735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_3980735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980735 prefixEnd_3980735 := by exact prefixLift 3980735
  have htrace : WordTrace (prefixWord ++ tailWord_3980735) baseStart_3980735 baseEnd_3980735 := by
    simpa [prefixWord, tailWord_3980735, baseEnd_3980735] using wordTrace_append hprefix tailTrace_3980735
  have hstable : (prefixWord ++ tailWord_3980735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980735).length < 2 ^ (prefixWord ++ tailWord_3980735).sum := by decide
  have hdescent : baseEnd_3980735 < baseStart_3980735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980751 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_3980751 : Nat := 118140960795 + 3980751 * 2 ^ 59
def prefixEnd_3980751 : Nat := 4983230072969 + 3 ^ 40 * 3980751 * 2
def baseEnd_3980751 : Nat := 2044038628866060027105365

theorem tailTrace_3980751 : CollatzResearch.WordTrace tailWord_3980751 prefixEnd_3980751 2044038628866060027105365 := by
  unfold tailWord_3980751
  simp only [CollatzResearch.WordTrace]
  refine ⟨145189916801426459989638107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96793277867617639993092071 145189916801426459989638107)
  ·
    refine ⟨217784875202139689984457161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145189916801426459989638107 217784875202139689984457161)
    ·
      refine ⟨163338656401604767488342871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217784875202139689984457161 163338656401604767488342871)
      ·
        refine ⟨245007984602407151232514307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163338656401604767488342871 245007984602407151232514307)
        ·
          refine ⟨367511976903610726848771461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245007984602407151232514307 367511976903610726848771461)
          ·
            refine ⟨68908495669427011284144649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367511976903610726848771461 68908495669427011284144649)
            ·
              refine ⟨51681371752070258463108487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68908495669427011284144649 51681371752070258463108487)
              ·
                refine ⟨77522057628105387694662731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51681371752070258463108487 77522057628105387694662731)
                ·
                  refine ⟨116283086442158081541994097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77522057628105387694662731 116283086442158081541994097)
                  ·
                    refine ⟨87212314831618561156495573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116283086442158081541994097 87212314831618561156495573)
                    ·
                      refine ⟨2044038628866060027105365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87212314831618561156495573 2044038628866060027105365)
                      ·
                        rfl

theorem cell23_3980751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_3980751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980751 prefixEnd_3980751 := by exact prefixLift 3980751
  have htrace : WordTrace (prefixWord ++ tailWord_3980751) baseStart_3980751 baseEnd_3980751 := by
    simpa [prefixWord, tailWord_3980751, baseEnd_3980751] using wordTrace_append hprefix tailTrace_3980751
  have hstable : (prefixWord ++ tailWord_3980751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980751).length < 2 ^ (prefixWord ++ tailWord_3980751).sum := by decide
  have hdescent : baseEnd_3980751 < baseStart_3980751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980765 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3980765 : Nat := 118140960795 + 3980765 * 2 ^ 59
def prefixEnd_3980765 : Nat := 4983230072969 + 3 ^ 40 * 3980765 * 2
def baseEnd_3980765 : Nat := 2044045817595222972330301

theorem tailTrace_3980765 : CollatzResearch.WordTrace tailWord_3980765 prefixEnd_3980765 2044045817595222972330301 := by
  unfold tailWord_3980765
  simp only [CollatzResearch.WordTrace]
  refine ⟨145190427423375740380647749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96793618282250493587098499 145190427423375740380647749)
  ·
    refine ⟨27223205141882951321371453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145190427423375740380647749 27223205141882951321371453)
    ·
      refine ⟨10208701928206106745514295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27223205141882951321371453 10208701928206106745514295)
      ·
        refine ⟨15313052892309160118271443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10208701928206106745514295 15313052892309160118271443)
        ·
          refine ⟨22969579338463740177407165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313052892309160118271443 22969579338463740177407165)
          ·
            refine ⟨8613592251923902566527687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22969579338463740177407165 8613592251923902566527687)
            ·
              refine ⟨12920388377885853849791531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613592251923902566527687 12920388377885853849791531)
              ·
                refine ⟨19380582566828780774687297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920388377885853849791531 19380582566828780774687297)
                ·
                  refine ⟨14535436925121585581015473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19380582566828780774687297 14535436925121585581015473)
                  ·
                    refine ⟨10901577693841189185761605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14535436925121585581015473 10901577693841189185761605)
                    ·
                      refine ⟨2044045817595222972330301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10901577693841189185761605 2044045817595222972330301)
                      ·
                        rfl

theorem cell23_3980765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3980765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980765 prefixEnd_3980765 := by exact prefixLift 3980765
  have htrace : WordTrace (prefixWord ++ tailWord_3980765) baseStart_3980765 baseEnd_3980765 := by
    simpa [prefixWord, tailWord_3980765, baseEnd_3980765] using wordTrace_append hprefix tailTrace_3980765
  have hstable : (prefixWord ++ tailWord_3980765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980765).length < 2 ^ (prefixWord ++ tailWord_3980765).sum := by decide
  have hdescent : baseEnd_3980765 < baseStart_3980765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980802 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3980802 : Nat := 118140960795 + 3980802 * 2 ^ 59
def prefixEnd_3980802 : Nat := 4983230072969 + 3 ^ 40 * 3980802 * 2
def baseEnd_3980802 : Nat := 2044064816379439327567631

theorem tailTrace_3980802 : CollatzResearch.WordTrace tailWord_3980802 prefixEnd_3980802 2044064816379439327567631 := by
  unfold tailWord_3980802
  simp only [CollatzResearch.WordTrace]
  refine ⟨36297944231060423924936165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96794517949494463799829773 36297944231060423924936165)
  ·
    refine ⟨6805864543323829485925531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36297944231060423924936165 6805864543323829485925531)
    ·
      refine ⟨10208796814985744228888297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6805864543323829485925531 10208796814985744228888297)
      ·
        refine ⟨7656597611239308171666223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208796814985744228888297 7656597611239308171666223)
        ·
          refine ⟨11484896416858962257499335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656597611239308171666223 11484896416858962257499335)
          ·
            refine ⟨17227344625288443386249003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11484896416858962257499335 17227344625288443386249003)
            ·
              refine ⟨25841016937932665079373505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17227344625288443386249003 25841016937932665079373505)
              ·
                refine ⟨19380762703449498809530129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25841016937932665079373505 19380762703449498809530129)
                ·
                  refine ⟨14535572027587124107147597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19380762703449498809530129 14535572027587124107147597)
                  ·
                    refine ⟨5450839510345171540180349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14535572027587124107147597 5450839510345171540180349)
                    ·
                      refine ⟨2044064816379439327567631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5450839510345171540180349 2044064816379439327567631)
                      ·
                        rfl

theorem cell23_3980802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3980802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980802 prefixEnd_3980802 := by exact prefixLift 3980802
  have htrace : WordTrace (prefixWord ++ tailWord_3980802) baseStart_3980802 baseEnd_3980802 := by
    simpa [prefixWord, tailWord_3980802, baseEnd_3980802] using wordTrace_append hprefix tailTrace_3980802
  have hstable : (prefixWord ++ tailWord_3980802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980802).length < 2 ^ (prefixWord ++ tailWord_3980802).sum := by decide
  have hdescent : baseEnd_3980802 < baseStart_3980802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980865 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 6]
def baseStart_3980865 : Nat := 118140960795 + 3980865 * 2 ^ 59
def prefixEnd_3980865 : Nat := 4983230072969 + 3 ^ 40 * 3980865 * 2
def baseEnd_3980865 : Nat := 227121907295630286786649

theorem tailTrace_3980865 : CollatzResearch.WordTrace tailWord_3980865 prefixEnd_3980865 227121907295630286786649 := by
  unfold tailWord_3980865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145194074723013457459288049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96796049815342304972858699 145194074723013457459288049)
  ·
    refine ⟨108895556042260093094466037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145194074723013457459288049 108895556042260093094466037)
    ·
      refine ⟨10208958378961883727606191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108895556042260093094466037 10208958378961883727606191)
      ·
        refine ⟨15313437568442825591409287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10208958378961883727606191 15313437568442825591409287)
        ·
          refine ⟨22970156352664238387113931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313437568442825591409287 22970156352664238387113931)
          ·
            refine ⟨34455234528996357580670897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22970156352664238387113931 34455234528996357580670897)
            ·
              refine ⟨25841425896747268185503173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34455234528996357580670897 25841425896747268185503173)
              ·
                refine ⟨4845267355640112784781845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25841425896747268185503173 4845267355640112784781845)
                ·
                  refine ⟨227121907295630286786649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4845267355640112784781845 227121907295630286786649)
                  ·
                    rfl

theorem cell23_3980865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_3980865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980865 prefixEnd_3980865 := by exact prefixLift 3980865
  have htrace : WordTrace (prefixWord ++ tailWord_3980865) baseStart_3980865 baseEnd_3980865 := by
    simpa [prefixWord, tailWord_3980865, baseEnd_3980865] using wordTrace_append hprefix tailTrace_3980865
  have hstable : (prefixWord ++ tailWord_3980865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980865).length < 2 ^ (prefixWord ++ tailWord_3980865).sum := by decide
  have hdescent : baseEnd_3980865 < baseStart_3980865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980869 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_3980869 : Nat := 118140960795 + 3980869 * 2 ^ 59
def prefixEnd_3980869 : Nat := 4983230072969 + 3 ^ 40 * 3980869 * 2
def baseEnd_3980869 : Nat := 681366406527763521809941

theorem tailTrace_3980869 : CollatzResearch.WordTrace tailWord_3980869 prefixEnd_3980869 681366406527763521809941 := by
  unfold tailWord_3980869
  simp only [CollatzResearch.WordTrace]
  refine ⟨145194220614998966142433661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96796147076665977428289107 145194220614998966142433661)
  ·
    refine ⟨54447832730624612303412623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145194220614998966142433661 54447832730624612303412623)
    ·
      refine ⟨81671749095936918455118935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54447832730624612303412623 81671749095936918455118935)
      ·
        refine ⟨122507623643905377682678403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81671749095936918455118935 122507623643905377682678403)
        ·
          refine ⟨183761435465858066524017605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122507623643905377682678403 183761435465858066524017605)
          ·
            refine ⟨34455269149848387473253301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183761435465858066524017605 34455269149848387473253301)
            ·
              refine ⟨3230181482798286325617497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34455269149848387473253301 3230181482798286325617497)
              ·
                refine ⟨2422636112098714744213123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230181482798286325617497 2422636112098714744213123)
                ·
                  refine ⟨3633954168148072116319685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422636112098714744213123 3633954168148072116319685)
                  ·
                    refine ⟨681366406527763521809941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633954168148072116319685 681366406527763521809941)
                    ·
                      rfl

theorem cell23_3980869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_3980869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980869 prefixEnd_3980869 := by exact prefixLift 3980869
  have htrace : WordTrace (prefixWord ++ tailWord_3980869) baseStart_3980869 baseEnd_3980869 := by
    simpa [prefixWord, tailWord_3980869, baseEnd_3980869] using wordTrace_append hprefix tailTrace_3980869
  have hstable : (prefixWord ++ tailWord_3980869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980869).length < 2 ^ (prefixWord ++ tailWord_3980869).sum := by decide
  have hdescent : baseEnd_3980869 < baseStart_3980869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980878 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3980878 : Nat := 118140960795 + 3980878 * 2 ^ 59
def prefixEnd_3980878 : Nat := 4983230072969 + 3 ^ 40 * 3980878 * 2
def baseEnd_3980878 : Nat := 681367946969727010072427

theorem tailTrace_3980878 : CollatzResearch.WordTrace tailWord_3980878 prefixEnd_3980878 681367946969727010072427 := by
  unfold tailWord_3980878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18149318608995795084938911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96796365914644240453007525 18149318608995795084938911)
  ·
    refine ⟨27223977913493692627408367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18149318608995795084938911 27223977913493692627408367)
    ·
      refine ⟨40835966870240538941112551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27223977913493692627408367 40835966870240538941112551)
      ·
        refine ⟨61253950305360808411668827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40835966870240538941112551 61253950305360808411668827)
        ·
          refine ⟨91880925458041212617503241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61253950305360808411668827 91880925458041212617503241)
          ·
            refine ⟨68910694093530909463127431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91880925458041212617503241 68910694093530909463127431)
            ·
              refine ⟨103366041140296364194691147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68910694093530909463127431 103366041140296364194691147)
              ·
                refine ⟨155049061710444546292036721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103366041140296364194691147 155049061710444546292036721)
                ·
                  refine ⟨116286796282833409719027541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155049061710444546292036721 116286796282833409719027541)
                  ·
                    refine ⟨681367946969727010072427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116286796282833409719027541 681367946969727010072427)
                    ·
                      rfl

theorem cell23_3980878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3980878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980878 prefixEnd_3980878 := by exact prefixLift 3980878
  have htrace : WordTrace (prefixWord ++ tailWord_3980878) baseStart_3980878 baseEnd_3980878 := by
    simpa [prefixWord, tailWord_3980878, baseEnd_3980878] using wordTrace_append hprefix tailTrace_3980878
  have hstable : (prefixWord ++ tailWord_3980878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980878).length < 2 ^ (prefixWord ++ tailWord_3980878).sum := by decide
  have hdescent : baseEnd_3980878 < baseStart_3980878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980882 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_3980882 : Nat := 118140960795 + 3980882 * 2 ^ 59
def prefixEnd_3980882 : Nat := 4983230072969 + 3 ^ 40 * 3980882 * 2
def baseEnd_3980882 : Nat := 227122877203533223840807

theorem tailTrace_3980882 : CollatzResearch.WordTrace tailWord_3980882 prefixEnd_3980882 227122877203533223840807 := by
  unfold tailWord_3980882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298673690987967340664225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96796463175967912908437933 36298673690987967340664225)
  ·
    refine ⟨27224005268240975505498169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36298673690987967340664225 27224005268240975505498169)
    ·
      refine ⟨20418003951180731629123627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27224005268240975505498169 20418003951180731629123627)
      ·
        refine ⟨30627005926771097443685441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20418003951180731629123627 30627005926771097443685441)
        ·
          refine ⟨22970254445078323082764081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30627005926771097443685441 22970254445078323082764081)
          ·
            refine ⟨17227690833808742312073061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22970254445078323082764081 17227690833808742312073061)
            ·
              refine ⟨3230192031339139183513699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17227690833808742312073061 3230192031339139183513699)
              ·
                refine ⟨4845288047008708775270549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230192031339139183513699 4845288047008708775270549)
                ·
                  refine ⟨227122877203533223840807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4845288047008708775270549 227122877203533223840807)
                  ·
                    rfl

theorem cell23_3980882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_3980882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980882 prefixEnd_3980882 := by exact prefixLift 3980882
  have htrace : WordTrace (prefixWord ++ tailWord_3980882) baseStart_3980882 baseEnd_3980882 := by
    simpa [prefixWord, tailWord_3980882, baseEnd_3980882] using wordTrace_append hprefix tailTrace_3980882
  have hstable : (prefixWord ++ tailWord_3980882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980882).length < 2 ^ (prefixWord ++ tailWord_3980882).sum := by decide
  have hdescent : baseEnd_3980882 < baseStart_3980882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980915 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 6, 2]
def baseStart_3980915 : Nat := 118140960795 + 3980915 * 2 ^ 59
def prefixEnd_3980915 : Nat := 4983230072969 + 3 ^ 40 * 3980915 * 2
def baseEnd_3980915 : Nat := 2044122839693397385454611

theorem tailTrace_3980915 : CollatzResearch.WordTrace tailWord_3980915 prefixEnd_3980915 2044122839693397385454611 := by
  unfold tailWord_3980915
  simp only [CollatzResearch.WordTrace]
  refine ⟨145195898372832315998608199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96797265581888210665738799 145195898372832315998608199)
  ·
    refine ⟨217793847559248473997912299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145195898372832315998608199 217793847559248473997912299)
    ·
      refine ⟨326690771338872710996868449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217793847559248473997912299 326690771338872710996868449)
      ·
        refine ⟨245018078504154533247651337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326690771338872710996868449 245018078504154533247651337)
        ·
          refine ⟨183763558878115899935738503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245018078504154533247651337 183763558878115899935738503)
          ·
            refine ⟨275645338317173849903607755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183763558878115899935738503 275645338317173849903607755)
            ·
              refine ⟨413468007475760774855411633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275645338317173849903607755 413468007475760774855411633)
              ·
                refine ⟨310101005606820581141558725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413468007475760774855411633 310101005606820581141558725)
                ·
                  refine ⟨58143938551278858964042261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310101005606820581141558725 58143938551278858964042261)
                  ·
                    refine ⟨2725497119591196513939481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58143938551278858964042261 2725497119591196513939481)
                    ·
                      refine ⟨2044122839693397385454611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725497119591196513939481 2044122839693397385454611)
                      ·
                        rfl

theorem cell23_3980915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6, 2].length) (baseStart_3980915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980915 prefixEnd_3980915 := by exact prefixLift 3980915
  have htrace : WordTrace (prefixWord ++ tailWord_3980915) baseStart_3980915 baseEnd_3980915 := by
    simpa [prefixWord, tailWord_3980915, baseEnd_3980915] using wordTrace_append hprefix tailTrace_3980915
  have hstable : (prefixWord ++ tailWord_3980915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980915).length < 2 ^ (prefixWord ++ tailWord_3980915).sum := by decide
  have hdescent : baseEnd_3980915 < baseStart_3980915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980942 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3980942 : Nat := 118140960795 + 3980942 * 2 ^ 59
def prefixEnd_3980942 : Nat := 4983230072969 + 3 ^ 40 * 3980942 * 2
def baseEnd_3980942 : Nat := 681378901223689593272329

theorem tailTrace_3980942 : CollatzResearch.WordTrace tailWord_3980942 prefixEnd_3980942 681378901223689593272329 := by
  unfold tailWord_3980942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18149610392966812451230135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96797922095822999739894053 18149610392966812451230135)
  ·
    refine ⟨27224415589450218676845203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18149610392966812451230135 27224415589450218676845203)
    ·
      refine ⟨40836623384175328015267805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27224415589450218676845203 40836623384175328015267805)
      ·
        refine ⟨15313733769065748005725427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40836623384175328015267805 15313733769065748005725427)
        ·
          refine ⟨22970600653598622008588141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313733769065748005725427 22970600653598622008588141)
          ·
            refine ⟨8613975245099483253220553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22970600653598622008588141 8613975245099483253220553)
            ·
              refine ⟨6460481433824612439915415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613975245099483253220553 6460481433824612439915415)
              ·
                refine ⟨9690722150736918659873123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460481433824612439915415 9690722150736918659873123)
                ·
                  refine ⟨14536083226105377989809685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690722150736918659873123 14536083226105377989809685)
                  ·
                    refine ⟨681378901223689593272329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14536083226105377989809685 681378901223689593272329)
                    ·
                      rfl

theorem cell23_3980942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3980942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980942 prefixEnd_3980942 := by exact prefixLift 3980942
  have htrace : WordTrace (prefixWord ++ tailWord_3980942) baseStart_3980942 baseEnd_3980942 := by
    simpa [prefixWord, tailWord_3980942, baseEnd_3980942] using wordTrace_append hprefix tailTrace_3980942
  have hstable : (prefixWord ++ tailWord_3980942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980942).length < 2 ^ (prefixWord ++ tailWord_3980942).sum := by decide
  have hdescent : baseEnd_3980942 < baseStart_3980942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3980952 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3980952 : Nat := 118140960795 + 3980952 * 2 ^ 59
def prefixEnd_3980952 : Nat := 4983230072969 + 3 ^ 40 * 3980952 * 2
def baseEnd_3980952 : Nat := 2044141838477613740691941

theorem tailTrace_3980952 : CollatzResearch.WordTrace tailWord_3980952 prefixEnd_3980952 2044141838477613740691941 := by
  unfold tailWord_3980952
  simp only [CollatzResearch.WordTrace]
  refine ⟨72598623936849135658852555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96798165249132180878470073 72598623936849135658852555)
  ·
    refine ⟨108897935905273703488278833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72598623936849135658852555 108897935905273703488278833)
    ·
      refine ⟨81673451928955277616209125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108897935905273703488278833 81673451928955277616209125)
      ·
        refine ⟨15313772236679114553039211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81673451928955277616209125 15313772236679114553039211)
        ·
          refine ⟨22970658355018671829558817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15313772236679114553039211 22970658355018671829558817)
          ·
            refine ⟨17227993766264003872169113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22970658355018671829558817 17227993766264003872169113)
            ·
              refine ⟨12920995324698002904126835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17227993766264003872169113 12920995324698002904126835)
              ·
                refine ⟨19381492987047004356190253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920995324698002904126835 19381492987047004356190253)
                ·
                  refine ⟨7268059870142626633571345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19381492987047004356190253 7268059870142626633571345)
                  ·
                    refine ⟨5451044902606969975178509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7268059870142626633571345 5451044902606969975178509)
                    ·
                      refine ⟨2044141838477613740691941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451044902606969975178509 2044141838477613740691941)
                      ·
                        rfl

theorem cell23_3980952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3980952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3980952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3980952 prefixEnd_3980952 := by exact prefixLift 3980952
  have htrace : WordTrace (prefixWord ++ tailWord_3980952) baseStart_3980952 baseEnd_3980952 := by
    simpa [prefixWord, tailWord_3980952, baseEnd_3980952] using wordTrace_append hprefix tailTrace_3980952
  have hstable : (prefixWord ++ tailWord_3980952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3980952).length < 2 ^ (prefixWord ++ tailWord_3980952).sum := by decide
  have hdescent : baseEnd_3980952 < baseStart_3980952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3980952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981009 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_3981009 : Nat := 118140960795 + 3981009 * 2 ^ 59
def prefixEnd_3981009 : Nat := 4983230072969 + 3 ^ 40 * 3981009 * 2
def baseEnd_3981009 : Nat := 2044171106874920017679179

theorem tailTrace_3981009 : CollatzResearch.WordTrace tailWord_3981009 prefixEnd_3981009 2044171106874920017679179 := by
  unfold tailWord_3981009
  simp only [CollatzResearch.WordTrace]
  refine ⟨145199326834491770052530081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96799551222994513368353387 145199326834491770052530081)
  ·
    refine ⟨108899495125868827539397561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145199326834491770052530081 108899495125868827539397561)
    ·
      refine ⟨81674621344401620654548171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108899495125868827539397561 81674621344401620654548171)
      ·
        refine ⟨122511932016602430981822257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81674621344401620654548171 122511932016602430981822257)
        ·
          refine ⟨91883949012451823236366693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122511932016602430981822257 91883949012451823236366693)
          ·
            refine ⟨17228240439834716856818755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91883949012451823236366693 17228240439834716856818755)
            ·
              refine ⟨25842360659752075285228133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228240439834716856818755 25842360659752075285228133)
              ·
                refine ⟨4845442623703514115980275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25842360659752075285228133 4845442623703514115980275)
                ·
                  refine ⟨7268163935555271173970413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845442623703514115980275 7268163935555271173970413)
                  ·
                    refine ⟨2725561475833226690238905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7268163935555271173970413 2725561475833226690238905)
                    ·
                      refine ⟨2044171106874920017679179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725561475833226690238905 2044171106874920017679179)
                      ·
                        rfl

theorem cell23_3981009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_3981009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981009 prefixEnd_3981009 := by exact prefixLift 3981009
  have htrace : WordTrace (prefixWord ++ tailWord_3981009) baseStart_3981009 baseEnd_3981009 := by
    simpa [prefixWord, tailWord_3981009, baseEnd_3981009] using wordTrace_append hprefix tailTrace_3981009
  have hstable : (prefixWord ++ tailWord_3981009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981009).length < 2 ^ (prefixWord ++ tailWord_3981009).sum := by decide
  have hdescent : baseEnd_3981009 < baseStart_3981009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981012 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3981012 : Nat := 118140960795 + 3981012 * 2 ^ 59
def prefixEnd_3981012 : Nat := 4983230072969 + 3 ^ 40 * 3981012 * 2
def baseEnd_3981012 : Nat := 2044172647316883505941665

theorem tailTrace_3981012 : CollatzResearch.WordTrace tailWord_3981012 prefixEnd_3981012 2044172647316883505941665 := by
  unfold tailWord_3981012
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599718126740450782444645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96799624168987267709926193 72599718126740450782444645)
  ·
    refine ⟨13612447148763834521708371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72599718126740450782444645 13612447148763834521708371)
    ·
      refine ⟨20418670723145751782562557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612447148763834521708371 20418670723145751782562557)
      ·
        refine ⟨7657001521179656918460959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20418670723145751782562557 7657001521179656918460959)
        ·
          refine ⟨11485502281769485377691439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7657001521179656918460959 11485502281769485377691439)
          ·
            refine ⟨17228253422654228066537159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485502281769485377691439 17228253422654228066537159)
            ·
              refine ⟨25842380133981342099805739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228253422654228066537159 25842380133981342099805739)
              ·
                refine ⟨38763570200972013149708609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25842380133981342099805739 38763570200972013149708609)
                ·
                  refine ⟨29072677650729009862281457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38763570200972013149708609 29072677650729009862281457)
                  ·
                    refine ⟨21804508238046757396711093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29072677650729009862281457 21804508238046757396711093)
                    ·
                      refine ⟨2044172647316883505941665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21804508238046757396711093 2044172647316883505941665)
                      ·
                        rfl

theorem cell23_3981012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3981012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981012 prefixEnd_3981012 := by exact prefixLift 3981012
  have htrace : WordTrace (prefixWord ++ tailWord_3981012) baseStart_3981012 baseEnd_3981012 := by
    simpa [prefixWord, tailWord_3981012, baseEnd_3981012] using wordTrace_append hprefix tailTrace_3981012
  have hstable : (prefixWord ++ tailWord_3981012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981012).length < 2 ^ (prefixWord ++ tailWord_3981012).sum := by decide
  have hdescent : baseEnd_3981012 < baseStart_3981012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981035 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_3981035 : Nat := 118140960795 + 3981035 * 2 ^ 59
def prefixEnd_3981035 : Nat := 4983230072969 + 3 ^ 40 * 3981035 * 2
def baseEnd_3981035 : Nat := 2044184457371936915954059

theorem tailTrace_3981035 : CollatzResearch.WordTrace tailWord_3981035 prefixEnd_3981035 2044184457371936915954059 := by
  unfold tailWord_3981035
  simp only [CollatzResearch.WordTrace]
  refine ⟨145200275132397576492976559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96800183421598384328651039 145200275132397576492976559)
  ·
    refine ⟨217800412698596364739464839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145200275132397576492976559 217800412698596364739464839)
    ·
      refine ⟨326700619047894547109197259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217800412698596364739464839 326700619047894547109197259)
      ·
        refine ⟨490050928571841820663795889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326700619047894547109197259 490050928571841820663795889)
        ·
          refine ⟨367538196428881365497846917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490050928571841820663795889 367538196428881365497846917)
          ·
            refine ⟨68913411830415256030846297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367538196428881365497846917 68913411830415256030846297)
            ·
              refine ⟨51685058872811442023134723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68913411830415256030846297 51685058872811442023134723)
              ·
                refine ⟨77527588309217163034702085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51685058872811442023134723 77527588309217163034702085)
                ·
                  refine ⟨14536422807978218069006641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77527588309217163034702085 14536422807978218069006641)
                  ·
                    refine ⟨10902317105983663551754981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14536422807978218069006641 10902317105983663551754981)
                    ·
                      refine ⟨2044184457371936915954059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10902317105983663551754981 2044184457371936915954059)
                      ·
                        rfl

theorem cell23_3981035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_3981035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981035 prefixEnd_3981035 := by exact prefixLift 3981035
  have htrace : WordTrace (prefixWord ++ tailWord_3981035) baseStart_3981035 baseEnd_3981035 := by
    simpa [prefixWord, tailWord_3981035, baseEnd_3981035] using wordTrace_append hprefix tailTrace_3981035
  have hstable : (prefixWord ++ tailWord_3981035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981035).length < 2 ^ (prefixWord ++ tailWord_3981035).sum := by decide
  have hdescent : baseEnd_3981035 < baseStart_3981035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981039 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 4, 2, 2]
def baseStart_3981039 : Nat := 118140960795 + 3981039 * 2 ^ 59
def prefixEnd_3981039 : Nat := 4983230072969 + 3 ^ 40 * 3981039 * 2
def baseEnd_3981039 : Nat := 2044186511294554900304041

theorem tailTrace_3981039 : CollatzResearch.WordTrace tailWord_3981039 prefixEnd_3981039 2044186511294554900304041 := by
  unfold tailWord_3981039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145200421024383085176122171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96800280682922056784081447 145200421024383085176122171)
  ·
    refine ⟨217800631536574627764183257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145200421024383085176122171 217800631536574627764183257)
    ·
      refine ⟨163350473652430970823137443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217800631536574627764183257 163350473652430970823137443)
      ·
        refine ⟨245025710478646456234706165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163350473652430970823137443 245025710478646456234706165)
        ·
          refine ⟨22971160357373105272003703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245025710478646456234706165 22971160357373105272003703)
          ·
            refine ⟨34456740536059657908005555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971160357373105272003703 34456740536059657908005555)
            ·
              refine ⟨51685110804089486862008333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34456740536059657908005555 51685110804089486862008333)
              ·
                refine ⟨19381916551533557573253125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51685110804089486862008333 19381916551533557573253125)
                ·
                  refine ⟨3634109353412542044984961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19381916551533557573253125 3634109353412542044984961)
                  ·
                    refine ⟨2725582015059406533738721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634109353412542044984961 2725582015059406533738721)
                    ·
                      refine ⟨2044186511294554900304041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725582015059406533738721 2044186511294554900304041)
                      ·
                        rfl

theorem cell23_3981039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2, 2].length) (baseStart_3981039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981039 prefixEnd_3981039 := by exact prefixLift 3981039
  have htrace : WordTrace (prefixWord ++ tailWord_3981039) baseStart_3981039 baseEnd_3981039 := by
    simpa [prefixWord, tailWord_3981039, baseEnd_3981039] using wordTrace_append hprefix tailTrace_3981039
  have hstable : (prefixWord ++ tailWord_3981039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981039).length < 2 ^ (prefixWord ++ tailWord_3981039).sum := by decide
  have hdescent : baseEnd_3981039 < baseStart_3981039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981042 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3981042 : Nat := 118140960795 + 3981042 * 2 ^ 59
def prefixEnd_3981042 : Nat := 4983230072969 + 3 ^ 40 * 3981042 * 2
def baseEnd_3981042 : Nat := 2044188051736518388566527

theorem tailTrace_3981042 : CollatzResearch.WordTrace tailWord_3981042 prefixEnd_3981042 2044188051736518388566527 := by
  unfold tailWord_3981042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36300132610843054172120345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96800353628914811125654253 36300132610843054172120345)
  ·
    refine ⟨27225099458132290629090259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36300132610843054172120345 27225099458132290629090259)
    ·
      refine ⟨40837649187198435943635389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27225099458132290629090259 40837649187198435943635389)
      ·
        refine ⟨15314118445199413478863271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40837649187198435943635389 15314118445199413478863271)
        ·
          refine ⟨22971177667799120218294907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15314118445199413478863271 22971177667799120218294907)
          ·
            refine ⟨34456766501698680327442361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971177667799120218294907 34456766501698680327442361)
            ·
              refine ⟨25842574876274010245581771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34456766501698680327442361 25842574876274010245581771)
              ·
                refine ⟨38763862314411015368372657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25842574876274010245581771 38763862314411015368372657)
                ·
                  refine ⟨29072896735808261526279493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38763862314411015368372657 29072896735808261526279493)
                  ·
                    refine ⟨5451168137964049036177405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29072896735808261526279493 5451168137964049036177405)
                    ·
                      refine ⟨2044188051736518388566527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451168137964049036177405 2044188051736518388566527)
                      ·
                        rfl

theorem cell23_3981042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3981042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981042 prefixEnd_3981042 := by exact prefixLift 3981042
  have htrace : WordTrace (prefixWord ++ tailWord_3981042) baseStart_3981042 baseEnd_3981042 := by
    simpa [prefixWord, tailWord_3981042, baseEnd_3981042] using wordTrace_append hprefix tailTrace_3981042
  have hstable : (prefixWord ++ tailWord_3981042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981042).length < 2 ^ (prefixWord ++ tailWord_3981042).sum := by decide
  have hdescent : baseEnd_3981042 < baseStart_3981042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981096 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 5]
def baseStart_3981096 : Nat := 118140960795 + 3981096 * 2 ^ 59
def prefixEnd_3981096 : Nat := 4983230072969 + 3 ^ 40 * 3981096 * 2
def baseEnd_3981096 : Nat := 227135086632429019699031

theorem tailTrace_3981096 : CollatzResearch.WordTrace tailWord_3981096 prefixEnd_3981096 227135086632429019699031 := by
  unfold tailWord_3981096
  simp only [CollatzResearch.WordTrace]
  refine ⟨72601249992588291955473571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96801666656784389273964761 72601249992588291955473571)
  ·
    refine ⟨108901874988882437933210357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72601249992588291955473571 108901874988882437933210357)
    ·
      refine ⟨10209550780207728556238471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108901874988882437933210357 10209550780207728556238471)
      ·
        refine ⟨15314326170311592834357707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209550780207728556238471 15314326170311592834357707)
        ·
          refine ⟨22971489255467389251536561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15314326170311592834357707 22971489255467389251536561)
          ·
            refine ⟨17228616941600541938652421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22971489255467389251536561 17228616941600541938652421)
            ·
              refine ⟨3230365676550101613497329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17228616941600541938652421 3230365676550101613497329)
              ·
                refine ⟨2422774257412576210122997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230365676550101613497329 2422774257412576210122997)
                ·
                  refine ⟨227135086632429019699031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422774257412576210122997 227135086632429019699031)
                  ·
                    rfl

theorem cell23_3981096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 5].length) (baseStart_3981096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981096 prefixEnd_3981096 := by exact prefixLift 3981096
  have htrace : WordTrace (prefixWord ++ tailWord_3981096) baseStart_3981096 baseEnd_3981096 := by
    simpa [prefixWord, tailWord_3981096, baseEnd_3981096] using wordTrace_append hprefix tailTrace_3981096
  have hstable : (prefixWord ++ tailWord_3981096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981096).length < 2 ^ (prefixWord ++ tailWord_3981096).sum := by decide
  have hdescent : baseEnd_3981096 < baseStart_3981096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981126 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3981126 : Nat := 118140960795 + 3981126 * 2 ^ 59
def prefixEnd_3981126 : Nat := 4983230072969 + 3 ^ 40 * 3981126 * 2
def baseEnd_3981126 : Nat := 681410394703832019972047

theorem tailTrace_3981126 : CollatzResearch.WordTrace tailWord_3981126 prefixEnd_3981126 681410394703832019972047 := by
  unfold tailWord_3981126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537612317970871844829351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96802396116711932689692821 4537612317970871844829351)
  ·
    refine ⟨6806418476956307767244027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4537612317970871844829351 6806418476956307767244027)
    ·
      refine ⟨10209627715434461650866041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806418476956307767244027 10209627715434461650866041)
      ·
        refine ⟨7657220786575846238149531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10209627715434461650866041 7657220786575846238149531)
        ·
          refine ⟨11485831179863769357224297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7657220786575846238149531 11485831179863769357224297)
          ·
            refine ⟨8614373384897827017918223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485831179863769357224297 8614373384897827017918223)
            ·
              refine ⟨12921560077346740526877335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614373384897827017918223 12921560077346740526877335)
              ·
                refine ⟨19382340116020110790316003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12921560077346740526877335 19382340116020110790316003)
                ·
                  refine ⟨29073510174030166185474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19382340116020110790316003 29073510174030166185474005)
                  ·
                    refine ⟨681410394703832019972047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29073510174030166185474005 681410394703832019972047)
                    ·
                      rfl

theorem cell23_3981126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3981126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981126 prefixEnd_3981126 := by exact prefixLift 3981126
  have htrace : WordTrace (prefixWord ++ tailWord_3981126) baseStart_3981126 baseEnd_3981126 := by
    simpa [prefixWord, tailWord_3981126, baseEnd_3981126] using wordTrace_append hprefix tailTrace_3981126
  have hstable : (prefixWord ++ tailWord_3981126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981126).length < 2 ^ (prefixWord ++ tailWord_3981126).sum := by decide
  have hdescent : baseEnd_3981126 < baseStart_3981126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981152 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 8]
def baseStart_3981152 : Nat := 118140960795 + 3981152 * 2 ^ 59
def prefixEnd_3981152 : Nat := 4983230072969 + 3 ^ 40 * 3981152 * 2
def baseEnd_3981152 : Nat := 227138281623168106465669

theorem tailTrace_3981152 : CollatzResearch.WordTrace tailWord_3981152 prefixEnd_3981152 227138281623168106465669 := by
  unfold tailWord_3981152
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602271236486852737492855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96803028315315803649990473 72602271236486852737492855)
  ·
    refine ⟨108903406854730279106239283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72602271236486852737492855 108903406854730279106239283)
    ·
      refine ⟨163355110282095418659358925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108903406854730279106239283 163355110282095418659358925)
      ·
        refine ⟨61258166355785781997259597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163355110282095418659358925 61258166355785781997259597)
        ·
          refine ⟨22971812383419668248972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61258166355785781997259597 22971812383419668248972349)
          ·
            refine ⟨8614429643782375593364631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22971812383419668248972349 8614429643782375593364631)
            ·
              refine ⟨12921644465673563390046947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614429643782375593364631 12921644465673563390046947)
              ·
                refine ⟨19382466698510345085070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12921644465673563390046947 19382466698510345085070421)
                ·
                  refine ⟨227138281623168106465669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19382466698510345085070421 227138281623168106465669)
                  ·
                    rfl

theorem cell23_3981152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_3981152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981152 prefixEnd_3981152 := by exact prefixLift 3981152
  have htrace : WordTrace (prefixWord ++ tailWord_3981152) baseStart_3981152 baseEnd_3981152 := by
    simpa [prefixWord, tailWord_3981152, baseEnd_3981152] using wordTrace_append hprefix tailTrace_3981152
  have hstable : (prefixWord ++ tailWord_3981152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981152).length < 2 ^ (prefixWord ++ tailWord_3981152).sum := by decide
  have hdescent : baseEnd_3981152 < baseStart_3981152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981156 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3981156 : Nat := 118140960795 + 3981156 * 2 ^ 59
def prefixEnd_3981156 : Nat := 4983230072969 + 3 ^ 40 * 3981156 * 2
def baseEnd_3981156 : Nat := 681415529510376980847001

theorem tailTrace_3981156 : CollatzResearch.WordTrace tailWord_3981156 prefixEnd_3981156 681415529510376980847001 := by
  unfold tailWord_3981156
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602344182479607079065661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96803125576639476105420881 72602344182479607079065661)
  ·
    refine ⟨27225879068429852654649623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72602344182479607079065661 27225879068429852654649623)
    ·
      refine ⟨40838818602644778981974435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27225879068429852654649623 40838818602644778981974435)
      ·
        refine ⟨61258227903967168472961653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40838818602644778981974435 61258227903967168472961653)
        ·
          refine ⟨5742958865996922044340155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61258227903967168472961653 5742958865996922044340155)
          ·
            refine ⟨8614438298995383066510233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742958865996922044340155 8614438298995383066510233)
            ·
              refine ⟨6460828724246537299882675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614438298995383066510233 6460828724246537299882675)
              ·
                refine ⟨9691243086369805949824013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460828724246537299882675 9691243086369805949824013)
                ·
                  refine ⟨3634216157388677231184005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691243086369805949824013 3634216157388677231184005)
                  ·
                    refine ⟨681415529510376980847001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3634216157388677231184005 681415529510376980847001)
                    ·
                      rfl

theorem cell23_3981156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3981156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981156 prefixEnd_3981156 := by exact prefixLift 3981156
  have htrace : WordTrace (prefixWord ++ tailWord_3981156) baseStart_3981156 baseEnd_3981156 := by
    simpa [prefixWord, tailWord_3981156, baseEnd_3981156] using wordTrace_append hprefix tailTrace_3981156
  have hstable : (prefixWord ++ tailWord_3981156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981156).length < 2 ^ (prefixWord ++ tailWord_3981156).sum := by decide
  have hdescent : baseEnd_3981156 < baseStart_3981156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981169 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 6]
def baseStart_3981169 : Nat := 118140960795 + 3981169 * 2 ^ 59
def prefixEnd_3981169 : Nat := 4983230072969 + 3 ^ 40 * 3981169 * 2
def baseEnd_3981169 : Nat := 227139251531071043519827

theorem tailTrace_3981169 : CollatzResearch.WordTrace tailWord_3981169 prefixEnd_3981169 227139251531071043519827 := by
  unfold tailWord_3981169
  simp only [CollatzResearch.WordTrace]
  refine ⟨145205162513912117378354561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96803441675941411585569707 145205162513912117378354561)
  ·
    refine ⟨108903871885434088033765921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145205162513912117378354561 108903871885434088033765921)
    ·
      refine ⟨81677903914075566025324441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108903871885434088033765921 81677903914075566025324441)
      ·
        refine ⟨61258427935556674518993331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81677903914075566025324441 61258427935556674518993331)
        ·
          refine ⟨91887641903335011778489997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61258427935556674518993331 91887641903335011778489997)
          ·
            refine ⟨34457865713750629416933749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91887641903335011778489997 34457865713750629416933749)
            ·
              refine ⟨3230424910664121507837539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34457865713750629416933749 3230424910664121507837539)
              ·
                refine ⟨4845637365996182261756309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230424910664121507837539 4845637365996182261756309)
                ·
                  refine ⟨227139251531071043519827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4845637365996182261756309 227139251531071043519827)
                  ·
                    rfl

theorem cell23_3981169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_3981169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981169 prefixEnd_3981169 := by exact prefixLift 3981169
  have htrace : WordTrace (prefixWord ++ tailWord_3981169) baseStart_3981169 baseEnd_3981169 := by
    simpa [prefixWord, tailWord_3981169, baseEnd_3981169] using wordTrace_append hprefix tailTrace_3981169
  have hstable : (prefixWord ++ tailWord_3981169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981169).length < 2 ^ (prefixWord ++ tailWord_3981169).sum := by decide
  have hdescent : baseEnd_3981169 < baseStart_3981169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981189 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_3981189 : Nat := 118140960795 + 3981189 * 2 ^ 59
def prefixEnd_3981189 : Nat := 4983230072969 + 3 ^ 40 * 3981189 * 2
def baseEnd_3981189 : Nat := 2044263533392729313428351

theorem tailTrace_3981189 : CollatzResearch.WordTrace tailWord_3981189 prefixEnd_3981189 2044263533392729313428351 := by
  unfold tailWord_3981189
  simp only [CollatzResearch.WordTrace]
  refine ⟨145205891973839660794082621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96803927982559773862721747 145205891973839660794082621)
  ·
    refine ⟨54452209490189872797780983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145205891973839660794082621 54452209490189872797780983)
    ·
      refine ⟨81678314235284809196671475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54452209490189872797780983 81678314235284809196671475)
      ·
        refine ⟨122517471352927213795007213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81678314235284809196671475 122517471352927213795007213)
        ·
          refine ⟨45944051757347705173127705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122517471352927213795007213 45944051757347705173127705)
          ·
            refine ⟨34458038818010778879845779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45944051757347705173127705 34458038818010778879845779)
            ·
              refine ⟨51687058227016168319768669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34458038818010778879845779 51687058227016168319768669)
              ·
                refine ⟨19382646835131063119913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51687058227016168319768669 19382646835131063119913251)
                ·
                  refine ⟨29073970252696594679869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19382646835131063119913251 29073970252696594679869877)
                  ·
                    refine ⟨2725684711190305751237801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29073970252696594679869877 2725684711190305751237801)
                    ·
                      refine ⟨2044263533392729313428351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725684711190305751237801 2044263533392729313428351)
                      ·
                        rfl

theorem cell23_3981189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_3981189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981189 prefixEnd_3981189 := by exact prefixLift 3981189
  have htrace : WordTrace (prefixWord ++ tailWord_3981189) baseStart_3981189 baseEnd_3981189 := by
    simpa [prefixWord, tailWord_3981189, baseEnd_3981189] using wordTrace_append hprefix tailTrace_3981189
  have hstable : (prefixWord ++ tailWord_3981189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981189).length < 2 ^ (prefixWord ++ tailWord_3981189).sum := by decide
  have hdescent : baseEnd_3981189 < baseStart_3981189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981213 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3981213 : Nat := 118140960795 + 3981213 * 2 ^ 59
def prefixEnd_3981213 : Nat := 4983230072969 + 3 ^ 40 * 3981213 * 2
def baseEnd_3981213 : Nat := 2044275856928437219528241

theorem tailTrace_3981213 : CollatzResearch.WordTrace tailWord_3981213 prefixEnd_3981213 2044275856928437219528241 := by
  unfold tailWord_3981213
  simp only [CollatzResearch.WordTrace]
  refine ⟨145206767325752712892956293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96804511550501808595304195 145206767325752712892956293)
  ·
    refine ⟨27226268873578633667429305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145206767325752712892956293 27226268873578633667429305)
    ·
      refine ⟨20419701655183975250571979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27226268873578633667429305 20419701655183975250571979)
      ·
        refine ⟨30629552482775962875857969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419701655183975250571979 30629552482775962875857969)
        ·
          refine ⟨22972164362081972156893477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30629552482775962875857969 22972164362081972156893477)
          ·
            refine ⟨4307280817890369779417527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22972164362081972156893477 4307280817890369779417527)
            ·
              refine ⟨6460921226835554669126291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307280817890369779417527 6460921226835554669126291)
              ·
                refine ⟨9691381840253332003689437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460921226835554669126291 9691381840253332003689437)
                ·
                  refine ⟨3634268190094999501383539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9691381840253332003689437 3634268190094999501383539)
                  ·
                    refine ⟨5451402285142499252075309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3634268190094999501383539 5451402285142499252075309)
                    ·
                      refine ⟨2044275856928437219528241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451402285142499252075309 2044275856928437219528241)
                      ·
                        rfl

theorem cell23_3981213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3981213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981213 prefixEnd_3981213 := by exact prefixLift 3981213
  have htrace : WordTrace (prefixWord ++ tailWord_3981213) baseStart_3981213 baseEnd_3981213 := by
    simpa [prefixWord, tailWord_3981213, baseEnd_3981213] using wordTrace_append hprefix tailTrace_3981213
  have hstable : (prefixWord ++ tailWord_3981213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981213).length < 2 ^ (prefixWord ++ tailWord_3981213).sum := by decide
  have hdescent : baseEnd_3981213 < baseStart_3981213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981232 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_3981232 : Nat := 118140960795 + 3981232 * 2 ^ 59
def prefixEnd_3981232 : Nat := 4983230072969 + 3 ^ 40 * 3981232 * 2
def baseEnd_3981232 : Nat := 2044285613060872645190653

theorem tailTrace_3981232 : CollatzResearch.WordTrace tailWord_3981232 prefixEnd_3981232 2044285613060872645190653 := by
  unfold tailWord_3981232
  simp only [CollatzResearch.WordTrace]
  refine ⟨72603730156341939568948975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96804973541789252758598633 72603730156341939568948975)
  ·
    refine ⟨108905595234512909353423463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72603730156341939568948975 108905595234512909353423463)
    ·
      refine ⟨163358392851769364030135195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108905595234512909353423463 163358392851769364030135195)
      ·
        refine ⟨245037589277654046045202793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163358392851769364030135195 245037589277654046045202793)
        ·
          refine ⟨183778191958240534533902095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245037589277654046045202793 183778191958240534533902095)
          ·
            refine ⟨275667287937360801800853143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183778191958240534533902095 275667287937360801800853143)
            ·
              refine ⟨413500931906041202701279715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275667287937360801800853143 413500931906041202701279715)
              ·
                refine ⟨620251397859061804051919573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413500931906041202701279715 620251397859061804051919573)
                ·
                  refine ⟨14537142137321761032466865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 620251397859061804051919573 14537142137321761032466865)
                  ·
                    refine ⟨10902856602991320774350149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14537142137321761032466865 10902856602991320774350149)
                    ·
                      refine ⟨2044285613060872645190653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10902856602991320774350149 2044285613060872645190653)
                      ·
                        rfl

theorem cell23_3981232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_3981232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981232 prefixEnd_3981232 := by exact prefixLift 3981232
  have htrace : WordTrace (prefixWord ++ tailWord_3981232) baseStart_3981232 baseEnd_3981232 := by
    simpa [prefixWord, tailWord_3981232, baseEnd_3981232] using wordTrace_append hprefix tailTrace_3981232
  have hstable : (prefixWord ++ tailWord_3981232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981232).length < 2 ^ (prefixWord ++ tailWord_3981232).sum := by decide
  have hdescent : baseEnd_3981232 < baseStart_3981232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981256 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_3981256 : Nat := 118140960795 + 3981256 * 2 ^ 59
def prefixEnd_3981256 : Nat := 4983230072969 + 3 ^ 40 * 3981256 * 2
def baseEnd_3981256 : Nat := 2044297936596580551290543

theorem tailTrace_3981256 : CollatzResearch.WordTrace tailWord_3981256 prefixEnd_3981256 2044297936596580551290543 := by
  unfold tailWord_3981256
  simp only [CollatzResearch.WordTrace]
  refine ⟨72604167832298465618385811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96805557109731287491181081 72604167832298465618385811)
  ·
    refine ⟨108906251748447698427578717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72604167832298465618385811 108906251748447698427578717)
    ·
      refine ⟨40839844405667886910342019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108906251748447698427578717 40839844405667886910342019)
      ·
        refine ⟨61259766608501830365513029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40839844405667886910342019 61259766608501830365513029)
        ·
          refine ⟨11486206239094093193533693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61259766608501830365513029 11486206239094093193533693)
          ·
            refine ⟨4307327339660284947575135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11486206239094093193533693 4307327339660284947575135)
            ·
              refine ⟨6460991009490427421362703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307327339660284947575135 6460991009490427421362703)
              ·
                refine ⟨9691486514235641132044055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460991009490427421362703 9691486514235641132044055)
                ·
                  refine ⟨14537229771353461698066083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9691486514235641132044055 14537229771353461698066083)
                  ·
                    refine ⟨21805844657030192547099125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14537229771353461698066083 21805844657030192547099125)
                    ·
                      refine ⟨2044297936596580551290543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21805844657030192547099125 2044297936596580551290543)
                      ·
                        rfl

theorem cell23_3981256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_3981256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981256 prefixEnd_3981256 := by exact prefixLift 3981256
  have htrace : WordTrace (prefixWord ++ tailWord_3981256) baseStart_3981256 baseEnd_3981256 := by
    simpa [prefixWord, tailWord_3981256, baseEnd_3981256] using wordTrace_append hprefix tailTrace_3981256
  have hstable : (prefixWord ++ tailWord_3981256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981256).length < 2 ^ (prefixWord ++ tailWord_3981256).sum := by decide
  have hdescent : baseEnd_3981256 < baseStart_3981256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981272 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_3981272 : Nat := 118140960795 + 3981272 * 2 ^ 59
def prefixEnd_3981272 : Nat := 4983230072969 + 3 ^ 40 * 3981272 * 2
def baseEnd_3981272 : Nat := 681435384095684162896823

theorem tailTrace_3981272 : CollatzResearch.WordTrace tailWord_3981272 prefixEnd_3981272 681435384095684162896823 := by
  unfold tailWord_3981272
  simp only [CollatzResearch.WordTrace]
  refine ⟨72604459616269482984677035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96805946155025977312902713 72604459616269482984677035)
  ·
    refine ⟨108906689424404224477015553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72604459616269482984677035 108906689424404224477015553)
    ·
      refine ⟨81680017068303168357761665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108906689424404224477015553 81680017068303168357761665)
      ·
        refine ⟨61260012801227376268321249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81680017068303168357761665 61260012801227376268321249)
        ·
          refine ⟨45945009600920532201240937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61260012801227376268321249 45945009600920532201240937)
          ·
            refine ⟨34458757200690399150930703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45945009600920532201240937 34458757200690399150930703)
            ·
              refine ⟨51688135801035598726396055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34458757200690399150930703 51688135801035598726396055)
              ·
                refine ⟨77532203701553398089594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51688135801035598726396055 77532203701553398089594083)
                ·
                  refine ⟨116298305552330097134391125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77532203701553398089594083 116298305552330097134391125)
                  ·
                    refine ⟨681435384095684162896823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116298305552330097134391125 681435384095684162896823)
                    ·
                      rfl

theorem cell23_3981272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_3981272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981272 prefixEnd_3981272 := by exact prefixLift 3981272
  have htrace : WordTrace (prefixWord ++ tailWord_3981272) baseStart_3981272 baseEnd_3981272 := by
    simpa [prefixWord, tailWord_3981272, baseEnd_3981272] using wordTrace_append hprefix tailTrace_3981272
  have hstable : (prefixWord ++ tailWord_3981272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981272).length < 2 ^ (prefixWord ++ tailWord_3981272).sum := by decide
  have hdescent : baseEnd_3981272 < baseStart_3981272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981293 : List Nat := [1, 5, 1, 4, 1, 1, 3, 7]
def baseStart_3981293 : Nat := 118140960795 + 3981293 * 2 ^ 59
def prefixEnd_3981293 : Nat := 4983230072969 + 3 ^ 40 * 3981293 * 2
def baseEnd_3981293 : Nat := 75715442051140626167699

theorem tailTrace_3981293 : CollatzResearch.WordTrace tailWord_3981293 prefixEnd_3981293 75715442051140626167699 := by
  unfold tailWord_3981293
  simp only [CollatzResearch.WordTrace]
  refine ⟨145209685165462886555868533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96806456776975257703912355 145209685165462886555868533)
  ·
    refine ⟨13613407984262145614612675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145209685165462886555868533 13613407984262145614612675)
    ·
      refine ⟨20420111976393218421919013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13613407984262145614612675 20420111976393218421919013)
      ·
        refine ⟨3828770995573728454109815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20420111976393218421919013 3828770995573728454109815)
        ·
          refine ⟨5743156493360592681164723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828770995573728454109815 5743156493360592681164723)
          ·
            refine ⟨8614734740040889021747085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743156493360592681164723 8614734740040889021747085)
            ·
              refine ⟨3230525527515333383155157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8614734740040889021747085 3230525527515333383155157)
              ·
                refine ⟨75715442051140626167699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3230525527515333383155157 75715442051140626167699)
                ·
                  rfl

theorem cell23_3981293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 7].length) (baseStart_3981293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981293 prefixEnd_3981293 := by exact prefixLift 3981293
  have htrace : WordTrace (prefixWord ++ tailWord_3981293) baseStart_3981293 baseEnd_3981293 := by
    simpa [prefixWord, tailWord_3981293, baseEnd_3981293] using wordTrace_append hprefix tailTrace_3981293
  have hstable : (prefixWord ++ tailWord_3981293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981293).length < 2 ^ (prefixWord ++ tailWord_3981293).sum := by decide
  have hdescent : baseEnd_3981293 < baseStart_3981293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981296 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2]
def baseStart_3981296 : Nat := 118140960795 + 3981296 * 2 ^ 59
def prefixEnd_3981296 : Nat := 4983230072969 + 3 ^ 40 * 3981296 * 2
def baseEnd_3981296 : Nat := 2044318475822760394790359

theorem tailTrace_3981296 : CollatzResearch.WordTrace tailWord_3981296 prefixEnd_3981296 2044318475822760394790359 := by
  unfold tailWord_3981296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72604897292226009034113871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96806529722968012045485161 72604897292226009034113871)
  ·
    refine ⟨108907345938339013551170807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72604897292226009034113871 108907345938339013551170807)
    ·
      refine ⟨163361018907508520326756211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108907345938339013551170807 163361018907508520326756211)
      ·
        refine ⟨245041528361262780490134317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163361018907508520326756211 245041528361262780490134317)
        ·
          refine ⟨91890573135473542683800369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245041528361262780490134317 91890573135473542683800369)
          ·
            refine ⟨68917929851605157012850277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91890573135473542683800369 68917929851605157012850277)
            ·
              refine ⟨12922111847175966939909427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68917929851605157012850277 12922111847175966939909427)
              ·
                refine ⟨19383167770763950409864141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922111847175966939909427 19383167770763950409864141)
                ·
                  refine ⟨7268687914036481403699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19383167770763950409864141 7268687914036481403699053)
                  ·
                    refine ⟨2725757967763680526387145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7268687914036481403699053 2725757967763680526387145)
                    ·
                      refine ⟨2044318475822760394790359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725757967763680526387145 2044318475822760394790359)
                      ·
                        rfl

theorem cell23_3981296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 3, 2].length) (baseStart_3981296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981296 prefixEnd_3981296 := by exact prefixLift 3981296
  have htrace : WordTrace (prefixWord ++ tailWord_3981296) baseStart_3981296 baseEnd_3981296 := by
    simpa [prefixWord, tailWord_3981296, baseEnd_3981296] using wordTrace_append hprefix tailTrace_3981296
  have hstable : (prefixWord ++ tailWord_3981296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981296).length < 2 ^ (prefixWord ++ tailWord_3981296).sum := by decide
  have hdescent : baseEnd_3981296 < baseStart_3981296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981313 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3981313 : Nat := 118140960795 + 3981313 * 2 ^ 59
def prefixEnd_3981313 : Nat := 4983230072969 + 3 ^ 40 * 3981313 * 2
def baseEnd_3981313 : Nat := 2044327204993886828277781

theorem tailTrace_3981313 : CollatzResearch.WordTrace tailWord_3981313 prefixEnd_3981313 2044327204993886828277781 := by
  unfold tailWord_3981313
  simp only [CollatzResearch.WordTrace]
  refine ⟨145210414625390429971596593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96806943083593619981064395 145210414625390429971596593)
  ·
    refine ⟨108907810969042822478697445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145210414625390429971596593 108907810969042822478697445)
    ·
      refine ⟨20420214556695529214755771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108907810969042822478697445 20420214556695529214755771)
      ·
        refine ⟨30630321835043293822133657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20420214556695529214755771 30630321835043293822133657)
        ·
          refine ⟨22972741376282470366600243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30630321835043293822133657 22972741376282470366600243)
          ·
            refine ⟨34459112064423705549900365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22972741376282470366600243 34459112064423705549900365)
            ·
              refine ⟨12922167024158889581212637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34459112064423705549900365 12922167024158889581212637)
              ·
                refine ⟨4845812634059583592954739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12922167024158889581212637 4845812634059583592954739)
                ·
                  refine ⟨7268718951089375389432109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845812634059583592954739 7268718951089375389432109)
                  ·
                    refine ⟨2725769606658515771037041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7268718951089375389432109 2725769606658515771037041)
                    ·
                      refine ⟨2044327204993886828277781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725769606658515771037041 2044327204993886828277781)
                      ·
                        rfl

theorem cell23_3981313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3981313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981313 prefixEnd_3981313 := by exact prefixLift 3981313
  have htrace : WordTrace (prefixWord ++ tailWord_3981313) baseStart_3981313 baseEnd_3981313 := by
    simpa [prefixWord, tailWord_3981313, baseEnd_3981313] using wordTrace_append hprefix tailTrace_3981313
  have hstable : (prefixWord ++ tailWord_3981313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981313).length < 2 ^ (prefixWord ++ tailWord_3981313).sum := by decide
  have hdescent : baseEnd_3981313 < baseStart_3981313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981319 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3981319 : Nat := 118140960795 + 3981319 * 2 ^ 59
def prefixEnd_3981319 : Nat := 4983230072969 + 3 ^ 40 * 3981319 * 2
def baseEnd_3981319 : Nat := 681443428625937934934251

theorem tailTrace_3981319 : CollatzResearch.WordTrace tailWord_3981319 prefixEnd_3981319 681443428625937934934251 := by
  unfold tailWord_3981319
  simp only [CollatzResearch.WordTrace]
  refine ⟨145210633463368692996315011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96807088975579128664210007 145210633463368692996315011)
  ·
    refine ⟨217815950195053039494472517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145210633463368692996315011 217815950195053039494472517)
    ·
      refine ⟨40840490661572444905213597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217815950195053039494472517 40840490661572444905213597)
      ·
        refine ⟨15315183998089666839455099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40840490661572444905213597 15315183998089666839455099)
        ·
          refine ⟨22972775997134500259182649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15315183998089666839455099 22972775997134500259182649)
          ·
            refine ⟨17229581997850875194386987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22972775997134500259182649 17229581997850875194386987)
            ·
              refine ⟨25844372996776312791580481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17229581997850875194386987 25844372996776312791580481)
              ·
                refine ⟨19383279747582234593685361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25844372996776312791580481 19383279747582234593685361)
                ·
                  refine ⟨14537459810686675945264021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19383279747582234593685361 14537459810686675945264021)
                  ·
                    refine ⟨681443428625937934934251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14537459810686675945264021 681443428625937934934251)
                    ·
                      rfl

theorem cell23_3981319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3981319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981319 prefixEnd_3981319 := by exact prefixLift 3981319
  have htrace : WordTrace (prefixWord ++ tailWord_3981319) baseStart_3981319 baseEnd_3981319 := by
    simpa [prefixWord, tailWord_3981319, baseEnd_3981319] using wordTrace_append hprefix tailTrace_3981319
  have hstable : (prefixWord ++ tailWord_3981319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981319).length < 2 ^ (prefixWord ++ tailWord_3981319).sum := by decide
  have hdescent : baseEnd_3981319 < baseStart_3981319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981349 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 7]
def baseStart_3981349 : Nat := 118140960795 + 3981349 * 2 ^ 59
def prefixEnd_3981349 : Nat := 4983230072969 + 3 ^ 40 * 3981349 * 2
def baseEnd_3981349 : Nat := 227149521144160965269735

theorem tailTrace_3981349 : CollatzResearch.WordTrace tailWord_3981349 prefixEnd_3981349 227149521144160965269735 := by
  unfold tailWord_3981349
  simp only [CollatzResearch.WordTrace]
  refine ⟨145211727653260008119907101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96807818435506672079938067 145211727653260008119907101)
  ·
    refine ⟨54454397869972503044965163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145211727653260008119907101 54454397869972503044965163)
    ·
      refine ⟨81681596804958754567447745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54454397869972503044965163 81681596804958754567447745)
      ·
        refine ⟨61261197603719065925585809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81681596804958754567447745 61261197603719065925585809)
        ·
          refine ⟨45945898202789299444189357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61261197603719065925585809 45945898202789299444189357)
          ·
            refine ⟨17229711826045987291571009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45945898202789299444189357 17229711826045987291571009)
            ·
              refine ⟨12922283869534490468678257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17229711826045987291571009 12922283869534490468678257)
              ·
                refine ⟨9691712902150867851508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12922283869534490468678257 9691712902150867851508693)
                ·
                  refine ⟨227149521144160965269735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9691712902150867851508693 227149521144160965269735)
                  ·
                    rfl

theorem cell23_3981349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_3981349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981349 prefixEnd_3981349 := by exact prefixLift 3981349
  have htrace : WordTrace (prefixWord ++ tailWord_3981349) baseStart_3981349 baseEnd_3981349 := by
    simpa [prefixWord, tailWord_3981349, baseEnd_3981349] using wordTrace_append hprefix tailTrace_3981349
  have hstable : (prefixWord ++ tailWord_3981349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981349).length < 2 ^ (prefixWord ++ tailWord_3981349).sum := by decide
  have hdescent : baseEnd_3981349 < baseStart_3981349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_3981359 : Nat := 118140960795 + 3981359 * 2 ^ 59
def prefixEnd_3981359 : Nat := 4983230072969 + 3 ^ 40 * 3981359 * 2
def baseEnd_3981359 : Nat := 2044350825103993648302569

theorem tailTrace_3981359 : CollatzResearch.WordTrace tailWord_3981359 prefixEnd_3981359 2044350825103993648302569 := by
  unfold tailWord_3981359
  simp only [CollatzResearch.WordTrace]
  refine ⟨145212092383223779827771131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96808061588815853218514087 145212092383223779827771131)
  ·
    refine ⟨217818138574835669741656697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145212092383223779827771131 217818138574835669741656697)
    ·
      refine ⟨163363603931126752306242523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217818138574835669741656697 163363603931126752306242523)
      ·
        refine ⟨245045405896690128459363785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163363603931126752306242523 245045405896690128459363785)
        ·
          refine ⟨183784054422517596344522839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245045405896690128459363785 183784054422517596344522839)
          ·
            refine ⟨275676081633776394516784259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183784054422517596344522839 275676081633776394516784259)
            ·
              refine ⟨413514122450664591775176389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275676081633776394516784259 413514122450664591775176389)
              ·
                refine ⟨77533897959499610957845573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413514122450664591775176389 77533897959499610957845573)
                ·
                  refine ⟨14537605867406177054596045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77533897959499610957845573 14537605867406177054596045)
                  ·
                    refine ⟨5451602200277316395473517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14537605867406177054596045 5451602200277316395473517)
                    ·
                      refine ⟨2044350825103993648302569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451602200277316395473517 2044350825103993648302569)
                      ·
                        rfl

theorem cell23_3981359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_3981359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981359 prefixEnd_3981359 := by exact prefixLift 3981359
  have htrace : WordTrace (prefixWord ++ tailWord_3981359) baseStart_3981359 baseEnd_3981359 := by
    simpa [prefixWord, tailWord_3981359, baseEnd_3981359] using wordTrace_append hprefix tailTrace_3981359
  have hstable : (prefixWord ++ tailWord_3981359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981359).length < 2 ^ (prefixWord ++ tailWord_3981359).sum := by decide
  have hdescent : baseEnd_3981359 < baseStart_3981359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981383 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 5]
def baseStart_3981383 : Nat := 118140960795 + 3981383 * 2 ^ 59
def prefixEnd_3981383 : Nat := 4983230072969 + 3 ^ 40 * 3981383 * 2
def baseEnd_3981383 : Nat := 227151460959966839378051

theorem tailTrace_3981383 : CollatzResearch.WordTrace tailWord_3981383 prefixEnd_3981383 227151460959966839378051 := by
  unfold tailWord_3981383
  simp only [CollatzResearch.WordTrace]
  refine ⟨145212967735136831926644803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96808645156757887951096535 145212967735136831926644803)
  ·
    refine ⟨217819451602705247889967205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145212967735136831926644803 217819451602705247889967205)
    ·
      refine ⟨40841147175507233979368851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217819451602705247889967205 40841147175507233979368851)
      ·
        refine ⟨61261720763260850969053277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40841147175507233979368851 61261720763260850969053277)
        ·
          refine ⟨22973145286222819113394979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61261720763260850969053277 22973145286222819113394979)
          ·
            refine ⟨34459717929334228670092469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22973145286222819113394979 34459717929334228670092469)
            ·
              refine ⟨3230598555875083937821169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34459717929334228670092469 3230598555875083937821169)
              ·
                refine ⟨2422948916906312953365877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230598555875083937821169 2422948916906312953365877)
                ·
                  refine ⟨227151460959966839378051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422948916906312953365877 227151460959966839378051)
                  ·
                    rfl

theorem cell23_3981383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 5].length) (baseStart_3981383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981383 prefixEnd_3981383 := by exact prefixLift 3981383
  have htrace : WordTrace (prefixWord ++ tailWord_3981383) baseStart_3981383 baseEnd_3981383 := by
    simpa [prefixWord, tailWord_3981383, baseEnd_3981383] using wordTrace_append hprefix tailTrace_3981383
  have hstable : (prefixWord ++ tailWord_3981383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981383).length < 2 ^ (prefixWord ++ tailWord_3981383).sum := by decide
  have hdescent : baseEnd_3981383 < baseStart_3981383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981386 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_3981386 : Nat := 118140960795 + 3981386 * 2 ^ 59
def prefixEnd_3981386 : Nat := 4983230072969 + 3 ^ 40 * 3981386 * 2
def baseEnd_3981386 : Nat := 2044364689081665042664945

theorem tailTrace_3981386 : CollatzResearch.WordTrace tailWord_3981386 prefixEnd_3981386 2044364689081665042664945 := by
  unfold tailWord_3981386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303269288531490859751003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96808718102750642292669341 36303269288531490859751003)
  ·
    refine ⟨54454903932797236289626505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303269288531490859751003 54454903932797236289626505)
    ·
      refine ⟨40841177949597927217219879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54454903932797236289626505 40841177949597927217219879)
      ·
        refine ⟨61261766924396890825829819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40841177949597927217219879 61261766924396890825829819)
        ·
          refine ⟨91892650386595336238744729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61261766924396890825829819 91892650386595336238744729)
          ·
            refine ⟨68919487789946502179058547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91892650386595336238744729 68919487789946502179058547)
            ·
              refine ⟨103379231684919753268587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68919487789946502179058547 103379231684919753268587821)
              ·
                refine ⟨38767211881844907475720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103379231684919753268587821 38767211881844907475720433)
                ·
                  refine ⟨29075408911383680606790325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38767211881844907475720433 29075408911383680606790325)
                  ·
                    refine ⟨2725819585442220056886593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29075408911383680606790325 2725819585442220056886593)
                    ·
                      refine ⟨2044364689081665042664945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725819585442220056886593 2044364689081665042664945)
                      ·
                        rfl

theorem cell23_3981386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_3981386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981386 prefixEnd_3981386 := by exact prefixLift 3981386
  have htrace : WordTrace (prefixWord ++ tailWord_3981386) baseStart_3981386 baseEnd_3981386 := by
    simpa [prefixWord, tailWord_3981386, baseEnd_3981386] using wordTrace_append hprefix tailTrace_3981386
  have hstable : (prefixWord ++ tailWord_3981386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981386).length < 2 ^ (prefixWord ++ tailWord_3981386).sum := by decide
  have hdescent : baseEnd_3981386 < baseStart_3981386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981394 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_3981394 : Nat := 118140960795 + 3981394 * 2 ^ 59
def prefixEnd_3981394 : Nat := 4983230072969 + 3 ^ 40 * 3981394 * 2
def baseEnd_3981394 : Nat := 2044368796926901011364909

theorem tailTrace_3981394 : CollatzResearch.WordTrace tailWord_3981394 prefixEnd_3981394 2044368796926901011364909 := by
  unfold tailWord_3981394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303342234524245201323809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96808912625397987203530157 36303342234524245201323809)
  ·
    refine ⟨27227506675893183900992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36303342234524245201323809 27227506675893183900992857)
    ·
      refine ⟨20420630006919887925744643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27227506675893183900992857 20420630006919887925744643)
      ·
        refine ⟨30630945010379831888616965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20420630006919887925744643 30630945010379831888616965)
        ·
          refine ⟨5743302189446218479115681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30630945010379831888616965 5743302189446218479115681)
          ·
            refine ⟨4307476642084663859336761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743302189446218479115681 4307476642084663859336761)
            ·
              refine ⟨3230607481563497894502571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307476642084663859336761 3230607481563497894502571)
              ·
                refine ⟨4845911222345246841753857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230607481563497894502571 4845911222345246841753857)
                ·
                  refine ⟨3634433416758935131315393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4845911222345246841753857 3634433416758935131315393)
                  ·
                    refine ⟨2725825062569201348486545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634433416758935131315393 2725825062569201348486545)
                    ·
                      refine ⟨2044368796926901011364909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725825062569201348486545 2044368796926901011364909)
                      ·
                        rfl

theorem cell23_3981394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_3981394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981394 prefixEnd_3981394 := by exact prefixLift 3981394
  have htrace : WordTrace (prefixWord ++ tailWord_3981394) baseStart_3981394 baseEnd_3981394 := by
    simpa [prefixWord, tailWord_3981394, baseEnd_3981394] using wordTrace_append hprefix tailTrace_3981394
  have hstable : (prefixWord ++ tailWord_3981394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981394).length < 2 ^ (prefixWord ++ tailWord_3981394).sum := by decide
  have hdescent : baseEnd_3981394 < baseStart_3981394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981399 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3981399 : Nat := 118140960795 + 3981399 * 2 ^ 59
def prefixEnd_3981399 : Nat := 4983230072969 + 3 ^ 40 * 3981399 * 2
def baseEnd_3981399 : Nat := 2044371364330173491802385

theorem tailTrace_3981399 : CollatzResearch.WordTrace tailWord_3981399 prefixEnd_3981399 2044371364330173491802385 := by
  unfold tailWord_3981399
  simp only [CollatzResearch.WordTrace]
  refine ⟨145213551303078866659227251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96809034202052577772818167 145213551303078866659227251)
  ·
    refine ⟨217820326954618299988840877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145213551303078866659227251 217820326954618299988840877)
    ·
      refine ⟨81682622607981862495815329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217820326954618299988840877 81682622607981862495815329)
      ·
        refine ⟨61261966955986396871861497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81682622607981862495815329 61261966955986396871861497)
        ·
          refine ⟨45946475216989797653896123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61261966955986396871861497 45946475216989797653896123)
          ·
            refine ⟨68919712825484696480844185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45946475216989797653896123 68919712825484696480844185)
            ·
              refine ⟨51689784619113522360633139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68919712825484696480844185 51689784619113522360633139)
              ·
                refine ⟨77534676928670283540949709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51689784619113522360633139 77534676928670283540949709)
                ·
                  refine ⟨29075503848251356327856141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77534676928670283540949709 29075503848251356327856141)
                  ·
                    refine ⟨10903313943094258622946053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29075503848251356327856141 10903313943094258622946053)
                    ·
                      refine ⟨2044371364330173491802385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10903313943094258622946053 2044371364330173491802385)
                      ·
                        rfl

theorem cell23_3981399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3981399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981399 prefixEnd_3981399 := by exact prefixLift 3981399
  have htrace : WordTrace (prefixWord ++ tailWord_3981399) baseStart_3981399 baseEnd_3981399 := by
    simpa [prefixWord, tailWord_3981399, baseEnd_3981399] using wordTrace_append hprefix tailTrace_3981399
  have hstable : (prefixWord ++ tailWord_3981399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981399).length < 2 ^ (prefixWord ++ tailWord_3981399).sum := by decide
  have hdescent : baseEnd_3981399 < baseStart_3981399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981470 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3981470 : Nat := 118140960795 + 3981470 * 2 ^ 59
def prefixEnd_3981470 : Nat := 4983230072969 + 3 ^ 40 * 3981470 * 2
def baseEnd_3981470 : Nat := 2044407821456642714014559

theorem tailTrace_3981470 : CollatzResearch.WordTrace tailWord_3981470 prefixEnd_3981470 2044407821456642714014559 := by
  unfold tailWord_3981470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152017610727705723132733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96810760590547763856707909 18152017610727705723132733)
  ·
    refine ⟨6807006604022889646174775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18152017610727705723132733 6807006604022889646174775)
    ·
      refine ⟨10210509906034334469262163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807006604022889646174775 10210509906034334469262163)
      ·
        refine ⟨15315764859051501703893245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210509906034334469262163 15315764859051501703893245)
        ·
          refine ⟨5743411822144313138959967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15315764859051501703893245 5743411822144313138959967)
          ·
            refine ⟨8615117733216469708439951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743411822144313138959967 8615117733216469708439951)
            ·
              refine ⟨12922676599824704562659927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615117733216469708439951 12922676599824704562659927)
              ·
                refine ⟨19384014899737056843989891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922676599824704562659927 19384014899737056843989891)
                ·
                  refine ⟨29076022349605585265984837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19384014899737056843989891 29076022349605585265984837)
                  ·
                    refine ⟨5451754190551047237372157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29076022349605585265984837 5451754190551047237372157)
                    ·
                      refine ⟨2044407821456642714014559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451754190551047237372157 2044407821456642714014559)
                      ·
                        rfl

theorem cell23_3981470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3981470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981470 prefixEnd_3981470 := by exact prefixLift 3981470
  have htrace : WordTrace (prefixWord ++ tailWord_3981470) baseStart_3981470 baseEnd_3981470 := by
    simpa [prefixWord, tailWord_3981470, baseEnd_3981470] using wordTrace_append hprefix tailTrace_3981470
  have hstable : (prefixWord ++ tailWord_3981470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981470).length < 2 ^ (prefixWord ++ tailWord_3981470).sum := by decide
  have hdescent : baseEnd_3981470 < baseStart_3981470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981536 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3981536 : Nat := 118140960795 + 3981536 * 2 ^ 59
def prefixEnd_3981536 : Nat := 4983230072969 + 3 ^ 40 * 3981536 * 2
def baseEnd_3981536 : Nat := 2044441711179839455789255

theorem tailTrace_3981536 : CollatzResearch.WordTrace tailWord_3981536 prefixEnd_3981536 2044441711179839455789255 := by
  unfold tailWord_3981536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72609274051791269528482231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96812365402388359371309641 72609274051791269528482231)
  ·
    refine ⟨108913911077686904292723347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72609274051791269528482231 108913911077686904292723347)
    ·
      refine ⟨163370866616530356439085021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108913911077686904292723347 163370866616530356439085021)
      ·
        refine ⟨61264074981198883664656883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163370866616530356439085021 61264074981198883664656883)
        ·
          refine ⟨91896112471798325496985325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61264074981198883664656883 91896112471798325496985325)
          ·
            refine ⟨34461042176924372061369497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91896112471798325496985325 34461042176924372061369497)
            ·
              refine ⟨25845781632693279046027123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34461042176924372061369497 25845781632693279046027123)
              ·
                refine ⟨38768672449039918569040685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25845781632693279046027123 38768672449039918569040685)
                ·
                  refine ⟨14538252168389969463390257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38768672449039918569040685 14538252168389969463390257)
                  ·
                    refine ⟨10903689126292477097542693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14538252168389969463390257 10903689126292477097542693)
                    ·
                      refine ⟨2044441711179839455789255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10903689126292477097542693 2044441711179839455789255)
                      ·
                        rfl

theorem cell23_3981536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3981536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981536 prefixEnd_3981536 := by exact prefixLift 3981536
  have htrace : WordTrace (prefixWord ++ tailWord_3981536) baseStart_3981536 baseEnd_3981536 := by
    simpa [prefixWord, tailWord_3981536, baseEnd_3981536] using wordTrace_append hprefix tailTrace_3981536
  have hstable : (prefixWord ++ tailWord_3981536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981536).length < 2 ^ (prefixWord ++ tailWord_3981536).sum := by decide
  have hdescent : baseEnd_3981536 < baseStart_3981536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981543 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3981543 : Nat := 118140960795 + 3981543 * 2 ^ 59
def prefixEnd_3981543 : Nat := 4983230072969 + 3 ^ 40 * 3981543 * 2
def baseEnd_3981543 : Nat := 2044445305544420928401723

theorem tailTrace_3981543 : CollatzResearch.WordTrace tailWord_3981543 prefixEnd_3981543 2044445305544420928401723 := by
  unfold tailWord_3981543
  simp only [CollatzResearch.WordTrace]
  refine ⟨145218803414557179252469283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96812535609704786168312855 145218803414557179252469283)
  ·
    refine ⟨217828205121835768878703925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145218803414557179252469283 217828205121835768878703925)
    ·
      refine ⟨20421394230172103332378493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217828205121835768878703925 20421394230172103332378493)
      ·
        refine ⟨7658022836314538749641935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20421394230172103332378493 7658022836314538749641935)
        ·
          refine ⟨11487034254471808124462903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658022836314538749641935 11487034254471808124462903)
          ·
            refine ⟨17230551381707712186694355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487034254471808124462903 17230551381707712186694355)
            ·
              refine ⟨25845827072561568280041533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17230551381707712186694355 25845827072561568280041533)
              ·
                refine ⟨9692185152210588105015575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25845827072561568280041533 9692185152210588105015575)
                ·
                  refine ⟨14538277728315882157523363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9692185152210588105015575 14538277728315882157523363)
                  ·
                    refine ⟨21807416592473823236285045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14538277728315882157523363 21807416592473823236285045)
                    ·
                      refine ⟨2044445305544420928401723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21807416592473823236285045 2044445305544420928401723)
                      ·
                        rfl

theorem cell23_3981543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3981543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981543 prefixEnd_3981543 := by exact prefixLift 3981543
  have htrace : WordTrace (prefixWord ++ tailWord_3981543) baseStart_3981543 baseEnd_3981543 := by
    simpa [prefixWord, tailWord_3981543, baseEnd_3981543] using wordTrace_append hprefix tailTrace_3981543
  have hstable : (prefixWord ++ tailWord_3981543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981543).length < 2 ^ (prefixWord ++ tailWord_3981543).sum := by decide
  have hdescent : baseEnd_3981543 < baseStart_3981543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981573 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_3981573 : Nat := 118140960795 + 3981573 * 2 ^ 59
def prefixEnd_3981573 : Nat := 4983230072969 + 3 ^ 40 * 3981573 * 2
def baseEnd_3981573 : Nat := 2044460709964055811026585

theorem tailTrace_3981573 : CollatzResearch.WordTrace tailWord_3981573 prefixEnd_3981573 2044460709964055811026585 := by
  unfold tailWord_3981573
  simp only [CollatzResearch.WordTrace]
  refine ⟨145219897604448494376061373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96813265069632329584040915 145219897604448494376061373)
  ·
    refine ⟨54457461601668185391023015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145219897604448494376061373 54457461601668185391023015)
    ·
      refine ⟨81686192402502278086534523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54457461601668185391023015 81686192402502278086534523)
      ·
        refine ⟨122529288603753417129801785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81686192402502278086534523 122529288603753417129801785)
        ·
          refine ⟨91896966452815062847351339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122529288603753417129801785 91896966452815062847351339)
          ·
            refine ⟨137845449679222594271027009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91896966452815062847351339 137845449679222594271027009)
            ·
              refine ⟨103384087259416945703270257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137845449679222594271027009 103384087259416945703270257)
              ·
                refine ⟨77538065444562709277452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103384087259416945703270257 77538065444562709277452693)
                ·
                  refine ⟨3634596817713876997380595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77538065444562709277452693 3634596817713876997380595)
                  ·
                    refine ⟨5451895226570815496070893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3634596817713876997380595 5451895226570815496070893)
                    ·
                      refine ⟨2044460709964055811026585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5451895226570815496070893 2044460709964055811026585)
                      ·
                        rfl

theorem cell23_3981573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_3981573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981573 prefixEnd_3981573 := by exact prefixLift 3981573
  have htrace : WordTrace (prefixWord ++ tailWord_3981573) baseStart_3981573 baseEnd_3981573 := by
    simpa [prefixWord, tailWord_3981573, baseEnd_3981573] using wordTrace_append hprefix tailTrace_3981573
  have hstable : (prefixWord ++ tailWord_3981573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981573).length < 2 ^ (prefixWord ++ tailWord_3981573).sum := by decide
  have hdescent : baseEnd_3981573 < baseStart_3981573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981608 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3981608 : Nat := 118140960795 + 3981608 * 2 ^ 59
def prefixEnd_3981608 : Nat := 4983230072969 + 3 ^ 40 * 3981608 * 2
def baseEnd_3981608 : Nat := 2044478681786963174088925

theorem tailTrace_3981608 : CollatzResearch.WordTrace tailWord_3981608 prefixEnd_3981608 2044478681786963174088925 := by
  unfold tailWord_3981608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72610587079660847676792739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96814116106214463569056985 72610587079660847676792739)
  ·
    refine ⟨108915880619491271515189109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72610587079660847676792739 108915880619491271515189109)
    ·
      refine ⟨10210863808077306704548979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108915880619491271515189109 10210863808077306704548979)
      ·
        refine ⟨15316295712115960056823469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210863808077306704548979 15316295712115960056823469)
        ·
          refine ⟨5743610892043485021308801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15316295712115960056823469 5743610892043485021308801)
          ·
            refine ⟨4307708169032613765981601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743610892043485021308801 4307708169032613765981601)
            ·
              refine ⟨3230781126774460324486201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307708169032613765981601 3230781126774460324486201)
              ·
                refine ⟨2423085845080845243364651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230781126774460324486201 2423085845080845243364651)
                ·
                  refine ⟨3634628767621267865046977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423085845080845243364651 3634628767621267865046977)
                  ·
                    refine ⟨2725971575715950898785233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634628767621267865046977 2725971575715950898785233)
                    ·
                      refine ⟨2044478681786963174088925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2725971575715950898785233 2044478681786963174088925)
                      ·
                        rfl

theorem cell23_3981608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3981608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981608 prefixEnd_3981608 := by exact prefixLift 3981608
  have htrace : WordTrace (prefixWord ++ tailWord_3981608) baseStart_3981608 baseEnd_3981608 := by
    simpa [prefixWord, tailWord_3981608, baseEnd_3981608] using wordTrace_append hprefix tailTrace_3981608
  have hstable : (prefixWord ++ tailWord_3981608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981608).length < 2 ^ (prefixWord ++ tailWord_3981608).sum := by decide
  have hdescent : baseEnd_3981608 < baseStart_3981608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_3981616 : Nat := 118140960795 + 3981616 * 2 ^ 59
def prefixEnd_3981616 : Nat := 4983230072969 + 3 ^ 40 * 3981616 * 2
def baseEnd_3981616 : Nat := 2044482789632199142788887

theorem tailTrace_3981616 : CollatzResearch.WordTrace tailWord_3981616 prefixEnd_3981616 2044482789632199142788887 := by
  unfold tailWord_3981616
  simp only [CollatzResearch.WordTrace]
  refine ⟨72610732971646356359938351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96814310628861808479917801 72610732971646356359938351)
  ·
    refine ⟨108916099457469534539907527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72610732971646356359938351 108916099457469534539907527)
    ·
      refine ⟨163374149186204301809861291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108916099457469534539907527 163374149186204301809861291)
      ·
        refine ⟨245061223779306452714791937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163374149186204301809861291 245061223779306452714791937)
        ·
          refine ⟨183795917834479839536093953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245061223779306452714791937 183795917834479839536093953)
          ·
            refine ⟨137846938375859879652070465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183795917834479839536093953 137846938375859879652070465)
            ·
              refine ⟨103385203781894909739052849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137846938375859879652070465 103385203781894909739052849)
              ·
                refine ⟨77538902836421182304289637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103385203781894909739052849 77538902836421182304289637)
                ·
                  refine ⟨14538544281828971682054307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77538902836421182304289637 14538544281828971682054307)
                  ·
                    refine ⟨21807816422743457523081461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14538544281828971682054307 21807816422743457523081461)
                    ·
                      refine ⟨2044482789632199142788887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21807816422743457523081461 2044482789632199142788887)
                      ·
                        rfl

theorem cell23_3981616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_3981616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981616 prefixEnd_3981616 := by exact prefixLift 3981616
  have htrace : WordTrace (prefixWord ++ tailWord_3981616) baseStart_3981616 baseEnd_3981616 := by
    simpa [prefixWord, tailWord_3981616, baseEnd_3981616] using wordTrace_append hprefix tailTrace_3981616
  have hstable : (prefixWord ++ tailWord_3981616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981616).length < 2 ^ (prefixWord ++ tailWord_3981616).sum := by decide
  have hdescent : baseEnd_3981616 < baseStart_3981616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981663 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_3981663 : Nat := 118140960795 + 3981663 * 2 ^ 59
def prefixEnd_3981663 : Nat := 4983230072969 + 3 ^ 40 * 3981663 * 2
def baseEnd_3981663 : Nat := 2044506923222960458901171

theorem tailTrace_3981663 : CollatzResearch.WordTrace tailWord_3981663 prefixEnd_3981663 2044506923222960458901171 := by
  unfold tailWord_3981663
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223180174122439746837643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96815453449414959831225095 145223180174122439746837643)
  ·
    refine ⟨217834770261183659620256465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145223180174122439746837643 217834770261183659620256465)
    ·
      refine ⟨163376077695887744715192349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217834770261183659620256465 163376077695887744715192349)
      ·
        refine ⟨61266029135957904268197131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163376077695887744715192349 61266029135957904268197131)
        ·
          refine ⟨91899043703936856402295697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61266029135957904268197131 91899043703936856402295697)
          ·
            refine ⟨68924282777952642301721773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91899043703936856402295697 68924282777952642301721773)
            ·
              refine ⟨25846606041732240863145665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68924282777952642301721773 25846606041732240863145665)
              ·
                refine ⟨19384954531299180647359249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25846606041732240863145665 19384954531299180647359249)
                ·
                  refine ⟨14538715898474385485519437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19384954531299180647359249 14538715898474385485519437)
                  ·
                    refine ⟨5452018461927894557069789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14538715898474385485519437 5452018461927894557069789)
                    ·
                      refine ⟨2044506923222960458901171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5452018461927894557069789 2044506923222960458901171)
                      ·
                        rfl

theorem cell23_3981663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_3981663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981663 prefixEnd_3981663 := by exact prefixLift 3981663
  have htrace : WordTrace (prefixWord ++ tailWord_3981663) baseStart_3981663 baseEnd_3981663 := by
    simpa [prefixWord, tailWord_3981663, baseEnd_3981663] using wordTrace_append hprefix tailTrace_3981663
  have hstable : (prefixWord ++ tailWord_3981663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981663).length < 2 ^ (prefixWord ++ tailWord_3981663).sum := by decide
  have hdescent : baseEnd_3981663 < baseStart_3981663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981703 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3981703 : Nat := 118140960795 + 3981703 * 2 ^ 59
def prefixEnd_3981703 : Nat := 4983230072969 + 3 ^ 40 * 3981703 * 2
def baseEnd_3981703 : Nat := 2044527462449140302400987

theorem tailTrace_3981703 : CollatzResearch.WordTrace tailWord_3981703 prefixEnd_3981703 2044527462449140302400987 := by
  unfold tailWord_3981703
  simp only [CollatzResearch.WordTrace]
  refine ⟨145224639093977526578293763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96816426062651684385529175 145224639093977526578293763)
  ·
    refine ⟨217836958640966289867440645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145224639093977526578293763 217836958640966289867440645)
    ·
      refine ⟨40844429745181179350145121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217836958640966289867440645 40844429745181179350145121)
      ·
        refine ⟨30633322308885884512608841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40844429745181179350145121 30633322308885884512608841)
        ·
          refine ⟨22974991731664413384456631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30633322308885884512608841 22974991731664413384456631)
          ·
            refine ⟨34462487597496620076684947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22974991731664413384456631 34462487597496620076684947)
            ·
              refine ⟨51693731396244930115027421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34462487597496620076684947 51693731396244930115027421)
              ·
                refine ⟨19385149273591848793135283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51693731396244930115027421 19385149273591848793135283)
                ·
                  refine ⟨29077723910387773189702925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19385149273591848793135283 29077723910387773189702925)
                  ·
                    refine ⟨10904146466395414946138597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29077723910387773189702925 10904146466395414946138597)
                    ·
                      refine ⟨2044527462449140302400987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10904146466395414946138597 2044527462449140302400987)
                      ·
                        rfl

theorem cell23_3981703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3981703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981703 prefixEnd_3981703 := by exact prefixLift 3981703
  have htrace : WordTrace (prefixWord ++ tailWord_3981703) baseStart_3981703 baseEnd_3981703 := by
    simpa [prefixWord, tailWord_3981703, baseEnd_3981703] using wordTrace_append hprefix tailTrace_3981703
  have hstable : (prefixWord ++ tailWord_3981703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981703).length < 2 ^ (prefixWord ++ tailWord_3981703).sum := by decide
  have hdescent : baseEnd_3981703 < baseStart_3981703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981720 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3981720 : Nat := 118140960795 + 3981720 * 2 ^ 59
def prefixEnd_3981720 : Nat := 4983230072969 + 3 ^ 40 * 3981720 * 2
def baseEnd_3981720 : Nat := 2044536191620266735888409

theorem tailTrace_3981720 : CollatzResearch.WordTrace tailWord_3981720 prefixEnd_3981720 2044536191620266735888409 := by
  unfold tailWord_3981720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72612629567457969240831307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96816839423277292321108409 72612629567457969240831307)
  ·
    refine ⟨108918944351186953861246961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72612629567457969240831307 108918944351186953861246961)
    ·
      refine ⟨81689208263390215395935221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108918944351186953861246961 81689208263390215395935221)
      ·
        refine ⟨7658363274692832693368927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81689208263390215395935221 7658363274692832693368927)
        ·
          refine ⟨11487544912039249040053391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658363274692832693368927 11487544912039249040053391)
          ·
            refine ⟨17231317368058873560080087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487544912039249040053391 17231317368058873560080087)
            ·
              refine ⟨25846976052088310340120131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231317368058873560080087 25846976052088310340120131)
              ·
                refine ⟨38770464078132465510180197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25846976052088310340120131 38770464078132465510180197)
                ·
                  refine ⟨7269462014649837283158787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38770464078132465510180197 7269462014649837283158787)
                  ·
                    refine ⟨10904193021974755924738181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269462014649837283158787 10904193021974755924738181)
                    ·
                      refine ⟨2044536191620266735888409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10904193021974755924738181 2044536191620266735888409)
                      ·
                        rfl

theorem cell23_3981720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3981720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981720 prefixEnd_3981720 := by exact prefixLift 3981720
  have htrace : WordTrace (prefixWord ++ tailWord_3981720) baseStart_3981720 baseEnd_3981720 := by
    simpa [prefixWord, tailWord_3981720, baseEnd_3981720] using wordTrace_append hprefix tailTrace_3981720
  have hstable : (prefixWord ++ tailWord_3981720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981720).length < 2 ^ (prefixWord ++ tailWord_3981720).sum := by decide
  have hdescent : baseEnd_3981720 < baseStart_3981720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981757 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3981757 : Nat := 118140960795 + 3981757 * 2 ^ 59
def prefixEnd_3981757 : Nat := 4983230072969 + 3 ^ 40 * 3981757 * 2
def baseEnd_3981757 : Nat := 2044555190404483091125739

theorem tailTrace_3981757 : CollatzResearch.WordTrace tailWord_3981757 prefixEnd_3981757 2044555190404483091125739 := by
  unfold tailWord_3981757
  simp only [CollatzResearch.WordTrace]
  refine ⟨145226608635781893800759525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96817739090521262533839683 145226608635781893800759525)
  ·
    refine ⟨27229989119209105087642411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145226608635781893800759525 27229989119209105087642411)
    ·
      refine ⟨40844983678813657631463617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27229989119209105087642411 40844983678813657631463617)
      ·
        refine ⟨30633737759110243223597713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40844983678813657631463617 30633737759110243223597713)
        ·
          refine ⟨22975303319332682417698285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30633737759110243223597713 22975303319332682417698285)
          ·
            refine ⟨8615738744749755906636857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22975303319332682417698285 8615738744749755906636857)
            ·
              refine ⟨6461804058562316929977643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615738744749755906636857 6461804058562316929977643)
              ·
                refine ⟨9692706087843475394966465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461804058562316929977643 9692706087843475394966465)
                ·
                  refine ⟨7269529565882606546224849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692706087843475394966465 7269529565882606546224849)
                  ·
                    refine ⟨5452147174411954909668637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269529565882606546224849 5452147174411954909668637)
                    ·
                      refine ⟨2044555190404483091125739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5452147174411954909668637 2044555190404483091125739)
                      ·
                        rfl

theorem cell23_3981757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3981757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981757 prefixEnd_3981757 := by exact prefixLift 3981757
  have htrace : WordTrace (prefixWord ++ tailWord_3981757) baseStart_3981757 baseEnd_3981757 := by
    simpa [prefixWord, tailWord_3981757, baseEnd_3981757] using wordTrace_append hprefix tailTrace_3981757
  have hstable : (prefixWord ++ tailWord_3981757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981757).length < 2 ^ (prefixWord ++ tailWord_3981757).sum := by decide
  have hdescent : baseEnd_3981757 < baseStart_3981757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981781 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3981781 : Nat := 118140960795 + 3981781 * 2 ^ 59
def prefixEnd_3981781 : Nat := 4983230072969 + 3 ^ 40 * 3981781 * 2
def baseEnd_3981781 : Nat := 681522504646730332408543

theorem tailTrace_3981781 : CollatzResearch.WordTrace tailWord_3981781 prefixEnd_3981781 681522504646730332408543 := by
  unfold tailWord_3981781
  simp only [CollatzResearch.WordTrace]
  refine ⟨145227483987694945899633197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96818322658463297266422131 145227483987694945899633197)
  ·
    refine ⟨54460306495385604712362449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145227483987694945899633197 54460306495385604712362449)
    ·
      refine ⟨40845229871539203534271837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54460306495385604712362449 40845229871539203534271837)
      ·
        refine ⟨15316961201827201325351939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40845229871539203534271837 15316961201827201325351939)
        ·
          refine ⟨22975441802740801988027909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316961201827201325351939 22975441802740801988027909)
          ·
            refine ⟨4307895338013900372755233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22975441802740801988027909 4307895338013900372755233)
            ·
              refine ⟨3230921503510425279566425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307895338013900372755233 3230921503510425279566425)
              ·
                refine ⟨2423191127632818959674819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230921503510425279566425 2423191127632818959674819)
                ·
                  refine ⟨3634786691449228439512229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423191127632818959674819 3634786691449228439512229)
                  ·
                    refine ⟨681522504646730332408543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3634786691449228439512229 681522504646730332408543)
                    ·
                      rfl

theorem cell23_3981781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3981781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981781 prefixEnd_3981781 := by exact prefixLift 3981781
  have htrace : WordTrace (prefixWord ++ tailWord_3981781) baseStart_3981781 baseEnd_3981781 := by
    simpa [prefixWord, tailWord_3981781, baseEnd_3981781] using wordTrace_append hprefix tailTrace_3981781
  have hstable : (prefixWord ++ tailWord_3981781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981781).length < 2 ^ (prefixWord ++ tailWord_3981781).sum := by decide
  have hdescent : baseEnd_3981781 < baseStart_3981781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981820 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_3981820 : Nat := 118140960795 + 3981820 * 2 ^ 59
def prefixEnd_3981820 : Nat := 4983230072969 + 3 ^ 40 * 3981820 * 2
def baseEnd_3981820 : Nat := 681529179895238781545983

theorem tailTrace_3981820 : CollatzResearch.WordTrace tailWord_3981820 prefixEnd_3981820 681529179895238781545983 := by
  unfold tailWord_3981820
  simp only [CollatzResearch.WordTrace]
  refine ⟨72614453217276827780151457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96819270956369103706868609 72614453217276827780151457)
  ·
    refine ⟨54460839912957620835113593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72614453217276827780151457 54460839912957620835113593)
    ·
      refine ⟨40845629934718215626335195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54460839912957620835113593 40845629934718215626335195)
      ·
        refine ⟨61268444902077323439502793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40845629934718215626335195 61268444902077323439502793)
        ·
          refine ⟨45951333676557992579627095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61268444902077323439502793 45951333676557992579627095)
          ·
            refine ⟨68927000514836988869440643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45951333676557992579627095 68927000514836988869440643)
            ·
              refine ⟨103390500772255483304160965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68927000514836988869440643 103390500772255483304160965)
              ·
                refine ⟨19385718894797903119530181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103390500772255483304160965 19385718894797903119530181)
                ·
                  refine ⟨3634822292774606834911909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19385718894797903119530181 3634822292774606834911909)
                  ·
                    refine ⟨681529179895238781545983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3634822292774606834911909 681529179895238781545983)
                    ·
                      rfl

theorem cell23_3981820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_3981820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981820 prefixEnd_3981820 := by exact prefixLift 3981820
  have htrace : WordTrace (prefixWord ++ tailWord_3981820) baseStart_3981820 baseEnd_3981820 := by
    simpa [prefixWord, tailWord_3981820, baseEnd_3981820] using wordTrace_append hprefix tailTrace_3981820
  have hstable : (prefixWord ++ tailWord_3981820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981820).length < 2 ^ (prefixWord ++ tailWord_3981820).sum := by decide
  have hdescent : baseEnd_3981820 < baseStart_3981820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981827 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 5, 2, 2]
def baseStart_3981827 : Nat := 118140960795 + 3981827 * 2 ^ 59
def prefixEnd_3981827 : Nat := 4983230072969 + 3 ^ 40 * 3981827 * 2
def baseEnd_3981827 : Nat := 2044591134050297817250417

theorem tailTrace_3981827 : CollatzResearch.WordTrace tailWord_3981827 prefixEnd_3981827 2044591134050297817250417 := by
  unfold tailWord_3981827
  simp only [CollatzResearch.WordTrace]
  refine ⟨145229161745528295755807735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96819441163685530503871823 145229161745528295755807735)
  ·
    refine ⟨217843742618292443633711603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145229161745528295755807735 217843742618292443633711603)
    ·
      refine ⟨326765613927438665450567405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217843742618292443633711603 326765613927438665450567405)
      ·
        refine ⟨122537105222789499543962777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326765613927438665450567405 122537105222789499543962777)
        ·
          refine ⟨91902828917092124657972083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122537105222789499543962777 91902828917092124657972083)
          ·
            refine ⟨137854243375638186986958125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91902828917092124657972083 137854243375638186986958125)
            ·
              refine ⟨51695341265864320120109297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137854243375638186986958125 51695341265864320120109297)
              ·
                refine ⟨38771505949398240090081973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51695341265864320120109297 38771505949398240090081973)
                ·
                  refine ⟨3634828682756085008445185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38771505949398240090081973 3634828682756085008445185)
                  ·
                    refine ⟨2726121512067063756333889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3634828682756085008445185 2726121512067063756333889)
                    ·
                      refine ⟨2044591134050297817250417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726121512067063756333889 2044591134050297817250417)
                      ·
                        rfl

theorem cell23_3981827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_3981827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981827 prefixEnd_3981827 := by exact prefixLift 3981827
  have htrace : WordTrace (prefixWord ++ tailWord_3981827) baseStart_3981827 baseEnd_3981827 := by
    simpa [prefixWord, tailWord_3981827, baseEnd_3981827] using wordTrace_append hprefix tailTrace_3981827
  have hstable : (prefixWord ++ tailWord_3981827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981827).length < 2 ^ (prefixWord ++ tailWord_3981827).sum := by decide
  have hdescent : baseEnd_3981827 < baseStart_3981827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981864 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3981864 : Nat := 118140960795 + 3981864 * 2 ^ 59
def prefixEnd_3981864 : Nat := 4983230072969 + 3 ^ 40 * 3981864 * 2
def baseEnd_3981864 : Nat := 2044610132834514172487747

theorem tailTrace_3981864 : CollatzResearch.WordTrace tailWord_3981864 prefixEnd_3981864 2044610132834514172487747 := by
  unfold tailWord_3981864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72615255623197125537452323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96820340830929500716603097 72615255623197125537452323)
  ·
    refine ⟨108922883434795688306178485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72615255623197125537452323 108922883434795688306178485)
    ·
      refine ⟨10211520322012095778704233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108922883434795688306178485 10211520322012095778704233)
      ·
        refine ⟨7658640241509071834028175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10211520322012095778704233 7658640241509071834028175)
        ·
          refine ⟨11487960362263607751042263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658640241509071834028175 11487960362263607751042263)
          ·
            refine ⟨17231940543395411626563395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487960362263607751042263 17231940543395411626563395)
            ·
              refine ⟨25847910815093117439845093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231940543395411626563395 25847910815093117439845093)
              ·
                refine ⟨4846483277829959519970955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25847910815093117439845093 4846483277829959519970955)
                ·
                  refine ⟨7269724916744939279956433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846483277829959519970955 7269724916744939279956433)
                  ·
                    refine ⟨5452293687558704459967325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269724916744939279956433 5452293687558704459967325)
                    ·
                      refine ⟨2044610132834514172487747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5452293687558704459967325 2044610132834514172487747)
                      ·
                        rfl

theorem cell23_3981864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3981864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981864 prefixEnd_3981864 := by exact prefixLift 3981864
  have htrace : WordTrace (prefixWord ++ tailWord_3981864) baseStart_3981864 baseEnd_3981864 := by
    simpa [prefixWord, tailWord_3981864, baseEnd_3981864] using wordTrace_append hprefix tailTrace_3981864
  have hstable : (prefixWord ++ tailWord_3981864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981864).length < 2 ^ (prefixWord ++ tailWord_3981864).sum := by decide
  have hdescent : baseEnd_3981864 < baseStart_3981864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981877 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3981877 : Nat := 118140960795 + 3981877 * 2 ^ 59
def prefixEnd_3981877 : Nat := 4983230072969 + 3 ^ 40 * 3981877 * 2
def baseEnd_3981877 : Nat := 2044616808083022621625187

theorem tailTrace_3981877 : CollatzResearch.WordTrace tailWord_3981877 prefixEnd_3981877 2044616808083022621625187 := by
  unfold tailWord_3981877
  simp only [CollatzResearch.WordTrace]
  refine ⟨145230985395347154295127885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96820656930231436196751923 145230985395347154295127885)
  ·
    refine ⟨54461619523255182860672957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145230985395347154295127885 54461619523255182860672957)
    ·
      refine ⟨20423107321220693572752359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54461619523255182860672957 20423107321220693572752359)
      ·
        refine ⟨30634660981831040359128539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20423107321220693572752359 30634660981831040359128539)
        ·
          refine ⟨45951991472746560538692809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30634660981831040359128539 45951991472746560538692809)
          ·
            refine ⟨34463993604559920404019607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45951991472746560538692809 34463993604559920404019607)
            ·
              refine ⟨51695990406839880606029411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34463993604559920404019607 51695990406839880606029411)
              ·
                refine ⟨77543985610259820909044117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51695990406839880606029411 77543985610259820909044117)
                ·
                  refine ⟨3634874325480929105111443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77543985610259820909044117 3634874325480929105111443)
                  ·
                    refine ⟨5452311488221393657667165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3634874325480929105111443 5452311488221393657667165)
                    ·
                      refine ⟨2044616808083022621625187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5452311488221393657667165 2044616808083022621625187)
                      ·
                        rfl

theorem cell23_3981877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3981877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981877 prefixEnd_3981877 := by exact prefixLift 3981877
  have htrace : WordTrace (prefixWord ++ tailWord_3981877) baseStart_3981877 baseEnd_3981877 := by
    simpa [prefixWord, tailWord_3981877, baseEnd_3981877] using wordTrace_append hprefix tailTrace_3981877
  have hstable : (prefixWord ++ tailWord_3981877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981877).length < 2 ^ (prefixWord ++ tailWord_3981877).sum := by decide
  have hdescent : baseEnd_3981877 < baseStart_3981877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981900 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3981900 : Nat := 118140960795 + 3981900 * 2 ^ 59
def prefixEnd_3981900 : Nat := 4983230072969 + 3 ^ 40 * 3981900 * 2
def baseEnd_3981900 : Nat := 2044628618138076031637581

theorem tailTrace_3981900 : CollatzResearch.WordTrace tailWord_3981900 prefixEnd_3981900 2044628618138076031637581 := by
  unfold tailWord_3981900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72615912137131914611607577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96821216182842552815476769 72615912137131914611607577)
  ·
    refine ⟨54461934102848935958705683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72615912137131914611607577 54461934102848935958705683)
    ·
      refine ⟨81692901154273403938058525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54461934102848935958705683 81692901154273403938058525)
      ·
        refine ⟨30634837932852526476771947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81692901154273403938058525 30634837932852526476771947)
        ·
          refine ⟨45952256899278789715157921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30634837932852526476771947 45952256899278789715157921)
          ·
            refine ⟨34464192674459092286368441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45952256899278789715157921 34464192674459092286368441)
            ·
              refine ⟨25848144505844319214776331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34464192674459092286368441 25848144505844319214776331)
              ·
                refine ⟨38772216758766478822164497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25848144505844319214776331 38772216758766478822164497)
                ·
                  refine ⟨29079162569074859116623373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38772216758766478822164497 29079162569074859116623373)
                  ·
                    refine ⟨10904685963403072168733765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29079162569074859116623373 10904685963403072168733765)
                    ·
                      refine ⟨2044628618138076031637581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10904685963403072168733765 2044628618138076031637581)
                      ·
                        rfl

theorem cell23_3981900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3981900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981900 prefixEnd_3981900 := by exact prefixLift 3981900
  have htrace : WordTrace (prefixWord ++ tailWord_3981900) baseStart_3981900 baseEnd_3981900 := by
    simpa [prefixWord, tailWord_3981900, baseEnd_3981900] using wordTrace_append hprefix tailTrace_3981900
  have hstable : (prefixWord ++ tailWord_3981900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981900).length < 2 ^ (prefixWord ++ tailWord_3981900).sum := by decide
  have hdescent : baseEnd_3981900 < baseStart_3981900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981920 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3981920 : Nat := 118140960795 + 3981920 * 2 ^ 59
def prefixEnd_3981920 : Nat := 4983230072969 + 3 ^ 40 * 3981920 * 2
def baseEnd_3981920 : Nat := 2044638887751165953387489

theorem tailTrace_3981920 : CollatzResearch.WordTrace tailWord_3981920 prefixEnd_3981920 2044638887751165953387489 := by
  unfold tailWord_3981920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72616276867095686319471607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96821702489460915092628809 72616276867095686319471607)
  ·
    refine ⟨108924415300643529479207411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72616276867095686319471607 108924415300643529479207411)
    ·
      refine ⟨163386622950965294218811117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108924415300643529479207411 163386622950965294218811117)
      ·
        refine ⟨61269983606611985332054169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163386622950965294218811117 61269983606611985332054169)
        ·
          refine ⟨45952487704958988999040627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61269983606611985332054169 45952487704958988999040627)
          ·
            refine ⟨68928731557438483498560941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45952487704958988999040627 68928731557438483498560941)
            ·
              refine ⟨25848274334039431311960353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68928731557438483498560941 25848274334039431311960353)
              ·
                refine ⟨19386205750529573483970265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25848274334039431311960353 19386205750529573483970265)
                ·
                  refine ⟨14539654312897180112977699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386205750529573483970265 14539654312897180112977699)
                  ·
                    refine ⟨21809481469345770169466549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14539654312897180112977699 21809481469345770169466549)
                    ·
                      refine ⟨2044638887751165953387489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21809481469345770169466549 2044638887751165953387489)
                      ·
                        rfl

theorem cell23_3981920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3981920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981920 prefixEnd_3981920 := by exact prefixLift 3981920
  have htrace : WordTrace (prefixWord ++ tailWord_3981920) baseStart_3981920 baseEnd_3981920 := by
    simpa [prefixWord, tailWord_3981920, baseEnd_3981920] using wordTrace_append hprefix tailTrace_3981920
  have hstable : (prefixWord ++ tailWord_3981920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981920).length < 2 ^ (prefixWord ++ tailWord_3981920).sum := by decide
  have hdescent : baseEnd_3981920 < baseStart_3981920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981921 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3981921 : Nat := 118140960795 + 3981921 * 2 ^ 59
def prefixEnd_3981921 : Nat := 4983230072969 + 3 ^ 40 * 3981921 * 2
def baseEnd_3981921 : Nat := 2044639401231820449474985

theorem tailTrace_3981921 : CollatzResearch.WordTrace tailWord_3981921 prefixEnd_3981921 2044639401231820449474985 := by
  unfold tailWord_3981921
  simp only [CollatzResearch.WordTrace]
  refine ⟨145232590207187749809729617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96821726804791833206486411 145232590207187749809729617)
  ·
    refine ⟨108924442655390812357297213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145232590207187749809729617 108924442655390812357297213)
    ·
      refine ⟨40846665995771554633986455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108924442655390812357297213 40846665995771554633986455)
      ·
        refine ⟨61269998993657331950979683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40846665995771554633986455 61269998993657331950979683)
        ·
          refine ⟨91904998490485997926469525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61269998993657331950979683 91904998490485997926469525)
          ·
            refine ⟨4308046804241531152803259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91904998490485997926469525 4308046804241531152803259)
            ·
              refine ⟨6462070206362296729204889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308046804241531152803259 6462070206362296729204889)
              ·
                refine ⟨4846552654771722546903667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6462070206362296729204889 4846552654771722546903667)
                ·
                  refine ⟨7269828982157583820355501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846552654771722546903667 7269828982157583820355501)
                  ·
                    refine ⟨2726185868309093932633313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7269828982157583820355501 2726185868309093932633313)
                    ·
                      refine ⟨2044639401231820449474985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726185868309093932633313 2044639401231820449474985)
                      ·
                        rfl

theorem cell23_3981921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3981921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981921 prefixEnd_3981921 := by exact prefixLift 3981921
  have htrace : WordTrace (prefixWord ++ tailWord_3981921) baseStart_3981921 baseEnd_3981921 := by
    simpa [prefixWord, tailWord_3981921, baseEnd_3981921] using wordTrace_append hprefix tailTrace_3981921
  have hstable : (prefixWord ++ tailWord_3981921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981921).length < 2 ^ (prefixWord ++ tailWord_3981921).sum := by decide
  have hdescent : baseEnd_3981921 < baseStart_3981921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981934 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3981934 : Nat := 118140960795 + 3981934 * 2 ^ 59
def prefixEnd_3981934 : Nat := 4983230072969 + 3 ^ 40 * 3981934 * 2
def baseEnd_3981934 : Nat := 2044646076480328898612425

theorem tailTrace_3981934 : CollatzResearch.WordTrace tailWord_3981934 prefixEnd_3981934 2044646076480328898612425 := by
  unfold tailWord_3981934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154133044517581628744107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96822042904093768686635237 18154133044517581628744107)
  ·
    refine ⟨27231199566776372443116161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18154133044517581628744107 27231199566776372443116161)
    ·
      refine ⟨20423399675082279332337121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27231199566776372443116161 20423399675082279332337121)
      ·
        refine ⟨15317549756311709499252841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20423399675082279332337121 15317549756311709499252841)
        ·
          refine ⟨11488162317233782124439631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15317549756311709499252841 11488162317233782124439631)
          ·
            refine ⟨17232243475850673186659447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488162317233782124439631 17232243475850673186659447)
            ·
              refine ⟨25848365213776009779989171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232243475850673186659447 25848365213776009779989171)
              ·
                refine ⟨38772547820664014669983757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25848365213776009779989171 38772547820664014669983757)
                ·
                  refine ⟨14539705432749005501243909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38772547820664014669983757 14539705432749005501243909)
                  ·
                    refine ⟨2726194768640438531483233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14539705432749005501243909 2726194768640438531483233)
                    ·
                      refine ⟨2044646076480328898612425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726194768640438531483233 2044646076480328898612425)
                      ·
                        rfl

theorem cell23_3981934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3981934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981934 prefixEnd_3981934 := by exact prefixLift 3981934
  have htrace : WordTrace (prefixWord ++ tailWord_3981934) baseStart_3981934 baseEnd_3981934 := by
    simpa [prefixWord, tailWord_3981934, baseEnd_3981934] using wordTrace_append hprefix tailTrace_3981934
  have hstable : (prefixWord ++ tailWord_3981934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981934).length < 2 ^ (prefixWord ++ tailWord_3981934).sum := by decide
  have hdescent : baseEnd_3981934 < baseStart_3981934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981938 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_3981938 : Nat := 118140960795 + 3981938 * 2 ^ 59
def prefixEnd_3981938 : Nat := 4983230072969 + 3 ^ 40 * 3981938 * 2
def baseEnd_3981938 : Nat := 2044648130402946882962407

theorem tailTrace_3981938 : CollatzResearch.WordTrace tailWord_3981938 prefixEnd_3981938 2044648130402946882962407 := by
  unfold tailWord_3981938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36308302562031540428274617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96822140165417441142065645 36308302562031540428274617)
  ·
    refine ⟨27231226921523655321205963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36308302562031540428274617 27231226921523655321205963)
    ·
      refine ⟨40846840382285482981808945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231226921523655321205963 40846840382285482981808945)
      ·
        refine ⟨30635130286714112236356709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40846840382285482981808945 30635130286714112236356709)
        ·
          refine ⟨5744086928758896044316883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30635130286714112236356709 5744086928758896044316883)
          ·
            refine ⟨8616130393138344066475325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744086928758896044316883 8616130393138344066475325)
            ·
              refine ⟨3231048897426879024928247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8616130393138344066475325 3231048897426879024928247)
              ·
                refine ⟨4846573346140318537392371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231048897426879024928247 4846573346140318537392371)
                ·
                  refine ⟨7269860019210477806088557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846573346140318537392371 7269860019210477806088557)
                  ·
                    refine ⟨2726197507203929177283209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7269860019210477806088557 2726197507203929177283209)
                    ·
                      refine ⟨2044648130402946882962407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726197507203929177283209 2044648130402946882962407)
                      ·
                        rfl

theorem cell23_3981938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_3981938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981938 prefixEnd_3981938 := by exact prefixLift 3981938
  have htrace : WordTrace (prefixWord ++ tailWord_3981938) baseStart_3981938 baseEnd_3981938 := by
    simpa [prefixWord, tailWord_3981938, baseEnd_3981938] using wordTrace_append hprefix tailTrace_3981938
  have hstable : (prefixWord ++ tailWord_3981938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981938).length < 2 ^ (prefixWord ++ tailWord_3981938).sum := by decide
  have hdescent : baseEnd_3981938 < baseStart_3981938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981977 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 5, 2]
def baseStart_3981977 : Nat := 118140960795 + 3981977 * 2 ^ 59
def prefixEnd_3981977 : Nat := 4983230072969 + 3 ^ 40 * 3981977 * 2
def baseEnd_3981977 : Nat := 2044668156148472230374727

theorem tailTrace_3981977 : CollatzResearch.WordTrace tailWord_3981977 prefixEnd_3981977 2044668156148472230374727 := by
  unfold tailWord_3981977
  simp only [CollatzResearch.WordTrace]
  refine ⟨145234632694984871373768185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96823088463323247582512123 145234632694984871373768185)
  ·
    refine ⟨108925974521238653530326139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145234632694984871373768185 108925974521238653530326139)
    ·
      refine ⟨163388961781857980295489209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108925974521238653530326139 163388961781857980295489209)
      ·
        refine ⟨122541721336393485221616907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163388961781857980295489209 122541721336393485221616907)
        ·
          refine ⟨183812582004590227832425361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122541721336393485221616907 183812582004590227832425361)
          ·
            refine ⟨137859436503442670874319021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183812582004590227832425361 137859436503442670874319021)
            ·
              refine ⟨51697288688791001577869633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137859436503442670874319021 51697288688791001577869633)
              ·
                refine ⟨38772966516593251183402225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51697288688791001577869633 38772966516593251183402225)
                ·
                  refine ⟨29079724887444938387551669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38772966516593251183402225 29079724887444938387551669)
                  ·
                    refine ⟨2726224208197962973832969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29079724887444938387551669 2726224208197962973832969)
                    ·
                      refine ⟨2044668156148472230374727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726224208197962973832969 2044668156148472230374727)
                      ·
                        rfl

theorem cell23_3981977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_3981977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3981977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3981977 prefixEnd_3981977 := by exact prefixLift 3981977
  have htrace : WordTrace (prefixWord ++ tailWord_3981977) baseStart_3981977 baseEnd_3981977 := by
    simpa [prefixWord, tailWord_3981977, baseEnd_3981977] using wordTrace_append hprefix tailTrace_3981977
  have hstable : (prefixWord ++ tailWord_3981977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981977).length < 2 ^ (prefixWord ++ tailWord_3981977).sum := by decide
  have hdescent : baseEnd_3981977 < baseStart_3981977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982024 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_3982024 : Nat := 118140960795 + 3982024 * 2 ^ 59
def prefixEnd_3982024 : Nat := 4983230072969 + 3 ^ 40 * 3982024 * 2
def baseEnd_3982024 : Nat := 2044692289739233546487011

theorem tailTrace_3982024 : CollatzResearch.WordTrace tailWord_3982024 prefixEnd_3982024 2044692289739233546487011 := by
  unfold tailWord_3982024
  simp only [CollatzResearch.WordTrace]
  refine ⟨72618173462907299200364563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96824231283876398933819417 72618173462907299200364563)
  ·
    refine ⟨108927260194360948800546845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72618173462907299200364563 108927260194360948800546845)
    ·
      refine ⟨40847722572885355800205067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108927260194360948800546845 40847722572885355800205067)
      ·
        refine ⟨61271583859328033700307601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40847722572885355800205067 61271583859328033700307601)
        ·
          refine ⟨45953687894496025275230701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61271583859328033700307601 45953687894496025275230701)
          ·
            refine ⟨17232632960436009478211513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45953687894496025275230701 17232632960436009478211513)
            ·
              refine ⟨12924474720327007108658635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232632960436009478211513 12924474720327007108658635)
              ·
                refine ⟨19386712080490510662987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924474720327007108658635 19386712080490510662987953)
                ·
                  refine ⟨14540034060367882997240965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386712080490510662987953 14540034060367882997240965)
                  ·
                    refine ⟨2726256386318978061982681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14540034060367882997240965 2726256386318978061982681)
                    ·
                      refine ⟨2044692289739233546487011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726256386318978061982681 2044692289739233546487011)
                      ·
                        rfl

theorem cell23_3982024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_3982024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982024 prefixEnd_3982024 := by exact prefixLift 3982024
  have htrace : WordTrace (prefixWord ++ tailWord_3982024) baseStart_3982024 baseEnd_3982024 := by
    simpa [prefixWord, tailWord_3982024, baseEnd_3982024] using wordTrace_append hprefix tailTrace_3982024
  have hstable : (prefixWord ++ tailWord_3982024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982024).length < 2 ^ (prefixWord ++ tailWord_3982024).sum := by decide
  have hdescent : baseEnd_3982024 < baseStart_3982024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982077 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3982077 : Nat := 118140960795 + 3982077 * 2 ^ 59
def prefixEnd_3982077 : Nat := 4983230072969 + 3 ^ 40 * 3982077 * 2
def baseEnd_3982077 : Nat := 681573168071307279708089

theorem tailTrace_3982077 : CollatzResearch.WordTrace tailWord_3982077 prefixEnd_3982077 681573168071307279708089 := by
  unfold tailWord_3982077
  simp only [CollatzResearch.WordTrace]
  refine ⟨145238279994622588452408485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96825519996415058968272323 145238279994622588452408485)
  ·
    refine ⟨27232177498991735334826591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145238279994622588452408485 27232177498991735334826591)
    ·
      refine ⟨40848266248487603002239887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27232177498991735334826591 40848266248487603002239887)
      ·
        refine ⟨61272399372731404503359831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848266248487603002239887 61272399372731404503359831)
        ·
          refine ⟨91908599059097106755039747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61272399372731404503359831 91908599059097106755039747)
          ·
            refine ⟨137862898588645660132559621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91908599059097106755039747 137862898588645660132559621)
            ·
              refine ⟨25849293485371061274854929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137862898588645660132559621 25849293485371061274854929)
              ·
                refine ⟨19386970114028295956141197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25849293485371061274854929 19386970114028295956141197)
                ·
                  refine ⟨7270113792760610983552949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19386970114028295956141197 7270113792760610983552949)
                  ·
                    refine ⟨681573168071307279708089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7270113792760610983552949 681573168071307279708089)
                    ·
                      rfl

theorem cell23_3982077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3982077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982077 prefixEnd_3982077 := by exact prefixLift 3982077
  have htrace : WordTrace (prefixWord ++ tailWord_3982077) baseStart_3982077 baseEnd_3982077 := by
    simpa [prefixWord, tailWord_3982077, baseEnd_3982077] using wordTrace_append hprefix tailTrace_3982077
  have hstable : (prefixWord ++ tailWord_3982077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982077).length < 2 ^ (prefixWord ++ tailWord_3982077).sum := by decide
  have hdescent : baseEnd_3982077 < baseStart_3982077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982101 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_3982101 : Nat := 118140960795 + 3982101 * 2 ^ 59
def prefixEnd_3982101 : Nat := 4983230072969 + 3 ^ 40 * 3982101 * 2
def baseEnd_3982101 : Nat := 2044731827749629745224157

theorem tailTrace_3982101 : CollatzResearch.WordTrace tailWord_3982101 prefixEnd_3982101 2044731827749629745224157 := by
  unfold tailWord_3982101
  simp only [CollatzResearch.WordTrace]
  refine ⟨145239155346535640551282157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96826103564357093700854771 145239155346535640551282157)
  ·
    refine ⟨54464683254950865206730809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145239155346535640551282157 54464683254950865206730809)
    ·
      refine ⟨40848512441213148905048107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54464683254950865206730809 40848512441213148905048107)
      ·
        refine ⟨61272768661819723357572161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848512441213148905048107 61272768661819723357572161)
        ·
          refine ⟨45954576496364792518179121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61272768661819723357572161 45954576496364792518179121)
          ·
            refine ⟨34465932372273594388634341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45954576496364792518179121 34465932372273594388634341)
            ·
              refine ⟨6462362319801298947868939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34465932372273594388634341 6462362319801298947868939)
              ·
                refine ⟨9693543479701948421803409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462362319801298947868939 9693543479701948421803409)
                ·
                  refine ⟨7270157609776461316352557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9693543479701948421803409 7270157609776461316352557)
                  ·
                    refine ⟨2726309103666172993632209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7270157609776461316352557 2726309103666172993632209)
                    ·
                      refine ⟨2044731827749629745224157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726309103666172993632209 2044731827749629745224157)
                      ·
                        rfl

theorem cell23_3982101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_3982101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982101 prefixEnd_3982101 := by exact prefixLift 3982101
  have htrace : WordTrace (prefixWord ++ tailWord_3982101) baseStart_3982101 baseEnd_3982101 := by
    simpa [prefixWord, tailWord_3982101, baseEnd_3982101] using wordTrace_append hprefix tailTrace_3982101
  have hstable : (prefixWord ++ tailWord_3982101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982101).length < 2 ^ (prefixWord ++ tailWord_3982101).sum := by decide
  have hdescent : baseEnd_3982101 < baseStart_3982101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982111 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 1, 5]
def baseStart_3982111 : Nat := 118140960795 + 3982111 * 2 ^ 59
def prefixEnd_3982111 : Nat := 4983230072969 + 3 ^ 40 * 3982111 * 2
def baseEnd_3982111 : Nat := 681578987518724902033037

theorem tailTrace_3982111 : CollatzResearch.WordTrace tailWord_3982111 prefixEnd_3982111 681578987518724902033037 := by
  unfold tailWord_3982111
  simp only [CollatzResearch.WordTrace]
  refine ⟨145239520076499412259146187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96826346717666274839430791 145239520076499412259146187)
  ·
    refine ⟨217859280114749118388719281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145239520076499412259146187 217859280114749118388719281)
    ·
      refine ⟨163394460086061838791539461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217859280114749118388719281 163394460086061838791539461)
      ·
        refine ⟨30636461266136594773413649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163394460086061838791539461 30636461266136594773413649)
        ·
          refine ⟨22977345949602446080060237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30636461266136594773413649 22977345949602446080060237)
          ·
            refine ⟨8616504731100917280022589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22977345949602446080060237 8616504731100917280022589)
            ·
              refine ⟨3231189274162843980008471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8616504731100917280022589 3231189274162843980008471)
              ·
                refine ⟨4846783911244265970012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231189274162843980008471 4846783911244265970012707)
                ·
                  refine ⟨7270175866866398955019061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846783911244265970012707 7270175866866398955019061)
                  ·
                    refine ⟨681578987518724902033037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7270175866866398955019061 681578987518724902033037)
                    ·
                      rfl

theorem cell23_3982111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_3982111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982111 prefixEnd_3982111 := by exact prefixLift 3982111
  have htrace : WordTrace (prefixWord ++ tailWord_3982111) baseStart_3982111 baseEnd_3982111 := by
    simpa [prefixWord, tailWord_3982111, baseEnd_3982111] using wordTrace_append hprefix tailTrace_3982111
  have hstable : (prefixWord ++ tailWord_3982111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982111).length < 2 ^ (prefixWord ++ tailWord_3982111).sum := by decide
  have hdescent : baseEnd_3982111 < baseStart_3982111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982141 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3982141 : Nat := 118140960795 + 3982141 * 2 ^ 59
def prefixEnd_3982141 : Nat := 4983230072969 + 3 ^ 40 * 3982141 * 2
def baseEnd_3982141 : Nat := 681584122325269862907991

theorem tailTrace_3982141 : CollatzResearch.WordTrace tailWord_3982141 prefixEnd_3982141 681584122325269862907991 := by
  unfold tailWord_3982141
  simp only [CollatzResearch.WordTrace]
  refine ⟨145240614266390727382738277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96827076177593818255158851 145240614266390727382738277)
  ·
    refine ⟨27232615174948261384263427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145240614266390727382738277 27232615174948261384263427)
    ·
      refine ⟨40848922762422392076395141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27232615174948261384263427 40848922762422392076395141)
      ·
        refine ⟨7659173017954198514324089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40848922762422392076395141 7659173017954198514324089)
        ·
          refine ⟨5744379763465648885743067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659173017954198514324089 5744379763465648885743067)
          ·
            refine ⟨8616569645198473328614601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744379763465648885743067 8616569645198473328614601)
            ·
              refine ⟨6462427233898854996460951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616569645198473328614601 6462427233898854996460951)
              ·
                refine ⟨9693640850848282494691427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462427233898854996460951 9693640850848282494691427)
                ·
                  refine ⟨14540461276272423742037141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693640850848282494691427 14540461276272423742037141)
                  ·
                    refine ⟨681584122325269862907991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14540461276272423742037141 681584122325269862907991)
                    ·
                      rfl

theorem cell23_3982141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3982141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982141 prefixEnd_3982141 := by exact prefixLift 3982141
  have htrace : WordTrace (prefixWord ++ tailWord_3982141) baseStart_3982141 baseEnd_3982141 := by
    simpa [prefixWord, tailWord_3982141, baseEnd_3982141] using wordTrace_append hprefix tailTrace_3982141
  have hstable : (prefixWord ++ tailWord_3982141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982141).length < 2 ^ (prefixWord ++ tailWord_3982141).sum := by decide
  have hdescent : baseEnd_3982141 < baseStart_3982141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982165 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3982165 : Nat := 118140960795 + 3982165 * 2 ^ 59
def prefixEnd_3982165 : Nat := 4983230072969 + 3 ^ 40 * 3982165 * 2
def baseEnd_3982165 : Nat := 2044764690511517494823863

theorem tailTrace_3982165 : CollatzResearch.WordTrace tailWord_3982165 prefixEnd_3982165 2044764690511517494823863 := by
  unfold tailWord_3982165
  simp only [CollatzResearch.WordTrace]
  refine ⟨145241489618303779481611949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96827659745535852987741299 145241489618303779481611949)
  ·
    refine ⟨54465558606863917305604481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145241489618303779481611949 54465558606863917305604481)
    ·
      refine ⟨40849168955147937979203361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54465558606863917305604481 40849168955147937979203361)
      ·
        refine ⟨30636876716360953484402521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40849168955147937979203361 30636876716360953484402521)
        ·
          refine ⟨22977657537270715113301891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30636876716360953484402521 22977657537270715113301891)
          ·
            refine ⟨34466486305906072669952837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22977657537270715113301891 34466486305906072669952837)
            ·
              refine ⟨6462466182357388625616157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34466486305906072669952837 6462466182357388625616157)
              ·
                refine ⟨2423424818384020734606059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6462466182357388625616157 2423424818384020734606059)
                ·
                  refine ⟨3635137227576031101909089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423424818384020734606059 3635137227576031101909089)
                  ·
                    refine ⟨2726352920682023326431817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3635137227576031101909089 2726352920682023326431817)
                    ·
                      refine ⟨2044764690511517494823863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726352920682023326431817 2044764690511517494823863)
                      ·
                        rfl

theorem cell23_3982165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3982165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982165 prefixEnd_3982165 := by exact prefixLift 3982165
  have htrace : WordTrace (prefixWord ++ tailWord_3982165) baseStart_3982165 baseEnd_3982165 := by
    simpa [prefixWord, tailWord_3982165, baseEnd_3982165] using wordTrace_append hprefix tailTrace_3982165
  have hstable : (prefixWord ++ tailWord_3982165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982165).length < 2 ^ (prefixWord ++ tailWord_3982165).sum := by decide
  have hdescent : baseEnd_3982165 < baseStart_3982165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982177 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3982177 : Nat := 118140960795 + 3982177 * 2 ^ 59
def prefixEnd_3982177 : Nat := 4983230072969 + 3 ^ 40 * 3982177 * 2
def baseEnd_3982177 : Nat := 2044770852279371447873807

theorem tailTrace_3982177 : CollatzResearch.WordTrace tailWord_3982177 prefixEnd_3982177 2044770852279371447873807 := by
  unfold tailWord_3982177
  simp only [CollatzResearch.WordTrace]
  refine ⟨145241927294260305531048785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96827951529506870354032523 145241927294260305531048785)
  ·
    refine ⟨108931445470695229148286589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145241927294260305531048785 108931445470695229148286589)
    ·
      refine ⟨40849292051510710930607471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108931445470695229148286589 40849292051510710930607471)
      ·
        refine ⟨61273938077266066395911207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40849292051510710930607471 61273938077266066395911207)
        ·
          refine ⟨91910907115899099593866811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273938077266066395911207 91910907115899099593866811)
          ·
            refine ⟨137866360673848649390800217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91910907115899099593866811 137866360673848649390800217)
            ·
              refine ⟨103399770505386487043100163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137866360673848649390800217 103399770505386487043100163)
              ·
                refine ⟨155099655758079730564650245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103399770505386487043100163 155099655758079730564650245)
                ·
                  refine ⟨29081185454639949480871921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155099655758079730564650245 29081185454639949480871921)
                  ·
                    refine ⟨21810889090979962110653941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29081185454639949480871921 21810889090979962110653941)
                    ·
                      refine ⟨2044770852279371447873807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21810889090979962110653941 2044770852279371447873807)
                      ·
                        rfl

theorem cell23_3982177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3982177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982177 prefixEnd_3982177 := by exact prefixLift 3982177
  have htrace : WordTrace (prefixWord ++ tailWord_3982177) baseStart_3982177 baseEnd_3982177 := by
    simpa [prefixWord, tailWord_3982177, baseEnd_3982177] using wordTrace_append hprefix tailTrace_3982177
  have hstable : (prefixWord ++ tailWord_3982177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982177).length < 2 ^ (prefixWord ++ tailWord_3982177).sum := by decide
  have hdescent : baseEnd_3982177 < baseStart_3982177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982187 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_3982187 : Nat := 118140960795 + 3982187 * 2 ^ 59
def prefixEnd_3982187 : Nat := 4983230072969 + 3 ^ 40 * 3982187 * 2
def baseEnd_3982187 : Nat := 2044775987085916408748761

theorem tailTrace_3982187 : CollatzResearch.WordTrace tailWord_3982187 prefixEnd_3982187 2044775987085916408748761 := by
  unfold tailWord_3982187
  simp only [CollatzResearch.WordTrace]
  refine ⟨145242292024224077238912815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96828194682816051492608543 145242292024224077238912815)
  ·
    refine ⟨217863438036336115858369223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145242292024224077238912815 217863438036336115858369223)
    ·
      refine ⟨326795157054504173787553835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217863438036336115858369223 326795157054504173787553835)
      ·
        refine ⟨490192735581756260681330753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326795157054504173787553835 490192735581756260681330753)
        ·
          refine ⟨367644551686317195510998065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490192735581756260681330753 367644551686317195510998065)
          ·
            refine ⟨275733413764737896633248549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367644551686317195510998065 275733413764737896633248549)
            ·
              refine ⟨51700015080888355618734103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275733413764737896633248549 51700015080888355618734103)
              ·
                refine ⟨77550022621332533428101155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51700015080888355618734103 77550022621332533428101155)
                ·
                  refine ⟨116325033931998800142151733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77550022621332533428101155 116325033931998800142151733)
                  ·
                    refine ⟨10905471931124887513326725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116325033931998800142151733 10905471931124887513326725)
                    ·
                      refine ⟨2044775987085916408748761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10905471931124887513326725 2044775987085916408748761)
                      ·
                        rfl

theorem cell23_3982187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_3982187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982187 prefixEnd_3982187 := by exact prefixLift 3982187
  have htrace : WordTrace (prefixWord ++ tailWord_3982187) baseStart_3982187 baseEnd_3982187 := by
    simpa [prefixWord, tailWord_3982187, baseEnd_3982187] using wordTrace_append hprefix tailTrace_3982187
  have hstable : (prefixWord ++ tailWord_3982187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982187).length < 2 ^ (prefixWord ++ tailWord_3982187).sum := by decide
  have hdescent : baseEnd_3982187 < baseStart_3982187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982198 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3982198 : Nat := 118140960795 + 3982198 * 2 ^ 59
def prefixEnd_3982198 : Nat := 4983230072969 + 3 ^ 40 * 3982198 * 2
def baseEnd_3982198 : Nat := 2044781635373115865711211

theorem tailTrace_3982198 : CollatzResearch.WordTrace tailWord_3982198 prefixEnd_3982198 2044781635373115865711211 := by
  unfold tailWord_3982198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077668326699014132347703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96828462151456150745042165 9077668326699014132347703)
  ·
    refine ⟨13616502490048521198521555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077668326699014132347703 13616502490048521198521555)
    ·
      refine ⟨20424753735072781797782333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616502490048521198521555 20424753735072781797782333)
      ·
        refine ⟨7659282650652293174168375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20424753735072781797782333 7659282650652293174168375)
        ·
          refine ⟨11488923975978439761252563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659282650652293174168375 11488923975978439761252563)
          ·
            refine ⟨17233385963967659641878845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488923975978439761252563 17233385963967659641878845)
            ·
              refine ⟨6462519736487872365704567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17233385963967659641878845 6462519736487872365704567)
              ·
                refine ⟨9693779604731808548556851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462519736487872365704567 9693779604731808548556851)
                ·
                  refine ⟨14540669407097712822835277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693779604731808548556851 14540669407097712822835277)
                  ·
                    refine ⟨5452751027661642308563229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14540669407097712822835277 5452751027661642308563229)
                    ·
                      refine ⟨2044781635373115865711211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5452751027661642308563229 2044781635373115865711211)
                      ·
                        rfl

theorem cell23_3982198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3982198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982198 prefixEnd_3982198 := by exact prefixLift 3982198
  have htrace : WordTrace (prefixWord ++ tailWord_3982198) baseStart_3982198 baseEnd_3982198 := by
    simpa [prefixWord, tailWord_3982198, baseEnd_3982198] using wordTrace_append hprefix tailTrace_3982198
  have hstable : (prefixWord ++ tailWord_3982198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982198).length < 2 ^ (prefixWord ++ tailWord_3982198).sum := by decide
  have hdescent : baseEnd_3982198 < baseStart_3982198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982284 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3982284 : Nat := 118140960795 + 3982284 * 2 ^ 59
def prefixEnd_3982284 : Nat := 4983230072969 + 3 ^ 40 * 3982284 * 2
def baseEnd_3982284 : Nat := 2044825794709402529235815

theorem tailTrace_3982284 : CollatzResearch.WordTrace tailWord_3982284 prefixEnd_3982284 2044825794709402529235815 := by
  unfold tailWord_3982284
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622914952436331402596953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96830553269915108536795937 72622914952436331402596953)
  ·
    refine ⟨54467186214327248551947715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72622914952436331402596953 54467186214327248551947715)
    ·
      refine ⟨81700779321490872827921573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54467186214327248551947715 81700779321490872827921573)
      ·
        refine ⟨15318896122779538655235295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81700779321490872827921573 15318896122779538655235295)
        ·
          refine ⟨22978344184169307982852943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318896122779538655235295 22978344184169307982852943)
          ·
            refine ⟨34467516276253961974279415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22978344184169307982852943 34467516276253961974279415)
            ·
              refine ⟨51701274414380942961419123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34467516276253961974279415 51701274414380942961419123)
              ·
                refine ⟨77551911621571414442128685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51701274414380942961419123 77551911621571414442128685)
                ·
                  refine ⟨29081966858089280415798257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77551911621571414442128685 29081966858089280415798257)
                  ·
                    refine ⟨21811475143566960311848693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29081966858089280415798257 21811475143566960311848693)
                    ·
                      refine ⟨2044825794709402529235815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21811475143566960311848693 2044825794709402529235815)
                      ·
                        rfl

theorem cell23_3982284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3982284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982284 prefixEnd_3982284 := by exact prefixLift 3982284
  have htrace : WordTrace (prefixWord ++ tailWord_3982284) baseStart_3982284 baseEnd_3982284 := by
    simpa [prefixWord, tailWord_3982284, baseEnd_3982284] using wordTrace_append hprefix tailTrace_3982284
  have hstable : (prefixWord ++ tailWord_3982284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982284).length < 2 ^ (prefixWord ++ tailWord_3982284).sum := by decide
  have hdescent : baseEnd_3982284 < baseStart_3982284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982301 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3982301 : Nat := 118140960795 + 3982301 * 2 ^ 59
def prefixEnd_3982301 : Nat := 4983230072969 + 3 ^ 40 * 3982301 * 2
def baseEnd_3982301 : Nat := 2044834523880528962723237

theorem tailTrace_3982301 : CollatzResearch.WordTrace tailWord_3982301 prefixEnd_3982301 2044834523880528962723237 := by
  unfold tailWord_3982301
  simp only [CollatzResearch.WordTrace]
  refine ⟨145246449945811074708562757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96830966630540716472375171 145246449945811074708562757)
  ·
    refine ⟨27233709364839576507855517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145246449945811074708562757 27233709364839576507855517)
    ·
      refine ⟨10212641011814841190445819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27233709364839576507855517 10212641011814841190445819)
      ·
        refine ⟨15318961517722261785668729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212641011814841190445819 15318961517722261785668729)
        ·
          refine ⟨11489221138291696339251547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15318961517722261785668729 11489221138291696339251547)
          ·
            refine ⟨17233831707437544508877321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489221138291696339251547 17233831707437544508877321)
            ·
              refine ⟨12925373780578158381657991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233831707437544508877321 12925373780578158381657991)
              ·
                refine ⟨19388060670867237572486987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925373780578158381657991 19388060670867237572486987)
                ·
                  refine ⟨29082091006300856358730481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19388060670867237572486987 29082091006300856358730481)
                  ·
                    refine ⟨21811568254725642269047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29082091006300856358730481 21811568254725642269047861)
                    ·
                      refine ⟨2044834523880528962723237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21811568254725642269047861 2044834523880528962723237)
                      ·
                        rfl

theorem cell23_3982301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3982301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982301 prefixEnd_3982301 := by exact prefixLift 3982301
  have htrace : WordTrace (prefixWord ++ tailWord_3982301) baseStart_3982301 baseEnd_3982301 := by
    simpa [prefixWord, tailWord_3982301, baseEnd_3982301] using wordTrace_append hprefix tailTrace_3982301
  have hstable : (prefixWord ++ tailWord_3982301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982301).length < 2 ^ (prefixWord ++ tailWord_3982301).sum := by decide
  have hdescent : baseEnd_3982301 < baseStart_3982301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982321 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_3982321 : Nat := 118140960795 + 3982321 * 2 ^ 59
def prefixEnd_3982321 : Nat := 4983230072969 + 3 ^ 40 * 3982321 * 2
def baseEnd_3982321 : Nat := 681614931164539628157715

theorem tailTrace_3982321 : CollatzResearch.WordTrace tailWord_3982321 prefixEnd_3982321 681614931164539628157715 := by
  unfold tailWord_3982321
  simp only [CollatzResearch.WordTrace]
  refine ⟨145247179405738618124290817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96831452937159078749527211 145247179405738618124290817)
  ·
    refine ⟨108935384554303963593218113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145247179405738618124290817 108935384554303963593218113)
    ·
      refine ⟨81701538415727972694913585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108935384554303963593218113 81701538415727972694913585)
      ·
        refine ⟨61276153811795979521185189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81701538415727972694913585 61276153811795979521185189)
        ·
          refine ⟨11489278839711746160222223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61276153811795979521185189 11489278839711746160222223)
          ·
            refine ⟨17233918259567619240333335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489278839711746160222223 17233918259567619240333335)
            ·
              refine ⟨25850877389351428860500003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233918259567619240333335 25850877389351428860500003)
              ·
                refine ⟨38776316084027143290750005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850877389351428860500003 38776316084027143290750005)
                ·
                  refine ⟨3635279632877544683507813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38776316084027143290750005 3635279632877544683507813)
                  ·
                    refine ⟨681614931164539628157715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635279632877544683507813 681614931164539628157715)
                    ·
                      rfl

theorem cell23_3982321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_3982321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982321 prefixEnd_3982321 := by exact prefixLift 3982321
  have htrace : WordTrace (prefixWord ++ tailWord_3982321) baseStart_3982321 baseEnd_3982321 := by
    simpa [prefixWord, tailWord_3982321, baseEnd_3982321] using wordTrace_append hprefix tailTrace_3982321
  have hstable : (prefixWord ++ tailWord_3982321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982321).length < 2 ^ (prefixWord ++ tailWord_3982321).sum := by decide
  have hdescent : baseEnd_3982321 < baseStart_3982321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982421 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3982421 : Nat := 118140960795 + 3982421 * 2 ^ 59
def prefixEnd_3982421 : Nat := 4983230072969 + 3 ^ 40 * 3982421 * 2
def baseEnd_3982421 : Nat := 2044896141559068493222685

theorem tailTrace_3982421 : CollatzResearch.WordTrace tailWord_3982421 prefixEnd_3982421 2044896141559068493222685 := by
  unfold tailWord_3982421
  simp only [CollatzResearch.WordTrace]
  refine ⟨145250826705376335202931117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96833884470250890135287411 145250826705376335202931117)
  ·
    refine ⟨54469060014516125701099169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145250826705376335202931117 54469060014516125701099169)
    ·
      refine ⟨40851795010887094275824377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54469060014516125701099169 40851795010887094275824377)
      ·
        refine ⟨30638846258165320706868283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40851795010887094275824377 30638846258165320706868283)
        ·
          refine ⟨45958269387247981060302425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30638846258165320706868283 45958269387247981060302425)
          ·
            refine ⟨34468702040435985795226819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45958269387247981060302425 34468702040435985795226819)
            ·
              refine ⟨51703053060653978692840229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34468702040435985795226819 51703053060653978692840229)
              ·
                refine ⟨9694322448872621004907543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51703053060653978692840229 9694322448872621004907543)
                ·
                  refine ⟨14541483673308931507361315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9694322448872621004907543 14541483673308931507361315)
                  ·
                    refine ⟨21812225509963397261041973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14541483673308931507361315 21812225509963397261041973)
                    ·
                      refine ⟨2044896141559068493222685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21812225509963397261041973 2044896141559068493222685)
                      ·
                        rfl

theorem cell23_3982421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3982421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982421 prefixEnd_3982421 := by exact prefixLift 3982421
  have htrace : WordTrace (prefixWord ++ tailWord_3982421) baseStart_3982421 baseEnd_3982421 := by
    simpa [prefixWord, tailWord_3982421, baseEnd_3982421] using wordTrace_append hprefix tailTrace_3982421
  have hstable : (prefixWord ++ tailWord_3982421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982421).length < 2 ^ (prefixWord ++ tailWord_3982421).sum := by decide
  have hdescent : baseEnd_3982421 < baseStart_3982421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982431 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_3982431 : Nat := 118140960795 + 3982431 * 2 ^ 59
def prefixEnd_3982431 : Nat := 4983230072969 + 3 ^ 40 * 3982431 * 2
def baseEnd_3982431 : Nat := 2044901276365613454097639

theorem tailTrace_3982431 : CollatzResearch.WordTrace tailWord_3982431 prefixEnd_3982431 2044901276365613454097639 := by
  unfold tailWord_3982431
  simp only [CollatzResearch.WordTrace]
  refine ⟨145251191435340106910795147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96834127623560071273863431 145251191435340106910795147)
  ·
    refine ⟨217876787153010160366192721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145251191435340106910795147 217876787153010160366192721)
    ·
      refine ⟨163407590364757620274644541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217876787153010160366192721 163407590364757620274644541)
      ·
        refine ⟨61277846386784107602991703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163407590364757620274644541 61277846386784107602991703)
        ·
          refine ⟨91916769580176161404487555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61277846386784107602991703 91916769580176161404487555)
          ·
            refine ⟨137875154370264242106731333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91916769580176161404487555 137875154370264242106731333)
            ·
              refine ⟨25851591444424545395012125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137875154370264242106731333 25851591444424545395012125)
              ·
                refine ⟨9694346791659204523129547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25851591444424545395012125 9694346791659204523129547)
                ·
                  refine ⟨14541520187488806784694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9694346791659204523129547 14541520187488806784694321)
                  ·
                    refine ⟨10906140140616605088520741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14541520187488806784694321 10906140140616605088520741)
                    ·
                      refine ⟨2044901276365613454097639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10906140140616605088520741 2044901276365613454097639)
                      ·
                        rfl

theorem cell23_3982431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_3982431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982431 prefixEnd_3982431 := by exact prefixLift 3982431
  have htrace : WordTrace (prefixWord ++ tailWord_3982431) baseStart_3982431 baseEnd_3982431 := by
    simpa [prefixWord, tailWord_3982431, baseEnd_3982431] using wordTrace_append hprefix tailTrace_3982431
  have hstable : (prefixWord ++ tailWord_3982431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982431).length < 2 ^ (prefixWord ++ tailWord_3982431).sum := by decide
  have hdescent : baseEnd_3982431 < baseStart_3982431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982455 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_3982455 : Nat := 118140960795 + 3982455 * 2 ^ 59
def prefixEnd_3982455 : Nat := 4983230072969 + 3 ^ 40 * 3982455 * 2
def baseEnd_3982455 : Nat := 2044913599901321360197529

theorem tailTrace_3982455 : CollatzResearch.WordTrace tailWord_3982455 prefixEnd_3982455 2044913599901321360197529 := by
  unfold tailWord_3982455
  simp only [CollatzResearch.WordTrace]
  refine ⟨145252066787253159009668819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96834711191502106006445879 145252066787253159009668819)
  ·
    refine ⟨217878100180879738514503229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145252066787253159009668819 217878100180879738514503229)
    ·
      refine ⟨81704287567829901942938711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217878100180879738514503229 81704287567829901942938711)
      ·
        refine ⟨122556431351744852914408067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81704287567829901942938711 122556431351744852914408067)
        ·
          refine ⟨183834647027617279371612101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122556431351744852914408067 183834647027617279371612101)
          ·
            refine ⟨34468996317678239882177269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183834647027617279371612101 34468996317678239882177269)
            ·
              refine ⟨3231468404782334988954119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34468996317678239882177269 3231468404782334988954119)
              ·
                refine ⟨4847202607173502483431179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231468404782334988954119 4847202607173502483431179)
                ·
                  refine ⟨7270803910760253725146769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847202607173502483431179 7270803910760253725146769)
                  ·
                    refine ⟨5453102933070190293860077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270803910760253725146769 5453102933070190293860077)
                    ·
                      refine ⟨2044913599901321360197529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453102933070190293860077 2044913599901321360197529)
                      ·
                        rfl

theorem cell23_3982455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_3982455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982455 prefixEnd_3982455 := by exact prefixLift 3982455
  have htrace : WordTrace (prefixWord ++ tailWord_3982455) baseStart_3982455 baseEnd_3982455 := by
    simpa [prefixWord, tailWord_3982455, baseEnd_3982455] using wordTrace_append hprefix tailTrace_3982455
  have hstable : (prefixWord ++ tailWord_3982455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982455).length < 2 ^ (prefixWord ++ tailWord_3982455).sum := by decide
  have hdescent : baseEnd_3982455 < baseStart_3982455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982469 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_3982469 : Nat := 118140960795 + 3982469 * 2 ^ 59
def prefixEnd_3982469 : Nat := 4983230072969 + 3 ^ 40 * 3982469 * 2
def baseEnd_3982469 : Nat := 2044920788630484305422465

theorem tailTrace_3982469 : CollatzResearch.WordTrace tailWord_3982469 prefixEnd_3982469 2044920788630484305422465 := by
  unfold tailWord_3982469
  simp only [CollatzResearch.WordTrace]
  refine ⟨145252577409202439400678461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96835051606134959600452307 145252577409202439400678461)
  ·
    refine ⟨54469716528450914775254423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145252577409202439400678461 54469716528450914775254423)
    ·
      refine ⟨81704574792676372162881635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54469716528450914775254423 81704574792676372162881635)
      ·
        refine ⟨122556862189014558244322453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81704574792676372162881635 122556862189014558244322453)
        ·
          refine ⟨5744852915110057417702615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122556862189014558244322453 5744852915110057417702615)
          ·
            refine ⟨8617279372665086126553923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744852915110057417702615 8617279372665086126553923)
            ·
              refine ⟨12925919058997629189830885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617279372665086126553923 12925919058997629189830885)
              ·
                refine ⟨2423609823562055473093291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12925919058997629189830885 2423609823562055473093291)
                ·
                  refine ⟨3635414735343083209639937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423609823562055473093291 3635414735343083209639937)
                  ·
                    refine ⟨2726561051507312407229953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3635414735343083209639937 2726561051507312407229953)
                    ·
                      refine ⟨2044920788630484305422465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726561051507312407229953 2044920788630484305422465)
                      ·
                        rfl

theorem cell23_3982469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_3982469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982469 prefixEnd_3982469 := by exact prefixLift 3982469
  have htrace : WordTrace (prefixWord ++ tailWord_3982469) baseStart_3982469 baseEnd_3982469 := by
    simpa [prefixWord, tailWord_3982469, baseEnd_3982469] using wordTrace_append hprefix tailTrace_3982469
  have hstable : (prefixWord ++ tailWord_3982469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982469).length < 2 ^ (prefixWord ++ tailWord_3982469).sum := by decide
  have hdescent : baseEnd_3982469 < baseStart_3982469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982508 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_3982508 : Nat := 118140960795 + 3982508 * 2 ^ 59
def prefixEnd_3982508 : Nat := 4983230072969 + 3 ^ 40 * 3982508 * 2
def baseEnd_3982508 : Nat := 2044940814376009652834785

theorem tailTrace_3982508 : CollatzResearch.WordTrace tailWord_3982508 prefixEnd_3982508 2044940814376009652834785 := by
  unfold tailWord_3982508
  simp only [CollatzResearch.WordTrace]
  refine ⟨72626999928030574530674089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96835999904040766040898785 72626999928030574530674089)
  ·
    refine ⟨54470249946022930898005567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72626999928030574530674089 54470249946022930898005567)
    ·
      refine ⟨81705374919034396347008351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54470249946022930898005567 81705374919034396347008351)
      ·
        refine ⟨122558062378551594520512527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81705374919034396347008351 122558062378551594520512527)
        ·
          refine ⟨183837093567827391780768791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122558062378551594520512527 183837093567827391780768791)
          ·
            refine ⟨275755640351741087671153187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183837093567827391780768791 275755640351741087671153187)
            ·
              refine ⟨413633460527611631506729781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275755640351741087671153187 413633460527611631506729781)
              ·
                refine ⟨38778136924463590453755917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 413633460527611631506729781 38778136924463590453755917)
                ·
                  refine ⟨14541801346673846420158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38778136924463590453755917 14541801346673846420158469)
                  ·
                    refine ⟨2726587752501346203779713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14541801346673846420158469 2726587752501346203779713)
                    ·
                      refine ⟨2044940814376009652834785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726587752501346203779713 2044940814376009652834785)
                      ·
                        rfl

theorem cell23_3982508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_3982508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982508 prefixEnd_3982508 := by exact prefixLift 3982508
  have htrace : WordTrace (prefixWord ++ tailWord_3982508) baseStart_3982508 baseEnd_3982508 := by
    simpa [prefixWord, tailWord_3982508, baseEnd_3982508] using wordTrace_append hprefix tailTrace_3982508
  have hstable : (prefixWord ++ tailWord_3982508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982508).length < 2 ^ (prefixWord ++ tailWord_3982508).sum := by decide
  have hdescent : baseEnd_3982508 < baseStart_3982508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982511 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_3982511 : Nat := 118140960795 + 3982511 * 2 ^ 59
def prefixEnd_3982511 : Nat := 4983230072969 + 3 ^ 40 * 3982511 * 2
def baseEnd_3982511 : Nat := 2044942354817973141097271

theorem tailTrace_3982511 : CollatzResearch.WordTrace tailWord_3982511 prefixEnd_3982511 2044942354817973141097271 := by
  unfold tailWord_3982511
  simp only [CollatzResearch.WordTrace]
  refine ⟨145254109275050280573707387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96836072850033520382471591 145254109275050280573707387)
  ·
    refine ⟨217881163912575420860561081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145254109275050280573707387 217881163912575420860561081)
    ·
      refine ⟨163410872934431565645420811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217881163912575420860561081 163410872934431565645420811)
      ·
        refine ⟨245116309401647348468131217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163410872934431565645420811 245116309401647348468131217)
        ·
          refine ⟨183837232051235511351098413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245116309401647348468131217 183837232051235511351098413)
          ·
            refine ⟨68938962019213316756661905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183837232051235511351098413 68938962019213316756661905)
            ·
              refine ⟨51704221514409987567496429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68938962019213316756661905 51704221514409987567496429)
              ·
                refine ⟨19389083067903745337811161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51704221514409987567496429 19389083067903745337811161)
                ·
                  refine ⟨14541812300927809003358371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19389083067903745337811161 14541812300927809003358371)
                  ·
                    refine ⟨21812718451391713505037557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14541812300927809003358371 21812718451391713505037557)
                    ·
                      refine ⟨2044942354817973141097271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21812718451391713505037557 2044942354817973141097271)
                      ·
                        rfl

theorem cell23_3982511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_3982511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982511 prefixEnd_3982511 := by exact prefixLift 3982511
  have htrace : WordTrace (prefixWord ++ tailWord_3982511) baseStart_3982511 baseEnd_3982511 := by
    simpa [prefixWord, tailWord_3982511, baseEnd_3982511] using wordTrace_append hprefix tailTrace_3982511
  have hstable : (prefixWord ++ tailWord_3982511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982511).length < 2 ^ (prefixWord ++ tailWord_3982511).sum := by decide
  have hdescent : baseEnd_3982511 < baseStart_3982511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982538 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_3982538 : Nat := 118140960795 + 3982538 * 2 ^ 59
def prefixEnd_3982538 : Nat := 4983230072969 + 3 ^ 40 * 3982538 * 2
def baseEnd_3982538 : Nat := 2044956218795644535459647

theorem tailTrace_3982538 : CollatzResearch.WordTrace tailWord_3982538 prefixEnd_3982538 2044956218795644535459647 := by
  unfold tailWord_3982538
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313773511488116046235067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96836729363968309456626845 36313773511488116046235067)
  ·
    refine ⟨54470660267232174069352601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36313773511488116046235067 54470660267232174069352601)
    ·
      refine ⟨40852995200424130552014451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54470660267232174069352601 40852995200424130552014451)
      ·
        refine ⟨61279492800636195828021677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40852995200424130552014451 61279492800636195828021677)
        ·
          refine ⟨22979809800238573435508129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61279492800636195828021677 22979809800238573435508129)
          ·
            refine ⟨17234857350178930076631097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22979809800238573435508129 17234857350178930076631097)
            ·
              refine ⟨12926143012634197557473323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17234857350178930076631097 12926143012634197557473323)
              ·
                refine ⟨19389214518951296336209985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926143012634197557473323 19389214518951296336209985)
                ·
                  refine ⟨14541910889213472252157489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19389214518951296336209985 14541910889213472252157489)
                  ·
                    refine ⟨10906433166910104189118117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14541910889213472252157489 10906433166910104189118117)
                    ·
                      refine ⟨2044956218795644535459647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10906433166910104189118117 2044956218795644535459647)
                      ·
                        rfl

theorem cell23_3982538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_3982538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982538 prefixEnd_3982538 := by exact prefixLift 3982538
  have htrace : WordTrace (prefixWord ++ tailWord_3982538) baseStart_3982538 baseEnd_3982538 := by
    simpa [prefixWord, tailWord_3982538, baseEnd_3982538] using wordTrace_append hprefix tailTrace_3982538
  have hstable : (prefixWord ++ tailWord_3982538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982538).length < 2 ^ (prefixWord ++ tailWord_3982538).sum := by decide
  have hdescent : baseEnd_3982538 < baseStart_3982538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_3982611 : Nat := 118140960795 + 3982611 * 2 ^ 59
def prefixEnd_3982611 : Nat := 4983230072969 + 3 ^ 40 * 3982611 * 2
def baseEnd_3982611 : Nat := 2044993702883422749846811

theorem tailTrace_3982611 : CollatzResearch.WordTrace tailWord_3982611 prefixEnd_3982611 2044993702883422749846811 := by
  unfold tailWord_3982611
  simp only [CollatzResearch.WordTrace]
  refine ⟨145257756574687997652347687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96838504383125331768231791 145257756574687997652347687)
  ·
    refine ⟨217886634862031996478521531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145257756574687997652347687 217886634862031996478521531)
    ·
      refine ⟨326829952293047994717782297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217886634862031996478521531 326829952293047994717782297)
      ·
        refine ⟨245122464219785996038336723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326829952293047994717782297 245122464219785996038336723)
        ·
          refine ⟨367683696329678994057505085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245122464219785996038336723 367683696329678994057505085)
          ·
            refine ⟨137881386123629622771564407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367683696329678994057505085 137881386123629622771564407)
            ·
              refine ⟨206822079185444434157346611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137881386123629622771564407 206822079185444434157346611)
              ·
                refine ⟨310233118778166651236019917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206822079185444434157346611 310233118778166651236019917)
                ·
                  refine ⟨116337419541812494213507469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310233118778166651236019917 116337419541812494213507469)
                  ·
                    refine ⟨43626532328179685330065301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116337419541812494213507469 43626532328179685330065301)
                    ·
                      refine ⟨2044993702883422749846811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43626532328179685330065301 2044993702883422749846811)
                      ·
                        rfl

theorem cell23_3982611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_3982611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982611 prefixEnd_3982611 := by exact prefixLift 3982611
  have htrace : WordTrace (prefixWord ++ tailWord_3982611) baseStart_3982611 baseEnd_3982611 := by
    simpa [prefixWord, tailWord_3982611, baseEnd_3982611] using wordTrace_append hprefix tailTrace_3982611
  have hstable : (prefixWord ++ tailWord_3982611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982611).length < 2 ^ (prefixWord ++ tailWord_3982611).sum := by decide
  have hdescent : baseEnd_3982611 < baseStart_3982611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982615 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3982615 : Nat := 118140960795 + 3982615 * 2 ^ 59
def prefixEnd_3982615 : Nat := 4983230072969 + 3 ^ 40 * 3982615 * 2
def baseEnd_3982615 : Nat := 2044995756806040734196793

theorem tailTrace_3982615 : CollatzResearch.WordTrace tailWord_3982615 prefixEnd_3982615 2044995756806040734196793 := by
  unfold tailWord_3982615
  simp only [CollatzResearch.WordTrace]
  refine ⟨145257902466673506335493299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96838601644449004223662199 145257902466673506335493299)
  ·
    refine ⟨217886853700010259503239949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145257902466673506335493299 217886853700010259503239949)
    ·
      refine ⟨81707570137503847313714981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217886853700010259503239949 81707570137503847313714981)
      ·
        refine ⟨15320169400781971371321559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81707570137503847313714981 15320169400781971371321559)
        ·
          refine ⟨22980254101172957056982339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320169400781971371321559 22980254101172957056982339)
          ·
            refine ⟨34470381151759435585473509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980254101172957056982339 34470381151759435585473509)
            ·
              refine ⟨6463196465954894172276283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34470381151759435585473509 6463196465954894172276283)
              ·
                refine ⟨9694794698932341258414425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463196465954894172276283 9694794698932341258414425)
                ·
                  refine ⟨7271096024199255943810819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694794698932341258414425 7271096024199255943810819)
                  ·
                    refine ⟨10906644036298883915716229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271096024199255943810819 10906644036298883915716229)
                    ·
                      refine ⟨2044995756806040734196793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10906644036298883915716229 2044995756806040734196793)
                      ·
                        rfl

theorem cell23_3982615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3982615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982615 prefixEnd_3982615 := by exact prefixLift 3982615
  have htrace : WordTrace (prefixWord ++ tailWord_3982615) baseStart_3982615 baseEnd_3982615 := by
    simpa [prefixWord, tailWord_3982615, baseEnd_3982615] using wordTrace_append hprefix tailTrace_3982615
  have hstable : (prefixWord ++ tailWord_3982615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982615).length < 2 ^ (prefixWord ++ tailWord_3982615).sum := by decide
  have hdescent : baseEnd_3982615 < baseStart_3982615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982628 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3982628 : Nat := 118140960795 + 3982628 * 2 ^ 59
def prefixEnd_3982628 : Nat := 4983230072969 + 3 ^ 40 * 3982628 * 2
def baseEnd_3982628 : Nat := 2045002432054549183334233

theorem tailTrace_3982628 : CollatzResearch.WordTrace tailWord_3982628 prefixEnd_3982628 2045002432054549183334233 := by
  unfold tailWord_3982628
  simp only [CollatzResearch.WordTrace]
  refine ⟨72629188307813204777858269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96838917743750939703811025 72629188307813204777858269)
  ·
    refine ⟨27235945615429951791696851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72629188307813204777858269 27235945615429951791696851)
    ·
      refine ⟨40853918423144927687545277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27235945615429951791696851 40853918423144927687545277)
      ·
        refine ⟨15320219408679347882829479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40853918423144927687545277 15320219408679347882829479)
        ·
          refine ⟨22980329113019021824244219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320219408679347882829479 22980329113019021824244219)
          ·
            refine ⟨34470493669528532736366329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980329113019021824244219 34470493669528532736366329)
            ·
              refine ⟨25852870252146399552274747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34470493669528532736366329 25852870252146399552274747)
              ·
                refine ⟨38779305378219599328412121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25852870252146399552274747 38779305378219599328412121)
                ·
                  refine ⟨29084479033664699496309091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38779305378219599328412121 29084479033664699496309091)
                  ·
                    refine ⟨43626718550497049244463637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29084479033664699496309091 43626718550497049244463637)
                    ·
                      refine ⟨2045002432054549183334233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43626718550497049244463637 2045002432054549183334233)
                      ·
                        rfl

theorem cell23_3982628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3982628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982628 prefixEnd_3982628 := by exact prefixLift 3982628
  have htrace : WordTrace (prefixWord ++ tailWord_3982628) baseStart_3982628 baseEnd_3982628 := by
    simpa [prefixWord, tailWord_3982628, baseEnd_3982628] using wordTrace_append hprefix tailTrace_3982628
  have hstable : (prefixWord ++ tailWord_3982628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982628).length < 2 ^ (prefixWord ++ tailWord_3982628).sum := by decide
  have hdescent : baseEnd_3982628 < baseStart_3982628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982648 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_3982648 : Nat := 118140960795 + 3982648 * 2 ^ 59
def prefixEnd_3982648 : Nat := 4983230072969 + 3 ^ 40 * 3982648 * 2
def baseEnd_3982648 : Nat := 2045012701667639105084141

theorem tailTrace_3982648 : CollatzResearch.WordTrace tailWord_3982648 prefixEnd_3982648 2045012701667639105084141 := by
  unfold tailWord_3982648
  simp only [CollatzResearch.WordTrace]
  refine ⟨72629553037776976485722299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96839404050369301980963065 72629553037776976485722299)
  ·
    refine ⟨108944329556665464728583449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72629553037776976485722299 108944329556665464728583449)
    ·
      refine ⟨81708247167499098546437587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108944329556665464728583449 81708247167499098546437587)
      ·
        refine ⟨122562370751248647819656381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81708247167499098546437587 122562370751248647819656381)
        ·
          refine ⟨45960889031718242932371143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122562370751248647819656381 45960889031718242932371143)
          ·
            refine ⟨68941333547577364398556715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45960889031718242932371143 68941333547577364398556715)
            ·
              refine ⟨103412000321366046597835073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68941333547577364398556715 103412000321366046597835073)
              ·
                refine ⟨77559000241024534948376305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103412000321366046597835073 77559000241024534948376305)
                ·
                  refine ⟨58169250180768401211282229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77559000241024534948376305 58169250180768401211282229)
                  ·
                    refine ⟨5453367204447037613557709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58169250180768401211282229 5453367204447037613557709)
                    ·
                      refine ⟨2045012701667639105084141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453367204447037613557709 2045012701667639105084141)
                      ·
                        rfl

theorem cell23_3982648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_3982648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982648 prefixEnd_3982648 := by exact prefixLift 3982648
  have htrace : WordTrace (prefixWord ++ tailWord_3982648) baseStart_3982648 baseEnd_3982648 := by
    simpa [prefixWord, tailWord_3982648, baseEnd_3982648] using wordTrace_append hprefix tailTrace_3982648
  have hstable : (prefixWord ++ tailWord_3982648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982648).length < 2 ^ (prefixWord ++ tailWord_3982648).sum := by decide
  have hdescent : baseEnd_3982648 < baseStart_3982648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982665 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_3982665 : Nat := 118140960795 + 3982665 * 2 ^ 59
def prefixEnd_3982665 : Nat := 4983230072969 + 3 ^ 40 * 3982665 * 2
def baseEnd_3982665 : Nat := 2045021430838765538571563

theorem tailTrace_3982665 : CollatzResearch.WordTrace tailWord_3982665 prefixEnd_3982665 2045021430838765538571563 := by
  unfold tailWord_3982665
  simp only [CollatzResearch.WordTrace]
  refine ⟨145259726116492364874813449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96839817410994909916542299 145259726116492364874813449)
  ·
    refine ⟨108944794587369273656110087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145259726116492364874813449 108944794587369273656110087)
    ·
      refine ⟨163417191881053910484165131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108944794587369273656110087 163417191881053910484165131)
      ·
        refine ⟨245125787821580865726247697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163417191881053910484165131 245125787821580865726247697)
        ·
          refine ⟨183844340866185649294685773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245125787821580865726247697 183844340866185649294685773)
          ·
            refine ⟨68941627824819618485507165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183844340866185649294685773 68941627824819618485507165)
            ·
              refine ⟨25853110434307356932065187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68941627824819618485507165 25853110434307356932065187)
              ·
                refine ⟨38779665651461035398097781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25853110434307356932065187 38779665651461035398097781)
                ·
                  refine ⟨3635593654824472068571667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38779665651461035398097781 3635593654824472068571667)
                  ·
                    refine ⟨5453390482236708102857501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635593654824472068571667 5453390482236708102857501)
                    ·
                      refine ⟨2045021430838765538571563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453390482236708102857501 2045021430838765538571563)
                      ·
                        rfl

theorem cell23_3982665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_3982665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982665 prefixEnd_3982665 := by exact prefixLift 3982665
  have htrace : WordTrace (prefixWord ++ tailWord_3982665) baseStart_3982665 baseEnd_3982665 := by
    simpa [prefixWord, tailWord_3982665, baseEnd_3982665] using wordTrace_append hprefix tailTrace_3982665
  have hstable : (prefixWord ++ tailWord_3982665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982665).length < 2 ^ (prefixWord ++ tailWord_3982665).sum := by decide
  have hdescent : baseEnd_3982665 < baseStart_3982665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982669 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3982669 : Nat := 118140960795 + 3982669 * 2 ^ 59
def prefixEnd_3982669 : Nat := 4983230072969 + 3 ^ 40 * 3982669 * 2
def baseEnd_3982669 : Nat := 2045023484761383522921545

theorem tailTrace_3982669 : CollatzResearch.WordTrace tailWord_3982669 prefixEnd_3982669 2045023484761383522921545 := by
  unfold tailWord_3982669
  simp only [CollatzResearch.WordTrace]
  refine ⟨145259872008477873557959061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96839914672318582371972707 145259872008477873557959061)
  ·
    refine ⟨6809056500397400323029331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145259872008477873557959061 6809056500397400323029331)
    ·
      refine ⟨10213584750596100484543997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809056500397400323029331 10213584750596100484543997)
      ·
        refine ⟨3830094281473537681703999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10213584750596100484543997 3830094281473537681703999)
        ·
          refine ⟨5745141422210306522555999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830094281473537681703999 5745141422210306522555999)
          ·
            refine ⟨8617712133315459783833999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745141422210306522555999 8617712133315459783833999)
            ·
              refine ⟨12926568199973189675750999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617712133315459783833999 12926568199973189675750999)
              ·
                refine ⟨19389852299959784513626499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926568199973189675750999 19389852299959784513626499)
                ·
                  refine ⟨29084778449939676770439749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389852299959784513626499 29084778449939676770439749)
                  ·
                    refine ⟨5453395959363689394457453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29084778449939676770439749 5453395959363689394457453)
                    ·
                      refine ⟨2045023484761383522921545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453395959363689394457453 2045023484761383522921545)
                      ·
                        rfl

theorem cell23_3982669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3982669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982669 prefixEnd_3982669 := by exact prefixLift 3982669
  have htrace : WordTrace (prefixWord ++ tailWord_3982669) baseStart_3982669 baseEnd_3982669 := by
    simpa [prefixWord, tailWord_3982669, baseEnd_3982669] using wordTrace_append hprefix tailTrace_3982669
  have hstable : (prefixWord ++ tailWord_3982669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982669).length < 2 ^ (prefixWord ++ tailWord_3982669).sum := by decide
  have hdescent : baseEnd_3982669 < baseStart_3982669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982675 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 5, 2]
def baseStart_3982675 : Nat := 118140960795 + 3982675 * 2 ^ 59
def prefixEnd_3982675 : Nat := 4983230072969 + 3 ^ 40 * 3982675 * 2
def baseEnd_3982675 : Nat := 2045026565645310499446517

theorem tailTrace_3982675 : CollatzResearch.WordTrace tailWord_3982675 prefixEnd_3982675 2045026565645310499446517 := by
  unfold tailWord_3982675
  simp only [CollatzResearch.WordTrace]
  refine ⟨145260090846456136582677479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96840060564304091055118319 145260090846456136582677479)
  ·
    refine ⟨217890136269684204874016219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145260090846456136582677479 217890136269684204874016219)
    ·
      refine ⟨326835204404526307311024329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217890136269684204874016219 326835204404526307311024329)
      ·
        refine ⟨245126403303394730483268247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326835204404526307311024329 245126403303394730483268247)
        ·
          refine ⟨367689604955092095724902371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245126403303394730483268247 367689604955092095724902371)
          ·
            refine ⟨551534407432638143587353557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367689604955092095724902371 551534407432638143587353557)
            ·
              refine ⟨12926587674202456490328599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 551534407432638143587353557 12926587674202456490328599)
              ·
                refine ⟨19389881511303684735492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926587674202456490328599 19389881511303684735492899)
                ·
                  refine ⟨29084822266955527103239349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389881511303684735492899 29084822266955527103239349)
                  ·
                    refine ⟨2726702087527080665928689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29084822266955527103239349 2726702087527080665928689)
                    ·
                      refine ⟨2045026565645310499446517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726702087527080665928689 2045026565645310499446517)
                      ·
                        rfl

theorem cell23_3982675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5, 2].length) (baseStart_3982675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982675 prefixEnd_3982675 := by exact prefixLift 3982675
  have htrace : WordTrace (prefixWord ++ tailWord_3982675) baseStart_3982675 baseEnd_3982675 := by
    simpa [prefixWord, tailWord_3982675, baseEnd_3982675] using wordTrace_append hprefix tailTrace_3982675
  have hstable : (prefixWord ++ tailWord_3982675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982675).length < 2 ^ (prefixWord ++ tailWord_3982675).sum := by decide
  have hdescent : baseEnd_3982675 < baseStart_3982675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982725 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_3982725 : Nat := 118140960795 + 3982725 * 2 ^ 59
def prefixEnd_3982725 : Nat := 4983230072969 + 3 ^ 40 * 3982725 * 2
def baseEnd_3982725 : Nat := 2045052239678035303821287

theorem tailTrace_3982725 : CollatzResearch.WordTrace tailWord_3982725 prefixEnd_3982725 2045052239678035303821287 := by
  unfold tailWord_3982725
  simp only [CollatzResearch.WordTrace]
  refine ⟨145261914496274995121997629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96841276330849996747998419 145261914496274995121997629)
  ·
    refine ⟨54473217936103123170749111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145261914496274995121997629 54473217936103123170749111)
    ·
      refine ⟨81709826904154684756123667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54473217936103123170749111 81709826904154684756123667)
      ·
        refine ⟨122564740356232027134185501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81709826904154684756123667 122564740356232027134185501)
        ·
          refine ⟨45961777633587010175319563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122564740356232027134185501 45961777633587010175319563)
          ·
            refine ⟨68942666450380515262979345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45961777633587010175319563 68942666450380515262979345)
            ·
              refine ⟨51706999837785386447234509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68942666450380515262979345 51706999837785386447234509)
              ·
                refine ⟨19390124939169519917712941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51706999837785386447234509 19390124939169519917712941)
                ·
                  refine ⟨7271296852188569969142353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19390124939169519917712941 7271296852188569969142353)
                  ·
                    refine ⟨5453472639141427476856765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271296852188569969142353 5453472639141427476856765)
                    ·
                      refine ⟨2045052239678035303821287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453472639141427476856765 2045052239678035303821287)
                      ·
                        rfl

theorem cell23_3982725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_3982725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982725 prefixEnd_3982725 := by exact prefixLift 3982725
  have htrace : WordTrace (prefixWord ++ tailWord_3982725) baseStart_3982725 baseEnd_3982725 := by
    simpa [prefixWord, tailWord_3982725, baseEnd_3982725] using wordTrace_append hprefix tailTrace_3982725
  have hstable : (prefixWord ++ tailWord_3982725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982725).length < 2 ^ (prefixWord ++ tailWord_3982725).sum := by decide
  have hdescent : baseEnd_3982725 < baseStart_3982725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982750 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3982750 : Nat := 118140960795 + 3982750 * 2 ^ 59
def prefixEnd_3982750 : Nat := 4983230072969 + 3 ^ 40 * 3982750 * 2
def baseEnd_3982750 : Nat := 2045065076694397706008673

theorem tailTrace_3982750 : CollatzResearch.WordTrace tailWord_3982750 prefixEnd_3982750 2045065076694397706008673 := by
  unfold tailWord_3982750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157853290148053048957213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96841884214122949594438469 18157853290148053048957213)
  ·
    refine ⟨6809194983805519893358955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18157853290148053048957213 6809194983805519893358955)
    ·
      refine ⟨10213792475708279840038433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809194983805519893358955 10213792475708279840038433)
      ·
        refine ⟨7660344356781209880028825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10213792475708279840038433 7660344356781209880028825)
        ·
          refine ⟨5745258267585907410021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660344356781209880028825 5745258267585907410021619)
          ·
            refine ⟨8617887401378861115032429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745258267585907410021619 8617887401378861115032429)
            ·
              refine ⟨3231707775517072918137161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8617887401378861115032429 3231707775517072918137161)
              ·
                refine ⟨2423780831637804688602871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231707775517072918137161 2423780831637804688602871)
                ·
                  refine ⟨3635671247456707032904307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423780831637804688602871 3635671247456707032904307)
                  ·
                    refine ⟨5453506871185060549356461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635671247456707032904307 5453506871185060549356461)
                    ·
                      refine ⟨2045065076694397706008673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453506871185060549356461 2045065076694397706008673)
                      ·
                        rfl

theorem cell23_3982750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3982750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982750 prefixEnd_3982750 := by exact prefixLift 3982750
  have htrace : WordTrace (prefixWord ++ tailWord_3982750) baseStart_3982750 baseEnd_3982750 := by
    simpa [prefixWord, tailWord_3982750, baseEnd_3982750] using wordTrace_append hprefix tailTrace_3982750
  have hstable : (prefixWord ++ tailWord_3982750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982750).length < 2 ^ (prefixWord ++ tailWord_3982750).sum := by decide
  have hdescent : baseEnd_3982750 < baseStart_3982750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982768 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_3982768 : Nat := 118140960795 + 3982768 * 2 ^ 59
def prefixEnd_3982768 : Nat := 4983230072969 + 3 ^ 40 * 3982768 * 2
def baseEnd_3982768 : Nat := 2045074319346178635583589

theorem tailTrace_3982768 : CollatzResearch.WordTrace tailWord_3982768 prefixEnd_3982768 2045074319346178635583589 := by
  unfold tailWord_3982768
  simp only [CollatzResearch.WordTrace]
  refine ⟨72631741417559606732906479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96842321890079475643875305 72631741417559606732906479)
  ·
    refine ⟨108947612126339410099359719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72631741417559606732906479 108947612126339410099359719)
    ·
      refine ⟨163421418189509115149039579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108947612126339410099359719 163421418189509115149039579)
      ·
        refine ⟨245132127284263672723559369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163421418189509115149039579 245132127284263672723559369)
        ·
          refine ⟨183849095463197754542669527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245132127284263672723559369 183849095463197754542669527)
          ·
            refine ⟨275773643194796631814004291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183849095463197754542669527 275773643194796631814004291)
            ·
              refine ⟨413660464792194947721006437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275773643194796631814004291 413660464792194947721006437)
              ·
                refine ⟨77561337148536552697688707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413660464792194947721006437 77561337148536552697688707)
                ·
                  refine ⟨116342005722804829046533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77561337148536552697688707 116342005722804829046533061)
                  ·
                    refine ⟨21814126073025905446224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116342005722804829046533061 21814126073025905446224949)
                    ·
                      refine ⟨2045074319346178635583589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21814126073025905446224949 2045074319346178635583589)
                      ·
                        rfl

theorem cell23_3982768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_3982768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982768 prefixEnd_3982768 := by exact prefixLift 3982768
  have htrace : WordTrace (prefixWord ++ tailWord_3982768) baseStart_3982768 baseEnd_3982768 := by
    simpa [prefixWord, tailWord_3982768, baseEnd_3982768] using wordTrace_append hprefix tailTrace_3982768
  have hstable : (prefixWord ++ tailWord_3982768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982768).length < 2 ^ (prefixWord ++ tailWord_3982768).sum := by decide
  have hdescent : baseEnd_3982768 < baseStart_3982768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_3982778 : Nat := 118140960795 + 3982778 * 2 ^ 59
def prefixEnd_3982778 : Nat := 4983230072969 + 3 ^ 40 * 3982778 * 2
def baseEnd_3982778 : Nat := 2045079454152723596458543

theorem tailTrace_3982778 : CollatzResearch.WordTrace tailWord_3982778 prefixEnd_3982778 2045079454152723596458543 := by
  unfold tailWord_3982778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315961891270746293419247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96842565043388656782451325 36315961891270746293419247)
  ·
    refine ⟨54473942836906119440128871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36315961891270746293419247 54473942836906119440128871)
    ·
      refine ⟨81710914255359179160193307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54473942836906119440128871 81710914255359179160193307)
      ·
        refine ⟨122566371383038768740289961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81710914255359179160193307 122566371383038768740289961)
        ·
          refine ⟨91924778537279076555217471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122566371383038768740289961 91924778537279076555217471)
          ·
            refine ⟨137887167805918614832826207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91924778537279076555217471 137887167805918614832826207)
            ·
              refine ⟨206830751708877922249239311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137887167805918614832826207 206830751708877922249239311)
              ·
                refine ⟨310246127563316883373858967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206830751708877922249239311 310246127563316883373858967)
                ·
                  refine ⟨465369191344975325060788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310246127563316883373858967 465369191344975325060788451)
                  ·
                    refine ⟨698053787017462987591182677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465369191344975325060788451 698053787017462987591182677)
                    ·
                      refine ⟨2045079454152723596458543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 698053787017462987591182677 2045079454152723596458543)
                      ·
                        rfl

theorem cell23_3982778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_3982778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982778 prefixEnd_3982778 := by exact prefixLift 3982778
  have htrace : WordTrace (prefixWord ++ tailWord_3982778) baseStart_3982778 baseEnd_3982778 := by
    simpa [prefixWord, tailWord_3982778, baseEnd_3982778] using wordTrace_append hprefix tailTrace_3982778
  have hstable : (prefixWord ++ tailWord_3982778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982778).length < 2 ^ (prefixWord ++ tailWord_3982778).sum := by decide
  have hdescent : baseEnd_3982778 < baseStart_3982778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982805 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3982805 : Nat := 118140960795 + 3982805 * 2 ^ 59
def prefixEnd_3982805 : Nat := 4983230072969 + 3 ^ 40 * 3982805 * 2
def baseEnd_3982805 : Nat := 681697772710131663606973

theorem tailTrace_3982805 : CollatzResearch.WordTrace tailWord_3982805 prefixEnd_3982805 681697772710131663606973 := by
  unfold tailWord_3982805
  simp only [CollatzResearch.WordTrace]
  refine ⟨145264832335985168784909869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96843221557323445856606579 145264832335985168784909869)
  ·
    refine ⟨54474312125994438294341201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145264832335985168784909869 54474312125994438294341201)
    ·
      refine ⟨40855734094495828720755901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54474312125994438294341201 40855734094495828720755901)
      ·
        refine ⟨15320900285435935770283463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40855734094495828720755901 15320900285435935770283463)
        ·
          refine ⟨22981350428153903655425195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320900285435935770283463 22981350428153903655425195)
          ·
            refine ⟨34472025642230855483137793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22981350428153903655425195 34472025642230855483137793)
            ·
              refine ⟨25854019231673141612353345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34472025642230855483137793 25854019231673141612353345)
              ·
                refine ⟨19390514423754856209265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25854019231673141612353345 19390514423754856209265009)
                ·
                  refine ⟨14542885817816142156948757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19390514423754856209265009 14542885817816142156948757)
                  ·
                    refine ⟨681697772710131663606973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14542885817816142156948757 681697772710131663606973)
                    ·
                      rfl

theorem cell23_3982805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3982805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982805 prefixEnd_3982805 := by exact prefixLift 3982805
  have htrace : WordTrace (prefixWord ++ tailWord_3982805) baseStart_3982805 baseEnd_3982805 := by
    simpa [prefixWord, tailWord_3982805, baseEnd_3982805] using wordTrace_append hprefix tailTrace_3982805
  have hstable : (prefixWord ++ tailWord_3982805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982805).length < 2 ^ (prefixWord ++ tailWord_3982805).sum := by decide
  have hdescent : baseEnd_3982805 < baseStart_3982805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982806 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3982806 : Nat := 118140960795 + 3982806 * 2 ^ 59
def prefixEnd_3982806 : Nat := 4983230072969 + 3 ^ 40 * 3982806 * 2
def baseEnd_3982806 : Nat := 2045093831611049486908415

theorem tailTrace_3982806 : CollatzResearch.WordTrace tailWord_3982806 prefixEnd_3982806 2045093831611049486908415 := by
  unfold tailWord_3982806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079054300561346622231017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96843245872654363970464181 9079054300561346622231017)
  ·
    refine ⟨6809290725421009966673263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9079054300561346622231017 6809290725421009966673263)
    ·
      refine ⟨10213936088131514950009895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809290725421009966673263 10213936088131514950009895)
      ·
        refine ⟨15320904132197272425014843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213936088131514950009895 15320904132197272425014843)
        ·
          refine ⟨22981356198295908637522265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320904132197272425014843 22981356198295908637522265)
          ·
            refine ⟨17236017148721931478141699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22981356198295908637522265 17236017148721931478141699)
            ·
              refine ⟨25854025723082897217212549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17236017148721931478141699 25854025723082897217212549)
              ·
                refine ⟨4847629823078043228227353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25854025723082897217212549 4847629823078043228227353)
                ·
                  refine ⟨3635722367308532421170515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4847629823078043228227353 3635722367308532421170515)
                  ·
                    refine ⟨5453583550962798631755773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3635722367308532421170515 5453583550962798631755773)
                    ·
                      refine ⟨2045093831611049486908415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453583550962798631755773 2045093831611049486908415)
                      ·
                        rfl

theorem cell23_3982806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3982806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982806 prefixEnd_3982806 := by exact prefixLift 3982806
  have htrace : WordTrace (prefixWord ++ tailWord_3982806) baseStart_3982806 baseEnd_3982806 := by
    simpa [prefixWord, tailWord_3982806, baseEnd_3982806] using wordTrace_append hprefix tailTrace_3982806
  have hstable : (prefixWord ++ tailWord_3982806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982806).length < 2 ^ (prefixWord ++ tailWord_3982806).sum := by decide
  have hdescent : baseEnd_3982806 < baseStart_3982806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982815 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_3982815 : Nat := 118140960795 + 3982815 * 2 ^ 59
def prefixEnd_3982815 : Nat := 4983230072969 + 3 ^ 40 * 3982815 * 2
def baseEnd_3982815 : Nat := 2045098452936939951695873

theorem tailTrace_3982815 : CollatzResearch.WordTrace tailWord_3982815 prefixEnd_3982815 2045098452936939951695873 := by
  unfold tailWord_3982815
  simp only [CollatzResearch.WordTrace]
  refine ⟨145265197065948940492773899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96843464710632626995182599 145265197065948940492773899)
  ·
    refine ⟨217897795598923410739160849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145265197065948940492773899 217897795598923410739160849)
    ·
      refine ⟨163423346699192558054370637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217897795598923410739160849 163423346699192558054370637)
      ·
        refine ⟨61283755012197209270388989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163423346699192558054370637 61283755012197209270388989)
        ·
          refine ⟨22981408129573953476395871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61283755012197209270388989 22981408129573953476395871)
          ·
            refine ⟨34472112194360930214593807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22981408129573953476395871 34472112194360930214593807)
            ·
              refine ⟨51708168291541395321890711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34472112194360930214593807 51708168291541395321890711)
              ·
                refine ⟨77562252437312092982836067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51708168291541395321890711 77562252437312092982836067)
                ·
                  refine ⟨116343378655968139474254101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77562252437312092982836067 116343378655968139474254101)
                  ·
                    refine ⟨5453595874498506537855661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116343378655968139474254101 5453595874498506537855661)
                    ·
                      refine ⟨2045098452936939951695873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5453595874498506537855661 2045098452936939951695873)
                      ·
                        rfl

theorem cell23_3982815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_3982815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982815 prefixEnd_3982815 := by exact prefixLift 3982815
  have htrace : WordTrace (prefixWord ++ tailWord_3982815) baseStart_3982815 baseEnd_3982815 := by
    simpa [prefixWord, tailWord_3982815, baseEnd_3982815] using wordTrace_append hprefix tailTrace_3982815
  have hstable : (prefixWord ++ tailWord_3982815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982815).length < 2 ^ (prefixWord ++ tailWord_3982815).sum := by decide
  have hdescent : baseEnd_3982815 < baseStart_3982815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982850 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3982850 : Nat := 118140960795 + 3982850 * 2 ^ 59
def prefixEnd_3982850 : Nat := 4983230072969 + 3 ^ 40 * 3982850 * 2
def baseEnd_3982850 : Nat := 2045116424759847314758213

theorem tailTrace_3982850 : CollatzResearch.WordTrace tailWord_3982850 prefixEnd_3982850 2045116424759847314758213 := by
  unfold tailWord_3982850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36316618405205535367574501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96844315747214760980198669 36316618405205535367574501)
  ·
    refine ⟨6809365950976037881420219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36316618405205535367574501 6809365950976037881420219)
    ·
      refine ⟨10214048926464056822130329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809365950976037881420219 10214048926464056822130329)
      ·
        refine ⟨7660536694848042616597747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10214048926464056822130329 7660536694848042616597747)
        ·
          refine ⟨11490805042272063924896621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660536694848042616597747 11490805042272063924896621)
          ·
            refine ⟨4309051890852023971836233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11490805042272063924896621 4309051890852023971836233)
            ·
              refine ⟨3231788918139017978877175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309051890852023971836233 3231788918139017978877175)
              ·
                refine ⟨4847683377208526968315763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231788918139017978877175 4847683377208526968315763)
                ·
                  refine ⟨7271525065812790452473645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847683377208526968315763 7271525065812790452473645)
                  ·
                    refine ⟨2726821899679796419677617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7271525065812790452473645 2726821899679796419677617)
                    ·
                      refine ⟨2045116424759847314758213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726821899679796419677617 2045116424759847314758213)
                      ·
                        rfl

theorem cell23_3982850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3982850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982850 prefixEnd_3982850 := by exact prefixLift 3982850
  have htrace : WordTrace (prefixWord ++ tailWord_3982850) baseStart_3982850 baseEnd_3982850 := by
    simpa [prefixWord, tailWord_3982850, baseEnd_3982850] using wordTrace_append hprefix tailTrace_3982850
  have hstable : (prefixWord ++ tailWord_3982850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982850).length < 2 ^ (prefixWord ++ tailWord_3982850).sum := by decide
  have hdescent : baseEnd_3982850 < baseStart_3982850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982865 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_3982865 : Nat := 118140960795 + 3982865 * 2 ^ 59
def prefixEnd_3982865 : Nat := 4983230072969 + 3 ^ 40 * 3982865 * 2
def baseEnd_3982865 : Nat := 681708042323221585356881

theorem tailTrace_3982865 : CollatzResearch.WordTrace tailWord_3982865 prefixEnd_3982865 681708042323221585356881 := by
  unfold tailWord_3982865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145267020715767799032094049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96844680477178532688062699 145267020715767799032094049)
  ·
    refine ⟨108950265536825849274070537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145267020715767799032094049 108950265536825849274070537)
    ·
      refine ⟨81712699152619386955552903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108950265536825849274070537 81712699152619386955552903)
      ·
        refine ⟨122569048728929080433329355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81712699152619386955552903 122569048728929080433329355)
        ·
          refine ⟨183853573093393620649994033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122569048728929080433329355 183853573093393620649994033)
          ·
            refine ⟨137890179820045215487495525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183853573093393620649994033 137890179820045215487495525)
            ·
              refine ⟨25854408716258477903905411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137890179820045215487495525 25854408716258477903905411)
              ·
                refine ⟨38781613074387716855858117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25854408716258477903905411 38781613074387716855858117)
                ·
                  refine ⟨7271552451447696910473397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38781613074387716855858117 7271552451447696910473397)
                  ·
                    refine ⟨681708042323221585356881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7271552451447696910473397 681708042323221585356881)
                    ·
                      rfl

theorem cell23_3982865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_3982865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982865 prefixEnd_3982865 := by exact prefixLift 3982865
  have htrace : WordTrace (prefixWord ++ tailWord_3982865) baseStart_3982865 baseEnd_3982865 := by
    simpa [prefixWord, tailWord_3982865, baseEnd_3982865] using wordTrace_append hprefix tailTrace_3982865
  have hstable : (prefixWord ++ tailWord_3982865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982865).length < 2 ^ (prefixWord ++ tailWord_3982865).sum := by decide
  have hdescent : baseEnd_3982865 < baseStart_3982865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982919 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_3982919 : Nat := 118140960795 + 3982919 * 2 ^ 59
def prefixEnd_3982919 : Nat := 4983230072969 + 3 ^ 40 * 3982919 * 2
def baseEnd_3982919 : Nat := 2045151854925007544795395

theorem tailTrace_3982919 : CollatzResearch.WordTrace tailWord_3982919 prefixEnd_3982919 2045151854925007544795395 := by
  unfold tailWord_3982919
  simp only [CollatzResearch.WordTrace]
  refine ⟨145268990257572166254559811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96845993505048110836373207 145268990257572166254559811)
  ·
    refine ⟨217903485386358249381839717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145268990257572166254559811 217903485386358249381839717)
    ·
      refine ⟨40856903509942171759094947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217903485386358249381839717 40856903509942171759094947)
      ·
        refine ⟨61285355264913257638642421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40856903509942171759094947 61285355264913257638642421)
        ·
          refine ⟨5745502056085617903622727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61285355264913257638642421 5745502056085617903622727)
          ·
            refine ⟨8618253084128426855434091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745502056085617903622727 8618253084128426855434091)
            ·
              refine ⟨12927379626192640283151137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618253084128426855434091 12927379626192640283151137)
              ·
                refine ⟨9695534719644480212363353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12927379626192640283151137 9695534719644480212363353)
                ·
                  refine ⟨7271651039733360159272515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695534719644480212363353 7271651039733360159272515)
                  ·
                    refine ⟨10907476559600040238908773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271651039733360159272515 10907476559600040238908773)
                    ·
                      refine ⟨2045151854925007544795395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10907476559600040238908773 2045151854925007544795395)
                      ·
                        rfl

theorem cell23_3982919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_3982919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982919 prefixEnd_3982919 := by exact prefixLift 3982919
  have htrace : WordTrace (prefixWord ++ tailWord_3982919) baseStart_3982919 baseEnd_3982919 := by
    simpa [prefixWord, tailWord_3982919, baseEnd_3982919] using wordTrace_append hprefix tailTrace_3982919
  have hstable : (prefixWord ++ tailWord_3982919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982919).length < 2 ^ (prefixWord ++ tailWord_3982919).sum := by decide
  have hdescent : baseEnd_3982919 < baseStart_3982919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3982980 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_3982980 : Nat := 118140960795 + 3982980 * 2 ^ 59
def prefixEnd_3982980 : Nat := 4983230072969 + 3 ^ 40 * 3982980 * 2
def baseEnd_3982980 : Nat := 681727725748310602044205

theorem tailTrace_3982980 : CollatzResearch.WordTrace tailWord_3982980 prefixEnd_3982980 681727725748310602044205 := by
  unfold tailWord_3982980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72635607555175586836265197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96847476740234115781686929 72635607555175586836265197)
  ·
    refine ⟨27238352833190845063599449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72635607555175586836265197 27238352833190845063599449)
    ·
      refine ⟨20428764624893133797699587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27238352833190845063599449 20428764624893133797699587)
      ·
        refine ⟨30643146937339700696549381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428764624893133797699587 30643146937339700696549381)
        ·
          refine ⟨5745590050751193880603009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30643146937339700696549381 5745590050751193880603009)
          ·
            refine ⟨4309192538063395410452257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5745590050751193880603009 4309192538063395410452257)
            ·
              refine ⟨3231894403547546557839193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309192538063395410452257 3231894403547546557839193)
              ·
                refine ⟨2423920802660659918379395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231894403547546557839193 2423920802660659918379395)
                ·
                  refine ⟨3635881203990989877569093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423920802660659918379395 3635881203990989877569093)
                  ·
                    refine ⟨681727725748310602044205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635881203990989877569093 681727725748310602044205)
                    ·
                      rfl

theorem cell23_3982980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_3982980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3982980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3982980 prefixEnd_3982980 := by exact prefixLift 3982980
  have htrace : WordTrace (prefixWord ++ tailWord_3982980) baseStart_3982980 baseEnd_3982980 := by
    simpa [prefixWord, tailWord_3982980, baseEnd_3982980] using wordTrace_append hprefix tailTrace_3982980
  have hstable : (prefixWord ++ tailWord_3982980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3982980).length < 2 ^ (prefixWord ++ tailWord_3982980).sum := by decide
  have hdescent : baseEnd_3982980 < baseStart_3982980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3982980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983009 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3983009 : Nat := 118140960795 + 3983009 * 2 ^ 59
def prefixEnd_3983009 : Nat := 4983230072969 + 3 ^ 40 * 3983009 * 2
def baseEnd_3983009 : Nat := 2045198068183912192669981

theorem tailTrace_3983009 : CollatzResearch.WordTrace tailWord_3983009 prefixEnd_3983009 2045198068183912192669981 := by
  unfold tailWord_3983009
  simp only [CollatzResearch.WordTrace]
  refine ⟨145272272827246111625336081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96848181884830741083557387 145272272827246111625336081)
  ·
    refine ⟨108954204620434583719002061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145272272827246111625336081 108954204620434583719002061)
    ·
      refine ⟨40857826732662968894625773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108954204620434583719002061 40857826732662968894625773)
      ·
        refine ⟨15321685024748613335484665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40857826732662968894625773 15321685024748613335484665)
        ·
          refine ⟨11491263768561460001613499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15321685024748613335484665 11491263768561460001613499)
          ·
            refine ⟨17236895652842190002420249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491263768561460001613499 17236895652842190002420249)
            ·
              refine ⟨12927671739631642501815187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17236895652842190002420249 12927671739631642501815187)
              ·
                refine ⟨19391507609447463752722781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927671739631642501815187 19391507609447463752722781)
                ·
                  refine ⟨7271815353542798907271043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19391507609447463752722781 7271815353542798907271043)
                  ·
                    refine ⟨10907723030314198360906565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271815353542798907271043 10907723030314198360906565)
                    ·
                      refine ⟨2045198068183912192669981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10907723030314198360906565 2045198068183912192669981)
                      ·
                        rfl

theorem cell23_3983009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3983009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983009 prefixEnd_3983009 := by exact prefixLift 3983009
  have htrace : WordTrace (prefixWord ++ tailWord_3983009) baseStart_3983009 baseEnd_3983009 := by
    simpa [prefixWord, tailWord_3983009, baseEnd_3983009] using wordTrace_append hprefix tailTrace_3983009
  have hstable : (prefixWord ++ tailWord_3983009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983009).length < 2 ^ (prefixWord ++ tailWord_3983009).sum := by decide
  have hdescent : baseEnd_3983009 < baseStart_3983009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983026 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_3983026 : Nat := 118140960795 + 3983026 * 2 ^ 59
def prefixEnd_3983026 : Nat := 4983230072969 + 3 ^ 40 * 3983026 * 2
def baseEnd_3983026 : Nat := 2045206797355038626157403

theorem tailTrace_3983026 : CollatzResearch.WordTrace tailWord_3983026 prefixEnd_3983026 2045206797355038626157403 := by
  unfold tailWord_3983026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318223217046130882176233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96848595245456349019136621 36318223217046130882176233)
  ·
    refine ⟨27238667412784598161632175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36318223217046130882176233 27238667412784598161632175)
    ·
      refine ⟨40858001119176897242448263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238667412784598161632175 40858001119176897242448263)
      ·
        refine ⟨61287001678765345863672395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40858001119176897242448263 61287001678765345863672395)
        ·
          refine ⟨91930502518148018795508593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61287001678765345863672395 91930502518148018795508593)
          ·
            refine ⟨68947876888611014096631445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91930502518148018795508593 68947876888611014096631445)
            ·
              refine ⟨3231931729153641285779599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68947876888611014096631445 3231931729153641285779599)
              ·
                refine ⟨4847897593730461928669399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231931729153641285779599 4847897593730461928669399)
                ·
                  refine ⟨7271846390595692893004099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847897593730461928669399 7271846390595692893004099)
                  ·
                    refine ⟨10907769585893539339506149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271846390595692893004099 10907769585893539339506149)
                    ·
                      refine ⟨2045206797355038626157403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10907769585893539339506149 2045206797355038626157403)
                      ·
                        rfl

theorem cell23_3983026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_3983026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983026 prefixEnd_3983026 := by exact prefixLift 3983026
  have htrace : WordTrace (prefixWord ++ tailWord_3983026) baseStart_3983026 baseEnd_3983026 := by
    simpa [prefixWord, tailWord_3983026, baseEnd_3983026] using wordTrace_append hprefix tailTrace_3983026
  have hstable : (prefixWord ++ tailWord_3983026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983026).length < 2 ^ (prefixWord ++ tailWord_3983026).sum := by decide
  have hdescent : baseEnd_3983026 < baseStart_3983026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983036 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3983036 : Nat := 118140960795 + 3983036 * 2 ^ 59
def prefixEnd_3983036 : Nat := 4983230072969 + 3 ^ 40 * 3983036 * 2
def baseEnd_3983036 : Nat := 681737310720527862344119

theorem tailTrace_3983036 : CollatzResearch.WordTrace tailWord_3983036 prefixEnd_3983036 681737310720527862344119 := by
  unfold tailWord_3983036
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636628799074147618284481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96848838398765530157712641 72636628799074147618284481)
  ·
    refine ⟨54477471599305610713713361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72636628799074147618284481 54477471599305610713713361)
    ·
      refine ⟨40858103699479208035285021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54477471599305610713713361 40858103699479208035285021)
      ·
        refine ⟨15321788887304703013231883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40858103699479208035285021 15321788887304703013231883)
        ·
          refine ⟨22982683330957054519847825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15321788887304703013231883 22982683330957054519847825)
          ·
            refine ⟨17237012498217790889885869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22982683330957054519847825 17237012498217790889885869)
            ·
              refine ⟨6463879686831671583707201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17237012498217790889885869 6463879686831671583707201)
              ·
                refine ⟨4847909765123753687780401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463879686831671583707201 4847909765123753687780401)
                ·
                  refine ⟨3635932323842815265835301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4847909765123753687780401 3635932323842815265835301)
                  ·
                    refine ⟨681737310720527862344119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635932323842815265835301 681737310720527862344119)
                    ·
                      rfl

theorem cell23_3983036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3983036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983036 prefixEnd_3983036 := by exact prefixLift 3983036
  have htrace : WordTrace (prefixWord ++ tailWord_3983036) baseStart_3983036 baseEnd_3983036 := by
    simpa [prefixWord, tailWord_3983036, baseEnd_3983036] using wordTrace_append hprefix tailTrace_3983036
  have hstable : (prefixWord ++ tailWord_3983036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983036).length < 2 ^ (prefixWord ++ tailWord_3983036).sum := by decide
  have hdescent : baseEnd_3983036 < baseStart_3983036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983053 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3983053 : Nat := 118140960795 + 3983053 * 2 ^ 59
def prefixEnd_3983053 : Nat := 4983230072969 + 3 ^ 40 * 3983053 * 2
def baseEnd_3983053 : Nat := 681740220444236673506593

theorem tailTrace_3983053 : CollatzResearch.WordTrace tailWord_3983053 prefixEnd_3983053 681740220444236673506593 := by
  unfold tailWord_3983053
  simp only [CollatzResearch.WordTrace]
  refine ⟨145273877639086707139937813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96849251759391138093291875 145273877639086707139937813)
  ·
    refine ⟨6809713014332189397184585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145273877639086707139937813 6809713014332189397184585)
    ·
      refine ⟨5107284760749142047888439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6809713014332189397184585 5107284760749142047888439)
      ·
        refine ⟨7660927141123713071832659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107284760749142047888439 7660927141123713071832659)
        ·
          refine ⟨11491390711685569607748989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660927141123713071832659 11491390711685569607748989)
          ·
            refine ⟨4309271516882088602905871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11491390711685569607748989 4309271516882088602905871)
            ·
              refine ⟨6463907275323132904358807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309271516882088602905871 6463907275323132904358807)
              ·
                refine ⟨9695860912984699356538211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463907275323132904358807 9695860912984699356538211)
                ·
                  refine ⟨14543791369477049034807317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9695860912984699356538211 14543791369477049034807317)
                  ·
                    refine ⟨681740220444236673506593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14543791369477049034807317 681740220444236673506593)
                    ·
                      rfl

theorem cell23_3983053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3983053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983053 prefixEnd_3983053 := by exact prefixLift 3983053
  have htrace : WordTrace (prefixWord ++ tailWord_3983053) baseStart_3983053 baseEnd_3983053 := by
    simpa [prefixWord, tailWord_3983053, baseEnd_3983053] using wordTrace_append hprefix tailTrace_3983053
  have hstable : (prefixWord ++ tailWord_3983053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983053).length < 2 ^ (prefixWord ++ tailWord_3983053).sum := by decide
  have hdescent : baseEnd_3983053 < baseStart_3983053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983072 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3983072 : Nat := 118140960795 + 3983072 * 2 ^ 59
def prefixEnd_3983072 : Nat := 4983230072969 + 3 ^ 40 * 3983072 * 2
def baseEnd_3983072 : Nat := 2045230417465145446182191

theorem tailTrace_3983072 : CollatzResearch.WordTrace tailWord_3983072 prefixEnd_3983072 2045230417465145446182191 := by
  unfold tailWord_3983072
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637285313008936692439735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96849713750678582256586313 72637285313008936692439735)
  ·
    refine ⟨108955927969513405038659603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72637285313008936692439735 108955927969513405038659603)
    ·
      refine ⟨163433891954270107557989405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108955927969513405038659603 163433891954270107557989405)
      ·
        refine ⟨61287709482851290334246027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163433891954270107557989405 61287709482851290334246027)
        ·
          refine ⟨91931564224276935501369041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61287709482851290334246027 91931564224276935501369041)
          ·
            refine ⟨68948673168207701626026781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91931564224276935501369041 68948673168207701626026781)
            ·
              refine ⟨25855752438077888109760043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68948673168207701626026781 25855752438077888109760043)
              ·
                refine ⟨38783628657116832164640065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25855752438077888109760043 38783628657116832164640065)
                ·
                  refine ⟨29087721492837624123480049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38783628657116832164640065 29087721492837624123480049)
                  ·
                    refine ⟨21815791119628218092610037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29087721492837624123480049 21815791119628218092610037)
                    ·
                      refine ⟨2045230417465145446182191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21815791119628218092610037 2045230417465145446182191)
                      ·
                        rfl

theorem cell23_3983072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3983072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983072 prefixEnd_3983072 := by exact prefixLift 3983072
  have htrace : WordTrace (prefixWord ++ tailWord_3983072) baseStart_3983072 baseEnd_3983072 := by
    simpa [prefixWord, tailWord_3983072, baseEnd_3983072] using wordTrace_append hprefix tailTrace_3983072
  have hstable : (prefixWord ++ tailWord_3983072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983072).length < 2 ^ (prefixWord ++ tailWord_3983072).sum := by decide
  have hdescent : baseEnd_3983072 < baseStart_3983072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 4, 2]
def baseStart_3983099 : Nat := 118140960795 + 3983099 * 2 ^ 59
def prefixEnd_3983099 : Nat := 4983230072969 + 3 ^ 40 * 3983099 * 2
def baseEnd_3983099 : Nat := 2045244281442816840544567

theorem tailTrace_3983099 : CollatzResearch.WordTrace tailWord_3983099 prefixEnd_3983099 2045244281442816840544567 := by
  unfold tailWord_3983099
  simp only [CollatzResearch.WordTrace]
  refine ⟨145275555396920056996112351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96850370264613371330741567 145275555396920056996112351)
  ·
    refine ⟨217913333095380085494168527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145275555396920056996112351 217913333095380085494168527)
    ·
      refine ⟨326869999643070128241252791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217913333095380085494168527 326869999643070128241252791)
      ·
        refine ⟨490304999464605192361879187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326869999643070128241252791 490304999464605192361879187)
        ·
          refine ⟨735457499196907788542818781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490304999464605192361879187 735457499196907788542818781)
          ·
            refine ⟨275796562198840420703557043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735457499196907788542818781 275796562198840420703557043)
            ·
              refine ⟨413694843298260631055335565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275796562198840420703557043 413694843298260631055335565)
              ·
                refine ⟨155135566236847736645750837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413694843298260631055335565 155135566236847736645750837)
                ·
                  refine ⟨14543959334704475310539141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155135566236847736645750837 14543959334704475310539141)
                  ·
                    refine ⟨2726992375257089120726089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14543959334704475310539141 2726992375257089120726089)
                    ·
                      refine ⟨2045244281442816840544567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2726992375257089120726089 2045244281442816840544567)
                      ·
                        rfl

theorem cell23_3983099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4, 2].length) (baseStart_3983099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983099 prefixEnd_3983099 := by exact prefixLift 3983099
  have htrace : WordTrace (prefixWord ++ tailWord_3983099) baseStart_3983099 baseEnd_3983099 := by
    simpa [prefixWord, tailWord_3983099, baseEnd_3983099] using wordTrace_append hprefix tailTrace_3983099
  have hstable : (prefixWord ++ tailWord_3983099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983099).length < 2 ^ (prefixWord ++ tailWord_3983099).sum := by decide
  have hdescent : baseEnd_3983099 < baseStart_3983099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983152 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_3983152 : Nat := 118140960795 + 3983152 * 2 ^ 59
def prefixEnd_3983152 : Nat := 4983230072969 + 3 ^ 40 * 3983152 * 2
def baseEnd_3983152 : Nat := 681757165305835044393941

theorem tailTrace_3983152 : CollatzResearch.WordTrace tailWord_3983152 prefixEnd_3983152 681757165305835044393941 := by
  unfold tailWord_3983152
  simp only [CollatzResearch.WordTrace]
  refine ⟨72638744232864023523895855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96851658977152031365194473 72638744232864023523895855)
  ·
    refine ⟨108958116349296035285843783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72638744232864023523895855 108958116349296035285843783)
    ·
      refine ⟨163437174523944052928765675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108958116349296035285843783 163437174523944052928765675)
      ·
        refine ⟨245155761785916079393148513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163437174523944052928765675 245155761785916079393148513)
        ·
          refine ⟨183866821339437059544861385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245155761785916079393148513 183866821339437059544861385)
          ·
            refine ⟨137900116004577794658646039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183866821339437059544861385 137900116004577794658646039)
            ·
              refine ⟨206850174006866691987969059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137900116004577794658646039 206850174006866691987969059)
              ·
                refine ⟨310275261010300037981953589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206850174006866691987969059 310275261010300037981953589)
                ·
                  refine ⟨29088305719715628560808149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310275261010300037981953589 29088305719715628560808149)
                  ·
                    refine ⟨681757165305835044393941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29088305719715628560808149 681757165305835044393941)
                    ·
                      rfl

theorem cell23_3983152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_3983152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983152 prefixEnd_3983152 := by exact prefixLift 3983152
  have htrace : WordTrace (prefixWord ++ tailWord_3983152) baseStart_3983152 baseEnd_3983152 := by
    simpa [prefixWord, tailWord_3983152, baseEnd_3983152] using wordTrace_append hprefix tailTrace_3983152
  have hstable : (prefixWord ++ tailWord_3983152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983152).length < 2 ^ (prefixWord ++ tailWord_3983152).sum := by decide
  have hdescent : baseEnd_3983152 < baseStart_3983152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983166 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3983166 : Nat := 118140960795 + 3983166 * 2 ^ 59
def prefixEnd_3983166 : Nat := 4983230072969 + 3 ^ 40 * 3983166 * 2
def baseEnd_3983166 : Nat := 2045278684646668078406759

theorem tailTrace_3983166 : CollatzResearch.WordTrace tailWord_3983166 prefixEnd_3983166 2045278684646668078406759 := by
  unfold tailWord_3983166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159749885959665929850169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96851999391784884959200901 18159749885959665929850169)
  ·
    refine ⟨13619812414469749447387627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18159749885959665929850169 13619812414469749447387627)
    ·
      refine ⟨20429718621704624171081441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13619812414469749447387627 20429718621704624171081441)
      ·
        refine ⟨15322288966278468128311081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20429718621704624171081441 15322288966278468128311081)
        ·
          refine ⟨11491716724708851096233311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15322288966278468128311081 11491716724708851096233311)
          ·
            refine ⟨17237575087063276644349967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491716724708851096233311 17237575087063276644349967)
            ·
              refine ⟨25856362630594914966524951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17237575087063276644349967 25856362630594914966524951)
              ·
                refine ⟨38784543945892372449787427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25856362630594914966524951 38784543945892372449787427)
                ·
                  refine ⟨58176815918838558674681141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38784543945892372449787427 58176815918838558674681141)
                  ·
                    refine ⟨5454076492391114875751357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58176815918838558674681141 5454076492391114875751357)
                    ·
                      refine ⟨2045278684646668078406759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454076492391114875751357 2045278684646668078406759)
                      ·
                        rfl

theorem cell23_3983166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3983166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983166 prefixEnd_3983166 := by exact prefixLift 3983166
  have htrace : WordTrace (prefixWord ++ tailWord_3983166) baseStart_3983166 baseEnd_3983166 := by
    simpa [prefixWord, tailWord_3983166, baseEnd_3983166] using wordTrace_append hprefix tailTrace_3983166
  have hstable : (prefixWord ++ tailWord_3983166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983166).length < 2 ^ (prefixWord ++ tailWord_3983166).sum := by decide
  have hdescent : baseEnd_3983166 < baseStart_3983166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983186 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3983186 : Nat := 118140960795 + 3983186 * 2 ^ 59
def prefixEnd_3983186 : Nat := 4983230072969 + 3 ^ 40 * 3983186 * 2
def baseEnd_3983186 : Nat := 681762984753252666718889

theorem tailTrace_3983186 : CollatzResearch.WordTrace tailWord_3983186 prefixEnd_3983186 681762984753252666718889 := by
  unfold tailWord_3983186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36319682136901217713632353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96852485698403247236352941 36319682136901217713632353)
  ·
    refine ⟨27239761602675913285224265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36319682136901217713632353 27239761602675913285224265)
    ·
      refine ⟨20429821202006934963918199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27239761602675913285224265 20429821202006934963918199)
      ·
        refine ⟨30644731803010402445877299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20429821202006934963918199 30644731803010402445877299)
        ·
          refine ⟨45967097704515603668815949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30644731803010402445877299 45967097704515603668815949)
          ·
            refine ⟨17237661639193351375805981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45967097704515603668815949 17237661639193351375805981)
            ·
              refine ⟨6464123114697506765927243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17237661639193351375805981 6464123114697506765927243)
              ·
                refine ⟨9696184672046260148890865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464123114697506765927243 9696184672046260148890865)
                ·
                  refine ⟨7272138504034695111668149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9696184672046260148890865 7272138504034695111668149)
                  ·
                    refine ⟨681762984753252666718889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7272138504034695111668149 681762984753252666718889)
                    ·
                      rfl

theorem cell23_3983186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3983186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983186 prefixEnd_3983186 := by exact prefixLift 3983186
  have htrace : WordTrace (prefixWord ++ tailWord_3983186) baseStart_3983186 baseEnd_3983186 := by
    simpa [prefixWord, tailWord_3983186, baseEnd_3983186] using wordTrace_append hprefix tailTrace_3983186
  have hstable : (prefixWord ++ tailWord_3983186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983186).length < 2 ^ (prefixWord ++ tailWord_3983186).sum := by decide
  have hdescent : baseEnd_3983186 < baseStart_3983186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983293 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3983293 : Nat := 118140960795 + 3983293 * 2 ^ 59
def prefixEnd_3983293 : Nat := 4983230072969 + 3 ^ 40 * 3983293 * 2
def baseEnd_3983293 : Nat := 681781298896596360506225

theorem tailTrace_3983293 : CollatzResearch.WordTrace tailWord_3983293 prefixEnd_3983293 681781298896596360506225 := by
  unfold tailWord_3983293
  simp only [CollatzResearch.WordTrace]
  refine ⟨145282631158217228128674533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96855087438811485419116355 145282631158217228128674533)
  ·
    refine ⟨27240493342165730274126475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145282631158217228128674533 27240493342165730274126475)
    ·
      refine ⟨40860740013248595411189713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27240493342165730274126475 40860740013248595411189713)
      ·
        refine ⟨30645555009936446558392285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40860740013248595411189713 30645555009936446558392285)
        ·
          refine ⟨11492083128726167459397107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30645555009936446558392285 11492083128726167459397107)
          ·
            refine ⟨17238124693089251189095661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492083128726167459397107 17238124693089251189095661)
            ·
              refine ⟨6464296759908469195910873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17238124693089251189095661 6464296759908469195910873)
              ·
                refine ⟨4848222569931351896933155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464296759908469195910873 4848222569931351896933155)
                ·
                  refine ⟨7272333854897027845399733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848222569931351896933155 7272333854897027845399733)
                  ·
                    refine ⟨681781298896596360506225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7272333854897027845399733 681781298896596360506225)
                    ·
                      rfl

theorem cell23_3983293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3983293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983293 prefixEnd_3983293 := by exact prefixLift 3983293
  have htrace : WordTrace (prefixWord ++ tailWord_3983293) baseStart_3983293 baseEnd_3983293 := by
    simpa [prefixWord, tailWord_3983293, baseEnd_3983293] using wordTrace_append hprefix tailTrace_3983293
  have hstable : (prefixWord ++ tailWord_3983293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983293).length < 2 ^ (prefixWord ++ tailWord_3983293).sum := by decide
  have hdescent : baseEnd_3983293 < baseStart_3983293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983296 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3983296 : Nat := 118140960795 + 3983296 * 2 ^ 59
def prefixEnd_3983296 : Nat := 4983230072969 + 3 ^ 40 * 3983296 * 2
def baseEnd_3983296 : Nat := 2045345437131752569781161

theorem tailTrace_3983296 : CollatzResearch.WordTrace tailWord_3983296 prefixEnd_3983296 2045345437131752569781161 := by
  unfold tailWord_3983296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72641370288603179820516871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96855160384804239760689161 72641370288603179820516871)
  ·
    refine ⟨108962055432904769730775307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72641370288603179820516871 108962055432904769730775307)
    ·
      refine ⟨163443083149357154596162961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108962055432904769730775307 163443083149357154596162961)
      ·
        refine ⟨122582312362017865947122221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163443083149357154596162961 122582312362017865947122221)
        ·
          refine ⟨45968367135756699730170833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122582312362017865947122221 45968367135756699730170833)
          ·
            refine ⟨34476275351817524797628125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45968367135756699730170833 34476275351817524797628125)
            ·
              refine ⟨12928603256931571799110547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34476275351817524797628125 12928603256931571799110547)
              ·
                refine ⟨19392904885397357698665821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12928603256931571799110547 19392904885397357698665821)
                ·
                  refine ⟨7272339332024009136999683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19392904885397357698665821 7272339332024009136999683)
                  ·
                    refine ⟨10908508998036013705499525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7272339332024009136999683 10908508998036013705499525)
                    ·
                      refine ⟨2045345437131752569781161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10908508998036013705499525 2045345437131752569781161)
                      ·
                        rfl

theorem cell23_3983296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3983296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983296 prefixEnd_3983296 := by exact prefixLift 3983296
  have htrace : WordTrace (prefixWord ++ tailWord_3983296) baseStart_3983296 baseEnd_3983296 := by
    simpa [prefixWord, tailWord_3983296, baseEnd_3983296] using wordTrace_append hprefix tailTrace_3983296
  have hstable : (prefixWord ++ tailWord_3983296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983296).length < 2 ^ (prefixWord ++ tailWord_3983296).sum := by decide
  have hdescent : baseEnd_3983296 < baseStart_3983296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983306 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_3983306 : Nat := 118140960795 + 3983306 * 2 ^ 59
def prefixEnd_3983306 : Nat := 4983230072969 + 3 ^ 40 * 3983306 * 2
def baseEnd_3983306 : Nat := 681783523979432510218705

theorem tailTrace_3983306 : CollatzResearch.WordTrace tailWord_3983306 prefixEnd_3983306 681783523979432510218705 := by
  unfold tailWord_3983306
  simp only [CollatzResearch.WordTrace]
  refine ⟨36320776326792532837224443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96855403538113420899265181 36320776326792532837224443)
  ·
    refine ⟨54481164490188799255836665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36320776326792532837224443 54481164490188799255836665)
    ·
      refine ⟨40860873367641599441877499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54481164490188799255836665 40860873367641599441877499)
      ·
        refine ⟨61291310051462399162816249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40860873367641599441877499 61291310051462399162816249)
        ·
          refine ⟨45968482538596799372112187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61291310051462399162816249 45968482538596799372112187)
          ·
            refine ⟨68952723807895199058168281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45968482538596799372112187 68952723807895199058168281)
            ·
              refine ⟨51714542855921399293626211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68952723807895199058168281 51714542855921399293626211)
              ·
                refine ⟨77571814283882098940439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51714542855921399293626211 77571814283882098940439317)
                ·
                  refine ⟨3636178794556973387833093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77571814283882098940439317 3636178794556973387833093)
                  ·
                    refine ⟨681783523979432510218705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636178794556973387833093 681783523979432510218705)
                    ·
                      rfl

theorem cell23_3983306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_3983306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983306 prefixEnd_3983306 := by exact prefixLift 3983306
  have htrace : WordTrace (prefixWord ++ tailWord_3983306) baseStart_3983306 baseEnd_3983306 := by
    simpa [prefixWord, tailWord_3983306, baseEnd_3983306] using wordTrace_append hprefix tailTrace_3983306
  have hstable : (prefixWord ++ tailWord_3983306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983306).length < 2 ^ (prefixWord ++ tailWord_3983306).sum := by decide
  have hdescent : baseEnd_3983306 < baseStart_3983306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983313 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_3983313 : Nat := 118140960795 + 3983313 * 2 ^ 59
def prefixEnd_3983313 : Nat := 4983230072969 + 3 ^ 40 * 3983313 * 2
def baseEnd_3983313 : Nat := 2045354166302879003268583

theorem tailTrace_3983313 : CollatzResearch.WordTrace tailWord_3983313 prefixEnd_3983313 2045354166302879003268583 := by
  unfold tailWord_3983313
  simp only [CollatzResearch.WordTrace]
  refine ⟨145283360618144771544402593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96855573745429847696268395 145283360618144771544402593)
  ·
    refine ⟨108962520463608578658301945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145283360618144771544402593 108962520463608578658301945)
    ·
      refine ⟨81721890347706433993726459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108962520463608578658301945 81721890347706433993726459)
      ·
        refine ⟨122582835521559650990589689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81721890347706433993726459 122582835521559650990589689)
        ·
          refine ⟨91937126641169738242942267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122582835521559650990589689 91937126641169738242942267)
          ·
            refine ⟨137905689961754607364413401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91937126641169738242942267 137905689961754607364413401)
            ·
              refine ⟨103429267471315955523310051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137905689961754607364413401 103429267471315955523310051)
              ·
                refine ⟨155143901206973933284965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103429267471315955523310051 155143901206973933284965077)
                ·
                  refine ⟨3636185184538451561366369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155143901206973933284965077 3636185184538451561366369)
                  ·
                    refine ⟨2727138888403838671024777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636185184538451561366369 2727138888403838671024777)
                    ·
                      refine ⟨2045354166302879003268583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727138888403838671024777 2045354166302879003268583)
                      ·
                        rfl

theorem cell23_3983313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_3983313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983313 prefixEnd_3983313 := by exact prefixLift 3983313
  have htrace : WordTrace (prefixWord ++ tailWord_3983313) baseStart_3983313 baseEnd_3983313 := by
    simpa [prefixWord, tailWord_3983313, baseEnd_3983313] using wordTrace_append hprefix tailTrace_3983313
  have hstable : (prefixWord ++ tailWord_3983313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983313).length < 2 ^ (prefixWord ++ tailWord_3983313).sum := by decide
  have hdescent : baseEnd_3983313 < baseStart_3983313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983339 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_3983339 : Nat := 118140960795 + 3983339 * 2 ^ 59
def prefixEnd_3983339 : Nat := 4983230072969 + 3 ^ 40 * 3983339 * 2
def baseEnd_3983339 : Nat := 2045367516799895901543463

theorem tailTrace_3983339 : CollatzResearch.WordTrace tailWord_3983339 prefixEnd_3983339 2045367516799895901543463 := by
  unfold tailWord_3983339
  simp only [CollatzResearch.WordTrace]
  refine ⟨145284308916050577984849071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96856205944033718656566047 145284308916050577984849071)
  ·
    refine ⟨217926463374075866977273607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145284308916050577984849071 217926463374075866977273607)
    ·
      refine ⟨326889695061113800465910411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217926463374075866977273607 326889695061113800465910411)
      ·
        refine ⟨490334542591670700698865617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326889695061113800465910411 490334542591670700698865617)
        ·
          refine ⟨367750906943753025524149213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490334542591670700698865617 367750906943753025524149213)
          ·
            refine ⟨137906590103907384571555955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367750906943753025524149213 137906590103907384571555955)
            ·
              refine ⟨206859885155861076857333933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137906590103907384571555955 206859885155861076857333933)
              ·
                refine ⟨77572456933447903821500225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206859885155861076857333933 77572456933447903821500225)
                ·
                  refine ⟨58179342700085927866125169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77572456933447903821500225 58179342700085927866125169)
                  ·
                    refine ⟨43634507025064445899593877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58179342700085927866125169 43634507025064445899593877)
                    ·
                      refine ⟨2045367516799895901543463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43634507025064445899593877 2045367516799895901543463)
                      ·
                        rfl

theorem cell23_3983339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_3983339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983339 prefixEnd_3983339 := by exact prefixLift 3983339
  have htrace : WordTrace (prefixWord ++ tailWord_3983339) baseStart_3983339 baseEnd_3983339 := by
    simpa [prefixWord, tailWord_3983339, baseEnd_3983339] using wordTrace_append hprefix tailTrace_3983339
  have hstable : (prefixWord ++ tailWord_3983339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983339).length < 2 ^ (prefixWord ++ tailWord_3983339).sum := by decide
  have hdescent : baseEnd_3983339 < baseStart_3983339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983364 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3983364 : Nat := 118140960795 + 3983364 * 2 ^ 59
def prefixEnd_3983364 : Nat := 4983230072969 + 3 ^ 40 * 3983364 * 2
def baseEnd_3983364 : Nat := 2045380353816258303730849

theorem tailTrace_3983364 : CollatzResearch.WordTrace tailWord_3983364 prefixEnd_3983364 2045380353816258303730849 := by
  unfold tailWord_3983364
  simp only [CollatzResearch.WordTrace]
  refine ⟨72642610370480003627254573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96856813827306671503006097 72642610370480003627254573)
  ·
    refine ⟨27240978888930001360220465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72642610370480003627254573 27240978888930001360220465)
    ·
      refine ⟨20430734166697501020165349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27240978888930001360220465 20430734166697501020165349)
      ·
        refine ⟨3830762656255781441281003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20430734166697501020165349 3830762656255781441281003)
        ·
          refine ⟨5746143984383672161921505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830762656255781441281003 5746143984383672161921505)
          ·
            refine ⟨4309607988287754121441129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5746143984383672161921505 4309607988287754121441129)
            ·
              refine ⟨3232205991215815591080847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309607988287754121441129 3232205991215815591080847)
              ·
                refine ⟨4848308986823723386621271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232205991215815591080847 4848308986823723386621271)
                ·
                  refine ⟨7272463480235585079931907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848308986823723386621271 7272463480235585079931907)
                  ·
                    refine ⟨10908695220353377619897861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7272463480235585079931907 10908695220353377619897861)
                    ·
                      refine ⟨2045380353816258303730849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10908695220353377619897861 2045380353816258303730849)
                      ·
                        rfl

theorem cell23_3983364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3983364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983364 prefixEnd_3983364 := by exact prefixLift 3983364
  have htrace : WordTrace (prefixWord ++ tailWord_3983364) baseStart_3983364 baseEnd_3983364 := by
    simpa [prefixWord, tailWord_3983364, baseEnd_3983364] using wordTrace_append hprefix tailTrace_3983364
  have hstable : (prefixWord ++ tailWord_3983364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983364).length < 2 ^ (prefixWord ++ tailWord_3983364).sum := by decide
  have hdescent : baseEnd_3983364 < baseStart_3983364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983367 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3983367 : Nat := 118140960795 + 3983367 * 2 ^ 59
def prefixEnd_3983367 : Nat := 4983230072969 + 3 ^ 40 * 3983367 * 2
def baseEnd_3983367 : Nat := 2045381894258221791993335

theorem tailTrace_3983367 : CollatzResearch.WordTrace tailWord_3983367 prefixEnd_3983367 2045381894258221791993335 := by
  unfold tailWord_3983367
  simp only [CollatzResearch.WordTrace]
  refine ⟨145285330159949138766868355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96856886773299425844578903 145285330159949138766868355)
  ·
    refine ⟨217927995239923708150302533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145285330159949138766868355 217927995239923708150302533)
    ·
      refine ⟨40861499107485695278181725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217927995239923708150302533 40861499107485695278181725)
      ·
        refine ⟨15323062165307135729318147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40861499107485695278181725 15323062165307135729318147)
        ·
          refine ⟨22984593247960703593977221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15323062165307135729318147 22984593247960703593977221)
          ·
            refine ⟨4309611233992631923870729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22984593247960703593977221 4309611233992631923870729)
            ·
              refine ⟨3232208425494473942903047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309611233992631923870729 3232208425494473942903047)
              ·
                refine ⟨4848312638241710914354571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232208425494473942903047 4848312638241710914354571)
                ·
                  refine ⟨7272468957362566371531857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848312638241710914354571 7272468957362566371531857)
                  ·
                    refine ⟨5454351718021924778648893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7272468957362566371531857 5454351718021924778648893)
                    ·
                      refine ⟨2045381894258221791993335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454351718021924778648893 2045381894258221791993335)
                      ·
                        rfl

theorem cell23_3983367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3983367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983367 prefixEnd_3983367 := by exact prefixLift 3983367
  have htrace : WordTrace (prefixWord ++ tailWord_3983367) baseStart_3983367 baseEnd_3983367 := by
    simpa [prefixWord, tailWord_3983367, baseEnd_3983367] using wordTrace_append hprefix tailTrace_3983367
  have hstable : (prefixWord ++ tailWord_3983367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983367).length < 2 ^ (prefixWord ++ tailWord_3983367).sum := by decide
  have hdescent : baseEnd_3983367 < baseStart_3983367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983397 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_3983397 : Nat := 118140960795 + 3983397 * 2 ^ 59
def prefixEnd_3983397 : Nat := 4983230072969 + 3 ^ 40 * 3983397 * 2
def baseEnd_3983397 : Nat := 2045397298677856674618197

theorem tailTrace_3983397 : CollatzResearch.WordTrace tailWord_3983397 prefixEnd_3983397 2045397298677856674618197 := by
  unfold tailWord_3983397
  simp only [CollatzResearch.WordTrace]
  refine ⟨145286424349840453890460445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96857616233226969260306963 145286424349840453890460445)
  ·
    refine ⟨54482409131190170208922667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145286424349840453890460445 54482409131190170208922667)
    ·
      refine ⟨81723613696785255313384001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54482409131190170208922667 81723613696785255313384001)
      ·
        refine ⟨61292710272588941485038001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81723613696785255313384001 61292710272588941485038001)
        ·
          refine ⟨45969532704441706113778501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61292710272588941485038001 45969532704441706113778501)
          ·
            refine ⟨8619287382082819896333469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45969532704441706113778501 8619287382082819896333469)
            ·
              refine ⟨3232232768281057461125051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8619287382082819896333469 3232232768281057461125051)
              ·
                refine ⟨4848349152421586191687577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232232768281057461125051 4848349152421586191687577)
                ·
                  refine ⟨3636261864316189643765683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848349152421586191687577 3636261864316189643765683)
                  ·
                    refine ⟨5454392796474284465648525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3636261864316189643765683 5454392796474284465648525)
                    ·
                      refine ⟨2045397298677856674618197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454392796474284465648525 2045397298677856674618197)
                      ·
                        rfl

theorem cell23_3983397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_3983397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983397 prefixEnd_3983397 := by exact prefixLift 3983397
  have htrace : WordTrace (prefixWord ++ tailWord_3983397) baseStart_3983397 baseEnd_3983397 := by
    simpa [prefixWord, tailWord_3983397, baseEnd_3983397] using wordTrace_append hprefix tailTrace_3983397
  have hstable : (prefixWord ++ tailWord_3983397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983397).length < 2 ^ (prefixWord ++ tailWord_3983397).sum := by decide
  have hdescent : baseEnd_3983397 < baseStart_3983397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983403 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 4, 2]
def baseStart_3983403 : Nat := 118140960795 + 3983403 * 2 ^ 59
def prefixEnd_3983403 : Nat := 4983230072969 + 3 ^ 40 * 3983403 * 2
def baseEnd_3983403 : Nat := 2045400379561783651143169

theorem tailTrace_3983403 : CollatzResearch.WordTrace tailWord_3983403 prefixEnd_3983403 2045400379561783651143169 := by
  unfold tailWord_3983403
  simp only [CollatzResearch.WordTrace]
  refine ⟨145286643187818716915178863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96857762125212477943452575 145286643187818716915178863)
  ·
    refine ⟨217929964781728075372768295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145286643187818716915178863 217929964781728075372768295)
    ·
      refine ⟨326894947172592113059152443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217929964781728075372768295 326894947172592113059152443)
      ·
        refine ⟨490342420758888169588728665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326894947172592113059152443 490342420758888169588728665)
        ·
          refine ⟨367756815569166127191546499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490342420758888169588728665 367756815569166127191546499)
          ·
            refine ⟨551635223353749190787319749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367756815569166127191546499 551635223353749190787319749)
            ·
              refine ⟨103431604378827973272622453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 551635223353749190787319749 103431604378827973272622453)
              ·
                refine ⟨9696712910515122494308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103431604378827973272622453 9696712910515122494308355)
                ·
                  refine ⟨14545069365772683741462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696712910515122494308355 14545069365772683741462533)
                  ·
                    refine ⟨2727200506082378201524225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14545069365772683741462533 2727200506082378201524225)
                    ·
                      refine ⟨2045400379561783651143169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727200506082378201524225 2045400379561783651143169)
                      ·
                        rfl

theorem cell23_3983403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4, 2].length) (baseStart_3983403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983403 prefixEnd_3983403 := by exact prefixLift 3983403
  have htrace : WordTrace (prefixWord ++ tailWord_3983403) baseStart_3983403 baseEnd_3983403 := by
    simpa [prefixWord, tailWord_3983403, baseEnd_3983403] using wordTrace_append hprefix tailTrace_3983403
  have hstable : (prefixWord ++ tailWord_3983403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983403).length < 2 ^ (prefixWord ++ tailWord_3983403).sum := by decide
  have hdescent : baseEnd_3983403 < baseStart_3983403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983420 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_3983420 : Nat := 118140960795 + 3983420 * 2 ^ 59
def prefixEnd_3983420 : Nat := 4983230072969 + 3 ^ 40 * 3983420 * 2
def baseEnd_3983420 : Nat := 2045409108732910084630591

theorem tailTrace_3983420 : CollatzResearch.WordTrace tailWord_3983420 prefixEnd_3983420 2045409108732910084630591 := by
  unfold tailWord_3983420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72643631614378564409273857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96858175485838085879031809 72643631614378564409273857)
  ·
    refine ⟨54482723710783923306955393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72643631614378564409273857 54482723710783923306955393)
    ·
      refine ⟨40862042783087942480216545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54482723710783923306955393 40862042783087942480216545)
      ·
        refine ⟨30646532087315956860162409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40862042783087942480216545 30646532087315956860162409)
        ·
          refine ⟨22984899065486967645121807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30646532087315956860162409 22984899065486967645121807)
          ·
            refine ⟨34477348598230451467682711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22984899065486967645121807 34477348598230451467682711)
            ·
              refine ⟨51716022897345677201524067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34477348598230451467682711 51716022897345677201524067)
              ·
                refine ⟨77574034346018515802286101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51716022897345677201524067 77574034346018515802286101)
                ·
                  refine ⟨3636282859969617928232161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77574034346018515802286101 3636282859969617928232161)
                  ·
                    refine ⟨2727212144977213446174121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636282859969617928232161 2727212144977213446174121)
                    ·
                      refine ⟨2045409108732910084630591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727212144977213446174121 2045409108732910084630591)
                      ·
                        rfl

theorem cell23_3983420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_3983420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983420 prefixEnd_3983420 := by exact prefixLift 3983420
  have htrace : WordTrace (prefixWord ++ tailWord_3983420) baseStart_3983420 baseEnd_3983420 := by
    simpa [prefixWord, tailWord_3983420, baseEnd_3983420] using wordTrace_append hprefix tailTrace_3983420
  have hstable : (prefixWord ++ tailWord_3983420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983420).length < 2 ^ (prefixWord ++ tailWord_3983420).sum := by decide
  have hdescent : baseEnd_3983420 < baseStart_3983420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983437 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3983437 : Nat := 118140960795 + 3983437 * 2 ^ 59
def prefixEnd_3983437 : Nat := 4983230072969 + 3 ^ 40 * 3983437 * 2
def baseEnd_3983437 : Nat := 2045417837904036518118013

theorem tailTrace_3983437 : CollatzResearch.WordTrace tailWord_3983437 prefixEnd_3983437 2045417837904036518118013 := by
  unfold tailWord_3983437
  simp only [CollatzResearch.WordTrace]
  refine ⟨145287883269695540721916565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96858588846463693814611043 145287883269695540721916565)
  ·
    refine ⟨6810369528266978471339839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145287883269695540721916565 6810369528266978471339839)
    ·
      refine ⟨10215554292400467707009759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810369528266978471339839 10215554292400467707009759)
      ·
        refine ⟨15323331438600701560514639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10215554292400467707009759 15323331438600701560514639)
        ·
          refine ⟨22984997157901052340771959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15323331438600701560514639 22984997157901052340771959)
          ·
            refine ⟨34477495736851578511157939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22984997157901052340771959 34477495736851578511157939)
            ·
              refine ⟨51716243605277367766736909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34477495736851578511157939 51716243605277367766736909)
              ·
                refine ⟨19393591351979012912526341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51716243605277367766736909 19393591351979012912526341)
                ·
                  refine ⟨3636298378496064921098689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19393591351979012912526341 3636298378496064921098689)
                  ·
                    refine ⟨2727223783872048690824017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636298378496064921098689 2727223783872048690824017)
                    ·
                      refine ⟨2045417837904036518118013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727223783872048690824017 2045417837904036518118013)
                      ·
                        rfl

theorem cell23_3983437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3983437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983437 prefixEnd_3983437 := by exact prefixLift 3983437
  have htrace : WordTrace (prefixWord ++ tailWord_3983437) baseStart_3983437 baseEnd_3983437 := by
    simpa [prefixWord, tailWord_3983437, baseEnd_3983437] using wordTrace_append hprefix tailTrace_3983437
  have hstable : (prefixWord ++ tailWord_3983437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983437).length < 2 ^ (prefixWord ++ tailWord_3983437).sum := by decide
  have hdescent : baseEnd_3983437 < baseStart_3983437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983473 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_3983473 : Nat := 118140960795 + 3983473 * 2 ^ 59
def prefixEnd_3983473 : Nat := 4983230072969 + 3 ^ 40 * 3983473 * 2
def baseEnd_3983473 : Nat := 681812107735866125755949

theorem tailTrace_3983473 : CollatzResearch.WordTrace tailWord_3983473 prefixEnd_3983473 681812107735866125755949 := by
  unfold tailWord_3983473
  simp only [CollatzResearch.WordTrace]
  refine ⟨145289196297565118870227073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96859464198376745913484715 145289196297565118870227073)
  ·
    refine ⟨108966897223173839152670305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145289196297565118870227073 108966897223173839152670305)
    ·
      refine ⟨81725172917380379364502729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108966897223173839152670305 81725172917380379364502729)
      ·
        refine ⟨61293879688035284523377047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81725172917380379364502729 61293879688035284523377047)
        ·
          refine ⟨91940819532052926785065571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61293879688035284523377047 91940819532052926785065571)
          ·
            refine ⟨137911229298079390177598357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91940819532052926785065571 137911229298079390177598357)
            ·
              refine ⟨6464588873347471414574923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137911229298079390177598357 6464588873347471414574923)
              ·
                refine ⟨9696883310021207121862385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464588873347471414574923 9696883310021207121862385)
                ·
                  refine ⟨7272662482515905341396789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9696883310021207121862385 7272662482515905341396789)
                  ·
                    refine ⟨681812107735866125755949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7272662482515905341396789 681812107735866125755949)
                    ·
                      rfl

theorem cell23_3983473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_3983473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983473 prefixEnd_3983473 := by exact prefixLift 3983473
  have htrace : WordTrace (prefixWord ++ tailWord_3983473) baseStart_3983473 baseEnd_3983473 := by
    simpa [prefixWord, tailWord_3983473, baseEnd_3983473] using wordTrace_append hprefix tailTrace_3983473
  have hstable : (prefixWord ++ tailWord_3983473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983473).length < 2 ^ (prefixWord ++ tailWord_3983473).sum := by decide
  have hdescent : baseEnd_3983473 < baseStart_3983473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983513 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_3983513 : Nat := 118140960795 + 3983513 * 2 ^ 59
def prefixEnd_3983513 : Nat := 4983230072969 + 3 ^ 40 * 3983513 * 2
def baseEnd_3983513 : Nat := 2045456862433778220767663

theorem tailTrace_3983513 : CollatzResearch.WordTrace tailWord_3983513 prefixEnd_3983513 2045456862433778220767663 := by
  unfold tailWord_3983513
  simp only [CollatzResearch.WordTrace]
  refine ⟨145290655217420205701683193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96860436811613470467788795 145290655217420205701683193)
  ·
    refine ⟨108967991413065154276262395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145290655217420205701683193 108967991413065154276262395)
    ·
      refine ⟨163451987119597731414393593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108967991413065154276262395 163451987119597731414393593)
      ·
        refine ⟨122588990339698298560795195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163451987119597731414393593 122588990339698298560795195)
        ·
          refine ⟨183883485509547447841192793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122588990339698298560795195 183883485509547447841192793)
          ·
            refine ⟨137912614132160585880894595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183883485509547447841192793 137912614132160585880894595)
            ·
              refine ⟨206868921198240878821341893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137912614132160585880894595 206868921198240878821341893)
              ·
                refine ⟨38787922724670164779001605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206868921198240878821341893 38787922724670164779001605)
                ·
                  refine ⟨7272735510875655896062801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38787922724670164779001605 7272735510875655896062801)
                  ·
                    refine ⟨5454551633156741922047101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7272735510875655896062801 5454551633156741922047101)
                    ·
                      refine ⟨2045456862433778220767663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454551633156741922047101 2045456862433778220767663)
                      ·
                        rfl

theorem cell23_3983513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_3983513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983513 prefixEnd_3983513 := by exact prefixLift 3983513
  have htrace : WordTrace (prefixWord ++ tailWord_3983513) baseStart_3983513 baseEnd_3983513 := by
    simpa [prefixWord, tailWord_3983513, baseEnd_3983513] using wordTrace_append hprefix tailTrace_3983513
  have hstable : (prefixWord ++ tailWord_3983513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983513).length < 2 ^ (prefixWord ++ tailWord_3983513).sum := by decide
  have hdescent : baseEnd_3983513 < baseStart_3983513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983520 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_3983520 : Nat := 118140960795 + 3983520 * 2 ^ 59
def prefixEnd_3983520 : Nat := 4983230072969 + 3 ^ 40 * 3983520 * 2
def baseEnd_3983520 : Nat := 681820152266119897793377

theorem tailTrace_3983520 : CollatzResearch.WordTrace tailWord_3983520 prefixEnd_3983520 681820152266119897793377 := by
  unfold tailWord_3983520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72645455264197422948594007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96860607018929897264792009 72645455264197422948594007)
  ·
    refine ⟨108968182896296134422891011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72645455264197422948594007 108968182896296134422891011)
    ·
      refine ⟨163452274344444201634336517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108968182896296134422891011 163452274344444201634336517)
      ·
        refine ⟨30647301439583287806438097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163452274344444201634336517 30647301439583287806438097)
        ·
          refine ⟨22985476079687465854828573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30647301439583287806438097 22985476079687465854828573)
          ·
            refine ⟨8619553529882799695560715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22985476079687465854828573 8619553529882799695560715)
            ·
              refine ⟨12929330294824199543341073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619553529882799695560715 12929330294824199543341073)
              ·
                refine ⟨9696997721118149657505805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12929330294824199543341073 9696997721118149657505805)
                ·
                  refine ⟨3636374145419306121564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9696997721118149657505805 3636374145419306121564677)
                  ·
                    refine ⟨681820152266119897793377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636374145419306121564677 681820152266119897793377)
                    ·
                      rfl

theorem cell23_3983520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_3983520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983520 prefixEnd_3983520 := by exact prefixLift 3983520
  have htrace : WordTrace (prefixWord ++ tailWord_3983520) baseStart_3983520 baseEnd_3983520 := by
    simpa [prefixWord, tailWord_3983520, baseEnd_3983520] using wordTrace_append hprefix tailTrace_3983520
  have hstable : (prefixWord ++ tailWord_3983520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983520).length < 2 ^ (prefixWord ++ tailWord_3983520).sum := by decide
  have hdescent : baseEnd_3983520 < baseStart_3983520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983536 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_3983536 : Nat := 118140960795 + 3983536 * 2 ^ 59
def prefixEnd_3983536 : Nat := 4983230072969 + 3 ^ 40 * 3983536 * 2
def baseEnd_3983536 : Nat := 2045468672488831630780057

theorem tailTrace_3983536 : CollatzResearch.WordTrace tailWord_3983536 prefixEnd_3983536 2045468672488831630780057 := by
  unfold tailWord_3983536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72645747048168440314885231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96860996064224587086513641 72645747048168440314885231)
  ·
    refine ⟨108968620572252660472327847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72645747048168440314885231 108968620572252660472327847)
    ·
      refine ⟨163452930858378990708491771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108968620572252660472327847 163452930858378990708491771)
      ·
        refine ⟨245179396287568486062737657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163452930858378990708491771 245179396287568486062737657)
        ·
          refine ⟨183884547215676364547053243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245179396287568486062737657 183884547215676364547053243)
          ·
            refine ⟨275826820823514546820579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183884547215676364547053243 275826820823514546820579865)
            ·
              refine ⟨206870115617635910115434899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275826820823514546820579865 206870115617635910115434899)
              ·
                refine ⟨310305173426453865173152349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206870115617635910115434899 310305173426453865173152349)
                ·
                  refine ⟨116364440034920199439932131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310305173426453865173152349 116364440034920199439932131)
                  ·
                    refine ⟨174546660052380299159898197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116364440034920199439932131 174546660052380299159898197)
                    ·
                      refine ⟨2045468672488831630780057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174546660052380299159898197 2045468672488831630780057)
                      ·
                        rfl

theorem cell23_3983536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_3983536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983536 prefixEnd_3983536 := by exact prefixLift 3983536
  have htrace : WordTrace (prefixWord ++ tailWord_3983536) baseStart_3983536 baseEnd_3983536 := by
    simpa [prefixWord, tailWord_3983536, baseEnd_3983536] using wordTrace_append hprefix tailTrace_3983536
  have hstable : (prefixWord ++ tailWord_3983536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983536).length < 2 ^ (prefixWord ++ tailWord_3983536).sum := by decide
  have hdescent : baseEnd_3983536 < baseStart_3983536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983550 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3983550 : Nat := 118140960795 + 3983550 * 2 ^ 59
def prefixEnd_3983550 : Nat := 4983230072969 + 3 ^ 40 * 3983550 * 2
def baseEnd_3983550 : Nat := 227275095690888286222777

theorem tailTrace_3983550 : CollatzResearch.WordTrace tailWord_3983550 prefixEnd_3983550 227275095690888286222777 := by
  unfold tailWord_3983550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161500589785770127597513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96861336478857440680520069 18161500589785770127597513)
  ·
    refine ⟨13621125442339327595698135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18161500589785770127597513 13621125442339327595698135)
    ·
      refine ⟨20431688163508991393547203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13621125442339327595698135 20431688163508991393547203)
      ·
        refine ⟨30647532245263487090320805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20431688163508991393547203 30647532245263487090320805)
        ·
          refine ⟨5746412295986903829435151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30647532245263487090320805 5746412295986903829435151)
          ·
            refine ⟨8619618443980355744152727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746412295986903829435151 8619618443980355744152727)
            ·
              refine ⟨12929427665970533616229091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619618443980355744152727 12929427665970533616229091)
              ·
                refine ⟨19394141498955800424343637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929427665970533616229091 19394141498955800424343637)
                ·
                  refine ⟨227275095690888286222777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19394141498955800424343637 227275095690888286222777)
                  ·
                    rfl

theorem cell23_3983550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3983550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983550 prefixEnd_3983550 := by exact prefixLift 3983550
  have htrace : WordTrace (prefixWord ++ tailWord_3983550) baseStart_3983550 baseEnd_3983550 := by
    simpa [prefixWord, tailWord_3983550, baseEnd_3983550] using wordTrace_append hprefix tailTrace_3983550
  have hstable : (prefixWord ++ tailWord_3983550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983550).length < 2 ^ (prefixWord ++ tailWord_3983550).sum := by decide
  have hdescent : baseEnd_3983550 < baseStart_3983550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983554 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3983554 : Nat := 118140960795 + 3983554 * 2 ^ 59
def prefixEnd_3983554 : Nat := 4983230072969 + 3 ^ 40 * 3983554 * 2
def baseEnd_3983554 : Nat := 681825971713537520118325

theorem tailTrace_3983554 : CollatzResearch.WordTrace tailWord_3983554 prefixEnd_3983554 681825971713537520118325 := by
  unfold tailWord_3983554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323037652567917425981429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96861433740181113135950477 36323037652567917425981429)
  ·
    refine ⟨3405284779928242258685759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36323037652567917425981429 3405284779928242258685759)
    ·
      refine ⟨5107927169892363388028639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405284779928242258685759 5107927169892363388028639)
      ·
        refine ⟨7661890754838545082042959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107927169892363388028639 7661890754838545082042959)
        ·
          refine ⟨11492836132257817623064439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661890754838545082042959 11492836132257817623064439)
          ·
            refine ⟨17239254198386726434596659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492836132257817623064439 17239254198386726434596659)
            ·
              refine ⟨25858881297580089651894989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17239254198386726434596659 25858881297580089651894989)
              ·
                refine ⟨9697080486592533619460621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25858881297580089651894989 9697080486592533619460621)
                ·
                  refine ⟨3636405182472200107297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9697080486592533619460621 3636405182472200107297733)
                  ·
                    refine ⟨681825971713537520118325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636405182472200107297733 681825971713537520118325)
                    ·
                      rfl

theorem cell23_3983554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3983554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983554 prefixEnd_3983554 := by exact prefixLift 3983554
  have htrace : WordTrace (prefixWord ++ tailWord_3983554) baseStart_3983554 baseEnd_3983554 := by
    simpa [prefixWord, tailWord_3983554, baseEnd_3983554] using wordTrace_append hprefix tailTrace_3983554
  have hstable : (prefixWord ++ tailWord_3983554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983554).length < 2 ^ (prefixWord ++ tailWord_3983554).sum := by decide
  have hdescent : baseEnd_3983554 < baseStart_3983554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983610 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_3983610 : Nat := 118140960795 + 3983610 * 2 ^ 59
def prefixEnd_3983610 : Nat := 4983230072969 + 3 ^ 40 * 3983610 * 2
def baseEnd_3983610 : Nat := 681835556685754780418239

theorem tailTrace_3983610 : CollatzResearch.WordTrace tailWord_3983610 prefixEnd_3983610 681835556685754780418239 := by
  unfold tailWord_3983610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323548274517197816991071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96862795398712527511976189 36323548274517197816991071)
  ·
    refine ⟨54485322411775796725486607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36323548274517197816991071 54485322411775796725486607)
    ·
      refine ⟨81727983617663695088229911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54485322411775796725486607 81727983617663695088229911)
      ·
        refine ⟨122591975426495542632344867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81727983617663695088229911 122591975426495542632344867)
        ·
          refine ⟨183887963139743313948517301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122591975426495542632344867 183887963139743313948517301)
          ·
            refine ⟨17239496544350935682673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183887963139743313948517301 17239496544350935682673497)
            ·
              refine ⟨12929622408263201762005123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17239496544350935682673497 12929622408263201762005123)
              ·
                refine ⟨19394433612394802643007685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929622408263201762005123 19394433612394802643007685)
                ·
                  refine ⟨3636456302324025495563941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19394433612394802643007685 3636456302324025495563941)
                  ·
                    refine ⟨681835556685754780418239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636456302324025495563941 681835556685754780418239)
                    ·
                      rfl

theorem cell23_3983610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_3983610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983610 prefixEnd_3983610 := by exact prefixLift 3983610
  have htrace : WordTrace (prefixWord ++ tailWord_3983610) baseStart_3983610 baseEnd_3983610 := by
    simpa [prefixWord, tailWord_3983610, baseEnd_3983610] using wordTrace_append hprefix tailTrace_3983610
  have hstable : (prefixWord ++ tailWord_3983610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983610).length < 2 ^ (prefixWord ++ tailWord_3983610).sum := by decide
  have hdescent : baseEnd_3983610 < baseStart_3983610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983630 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3983630 : Nat := 118140960795 + 3983630 * 2 ^ 59
def prefixEnd_3983630 : Nat := 4983230072969 + 3 ^ 40 * 3983630 * 2
def baseEnd_3983630 : Nat := 2045516939670354263004625

theorem tailTrace_3983630 : CollatzResearch.WordTrace tailWord_3983630 prefixEnd_3983630 2045516939670354263004625 := by
  unfold tailWord_3983630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161865319749541835461543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96863281705330889789128229 18161865319749541835461543)
  ·
    refine ⟨27242797979624312753192315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18161865319749541835461543 27242797979624312753192315)
    ·
      refine ⟨40864196969436469129788473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27242797979624312753192315 40864196969436469129788473)
      ·
        refine ⟨30648147727077351847341355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40864196969436469129788473 30648147727077351847341355)
        ·
          refine ⟨45972221590616027771012033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30648147727077351847341355 45972221590616027771012033)
          ·
            refine ⟨34479166192962020828259025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45972221590616027771012033 34479166192962020828259025)
            ·
              refine ⟨25859374644721515621194269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34479166192962020828259025 25859374644721515621194269)
              ·
                refine ⟨9697265491770568357947851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25859374644721515621194269 9697265491770568357947851)
                ·
                  refine ⟨14545898237655852536921777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697265491770568357947851 14545898237655852536921777)
                  ·
                    refine ⟨10909423678241889402691333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14545898237655852536921777 10909423678241889402691333)
                    ·
                      refine ⟨2045516939670354263004625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10909423678241889402691333 2045516939670354263004625)
                      ·
                        rfl

theorem cell23_3983630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3983630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983630 prefixEnd_3983630 := by exact prefixLift 3983630
  have htrace : WordTrace (prefixWord ++ tailWord_3983630) baseStart_3983630 baseEnd_3983630 := by
    simpa [prefixWord, tailWord_3983630, baseEnd_3983630] using wordTrace_append hprefix tailTrace_3983630
  have hstable : (prefixWord ++ tailWord_3983630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983630).length < 2 ^ (prefixWord ++ tailWord_3983630).sum := by decide
  have hdescent : baseEnd_3983630 < baseStart_3983630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983637 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3983637 : Nat := 118140960795 + 3983637 * 2 ^ 59
def prefixEnd_3983637 : Nat := 4983230072969 + 3 ^ 40 * 3983637 * 2
def baseEnd_3983637 : Nat := 2045520534034935735617093

theorem tailTrace_3983637 : CollatzResearch.WordTrace tailWord_3983637 prefixEnd_3983637 2045520534034935735617093 := by
  unfold tailWord_3983637
  simp only [CollatzResearch.WordTrace]
  refine ⟨145295177868970974879197165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96863451912647316586131443 145295177868970974879197165)
  ·
    refine ⟨54485691700864115579698937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145295177868970974879197165 54485691700864115579698937)
    ·
      refine ⟨40864268775648086684774203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54485691700864115579698937 40864268775648086684774203)
      ·
        refine ⟨61296403163472130027161305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40864268775648086684774203 61296403163472130027161305)
        ·
          refine ⟨45972302372604097520370979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61296403163472130027161305 45972302372604097520370979)
          ·
            refine ⟨68958453558906146280556469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45972302372604097520370979 68958453558906146280556469)
            ·
              refine ⟨6464855021147451213802169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68958453558906146280556469 6464855021147451213802169)
              ·
                refine ⟨4848641265860588410351627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464855021147451213802169 4848641265860588410351627)
                ·
                  refine ⟨7272961898790882615527441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848641265860588410351627 7272961898790882615527441)
                  ·
                    refine ⟨5454721424093161961645581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7272961898790882615527441 5454721424093161961645581)
                    ·
                      refine ⟨2045520534034935735617093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454721424093161961645581 2045520534034935735617093)
                      ·
                        rfl

theorem cell23_3983637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3983637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983637 prefixEnd_3983637 := by exact prefixLift 3983637
  have htrace : WordTrace (prefixWord ++ tailWord_3983637) baseStart_3983637 baseEnd_3983637 := by
    simpa [prefixWord, tailWord_3983637, baseEnd_3983637] using wordTrace_append hprefix tailTrace_3983637
  have hstable : (prefixWord ++ tailWord_3983637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983637).length < 2 ^ (prefixWord ++ tailWord_3983637).sum := by decide
  have hdescent : baseEnd_3983637 < baseStart_3983637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983661 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3983661 : Nat := 118140960795 + 3983661 * 2 ^ 59
def prefixEnd_3983661 : Nat := 4983230072969 + 3 ^ 40 * 3983661 * 2
def baseEnd_3983661 : Nat := 681844285856881213905661

theorem tailTrace_3983661 : CollatzResearch.WordTrace tailWord_3983661 prefixEnd_3983661 681844285856881213905661 := by
  unfold tailWord_3983661
  simp only [CollatzResearch.WordTrace]
  refine ⟨145296053220884026978070837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96864035480589351318713891 145296053220884026978070837)
  ·
    refine ⟨13621504989457877529194141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145296053220884026978070837 13621504989457877529194141)
    ·
      refine ⟨5108064371046704073447803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13621504989457877529194141 5108064371046704073447803)
      ·
        refine ⟨7662096556570056110171705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108064371046704073447803 7662096556570056110171705)
        ·
          refine ⟨5746572417427542082628779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7662096556570056110171705 5746572417427542082628779)
          ·
            refine ⟨8619858626141313123943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746572417427542082628779 8619858626141313123943169)
            ·
              refine ⟨6464893969605984842957377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8619858626141313123943169 6464893969605984842957377)
              ·
                refine ⟨4848670477204488632218033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464893969605984842957377 4848670477204488632218033)
                ·
                  refine ⟨3636502857903366474163525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4848670477204488632218033 3636502857903366474163525)
                  ·
                    refine ⟨681844285856881213905661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636502857903366474163525 681844285856881213905661)
                    ·
                      rfl

theorem cell23_3983661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3983661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983661 prefixEnd_3983661 := by exact prefixLift 3983661
  have htrace : WordTrace (prefixWord ++ tailWord_3983661) baseStart_3983661 baseEnd_3983661 := by
    simpa [prefixWord, tailWord_3983661, baseEnd_3983661] using wordTrace_append hprefix tailTrace_3983661
  have hstable : (prefixWord ++ tailWord_3983661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983661).length < 2 ^ (prefixWord ++ tailWord_3983661).sum := by decide
  have hdescent : baseEnd_3983661 < baseStart_3983661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983662 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3983662 : Nat := 118140960795 + 3983662 * 2 ^ 59
def prefixEnd_3983662 : Nat := 4983230072969 + 3 ^ 40 * 3983662 * 2
def baseEnd_3983662 : Nat := 2045533371051298137804479

theorem tailTrace_3983662 : CollatzResearch.WordTrace tailWord_3983662 prefixEnd_3983662 2045533371051298137804479 := by
  unfold tailWord_3983662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162011211735050518607155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96864059795920269432571493 18162011211735050518607155)
  ·
    refine ⟨27243016817602575777910733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162011211735050518607155 27243016817602575777910733)
    ·
      refine ⟨10216131306600965916716525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27243016817602575777910733 10216131306600965916716525)
      ·
        refine ⟨3831049239975362218768697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10216131306600965916716525 3831049239975362218768697)
        ·
          refine ⟨2873286929981521664076523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831049239975362218768697 2873286929981521664076523)
          ·
            refine ⟨4309930394972282496114785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873286929981521664076523 4309930394972282496114785)
            ·
              refine ⟨3232447796229211872086089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309930394972282496114785 3232447796229211872086089)
              ·
                refine ⟨2424335847171908904064567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3232447796229211872086089 2424335847171908904064567)
                ·
                  refine ⟨3636503770757863356096851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424335847171908904064567 3636503770757863356096851)
                  ·
                    refine ⟨5454755656136795034145277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3636503770757863356096851 5454755656136795034145277)
                    ·
                      refine ⟨2045533371051298137804479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454755656136795034145277 2045533371051298137804479)
                      ·
                        rfl

theorem cell23_3983662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3983662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983662 prefixEnd_3983662 := by exact prefixLift 3983662
  have htrace : WordTrace (prefixWord ++ tailWord_3983662) baseStart_3983662 baseEnd_3983662 := by
    simpa [prefixWord, tailWord_3983662, baseEnd_3983662] using wordTrace_append hprefix tailTrace_3983662
  have hstable : (prefixWord ++ tailWord_3983662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983662).length < 2 ^ (prefixWord ++ tailWord_3983662).sum := by decide
  have hdescent : baseEnd_3983662 < baseStart_3983662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983663 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_3983663 : Nat := 118140960795 + 3983663 * 2 ^ 59
def prefixEnd_3983663 : Nat := 4983230072969 + 3 ^ 40 * 3983663 * 2
def baseEnd_3983663 : Nat := 2045533884531952633891973

theorem tailTrace_3983663 : CollatzResearch.WordTrace tailWord_3983663 prefixEnd_3983663 2045533884531952633891973 := by
  unfold tailWord_3983663
  simp only [CollatzResearch.WordTrace]
  refine ⟨145296126166876781319643643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96864084111251187546429095 145296126166876781319643643)
  ·
    refine ⟨217944189250315171979465465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145296126166876781319643643 217944189250315171979465465)
    ·
      refine ⟨163458141937736378984599099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217944189250315171979465465 163458141937736378984599099)
      ·
        refine ⟨245187212906604568476898649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163458141937736378984599099 245187212906604568476898649)
        ·
          refine ⟨183890409679953426357673987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245187212906604568476898649 183890409679953426357673987)
          ·
            refine ⟨275835614519930139536510981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183890409679953426357673987 275835614519930139536510981)
            ·
              refine ⟨51719177722486901163095809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275835614519930139536510981 51719177722486901163095809)
              ·
                refine ⟨38789383291865175872321857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51719177722486901163095809 38789383291865175872321857)
                ·
                  refine ⟨29092037468898881904241393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38789383291865175872321857 29092037468898881904241393)
                  ·
                    refine ⟨21819028101674161428181045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29092037468898881904241393 21819028101674161428181045)
                    ·
                      refine ⟨2045533884531952633891973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21819028101674161428181045 2045533884531952633891973)
                      ·
                        rfl

theorem cell23_3983663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_3983663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983663 prefixEnd_3983663 := by exact prefixLift 3983663
  have htrace : WordTrace (prefixWord ++ tailWord_3983663) baseStart_3983663 baseEnd_3983663 := by
    simpa [prefixWord, tailWord_3983663, baseEnd_3983663] using wordTrace_append hprefix tailTrace_3983663
  have hstable : (prefixWord ++ tailWord_3983663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983663).length < 2 ^ (prefixWord ++ tailWord_3983663).sum := by decide
  have hdescent : baseEnd_3983663 < baseStart_3983663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983668 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_3983668 : Nat := 118140960795 + 3983668 * 2 ^ 59
def prefixEnd_3983668 : Nat := 4983230072969 + 3 ^ 40 * 3983668 * 2
def baseEnd_3983668 : Nat := 2045536451935225114329451

theorem tailTrace_3983668 : CollatzResearch.WordTrace tailWord_3983668 prefixEnd_3983668 2045536451935225114329451 := by
  unfold tailWord_3983668
  simp only [CollatzResearch.WordTrace]
  refine ⟨72648154265929333586787829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96864205687905778115717105 72648154265929333586787829)
  ·
    refine ⟨6810764462430875023761359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72648154265929333586787829 6810764462430875023761359)
    ·
      refine ⟨10216146693646312535642039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810764462430875023761359 10216146693646312535642039)
      ·
        refine ⟨15324220040469468803463059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216146693646312535642039 15324220040469468803463059)
        ·
          refine ⟨22986330060704203205194589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15324220040469468803463059 22986330060704203205194589)
          ·
            refine ⟨8619873772764076201947971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22986330060704203205194589 8619873772764076201947971)
            ·
              refine ⟨12929810659146114302921957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619873772764076201947971 12929810659146114302921957)
              ·
                refine ⟨2424339498589896431797867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12929810659146114302921957 2424339498589896431797867)
                ·
                  refine ⟨3636509247884844647696801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424339498589896431797867 3636509247884844647696801)
                  ·
                    refine ⟨2727381935913633485772601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636509247884844647696801 2727381935913633485772601)
                    ·
                      refine ⟨2045536451935225114329451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727381935913633485772601 2045536451935225114329451)
                      ·
                        rfl

theorem cell23_3983668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_3983668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983668 prefixEnd_3983668 := by exact prefixLift 3983668
  have htrace : WordTrace (prefixWord ++ tailWord_3983668) baseStart_3983668 baseEnd_3983668 := by
    simpa [prefixWord, tailWord_3983668, baseEnd_3983668] using wordTrace_append hprefix tailTrace_3983668
  have hstable : (prefixWord ++ tailWord_3983668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983668).length < 2 ^ (prefixWord ++ tailWord_3983668).sum := by decide
  have hdescent : baseEnd_3983668 < baseStart_3983668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983683 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 8]
def baseStart_3983683 : Nat := 118140960795 + 3983683 * 2 ^ 59
def prefixEnd_3983683 : Nat := 4983230072969 + 3 ^ 40 * 3983683 * 2
def baseEnd_3983683 : Nat := 681848051381680851880627

theorem tailTrace_3983683 : CollatzResearch.WordTrace tailWord_3983683 prefixEnd_3983683 681848051381680851880627 := by
  unfold tailWord_3983683
  simp only [CollatzResearch.WordTrace]
  refine ⟨145296855626804324735371703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96864570417869549823581135 145296855626804324735371703)
  ·
    refine ⟨217945283440206487103057555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145296855626804324735371703 217945283440206487103057555)
    ·
      refine ⟨326917925160309730654586333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217945283440206487103057555 326917925160309730654586333)
      ·
        refine ⟨122594221935116148995469875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326917925160309730654586333 122594221935116148995469875)
        ·
          refine ⟨183891332902674223493204813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122594221935116148995469875 183891332902674223493204813)
          ·
            refine ⟨68959249838502833809951805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183891332902674223493204813 68959249838502833809951805)
            ·
              refine ⟨25859718689438562678731927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68959249838502833809951805 25859718689438562678731927)
              ·
                refine ⟨38789578034157844018097891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25859718689438562678731927 38789578034157844018097891)
                ·
                  refine ⟨58184367051236766027146837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38789578034157844018097891 58184367051236766027146837)
                  ·
                    refine ⟨681848051381680851880627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58184367051236766027146837 681848051381680851880627)
                    ·
                      rfl

theorem cell23_3983683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_3983683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983683 prefixEnd_3983683 := by exact prefixLift 3983683
  have htrace : WordTrace (prefixWord ++ tailWord_3983683) baseStart_3983683 baseEnd_3983683 := by
    simpa [prefixWord, tailWord_3983683, baseEnd_3983683] using wordTrace_append hprefix tailTrace_3983683
  have hstable : (prefixWord ++ tailWord_3983683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983683).length < 2 ^ (prefixWord ++ tailWord_3983683).sum := by decide
  have hdescent : baseEnd_3983683 < baseStart_3983683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_3983723 : Nat := 118140960795 + 3983723 * 2 ^ 59
def prefixEnd_3983723 : Nat := 4983230072969 + 3 ^ 40 * 3983723 * 2
def baseEnd_3983723 : Nat := 2045564693371222399141697

theorem tailTrace_3983723 : CollatzResearch.WordTrace tailWord_3983723 prefixEnd_3983723 2045564693371222399141697 := by
  unfold tailWord_3983723
  simp only [CollatzResearch.WordTrace]
  refine ⟨145298314546659411566827823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96865543031106274377885215 145298314546659411566827823)
  ·
    refine ⟨217947471819989117350241735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145298314546659411566827823 217947471819989117350241735)
    ·
      refine ⟨326921207729983676025362603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217947471819989117350241735 326921207729983676025362603)
      ·
        refine ⟨490381811594975514038043905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326921207729983676025362603 490381811594975514038043905)
        ·
          refine ⟨367786358696231635528532929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490381811594975514038043905 367786358696231635528532929)
          ·
            refine ⟨275839769022173726646399697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367786358696231635528532929 275839769022173726646399697)
            ·
              refine ⟨206879826766630294984799773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275839769022173726646399697 206879826766630294984799773)
              ·
                refine ⟨77579935037486360619299915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206879826766630294984799773 77579935037486360619299915)
                ·
                  refine ⟨116369902556229540928949873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77579935037486360619299915 116369902556229540928949873)
                  ·
                    refine ⟨87277426917172155696712405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116369902556229540928949873 87277426917172155696712405)
                    ·
                      refine ⟨2045564693371222399141697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87277426917172155696712405 2045564693371222399141697)
                      ·
                        rfl

theorem cell23_3983723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_3983723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983723 prefixEnd_3983723 := by exact prefixLift 3983723
  have htrace : WordTrace (prefixWord ++ tailWord_3983723) baseStart_3983723 baseEnd_3983723 := by
    simpa [prefixWord, tailWord_3983723, baseEnd_3983723] using wordTrace_append hprefix tailTrace_3983723
  have hstable : (prefixWord ++ tailWord_3983723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983723).length < 2 ^ (prefixWord ++ tailWord_3983723).sum := by decide
  have hdescent : baseEnd_3983723 < baseStart_3983723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983730 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_3983730 : Nat := 118140960795 + 3983730 * 2 ^ 59
def prefixEnd_3983730 : Nat := 4983230072969 + 3 ^ 40 * 3983730 * 2
def baseEnd_3983730 : Nat := 227285365303978207972685

theorem tailTrace_3983730 : CollatzResearch.WordTrace tailWord_3983730 prefixEnd_3983730 227285365303978207972685 := by
  unfold tailWord_3983730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324642464408512940583161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96865713238422701174888429 36324642464408512940583161)
  ·
    refine ⟨27243481848306384705437371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36324642464408512940583161 27243481848306384705437371)
    ·
      refine ⟨40865222772459577058156057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27243481848306384705437371 40865222772459577058156057)
      ·
        refine ⟨30648917079344682793617043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40865222772459577058156057 30648917079344682793617043)
        ·
          refine ⟨45973375619017024190425565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30648917079344682793617043 45973375619017024190425565)
          ·
            refine ⟨17240015857131384071409587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45973375619017024190425565 17240015857131384071409587)
            ·
              refine ⟨25860023785697076107114381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17240015857131384071409587 25860023785697076107114381)
              ·
                refine ⟨9697508919636403540167893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25860023785697076107114381 9697508919636403540167893)
                ·
                  refine ⟨227285365303978207972685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9697508919636403540167893 227285365303978207972685)
                  ·
                    rfl

theorem cell23_3983730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_3983730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983730 prefixEnd_3983730 := by exact prefixLift 3983730
  have htrace : WordTrace (prefixWord ++ tailWord_3983730) baseStart_3983730 baseEnd_3983730 := by
    simpa [prefixWord, tailWord_3983730, baseEnd_3983730] using wordTrace_append hprefix tailTrace_3983730
  have hstable : (prefixWord ++ tailWord_3983730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983730).length < 2 ^ (prefixWord ++ tailWord_3983730).sum := by decide
  have hdescent : baseEnd_3983730 < baseStart_3983730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983740 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_3983740 : Nat := 118140960795 + 3983740 * 2 ^ 59
def prefixEnd_3983740 : Nat := 4983230072969 + 3 ^ 40 * 3983740 * 2
def baseEnd_3983740 : Nat := 2045573422542348832629119

theorem tailTrace_3983740 : CollatzResearch.WordTrace tailWord_3983740 prefixEnd_3983740 2045573422542348832629119 := by
  unfold tailWord_3983740
  simp only [CollatzResearch.WordTrace]
  refine ⟨72649467293798911735098337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96865956391731882313464449 72649467293798911735098337)
  ·
    refine ⟨54487100470349183801323753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72649467293798911735098337 54487100470349183801323753)
    ·
      refine ⟨40865325352761887850992815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54487100470349183801323753 40865325352761887850992815)
      ·
        refine ⟨61297988029142831776489223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40865325352761887850992815 61297988029142831776489223)
        ·
          refine ⟨91946982043714247664733835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61297988029142831776489223 91946982043714247664733835)
          ·
            refine ⟨137920473065571371497100753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91946982043714247664733835 137920473065571371497100753)
            ·
              refine ⟨103440354799178528622825565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137920473065571371497100753 103440354799178528622825565)
              ·
                refine ⟨38790133049691948233559587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103440354799178528622825565 38790133049691948233559587)
                ·
                  refine ⟨58185199574537922350339381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38790133049691948233559587 58185199574537922350339381)
                  ·
                    refine ⟨5454862460112930220344317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58185199574537922350339381 5454862460112930220344317)
                    ·
                      refine ⟨2045573422542348832629119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454862460112930220344317 2045573422542348832629119)
                      ·
                        rfl

theorem cell23_3983740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_3983740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983740 prefixEnd_3983740 := by exact prefixLift 3983740
  have htrace : WordTrace (prefixWord ++ tailWord_3983740) baseStart_3983740 baseEnd_3983740 := by
    simpa [prefixWord, tailWord_3983740, baseEnd_3983740] using wordTrace_append hprefix tailTrace_3983740
  have hstable : (prefixWord ++ tailWord_3983740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983740).length < 2 ^ (prefixWord ++ tailWord_3983740).sum := by decide
  have hdescent : baseEnd_3983740 < baseStart_3983740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983817 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_3983817 : Nat := 118140960795 + 3983817 * 2 ^ 59
def prefixEnd_3983817 : Nat := 4983230072969 + 3 ^ 40 * 3983817 * 2
def baseEnd_3983817 : Nat := 2045612960552745031366265

theorem tailTrace_3983817 : CollatzResearch.WordTrace tailWord_3983817 prefixEnd_3983817 2045612960552745031366265 := by
  unfold tailWord_3983817
  simp only [CollatzResearch.WordTrace]
  refine ⟨145301743008318865620749705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96867828672212577080499803 145301743008318865620749705)
  ·
    refine ⟨108976307256239149215562279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145301743008318865620749705 108976307256239149215562279)
    ·
      refine ⟨163464460884358723823343419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108976307256239149215562279 163464460884358723823343419)
      ·
        refine ⟨245196691326538085735015129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163464460884358723823343419 245196691326538085735015129)
        ·
          refine ⟨183897518494903564301261347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245196691326538085735015129 183897518494903564301261347)
          ·
            refine ⟨275846277742355346451892021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183897518494903564301261347 275846277742355346451892021)
            ·
              refine ⟨25860588538345813729864877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275846277742355346451892021 25860588538345813729864877)
              ·
                refine ⟨9697720701879680148699329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25860588538345813729864877 9697720701879680148699329)
                ·
                  refine ⟨7273290526409760111524497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9697720701879680148699329 7273290526409760111524497)
                  ·
                    refine ⟨5454967894807320083643373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7273290526409760111524497 5454967894807320083643373)
                    ·
                      refine ⟨2045612960552745031366265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5454967894807320083643373 2045612960552745031366265)
                      ·
                        rfl

theorem cell23_3983817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_3983817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983817 prefixEnd_3983817 := by exact prefixLift 3983817
  have htrace : WordTrace (prefixWord ++ tailWord_3983817) baseStart_3983817 baseEnd_3983817 := by
    simpa [prefixWord, tailWord_3983817, baseEnd_3983817] using wordTrace_append hprefix tailTrace_3983817
  have hstable : (prefixWord ++ tailWord_3983817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983817).length < 2 ^ (prefixWord ++ tailWord_3983817).sum := by decide
  have hdescent : baseEnd_3983817 < baseStart_3983817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983840 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3983840 : Nat := 118140960795 + 3983840 * 2 ^ 59
def prefixEnd_3983840 : Nat := 4983230072969 + 3 ^ 40 * 3983840 * 2
def baseEnd_3983840 : Nat := 2045624770607798441378659

theorem tailTrace_3983840 : CollatzResearch.WordTrace tailWord_3983840 prefixEnd_3983840 2045624770607798441378659 := by
  unfold tailWord_3983840
  simp only [CollatzResearch.WordTrace]
  refine ⟨72651290943617770274418487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96868387924823693699224649 72651290943617770274418487)
  ·
    refine ⟨108976936415426655411627731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72651290943617770274418487 108976936415426655411627731)
    ·
      refine ⟨163465404623139983117441597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108976936415426655411627731 163465404623139983117441597)
      ·
        refine ⟨61299526733677493669040599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163465404623139983117441597 61299526733677493669040599)
        ·
          refine ⟨91949290100516240503560899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61299526733677493669040599 91949290100516240503560899)
          ·
            refine ⟨137923935150774360755341349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91949290100516240503560899 137923935150774360755341349)
            ·
              refine ⟨25860737840770192641626503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137923935150774360755341349 25860737840770192641626503)
              ·
                refine ⟨38791106761155288962439755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25860737840770192641626503 38791106761155288962439755)
                ·
                  refine ⟨58186660141732933443659633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38791106761155288962439755 58186660141732933443659633)
                  ·
                    refine ⟨43639995106299700082744725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58186660141732933443659633 43639995106299700082744725)
                    ·
                      refine ⟨2045624770607798441378659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43639995106299700082744725 2045624770607798441378659)
                      ·
                        rfl

theorem cell23_3983840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3983840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983840 prefixEnd_3983840 := by exact prefixLift 3983840
  have htrace : WordTrace (prefixWord ++ tailWord_3983840) baseStart_3983840 baseEnd_3983840 := by
    simpa [prefixWord, tailWord_3983840, baseEnd_3983840] using wordTrace_append hprefix tailTrace_3983840
  have hstable : (prefixWord ++ tailWord_3983840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983840).length < 2 ^ (prefixWord ++ tailWord_3983840).sum := by decide
  have hdescent : baseEnd_3983840 < baseStart_3983840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983864 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_3983864 : Nat := 118140960795 + 3983864 * 2 ^ 59
def prefixEnd_3983864 : Nat := 4983230072969 + 3 ^ 40 * 3983864 * 2
def baseEnd_3983864 : Nat := 2045637094143506347478549

theorem tailTrace_3983864 : CollatzResearch.WordTrace tailWord_3983864 prefixEnd_3983864 2045637094143506347478549 := by
  unfold tailWord_3983864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72651728619574296323855323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96868971492765728431807097 72651728619574296323855323)
  ·
    refine ⟨108977592929361444485782985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72651728619574296323855323 108977592929361444485782985)
    ·
      refine ⟨81733194697021083364337239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108977592929361444485782985 81733194697021083364337239)
      ·
        refine ⟨122599792045531625046505859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81733194697021083364337239 122599792045531625046505859)
        ·
          refine ⟨183899688068297437569758789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122599792045531625046505859 183899688068297437569758789)
          ·
            refine ⟨34481191512805769544329773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183899688068297437569758789 34481191512805769544329773)
            ·
              refine ⟨12930446817302163579123665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34481191512805769544329773 12930446817302163579123665)
              ·
                refine ⟨9697835112976622684342749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12930446817302163579123665 9697835112976622684342749)
                ·
                  refine ⟨3636688167366233506628531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9697835112976622684342749 3636688167366233506628531)
                  ·
                    refine ⟨5455032251049350259942797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3636688167366233506628531 5455032251049350259942797)
                    ·
                      refine ⟨2045637094143506347478549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5455032251049350259942797 2045637094143506347478549)
                      ·
                        rfl

theorem cell23_3983864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_3983864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983864 prefixEnd_3983864 := by exact prefixLift 3983864
  have htrace : WordTrace (prefixWord ++ tailWord_3983864) baseStart_3983864 baseEnd_3983864 := by
    simpa [prefixWord, tailWord_3983864, baseEnd_3983864] using wordTrace_append hprefix tailTrace_3983864
  have hstable : (prefixWord ++ tailWord_3983864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983864).length < 2 ^ (prefixWord ++ tailWord_3983864).sum := by decide
  have hdescent : baseEnd_3983864 < baseStart_3983864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983884 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_3983884 : Nat := 118140960795 + 3983884 * 2 ^ 59
def prefixEnd_3983884 : Nat := 4983230072969 + 3 ^ 40 * 3983884 * 2
def baseEnd_3983884 : Nat := 681882454585532089742819

theorem tailTrace_3983884 : CollatzResearch.WordTrace tailWord_3983884 prefixEnd_3983884 681882454585532089742819 := by
  unfold tailWord_3983884
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652093349538068031719353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96869457799384090708959137 72652093349538068031719353)
  ·
    refine ⟨54489070012153551023789515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72652093349538068031719353 54489070012153551023789515)
    ·
      refine ⟨81733605018230326535684273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54489070012153551023789515 81733605018230326535684273)
      ·
        refine ⟨61300203763672744901763205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81733605018230326535684273 61300203763672744901763205)
        ·
          refine ⟨11493788205688639669080601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61300203763672744901763205 11493788205688639669080601)
          ·
            refine ⟨8620341154266479751810451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11493788205688639669080601 8620341154266479751810451)
            ·
              refine ⟨12930511731399719627715677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620341154266479751810451 12930511731399719627715677)
              ·
                refine ⟨4848941899274894860393379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12930511731399719627715677 4848941899274894860393379)
                ·
                  refine ⟨7273412848912342290590069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848941899274894860393379 7273412848912342290590069)
                  ·
                    refine ⟨681882454585532089742819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7273412848912342290590069 681882454585532089742819)
                    ·
                      rfl

theorem cell23_3983884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_3983884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983884 prefixEnd_3983884 := by exact prefixLift 3983884
  have htrace : WordTrace (prefixWord ++ tailWord_3983884) baseStart_3983884 baseEnd_3983884 := by
    simpa [prefixWord, tailWord_3983884, baseEnd_3983884] using wordTrace_append hprefix tailTrace_3983884
  have hstable : (prefixWord ++ tailWord_3983884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983884).length < 2 ^ (prefixWord ++ tailWord_3983884).sum := by decide
  have hdescent : baseEnd_3983884 < baseStart_3983884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983897 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_3983897 : Nat := 118140960795 + 3983897 * 2 ^ 59
def prefixEnd_3983897 : Nat := 4983230072969 + 3 ^ 40 * 3983897 * 2
def baseEnd_3983897 : Nat := 681884679668368239455299

theorem tailTrace_3983897 : CollatzResearch.WordTrace tailWord_3983897 prefixEnd_3983897 681884679668368239455299 := by
  unfold tailWord_3983897
  simp only [CollatzResearch.WordTrace]
  refine ⟨145304660848029039283661945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96869773898686026189107963 145304660848029039283661945)
  ·
    refine ⟨108978495636021779462746459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145304660848029039283661945 108978495636021779462746459)
    ·
      refine ⟨163467743454032669194119689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108978495636021779462746459 163467743454032669194119689)
      ·
        refine ⟨122600807590524501895589767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163467743454032669194119689 122600807590524501895589767)
        ·
          refine ⟨183901211385786752843384651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122600807590524501895589767 183901211385786752843384651)
          ·
            refine ⟨275851817078680129265076977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183901211385786752843384651 275851817078680129265076977)
            ·
              refine ⟨206888862809010096948807733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275851817078680129265076977 206888862809010096948807733)
              ·
                refine ⟨19395830888344696588950725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206888862809010096948807733 19395830888344696588950725)
                ·
                  refine ⟨3636718291564630610428261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19395830888344696588950725 3636718291564630610428261)
                  ·
                    refine ⟨681884679668368239455299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636718291564630610428261 681884679668368239455299)
                    ·
                      rfl

theorem cell23_3983897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_3983897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983897 prefixEnd_3983897 := by exact prefixLift 3983897
  have htrace : WordTrace (prefixWord ++ tailWord_3983897) baseStart_3983897 baseEnd_3983897 := by
    simpa [prefixWord, tailWord_3983897, baseEnd_3983897] using wordTrace_append hprefix tailTrace_3983897
  have hstable : (prefixWord ++ tailWord_3983897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983897).length < 2 ^ (prefixWord ++ tailWord_3983897).sum := by decide
  have hdescent : baseEnd_3983897 < baseStart_3983897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983907 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3983907 : Nat := 118140960795 + 3983907 * 2 ^ 59
def prefixEnd_3983907 : Nat := 4983230072969 + 3 ^ 40 * 3983907 * 2
def baseEnd_3983907 : Nat := 2045659173811649679240851

theorem tailTrace_3983907 : CollatzResearch.WordTrace tailWord_3983907 prefixEnd_3983907 2045659173811649679240851 := by
  unfold tailWord_3983907
  simp only [CollatzResearch.WordTrace]
  refine ⟨145305025577992810991525975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96870017051995207327683983 145305025577992810991525975)
  ·
    refine ⟨217957538366989216487288963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145305025577992810991525975 217957538366989216487288963)
    ·
      refine ⟨326936307550483824730933445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217957538366989216487288963 326936307550483824730933445)
      ·
        refine ⟨61300557665715717137050021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326936307550483824730933445 61300557665715717137050021)
        ·
          refine ⟨11493854562321696963196879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61300557665715717137050021 11493854562321696963196879)
          ·
            refine ⟨17240781843482545444795319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493854562321696963196879 17240781843482545444795319)
            ·
              refine ⟨25861172765223818167192979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17240781843482545444795319 25861172765223818167192979)
              ·
                refine ⟨38791759147835727250789469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25861172765223818167192979 38791759147835727250789469)
                ·
                  refine ⟨14546909680438397719046051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38791759147835727250789469 14546909680438397719046051)
                  ·
                    refine ⟨21820364520657596578569077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14546909680438397719046051 21820364520657596578569077)
                    ·
                      refine ⟨2045659173811649679240851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21820364520657596578569077 2045659173811649679240851)
                      ·
                        rfl

theorem cell23_3983907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3983907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983907 prefixEnd_3983907 := by exact prefixLift 3983907
  have htrace : WordTrace (prefixWord ++ tailWord_3983907) baseStart_3983907 baseEnd_3983907 := by
    simpa [prefixWord, tailWord_3983907, baseEnd_3983907] using wordTrace_append hprefix tailTrace_3983907
  have hstable : (prefixWord ++ tailWord_3983907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983907).length < 2 ^ (prefixWord ++ tailWord_3983907).sum := by decide
  have hdescent : baseEnd_3983907 < baseStart_3983907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983914 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3983914 : Nat := 118140960795 + 3983914 * 2 ^ 59
def prefixEnd_3983914 : Nat := 4983230072969 + 3 ^ 40 * 3983914 * 2
def baseEnd_3983914 : Nat := 681887589392077050617773

theorem tailTrace_3983914 : CollatzResearch.WordTrace tailWord_3983914 prefixEnd_3983914 681887589392077050617773 := by
  unfold tailWord_3983914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36326320222241862796757699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96870187259311634124687197 36326320222241862796757699)
  ·
    refine ⟨54489480333362794195136549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36326320222241862796757699 54489480333362794195136549)
    ·
      refine ⟨10216777562505523911588103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54489480333362794195136549 10216777562505523911588103)
      ·
        refine ⟨15325166343758285867382155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216777562505523911588103 15325166343758285867382155)
        ·
          refine ⟨22987749515637428801073233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325166343758285867382155 22987749515637428801073233)
          ·
            refine ⟨17240812136728071600804925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22987749515637428801073233 17240812136728071600804925)
            ·
              refine ⟨6465304551273026850301847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17240812136728071600804925 6465304551273026850301847)
              ·
                refine ⟨9697956826909540275452771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465304551273026850301847 9697956826909540275452771)
                ·
                  refine ⟨14546935240364310413179157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697956826909540275452771 14546935240364310413179157)
                  ·
                    refine ⟨681887589392077050617773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14546935240364310413179157 681887589392077050617773)
                    ·
                      rfl

theorem cell23_3983914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3983914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983914 prefixEnd_3983914 := by exact prefixLift 3983914
  have htrace : WordTrace (prefixWord ++ tailWord_3983914) baseStart_3983914 baseEnd_3983914 := by
    simpa [prefixWord, tailWord_3983914, baseEnd_3983914] using wordTrace_append hprefix tailTrace_3983914
  have hstable : (prefixWord ++ tailWord_3983914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983914).length < 2 ^ (prefixWord ++ tailWord_3983914).sum := by decide
  have hdescent : baseEnd_3983914 < baseStart_3983914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983921 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_3983921 : Nat := 118140960795 + 3983921 * 2 ^ 59
def prefixEnd_3983921 : Nat := 4983230072969 + 3 ^ 40 * 3983921 * 2
def baseEnd_3983921 : Nat := 2045666362540812624465787

theorem tailTrace_3983921 : CollatzResearch.WordTrace tailWord_3983921 prefixEnd_3983921 2045666362540812624465787 := by
  unfold tailWord_3983921
  simp only [CollatzResearch.WordTrace]
  refine ⟨145305536199942091382535617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96870357466628060921690411 145305536199942091382535617)
  ·
    refine ⟨108979152149956568536901713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145305536199942091382535617 108979152149956568536901713)
    ·
      refine ⟨81734364112467426402676285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108979152149956568536901713 81734364112467426402676285)
      ·
        refine ⟨30650386542175284901003607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81734364112467426402676285 30650386542175284901003607)
        ·
          refine ⟨45975579813262927351505411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30650386542175284901003607 45975579813262927351505411)
          ·
            refine ⟨68963369719894391027258117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45975579813262927351505411 68963369719894391027258117)
            ·
              refine ⟨12930631822480198317610897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68963369719894391027258117 12930631822480198317610897)
              ·
                refine ⟨9697973866860148738208173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12930631822480198317610897 9697973866860148738208173)
                ·
                  refine ⟨3636740200072555776828065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9697973866860148738208173 3636740200072555776828065)
                  ·
                    refine ⟨2727555150054416832621049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3636740200072555776828065 2727555150054416832621049)
                    ·
                      refine ⟨2045666362540812624465787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727555150054416832621049 2045666362540812624465787)
                      ·
                        rfl

theorem cell23_3983921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_3983921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983921 prefixEnd_3983921 := by exact prefixLift 3983921
  have htrace : WordTrace (prefixWord ++ tailWord_3983921) baseStart_3983921 baseEnd_3983921 := by
    simpa [prefixWord, tailWord_3983921, baseEnd_3983921] using wordTrace_append hprefix tailTrace_3983921
  have hstable : (prefixWord ++ tailWord_3983921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983921).length < 2 ^ (prefixWord ++ tailWord_3983921).sum := by decide
  have hdescent : baseEnd_3983921 < baseStart_3983921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3983971 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3983971 : Nat := 118140960795 + 3983971 * 2 ^ 59
def prefixEnd_3983971 : Nat := 4983230072969 + 3 ^ 40 * 3983971 * 2
def baseEnd_3983971 : Nat := 2045692036573537428840557

theorem tailTrace_3983971 : CollatzResearch.WordTrace tailWord_3983971 prefixEnd_3983971 2045692036573537428840557 := by
  unfold tailWord_3983971
  simp only [CollatzResearch.WordTrace]
  refine ⟨145307359849760949921855767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96871573233173966614570511 145307359849760949921855767)
  ·
    refine ⟨217961039774641424882783651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145307359849760949921855767 217961039774641424882783651)
    ·
      refine ⟨326941559661962137324175477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217961039774641424882783651 326941559661962137324175477)
      ·
        refine ⟨30650771218308950374141451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326941559661962137324175477 30650771218308950374141451)
        ·
          refine ⟨45976156827463425561212177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30650771218308950374141451 45976156827463425561212177)
          ·
            refine ⟨34482117620597569170909133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45976156827463425561212177 34482117620597569170909133)
            ·
              refine ⟨12930794107724088439090925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34482117620597569170909133 12930794107724088439090925)
              ·
                refine ⟨4849047790396533164659097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12930794107724088439090925 4849047790396533164659097)
                ·
                  refine ⟨3636785842797399873494323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4849047790396533164659097 3636785842797399873494323)
                  ·
                    refine ⟨5455178764196099810241485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3636785842797399873494323 5455178764196099810241485)
                    ·
                      refine ⟨2045692036573537428840557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5455178764196099810241485 2045692036573537428840557)
                      ·
                        rfl

theorem cell23_3983971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3983971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3983971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3983971 prefixEnd_3983971 := by exact prefixLift 3983971
  have htrace : WordTrace (prefixWord ++ tailWord_3983971) baseStart_3983971 baseEnd_3983971 := by
    simpa [prefixWord, tailWord_3983971, baseEnd_3983971] using wordTrace_append hprefix tailTrace_3983971
  have hstable : (prefixWord ++ tailWord_3983971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3983971).length < 2 ^ (prefixWord ++ tailWord_3983971).sum := by decide
  have hdescent : baseEnd_3983971 < baseStart_3983971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3983971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984014 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3984014 : Nat := 118140960795 + 3984014 * 2 ^ 59
def prefixEnd_3984014 : Nat := 4983230072969 + 3 ^ 40 * 3984014 * 2
def baseEnd_3984014 : Nat := 2045714116241680760602859

theorem tailTrace_3984014 : CollatzResearch.WordTrace tailWord_3984014 prefixEnd_3984014 2045714116241680760602859 := by
  unfold tailWord_3984014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163616023575646033208887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96872618792403445510447397 18163616023575646033208887)
  ·
    refine ⟨27245424035363469049813331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18163616023575646033208887 27245424035363469049813331)
    ·
      refine ⟨40868136053045203574719997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27245424035363469049813331 40868136053045203574719997)
      ·
        refine ⟨15325551019891951340519999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40868136053045203574719997 15325551019891951340519999)
        ·
          refine ⟨22988326529837927010779999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325551019891951340519999 22988326529837927010779999)
          ·
            refine ⟨34482489794756890516169999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22988326529837927010779999 34482489794756890516169999)
            ·
              refine ⟨51723734692135335774254999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34482489794756890516169999 51723734692135335774254999)
              ·
                refine ⟨77585602038203003661382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51723734692135335774254999 77585602038203003661382499)
                ·
                  refine ⟨116378403057304505492073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77585602038203003661382499 116378403057304505492073749)
                  ·
                    refine ⟨5455237643311148694940957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116378403057304505492073749 5455237643311148694940957)
                    ·
                      refine ⟨2045714116241680760602859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5455237643311148694940957 2045714116241680760602859)
                      ·
                        rfl

theorem cell23_3984014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3984014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984014 prefixEnd_3984014 := by exact prefixLift 3984014
  have htrace : WordTrace (prefixWord ++ tailWord_3984014) baseStart_3984014 baseEnd_3984014 := by
    simpa [prefixWord, tailWord_3984014, baseEnd_3984014] using wordTrace_append hprefix tailTrace_3984014
  have hstable : (prefixWord ++ tailWord_3984014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984014).length < 2 ^ (prefixWord ++ tailWord_3984014).sum := by decide
  have hdescent : baseEnd_3984014 < baseStart_3984014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984024 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3984024 : Nat := 118140960795 + 3984024 * 2 ^ 59
def prefixEnd_3984024 : Nat := 4983230072969 + 3 ^ 40 * 3984024 * 2
def baseEnd_3984024 : Nat := 2045719251048225721477813

theorem tailTrace_3984024 : CollatzResearch.WordTrace tailWord_3984024 prefixEnd_3984024 2045719251048225721477813 := by
  unfold tailWord_3984024
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654646459284469986767563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96872861945712626649023417 72654646459284469986767563)
  ·
    refine ⟨108981969688926704980151345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72654646459284469986767563 108981969688926704980151345)
    ·
      refine ⟨81736477266695028735113509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108981969688926704980151345 81736477266695028735113509)
      ·
        refine ⟨15325589487505317887833783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81736477266695028735113509 15325589487505317887833783)
        ·
          refine ⟨22988384231257976831750675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325589487505317887833783 22988384231257976831750675)
          ·
            refine ⟨34482576346886965247626013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22988384231257976831750675 34482576346886965247626013)
            ·
              refine ⟨12930966130082611967859755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34482576346886965247626013 12930966130082611967859755)
              ·
                refine ⟨19396449195123917951789633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930966130082611967859755 19396449195123917951789633)
                ·
                  refine ⟨14547336896342938463842225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19396449195123917951789633 14547336896342938463842225)
                  ·
                    refine ⟨10910502672257203847881669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14547336896342938463842225 10910502672257203847881669)
                    ·
                      refine ⟨2045719251048225721477813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10910502672257203847881669 2045719251048225721477813)
                      ·
                        rfl

theorem cell23_3984024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3984024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984024 prefixEnd_3984024 := by exact prefixLift 3984024
  have htrace : WordTrace (prefixWord ++ tailWord_3984024) baseStart_3984024 baseEnd_3984024 := by
    simpa [prefixWord, tailWord_3984024, baseEnd_3984024] using wordTrace_append hprefix tailTrace_3984024
  have hstable : (prefixWord ++ tailWord_3984024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984024).length < 2 ^ (prefixWord ++ tailWord_3984024).sum := by decide
  have hdescent : baseEnd_3984024 < baseStart_3984024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984028 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3984028 : Nat := 118140960795 + 3984028 * 2 ^ 59
def prefixEnd_3984028 : Nat := 4983230072969 + 3 ^ 40 * 3984028 * 2
def baseEnd_3984028 : Nat := 2045721304970843705827795

theorem tailTrace_3984028 : CollatzResearch.WordTrace tailWord_3984028 prefixEnd_3984028 2045721304970843705827795 := by
  unfold tailWord_3984028
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654719405277224328340369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96872959207036299104453825 72654719405277224328340369)
  ·
    refine ⟨54491039553957918246255277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72654719405277224328340369 54491039553957918246255277)
    ·
      refine ⟨20434139832734219342345729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54491039553957918246255277 20434139832734219342345729)
      ·
        refine ⟨15325604874550664506759297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20434139832734219342345729 15325604874550664506759297)
        ·
          refine ⟨11494203655912998380069473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15325604874550664506759297 11494203655912998380069473)
          ·
            refine ⟨8620652741934748785052105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11494203655912998380069473 8620652741934748785052105)
            ·
              refine ⟨6465489556451061588789079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620652741934748785052105 6465489556451061588789079)
              ·
                refine ⟨9698234334676592383183619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465489556451061588789079 9698234334676592383183619)
                ·
                  refine ⟨14547351502014888574775429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698234334676592383183619 14547351502014888574775429)
                  ·
                    refine ⟨2727628406627791607770393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14547351502014888574775429 2727628406627791607770393)
                    ·
                      refine ⟨2045721304970843705827795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727628406627791607770393 2045721304970843705827795)
                      ·
                        rfl

theorem cell23_3984028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3984028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984028 prefixEnd_3984028 := by exact prefixLift 3984028
  have htrace : WordTrace (prefixWord ++ tailWord_3984028) baseStart_3984028 baseEnd_3984028 := by
    simpa [prefixWord, tailWord_3984028, baseEnd_3984028] using wordTrace_append hprefix tailTrace_3984028
  have hstable : (prefixWord ++ tailWord_3984028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984028).length < 2 ^ (prefixWord ++ tailWord_3984028).sum := by decide
  have hdescent : baseEnd_3984028 < baseStart_3984028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984049 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3984049 : Nat := 118140960795 + 3984049 * 2 ^ 59
def prefixEnd_3984049 : Nat := 4983230072969 + 3 ^ 40 * 3984049 * 2
def baseEnd_3984049 : Nat := 2045732088064588123665199

theorem tailTrace_3984049 : CollatzResearch.WordTrace tailWord_3984049 prefixEnd_3984049 2045732088064588123665199 := by
  unfold tailWord_3984049
  simp only [CollatzResearch.WordTrace]
  refine ⟨145310204743478369243195201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96873469828985579495463467 145310204743478369243195201)
  ·
    refine ⟨108982653557608776932396401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145310204743478369243195201 108982653557608776932396401)
    ·
      refine ⟨81736990168206582699297301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108982653557608776932396401 81736990168206582699297301)
      ·
        refine ⟨3831421414134683564029561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81736990168206582699297301 3831421414134683564029561)
        ·
          refine ⟨2873566060601012673022171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831421414134683564029561 2873566060601012673022171)
          ·
            refine ⟨4310349090901519009533257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873566060601012673022171 4310349090901519009533257)
            ·
              refine ⟨3232761818176139257149943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310349090901519009533257 3232761818176139257149943)
              ·
                refine ⟨4849142727264208885724915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232761818176139257149943 4849142727264208885724915)
                ·
                  refine ⟨7273714090896313328587373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849142727264208885724915 7273714090896313328587373)
                  ·
                    refine ⟨2727642784086117498220265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7273714090896313328587373 2727642784086117498220265)
                    ·
                      refine ⟨2045732088064588123665199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727642784086117498220265 2045732088064588123665199)
                      ·
                        rfl

theorem cell23_3984049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3984049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984049 prefixEnd_3984049 := by exact prefixLift 3984049
  have htrace : WordTrace (prefixWord ++ tailWord_3984049) baseStart_3984049 baseEnd_3984049 := by
    simpa [prefixWord, tailWord_3984049, baseEnd_3984049] using wordTrace_append hprefix tailTrace_3984049
  have hstable : (prefixWord ++ tailWord_3984049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984049).length < 2 ^ (prefixWord ++ tailWord_3984049).sum := by decide
  have hdescent : baseEnd_3984049 < baseStart_3984049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984051 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 5]
def baseStart_3984051 : Nat := 118140960795 + 3984051 * 2 ^ 59
def prefixEnd_3984051 : Nat := 4983230072969 + 3 ^ 40 * 3984051 * 2
def baseEnd_3984051 : Nat := 227303679447321901760021

theorem tailTrace_3984051 : CollatzResearch.WordTrace tailWord_3984051 prefixEnd_3984051 227303679447321901760021 := by
  unfold tailWord_3984051
  simp only [CollatzResearch.WordTrace]
  refine ⟨145310277689471123584768007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96873518459647415723178671 145310277689471123584768007)
  ·
    refine ⟨217965416534206685377152011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145310277689471123584768007 217965416534206685377152011)
    ·
      refine ⟨326948124801310028065728017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217965416534206685377152011 326948124801310028065728017)
      ·
        refine ⟨245211093600982521049296013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326948124801310028065728017 245211093600982521049296013)
        ·
          refine ⟨91954160100368445393486005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245211093600982521049296013 91954160100368445393486005)
          ·
            refine ⟨8620702509409541755639313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91954160100368445393486005 8620702509409541755639313)
            ·
              refine ⟨6465526882057156316729485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620702509409541755639313 6465526882057156316729485)
              ·
                refine ⟨2424572580771433618773557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6465526882057156316729485 2424572580771433618773557)
                ·
                  refine ⟨227303679447321901760021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2424572580771433618773557 227303679447321901760021)
                  ·
                    rfl

theorem cell23_3984051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 5].length) (baseStart_3984051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984051 prefixEnd_3984051 := by exact prefixLift 3984051
  have htrace : WordTrace (prefixWord ++ tailWord_3984051) baseStart_3984051 baseEnd_3984051 := by
    simpa [prefixWord, tailWord_3984051, baseEnd_3984051] using wordTrace_append hprefix tailTrace_3984051
  have hstable : (prefixWord ++ tailWord_3984051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984051).length < 2 ^ (prefixWord ++ tailWord_3984051).sum := by decide
  have hdescent : baseEnd_3984051 < baseStart_3984051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984124 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 8]
def baseStart_3984124 : Nat := 118140960795 + 3984124 * 2 ^ 59
def prefixEnd_3984124 : Nat := 4983230072969 + 3 ^ 40 * 3984124 * 2
def baseEnd_3984124 : Nat := 227307844345963925580817

theorem tailTrace_3984124 : CollatzResearch.WordTrace tailWord_3984124 prefixEnd_3984124 227307844345963925580817 := by
  unfold tailWord_3984124
  simp only [CollatzResearch.WordTrace]
  refine ⟨72656470109103328526087713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96875293478804438034783617 72656470109103328526087713)
  ·
    refine ⟨54492352581827496394565785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72656470109103328526087713 54492352581827496394565785)
    ·
      refine ⟨40869264436370622295924339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54492352581827496394565785 40869264436370622295924339)
      ·
        refine ⟨61303896654555933443886509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40869264436370622295924339 61303896654555933443886509)
        ·
          refine ⟨22988961245458475041457441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61303896654555933443886509 22988961245458475041457441)
          ·
            refine ⟨17241720934093856281093081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22988961245458475041457441 17241720934093856281093081)
            ·
              refine ⟨12931290700570392210819811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17241720934093856281093081 12931290700570392210819811)
              ·
                refine ⟨19396936050855588316229717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12931290700570392210819811 19396936050855588316229717)
                ·
                  refine ⟨227307844345963925580817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19396936050855588316229717 227307844345963925580817)
                  ·
                    rfl

theorem cell23_3984124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_3984124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984124 prefixEnd_3984124 := by exact prefixLift 3984124
  have htrace : WordTrace (prefixWord ++ tailWord_3984124) baseStart_3984124 baseEnd_3984124 := by
    simpa [prefixWord, tailWord_3984124, baseEnd_3984124] using wordTrace_append hprefix tailTrace_3984124
  have hstable : (prefixWord ++ tailWord_3984124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984124).length < 2 ^ (prefixWord ++ tailWord_3984124).sum := by decide
  have hdescent : baseEnd_3984124 < baseStart_3984124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984178 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_3984178 : Nat := 118140960795 + 3984178 * 2 ^ 59
def prefixEnd_3984178 : Nat := 4983230072969 + 3 ^ 40 * 3984178 * 2
def baseEnd_3984178 : Nat := 2045798327069018118952105

theorem tailTrace_3984178 : CollatzResearch.WordTrace tailWord_3984178 prefixEnd_3984178 2045798327069018118952105 := by
  unfold tailWord_3984178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36328727440002756068660297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96876606506674016183094125 36328727440002756068660297)
  ·
    refine ⟨27246545580002067051495223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36328727440002756068660297 27246545580002067051495223)
    ·
      refine ⟨40869818370003100577242835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27246545580002067051495223 40869818370003100577242835)
      ·
        refine ⟨61304727555004650865864253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40869818370003100577242835 61304727555004650865864253)
        ·
          refine ⟨22989272833126744074699095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61304727555004650865864253 22989272833126744074699095)
          ·
            refine ⟨34483909249690116112048643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22989272833126744074699095 34483909249690116112048643)
            ·
              refine ⟨51725863874535174168072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34483909249690116112048643 51725863874535174168072965)
              ·
                refine ⟨9698599476475345156513681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51725863874535174168072965 9698599476475345156513681)
                ·
                  refine ⟨7273949607356508867385261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698599476475345156513681 7273949607356508867385261)
                  ·
                    refine ⟨2727731102758690825269473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7273949607356508867385261 2727731102758690825269473)
                    ·
                      refine ⟨2045798327069018118952105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727731102758690825269473 2045798327069018118952105)
                      ·
                        rfl

theorem cell23_3984178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_3984178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984178 prefixEnd_3984178 := by exact prefixLift 3984178
  have htrace : WordTrace (prefixWord ++ tailWord_3984178) baseStart_3984178 baseEnd_3984178 := by
    simpa [prefixWord, tailWord_3984178, baseEnd_3984178] using wordTrace_append hprefix tailTrace_3984178
  have hstable : (prefixWord ++ tailWord_3984178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984178).length < 2 ^ (prefixWord ++ tailWord_3984178).sum := by decide
  have hdescent : baseEnd_3984178 < baseStart_3984178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984184 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_3984184 : Nat := 118140960795 + 3984184 * 2 ^ 59
def prefixEnd_3984184 : Nat := 4983230072969 + 3 ^ 40 * 3984184 * 2
def baseEnd_3984184 : Nat := 681933802650981698492359

theorem tailTrace_3984184 : CollatzResearch.WordTrace tailWord_3984184 prefixEnd_3984184 681933802650981698492359 := by
  unfold tailWord_3984184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72657564298994643649679803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96876752398659524866239737 72657564298994643649679803)
  ·
    refine ⟨108986346448491965474519705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72657564298994643649679803 108986346448491965474519705)
    ·
      refine ⟨81739759836368974105889779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108986346448491965474519705 81739759836368974105889779)
      ·
        refine ⟨122609639754553461158834669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81739759836368974105889779 122609639754553461158834669)
        ·
          refine ⟨45978614907957547934563001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122609639754553461158834669 45978614907957547934563001)
          ·
            refine ⟨34483961180968160950922251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45978614907957547934563001 34483961180968160950922251)
            ·
              refine ⟨51725941771452241426383377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34483961180968160950922251 51725941771452241426383377)
              ·
                refine ⟨38794456328589181069787533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51725941771452241426383377 38794456328589181069787533)
                ·
                  refine ⟨14547921123220942901170325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38794456328589181069787533 14547921123220942901170325)
                  ·
                    refine ⟨681933802650981698492359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14547921123220942901170325 681933802650981698492359)
                    ·
                      rfl

theorem cell23_3984184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_3984184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984184 prefixEnd_3984184 := by exact prefixLift 3984184
  have htrace : WordTrace (prefixWord ++ tailWord_3984184) baseStart_3984184 baseEnd_3984184 := by
    simpa [prefixWord, tailWord_3984184, baseEnd_3984184] using wordTrace_append hprefix tailTrace_3984184
  have hstable : (prefixWord ++ tailWord_3984184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984184).length < 2 ^ (prefixWord ++ tailWord_3984184).sum := by decide
  have hdescent : baseEnd_3984184 < baseStart_3984184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984191 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_3984191 : Nat := 118140960795 + 3984191 * 2 ^ 59
def prefixEnd_3984191 : Nat := 4983230072969 + 3 ^ 40 * 3984191 * 2
def baseEnd_3984191 : Nat := 2045805002317526568089545

theorem tailTrace_3984191 : CollatzResearch.WordTrace tailWord_3984191 prefixEnd_3984191 2045805002317526568089545 := by
  unfold tailWord_3984191
  simp only [CollatzResearch.WordTrace]
  refine ⟨145315383908963927494864427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96876922605975951663242951 145315383908963927494864427)
  ·
    refine ⟨217973075863445891242296641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145315383908963927494864427 217973075863445891242296641)
    ·
      refine ⟨163479806897584418431722481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217973075863445891242296641 163479806897584418431722481)
      ·
        refine ⟨122609855173188313823791861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163479806897584418431722481 122609855173188313823791861)
        ·
          refine ⟨11494673922486404420980487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122609855173188313823791861 11494673922486404420980487)
          ·
            refine ⟨17242010883729606631470731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494673922486404420980487 17242010883729606631470731)
            ·
              refine ⟨25863016325594409947206097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242010883729606631470731 25863016325594409947206097)
              ·
                refine ⟨19397262244195807460404573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25863016325594409947206097 19397262244195807460404573)
                ·
                  refine ⟨7273973341573427797651715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19397262244195807460404573 7273973341573427797651715)
                  ·
                    refine ⟨10910960012360141696477573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7273973341573427797651715 10910960012360141696477573)
                    ·
                      refine ⟨2045805002317526568089545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10910960012360141696477573 2045805002317526568089545)
                      ·
                        rfl

theorem cell23_3984191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_3984191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984191 prefixEnd_3984191 := by exact prefixLift 3984191
  have htrace : WordTrace (prefixWord ++ tailWord_3984191) baseStart_3984191 baseEnd_3984191 := by
    simpa [prefixWord, tailWord_3984191, baseEnd_3984191] using wordTrace_append hprefix tailTrace_3984191
  have hstable : (prefixWord ++ tailWord_3984191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984191).length < 2 ^ (prefixWord ++ tailWord_3984191).sum := by decide
  have hdescent : baseEnd_3984191 < baseStart_3984191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984201 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_3984201 : Nat := 118140960795 + 3984201 * 2 ^ 59
def prefixEnd_3984201 : Nat := 4983230072969 + 3 ^ 40 * 3984201 * 2
def baseEnd_3984201 : Nat := 681936712374690509654833

theorem tailTrace_3984201 : CollatzResearch.WordTrace tailWord_3984201 prefixEnd_3984201 681936712374690509654833 := by
  unfold tailWord_3984201
  simp only [CollatzResearch.WordTrace]
  refine ⟨145315748638927699202728457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96877165759285132801818971 145315748638927699202728457)
  ·
    refine ⟨108986811479195774402046343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145315748638927699202728457 108986811479195774402046343)
    ·
      refine ⟨163480217218793661603069515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108986811479195774402046343 163480217218793661603069515)
      ·
        refine ⟨245220325828190492404604273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163480217218793661603069515 245220325828190492404604273)
        ·
          refine ⟨183915244371142869303453205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245220325828190492404604273 183915244371142869303453205)
          ·
            refine ⟨8621027079897321998599369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183915244371142869303453205 8621027079897321998599369)
            ·
              refine ⟨6465770309922991498949527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8621027079897321998599369 6465770309922991498949527)
              ·
                refine ⟨9698655464884487248424291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465770309922991498949527 9698655464884487248424291)
                ·
                  refine ⟨14547983197326730872636437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698655464884487248424291 14547983197326730872636437)
                  ·
                    refine ⟨681936712374690509654833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14547983197326730872636437 681936712374690509654833)
                    ·
                      rfl

theorem cell23_3984201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_3984201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984201 prefixEnd_3984201 := by exact prefixLift 3984201
  have htrace : WordTrace (prefixWord ++ tailWord_3984201) baseStart_3984201 baseEnd_3984201 := by
    simpa [prefixWord, tailWord_3984201, baseEnd_3984201] using wordTrace_append hprefix tailTrace_3984201
  have hstable : (prefixWord ++ tailWord_3984201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984201).length < 2 ^ (prefixWord ++ tailWord_3984201).sum := by decide
  have hdescent : baseEnd_3984201 < baseStart_3984201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984208 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2]
def baseStart_3984208 : Nat := 118140960795 + 3984208 * 2 ^ 59
def prefixEnd_3984208 : Nat := 4983230072969 + 3 ^ 40 * 3984208 * 2
def baseEnd_3984208 : Nat := 2045813731488653001576967

theorem tailTrace_3984208 : CollatzResearch.WordTrace tailWord_3984208 prefixEnd_3984208 2045813731488653001576967 := by
  unfold tailWord_3984208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72658001974951169699116639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96877335966601559598822185 72658001974951169699116639)
  ·
    refine ⟨108987002962426754548674959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72658001974951169699116639 108987002962426754548674959)
    ·
      refine ⟨163480504443640131823012439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108987002962426754548674959 163480504443640131823012439)
      ·
        refine ⟨245220756665460197734518659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163480504443640131823012439 245220756665460197734518659)
        ·
          refine ⟨367831134998190296601777989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245220756665460197734518659 367831134998190296601777989)
          ·
            refine ⟨68968337812160680612833373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367831134998190296601777989 68968337812160680612833373)
            ·
              refine ⟨25863126679560255229812515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68968337812160680612833373 25863126679560255229812515)
              ·
                refine ⟨38794690019340382844718773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25863126679560255229812515 38794690019340382844718773)
                ·
                  refine ⟨3637002189313160891692385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38794690019340382844718773 3637002189313160891692385)
                  ·
                    refine ⟨2727751641984870668769289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637002189313160891692385 2727751641984870668769289)
                    ·
                      refine ⟨2045813731488653001576967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727751641984870668769289 2045813731488653001576967)
                      ·
                        rfl

theorem cell23_3984208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 2, 2].length) (baseStart_3984208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984208 prefixEnd_3984208 := by exact prefixLift 3984208
  have htrace : WordTrace (prefixWord ++ tailWord_3984208) baseStart_3984208 baseEnd_3984208 := by
    simpa [prefixWord, tailWord_3984208, baseEnd_3984208] using wordTrace_append hprefix tailTrace_3984208
  have hstable : (prefixWord ++ tailWord_3984208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984208).length < 2 ^ (prefixWord ++ tailWord_3984208).sum := by decide
  have hdescent : baseEnd_3984208 < baseStart_3984208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984212 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_3984212 : Nat := 118140960795 + 3984212 * 2 ^ 59
def prefixEnd_3984212 : Nat := 4983230072969 + 3 ^ 40 * 3984212 * 2
def baseEnd_3984212 : Nat := 2045815785411270985926949

theorem tailTrace_3984212 : CollatzResearch.WordTrace tailWord_3984212 prefixEnd_3984212 2045815785411270985926949 := by
  unfold tailWord_3984212
  simp only [CollatzResearch.WordTrace]
  refine ⟨72658074920943924040689445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96877433227925232054252593 72658074920943924040689445)
  ·
    refine ⟨13623389047676985757629271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72658074920943924040689445 13623389047676985757629271)
    ·
      refine ⟨20435083571515478636443907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13623389047676985757629271 20435083571515478636443907)
      ·
        refine ⟨30652625357273217954665861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435083571515478636443907 30652625357273217954665861)
        ·
          refine ⟨5747367254488728366499849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30652625357273217954665861 5747367254488728366499849)
          ·
            refine ⟨4310525440866546274874887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747367254488728366499849 4310525440866546274874887)
            ·
              refine ⟨6465788161299819412312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310525440866546274874887 6465788161299819412312331)
              ·
                refine ⟨9698682241949729118468497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465788161299819412312331 9698682241949729118468497)
                ·
                  refine ⟨7274011681462296838851373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698682241949729118468497 7274011681462296838851373)
                  ·
                    refine ⟨2727754380548361314569265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7274011681462296838851373 2727754380548361314569265)
                    ·
                      refine ⟨2045815785411270985926949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727754380548361314569265 2045815785411270985926949)
                      ·
                        rfl

theorem cell23_3984212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_3984212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984212 prefixEnd_3984212 := by exact prefixLift 3984212
  have htrace : WordTrace (prefixWord ++ tailWord_3984212) baseStart_3984212 baseEnd_3984212 := by
    simpa [prefixWord, tailWord_3984212, baseEnd_3984212] using wordTrace_append hprefix tailTrace_3984212
  have hstable : (prefixWord ++ tailWord_3984212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984212).length < 2 ^ (prefixWord ++ tailWord_3984212).sum := by decide
  have hdescent : baseEnd_3984212 < baseStart_3984212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984242 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_3984242 : Nat := 118140960795 + 3984242 * 2 ^ 59
def prefixEnd_3984242 : Nat := 4983230072969 + 3 ^ 40 * 3984242 * 2
def baseEnd_3984242 : Nat := 2045831189830905868551811

theorem tailTrace_3984242 : CollatzResearch.WordTrace tailWord_3984242 prefixEnd_3984242 2045831189830905868551811 := by
  unfold tailWord_3984242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36329311007944790801242745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96878162687852775469980653 36329311007944790801242745)
  ·
    refine ⟨27246983255958593100932059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36329311007944790801242745 27246983255958593100932059)
    ·
      refine ⟨40870474883937889651398089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27246983255958593100932059 40870474883937889651398089)
      ·
        refine ⟨30652856162953417238548567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40870474883937889651398089 30652856162953417238548567)
        ·
          refine ⟨45979284244430125857822851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30652856162953417238548567 45979284244430125857822851)
          ·
            refine ⟨68968926366645188786734277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45979284244430125857822851 68968926366645188786734277)
            ·
              refine ⟨12931673693745972897512677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68968926366645188786734277 12931673693745972897512677)
              ·
                refine ⟨2424688817577369918283627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12931673693745972897512677 2424688817577369918283627)
                ·
                  refine ⟨3637033226366054877425441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424688817577369918283627 3637033226366054877425441)
                  ·
                    refine ⟨2727774919774541158069081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637033226366054877425441 2727774919774541158069081)
                    ·
                      refine ⟨2045831189830905868551811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727774919774541158069081 2045831189830905868551811)
                      ·
                        rfl

theorem cell23_3984242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_3984242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984242 prefixEnd_3984242 := by exact prefixLift 3984242
  have htrace : WordTrace (prefixWord ++ tailWord_3984242) baseStart_3984242 baseEnd_3984242 := by
    simpa [prefixWord, tailWord_3984242, baseEnd_3984242] using wordTrace_append hprefix tailTrace_3984242
  have hstable : (prefixWord ++ tailWord_3984242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984242).length < 2 ^ (prefixWord ++ tailWord_3984242).sum := by decide
  have hdescent : baseEnd_3984242 < baseStart_3984242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984268 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_3984268 : Nat := 118140960795 + 3984268 * 2 ^ 59
def prefixEnd_3984268 : Nat := 4983230072969 + 3 ^ 40 * 3984268 * 2
def baseEnd_3984268 : Nat := 2045844540327922766826691

theorem tailTrace_3984268 : CollatzResearch.WordTrace tailWord_3984268 prefixEnd_3984268 2045844540327922766826691 := by
  unfold tailWord_3984268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72659096164842484822708729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96878794886456646430278305 72659096164842484822708729)
  ·
    refine ⟨54494322123631863617031547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72659096164842484822708729 54494322123631863617031547)
    ·
      refine ⟨81741483185447795425547321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54494322123631863617031547 81741483185447795425547321)
      ·
        refine ⟨61306112389085846569160491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81741483185447795425547321 61306112389085846569160491)
        ·
          refine ⟨91959168583628769853740737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61306112389085846569160491 91959168583628769853740737)
          ·
            refine ⟨68969376437721577390305553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91959168583628769853740737 68969376437721577390305553)
            ·
              refine ⟨51727032328291183042729165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68969376437721577390305553 51727032328291183042729165)
              ·
                refine ⟨19397637123109193641023437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51727032328291183042729165 19397637123109193641023437)
                ·
                  refine ⟨7274113921165947615383789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19397637123109193641023437 7274113921165947615383789)
                  ·
                    refine ⟨2727792720437230355768921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7274113921165947615383789 2727792720437230355768921)
                    ·
                      refine ⟨2045844540327922766826691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727792720437230355768921 2045844540327922766826691)
                      ·
                        rfl

theorem cell23_3984268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_3984268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984268 prefixEnd_3984268 := by exact prefixLift 3984268
  have htrace : WordTrace (prefixWord ++ tailWord_3984268) baseStart_3984268 baseEnd_3984268 := by
    simpa [prefixWord, tailWord_3984268, baseEnd_3984268] using wordTrace_append hprefix tailTrace_3984268
  have hstable : (prefixWord ++ tailWord_3984268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984268).length < 2 ^ (prefixWord ++ tailWord_3984268).sum := by decide
  have hdescent : baseEnd_3984268 < baseStart_3984268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984285 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3984285 : Nat := 118140960795 + 3984285 * 2 ^ 59
def prefixEnd_3984285 : Nat := 4983230072969 + 3 ^ 40 * 3984285 * 2
def baseEnd_3984285 : Nat := 2045853269499049200314113

theorem tailTrace_3984285 : CollatzResearch.WordTrace tailWord_3984285 prefixEnd_3984285 2045853269499049200314113 := by
  unfold tailWord_3984285
  simp only [CollatzResearch.WordTrace]
  refine ⟨145318812370623381548786309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96879208247082254365857539 145318812370623381548786309)
  ·
    refine ⟨27247277319491884040397433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145318812370623381548786309 27247277319491884040397433)
    ·
      refine ⟨20435457989618913030298075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27247277319491884040397433 20435457989618913030298075)
      ·
        refine ⟨30653186984428369545447113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435457989618913030298075 30653186984428369545447113)
        ·
          refine ⟨22989890238321277159085335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30653186984428369545447113 22989890238321277159085335)
          ·
            refine ⟨34484835357481915738628003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22989890238321277159085335 34484835357481915738628003)
            ·
              refine ⟨51727253036222873607942005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34484835357481915738628003 51727253036222873607942005)
              ·
                refine ⟨4849429972145894400744563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51727253036222873607942005 4849429972145894400744563)
                ·
                  refine ⟨7274144958218841601116845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849429972145894400744563 7274144958218841601116845)
                  ·
                    refine ⟨2727804359332065600418817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7274144958218841601116845 2727804359332065600418817)
                    ·
                      refine ⟨2045853269499049200314113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727804359332065600418817 2045853269499049200314113)
                      ·
                        rfl

theorem cell23_3984285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3984285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984285 prefixEnd_3984285 := by exact prefixLift 3984285
  have htrace : WordTrace (prefixWord ++ tailWord_3984285) baseStart_3984285 baseEnd_3984285 := by
    simpa [prefixWord, tailWord_3984285, baseEnd_3984285] using wordTrace_append hprefix tailTrace_3984285
  have hstable : (prefixWord ++ tailWord_3984285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984285).length < 2 ^ (prefixWord ++ tailWord_3984285).sum := by decide
  have hdescent : baseEnd_3984285 < baseStart_3984285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984311 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3984311 : Nat := 118140960795 + 3984311 * 2 ^ 59
def prefixEnd_3984311 : Nat := 4983230072969 + 3 ^ 40 * 3984311 * 2
def baseEnd_3984311 : Nat := 2045866619996066098588993

theorem tailTrace_3984311 : CollatzResearch.WordTrace tailWord_3984311 prefixEnd_3984311 2045866619996066098588993 := by
  unfold tailWord_3984311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145319760668529187989232787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96879840445686125326155191 145319760668529187989232787)
  ·
    refine ⟨217979641002793781983849181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145319760668529187989232787 217979641002793781983849181)
    ·
      refine ⟨81742365376047668243943443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217979641002793781983849181 81742365376047668243943443)
      ·
        refine ⟨122613548064071502365915165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81742365376047668243943443 122613548064071502365915165)
        ·
          refine ⟨45980080524026813387218187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122613548064071502365915165 45980080524026813387218187)
          ·
            refine ⟨68970120786040220080827281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45980080524026813387218187 68970120786040220080827281)
            ·
              refine ⟨51727590589530165060620461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68970120786040220080827281 51727590589530165060620461)
              ·
                refine ⟨19397846471073811897732673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51727590589530165060620461 19397846471073811897732673)
                ·
                  refine ⟨14548384853305358923299505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19397846471073811897732673 14548384853305358923299505)
                  ·
                    refine ⟨10911288639979019192474629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14548384853305358923299505 10911288639979019192474629)
                    ·
                      refine ⟨2045866619996066098588993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10911288639979019192474629 2045866619996066098588993)
                      ·
                        rfl

theorem cell23_3984311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3984311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984311 prefixEnd_3984311 := by exact prefixLift 3984311
  have htrace : WordTrace (prefixWord ++ tailWord_3984311) baseStart_3984311 baseEnd_3984311 := by
    simpa [prefixWord, tailWord_3984311, baseEnd_3984311] using wordTrace_append hprefix tailTrace_3984311
  have hstable : (prefixWord ++ tailWord_3984311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984311).length < 2 ^ (prefixWord ++ tailWord_3984311).sum := by decide
  have hdescent : baseEnd_3984311 < baseStart_3984311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984326 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3984326 : Nat := 118140960795 + 3984326 * 2 ^ 59
def prefixEnd_3984326 : Nat := 4983230072969 + 3 ^ 40 * 3984326 * 2
def baseEnd_3984326 : Nat := 2045874322205883539901425

theorem tailTrace_3984326 : CollatzResearch.WordTrace tailWord_3984326 prefixEnd_3984326 2045874322205883539901425 := by
  unfold tailWord_3984326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541259617608588923469651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96880205175649897034019221 4541259617608588923469651)
  ·
    refine ⟨6811889426412883385204477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4541259617608588923469651 6811889426412883385204477)
    ·
      refine ⟨2554458534904831269451679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6811889426412883385204477 2554458534904831269451679)
      ·
        refine ⟨3831687802357246904177519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554458534904831269451679 3831687802357246904177519)
        ·
          refine ⟨5747531703535870356266279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831687802357246904177519 5747531703535870356266279)
          ·
            refine ⟨8621297555303805534399419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747531703535870356266279 8621297555303805534399419)
            ·
              refine ⟨12931946332955708301599129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621297555303805534399419 12931946332955708301599129)
              ·
                refine ⟨9698959749716781226199347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12931946332955708301599129 9698959749716781226199347)
                ·
                  refine ⟨14548439624575171839299021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698959749716781226199347 14548439624575171839299021)
                  ·
                    refine ⟨5455664859215689439737133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14548439624575171839299021 5455664859215689439737133)
                    ·
                      refine ⟨2045874322205883539901425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5455664859215689439737133 2045874322205883539901425)
                      ·
                        rfl

theorem cell23_3984326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3984326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984326 prefixEnd_3984326 := by exact prefixLift 3984326
  have htrace : WordTrace (prefixWord ++ tailWord_3984326) baseStart_3984326 baseEnd_3984326 := by
    simpa [prefixWord, tailWord_3984326, baseEnd_3984326] using wordTrace_append hprefix tailTrace_3984326
  have hstable : (prefixWord ++ tailWord_3984326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984326).length < 2 ^ (prefixWord ++ tailWord_3984326).sum := by decide
  have hdescent : baseEnd_3984326 < baseStart_3984326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984349 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3984349 : Nat := 118140960795 + 3984349 * 2 ^ 59
def prefixEnd_3984349 : Nat := 4983230072969 + 3 ^ 40 * 3984349 * 2
def baseEnd_3984349 : Nat := 2045886132260936949913819

theorem tailTrace_3984349 : CollatzResearch.WordTrace tailWord_3984349 prefixEnd_3984349 2045886132260936949913819 := by
  unfold tailWord_3984349
  simp only [CollatzResearch.WordTrace]
  refine ⟨145321146642391520479116101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96880764428261013652744067 145321146642391520479116101)
  ·
    refine ⟨27247714995448410089834269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145321146642391520479116101 27247714995448410089834269)
    ·
      refine ⟨10217893123293153783687851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27247714995448410089834269 10217893123293153783687851)
      ·
        refine ⟨15326839684939730675531777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10217893123293153783687851 15326839684939730675531777)
        ·
          refine ⟨11495129763704798006648833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15326839684939730675531777 11495129763704798006648833)
          ·
            refine ⟨8621347322778598504986625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11495129763704798006648833 8621347322778598504986625)
            ·
              refine ⟨6466010492083948878739969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8621347322778598504986625 6466010492083948878739969)
              ·
                refine ⟨4849507869062961659054977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466010492083948878739969 4849507869062961659054977)
                ·
                  refine ⟨3637130901797221244291233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4849507869062961659054977 3637130901797221244291233)
                  ·
                    refine ⟨2727848176347915933218425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637130901797221244291233 2727848176347915933218425)
                    ·
                      refine ⟨2045886132260936949913819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727848176347915933218425 2045886132260936949913819)
                      ·
                        rfl

theorem cell23_3984349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3984349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984349 prefixEnd_3984349 := by exact prefixLift 3984349
  have htrace : WordTrace (prefixWord ++ tailWord_3984349) baseStart_3984349 baseEnd_3984349 := by
    simpa [prefixWord, tailWord_3984349, baseEnd_3984349] using wordTrace_append hprefix tailTrace_3984349
  have hstable : (prefixWord ++ tailWord_3984349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984349).length < 2 ^ (prefixWord ++ tailWord_3984349).sum := by decide
  have hdescent : baseEnd_3984349 < baseStart_3984349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984385 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3984385 : Nat := 118140960795 + 3984385 * 2 ^ 59
def prefixEnd_3984385 : Nat := 4983230072969 + 3 ^ 40 * 3984385 * 2
def baseEnd_3984385 : Nat := 681968205854832936354551

theorem tailTrace_3984385 : CollatzResearch.WordTrace tailWord_3984385 prefixEnd_3984385 681968205854832936354551 := by
  unfold tailWord_3984385
  simp only [CollatzResearch.WordTrace]
  refine ⟨145322459670261098627426609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96881639780174065751617739 145322459670261098627426609)
  ·
    refine ⟨108991844752695823970569957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145322459670261098627426609 108991844752695823970569957)
    ·
      refine ⟨20435970891130466994481867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108991844752695823970569957 20435970891130466994481867)
      ·
        refine ⟨30653956336695700491722801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435970891130466994481867 30653956336695700491722801)
        ·
          refine ⟨22990467252521775368792101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30653956336695700491722801 22990467252521775368792101)
          ·
            refine ⟨4310712609847832881648519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22990467252521775368792101 4310712609847832881648519)
            ·
              refine ⟨6466068914771749322472779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310712609847832881648519 6466068914771749322472779)
              ·
                refine ⟨9699103372157623983709169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466068914771749322472779 9699103372157623983709169)
                ·
                  refine ⟨7274327529118217987781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699103372157623983709169 7274327529118217987781877)
                  ·
                    refine ⟨681968205854832936354551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7274327529118217987781877 681968205854832936354551)
                    ·
                      rfl

theorem cell23_3984385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3984385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984385 prefixEnd_3984385 := by exact prefixLift 3984385
  have htrace : WordTrace (prefixWord ++ tailWord_3984385) baseStart_3984385 baseEnd_3984385 := by
    simpa [prefixWord, tailWord_3984385, baseEnd_3984385] using wordTrace_append hprefix tailTrace_3984385
  have hstable : (prefixWord ++ tailWord_3984385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984385).length < 2 ^ (prefixWord ++ tailWord_3984385).sum := by decide
  have hdescent : baseEnd_3984385 < baseStart_3984385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984401 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_3984401 : Nat := 118140960795 + 3984401 * 2 ^ 59
def prefixEnd_3984401 : Nat := 4983230072969 + 3 ^ 40 * 3984401 * 2
def baseEnd_3984401 : Nat := 2045912833254970746463579

theorem tailTrace_3984401 : CollatzResearch.WordTrace tailWord_3984401 prefixEnd_3984401 2045912833254970746463579 := by
  unfold tailWord_3984401
  simp only [CollatzResearch.WordTrace]
  refine ⟨145323043238203133360009057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96882028825468755573339371 145323043238203133360009057)
  ·
    refine ⟨108992282428652350020006793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145323043238203133360009057 108992282428652350020006793)
    ·
      refine ⟨81744211821489262515005095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108992282428652350020006793 81744211821489262515005095)
      ·
        refine ⟨122616317732233893772507643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81744211821489262515005095 122616317732233893772507643)
        ·
          refine ⟨183924476598350840658761465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122616317732233893772507643 183924476598350840658761465)
          ·
            refine ⟨137943357448763130494071099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183924476598350840658761465 137943357448763130494071099)
            ·
              refine ⟨206915036173144695741106649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137943357448763130494071099 206915036173144695741106649)
              ·
                refine ⟨155186277129858521805829987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206915036173144695741106649 155186277129858521805829987)
                ·
                  refine ⟨232779415694787782708744981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155186277129858521805829987 232779415694787782708744981)
                  ·
                    refine ⟨10911535110693177314472421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232779415694787782708744981 10911535110693177314472421)
                    ·
                      refine ⟨2045912833254970746463579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10911535110693177314472421 2045912833254970746463579)
                      ·
                        rfl

theorem cell23_3984401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_3984401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984401 prefixEnd_3984401 := by exact prefixLift 3984401
  have htrace : WordTrace (prefixWord ++ tailWord_3984401) baseStart_3984401 baseEnd_3984401 := by
    simpa [prefixWord, tailWord_3984401, baseEnd_3984401] using wordTrace_append hprefix tailTrace_3984401
  have hstable : (prefixWord ++ tailWord_3984401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984401).length < 2 ^ (prefixWord ++ tailWord_3984401).sum := by decide
  have hdescent : baseEnd_3984401 < baseStart_3984401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984405 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_3984405 : Nat := 118140960795 + 3984405 * 2 ^ 59
def prefixEnd_3984405 : Nat := 4983230072969 + 3 ^ 40 * 3984405 * 2
def baseEnd_3984405 : Nat := 2045914887177588730813561

theorem tailTrace_3984405 : CollatzResearch.WordTrace tailWord_3984405 prefixEnd_3984405 2045914887177588730813561 := by
  unfold tailWord_3984405
  simp only [CollatzResearch.WordTrace]
  refine ⟨145323189130188642043154669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96882126086792428028769779 145323189130188642043154669)
  ·
    refine ⟨54496195923820740766183001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145323189130188642043154669 54496195923820740766183001)
    ·
      refine ⟨40872146942865555574637251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54496195923820740766183001 40872146942865555574637251)
      ·
        refine ⟨61308220414298333361955877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40872146942865555574637251 61308220414298333361955877)
        ·
          refine ⟨11495291327680937505366727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61308220414298333361955877 11495291327680937505366727)
          ·
            refine ⟨17242936991521406258050091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495291327680937505366727 17242936991521406258050091)
            ·
              refine ⟨25864405487282109387075137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242936991521406258050091 25864405487282109387075137)
              ·
                refine ⟨19398304115461582040306353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25864405487282109387075137 19398304115461582040306353)
                ·
                  refine ⟨14548728086596186530229765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19398304115461582040306353 14548728086596186530229765)
                  ·
                    refine ⟨2727886516236784974418081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14548728086596186530229765 2727886516236784974418081)
                    ·
                      refine ⟨2045914887177588730813561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727886516236784974418081 2045914887177588730813561)
                      ·
                        rfl

theorem cell23_3984405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_3984405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984405 prefixEnd_3984405 := by exact prefixLift 3984405
  have htrace : WordTrace (prefixWord ++ tailWord_3984405) baseStart_3984405 baseEnd_3984405 := by
    simpa [prefixWord, tailWord_3984405, baseEnd_3984405] using wordTrace_append hprefix tailTrace_3984405
  have hstable : (prefixWord ++ tailWord_3984405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984405).length < 2 ^ (prefixWord ++ tailWord_3984405).sum := by decide
  have hdescent : baseEnd_3984405 < baseStart_3984405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984415 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 3, 4]
def baseStart_3984415 : Nat := 118140960795 + 3984415 * 2 ^ 59
def prefixEnd_3984415 : Nat := 4983230072969 + 3 ^ 40 * 3984415 * 2
def baseEnd_3984415 : Nat := 681973340661377897229505

theorem tailTrace_3984415 : CollatzResearch.WordTrace tailWord_3984415 prefixEnd_3984415 681973340661377897229505 := by
  unfold tailWord_3984415
  simp only [CollatzResearch.WordTrace]
  refine ⟨145323553860152413751018699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96882369240101609167345799 145323553860152413751018699)
  ·
    refine ⟨217985330790228620626528049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145323553860152413751018699 217985330790228620626528049)
    ·
      refine ⟨163488998092671465469896037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217985330790228620626528049 163488998092671465469896037)
      ·
        refine ⟨30654187142375899775605507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163488998092671465469896037 30654187142375899775605507)
        ·
          refine ⟨45981280713563849663408261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30654187142375899775605507 45981280713563849663408261)
          ·
            refine ⟨8621490133793221811889049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45981280713563849663408261 8621490133793221811889049)
            ·
              refine ⟨6466117600344916358916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8621490133793221811889049 6466117600344916358916787)
              ·
                refine ⟨9699176400517374538375181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466117600344916358916787 9699176400517374538375181)
                ·
                  refine ⟨3637191150194015451890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699176400517374538375181 3637191150194015451890693)
                  ·
                    refine ⟨681973340661377897229505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637191150194015451890693 681973340661377897229505)
                    ·
                      rfl

theorem cell23_3984415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_3984415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984415 prefixEnd_3984415 := by exact prefixLift 3984415
  have htrace : WordTrace (prefixWord ++ tailWord_3984415) baseStart_3984415 baseEnd_3984415 := by
    simpa [prefixWord, tailWord_3984415, baseEnd_3984415] using wordTrace_append hprefix tailTrace_3984415
  have hstable : (prefixWord ++ tailWord_3984415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984415).length < 2 ^ (prefixWord ++ tailWord_3984415).sum := by decide
  have hdescent : baseEnd_3984415 < baseStart_3984415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984465 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_3984465 : Nat := 118140960795 + 3984465 * 2 ^ 59
def prefixEnd_3984465 : Nat := 4983230072969 + 3 ^ 40 * 3984465 * 2
def baseEnd_3984465 : Nat := 2045945696016858496063285

theorem tailTrace_3984465 : CollatzResearch.WordTrace tailWord_3984465 prefixEnd_3984465 2045945696016858496063285 := by
  unfold tailWord_3984465
  simp only [CollatzResearch.WordTrace]
  refine ⟨145325377509971272290338849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96883585006647514860225899 145325377509971272290338849)
  ·
    refine ⟨108994033132478454217754137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145325377509971272290338849 108994033132478454217754137)
    ·
      refine ⟨81745524849358840663315603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108994033132478454217754137 81745524849358840663315603)
      ·
        refine ⟨122618287274038260994973405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81745524849358840663315603 122618287274038260994973405)
        ·
          refine ⟨45981857727764347873115027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122618287274038260994973405 45981857727764347873115027)
          ·
            refine ⟨68972786591646521809672541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981857727764347873115027 68972786591646521809672541)
            ·
              refine ⟨25864794971867445678627203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68972786591646521809672541 25864794971867445678627203)
              ·
                refine ⟨38797192457801168517940805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864794971867445678627203 38797192457801168517940805)
                ·
                  refine ⟨7274473585837719097113901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38797192457801168517940805 7274473585837719097113901)
                  ·
                    refine ⟨2727927594689144661417713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7274473585837719097113901 2727927594689144661417713)
                    ·
                      refine ⟨2045945696016858496063285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727927594689144661417713 2045945696016858496063285)
                      ·
                        rfl

theorem cell23_3984465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_3984465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984465 prefixEnd_3984465 := by exact prefixLift 3984465
  have htrace : WordTrace (prefixWord ++ tailWord_3984465) baseStart_3984465 baseEnd_3984465 := by
    simpa [prefixWord, tailWord_3984465, baseEnd_3984465] using wordTrace_append hprefix tailTrace_3984465
  have hstable : (prefixWord ++ tailWord_3984465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984465).length < 2 ^ (prefixWord ++ tailWord_3984465).sum := by decide
  have hdescent : baseEnd_3984465 < baseStart_3984465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984505 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_3984505 : Nat := 118140960795 + 3984505 * 2 ^ 59
def prefixEnd_3984505 : Nat := 4983230072969 + 3 ^ 40 * 3984505 * 2
def baseEnd_3984505 : Nat := 681988745081012779854367

theorem tailTrace_3984505 : CollatzResearch.WordTrace tailWord_3984505 prefixEnd_3984505 681988745081012779854367 := by
  unfold tailWord_3984505
  simp only [CollatzResearch.WordTrace]
  refine ⟨145326836429826359121794969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96884557619884239414529979 145326836429826359121794969)
  ·
    refine ⟨108995127322369769341346227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145326836429826359121794969 108995127322369769341346227)
    ·
      refine ⟨163492690983554654012019341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108995127322369769341346227 163492690983554654012019341)
      ·
        refine ⟨61309759118832995254507253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163492690983554654012019341 61309759118832995254507253)
        ·
          refine ⟨5747789917390593305110055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61309759118832995254507253 5747789917390593305110055)
          ·
            refine ⟨8621684876085889957665083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747789917390593305110055 8621684876085889957665083)
            ·
              refine ⟨12932527314128834936497625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621684876085889957665083 12932527314128834936497625)
              ·
                refine ⟨9699395485596626202373219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932527314128834936497625 9699395485596626202373219)
                ·
                  refine ⟨14549093228394939303559829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699395485596626202373219 14549093228394939303559829)
                  ·
                    refine ⟨681988745081012779854367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14549093228394939303559829 681988745081012779854367)
                    ·
                      rfl

theorem cell23_3984505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_3984505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984505 prefixEnd_3984505 := by exact prefixLift 3984505
  have htrace : WordTrace (prefixWord ++ tailWord_3984505) baseStart_3984505 baseEnd_3984505 := by
    simpa [prefixWord, tailWord_3984505, baseEnd_3984505] using wordTrace_append hprefix tailTrace_3984505
  have hstable : (prefixWord ++ tailWord_3984505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984505).length < 2 ^ (prefixWord ++ tailWord_3984505).sum := by decide
  have hdescent : baseEnd_3984505 < baseStart_3984505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984522 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_3984522 : Nat := 118140960795 + 3984522 * 2 ^ 59
def prefixEnd_3984522 : Nat := 4983230072969 + 3 ^ 40 * 3984522 * 2
def baseEnd_3984522 : Nat := 681991654804721591016841

theorem tailTrace_3984522 : CollatzResearch.WordTrace tailWord_3984522 prefixEnd_3984522 681991654804721591016841 := by
  unfold tailWord_3984522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331864117691192756290955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96884970980509847350109213 36331864117691192756290955)
  ·
    refine ⟨54497796176536789134436433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331864117691192756290955 54497796176536789134436433)
    ·
      refine ⟨40873347132402591850827325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54497796176536789134436433 40873347132402591850827325)
      ·
        refine ⟨15327505174650971944060247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40873347132402591850827325 15327505174650971944060247)
        ·
          refine ⟨22991257761976457916090371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15327505174650971944060247 22991257761976457916090371)
          ·
            refine ⟨34486886642964686874135557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22991257761976457916090371 34486886642964686874135557)
            ·
              refine ⟨6466291245555878788900417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34486886642964686874135557 6466291245555878788900417)
              ·
                refine ⟨4849718434166909091675313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466291245555878788900417 4849718434166909091675313)
                ·
                  refine ⟨3637288825625181818756485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4849718434166909091675313 3637288825625181818756485)
                  ·
                    refine ⟨681991654804721591016841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637288825625181818756485 681991654804721591016841)
                    ·
                      rfl

theorem cell23_3984522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_3984522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984522 prefixEnd_3984522 := by exact prefixLift 3984522
  have htrace : WordTrace (prefixWord ++ tailWord_3984522) baseStart_3984522 baseEnd_3984522 := by
    simpa [prefixWord, tailWord_3984522, baseEnd_3984522] using wordTrace_append hprefix tailTrace_3984522
  have hstable : (prefixWord ++ tailWord_3984522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984522).length < 2 ^ (prefixWord ++ tailWord_3984522).sum := by decide
  have hdescent : baseEnd_3984522 < baseStart_3984522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984535 : List Nat := [1, 1, 3, 3, 3, 3, 1, 8]
def baseStart_3984535 : Nat := 118140960795 + 3984535 * 2 ^ 59
def prefixEnd_3984535 : Nat := 4983230072969 + 3 ^ 40 * 3984535 * 2
def baseEnd_3984535 : Nat := 75777097765284193414369

theorem tailTrace_3984535 : CollatzResearch.WordTrace tailWord_3984535 prefixEnd_3984535 75777097765284193414369 := by
  unfold tailWord_3984535
  simp only [CollatzResearch.WordTrace]
  refine ⟨145327930619717674245387059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96885287079811782830258039 145327930619717674245387059)
  ·
    refine ⟨217991895929576511368080589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145327930619717674245387059 217991895929576511368080589)
    ·
      refine ⟨81746960973591191763030221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217991895929576511368080589 81746960973591191763030221)
      ·
        refine ⟨30655110365096696911136333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81746960973591191763030221 30655110365096696911136333)
        ·
          refine ⟨11495666386911261341676125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30655110365096696911136333 11495666386911261341676125)
          ·
            refine ⟨4310874895091723003128547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11495666386911261341676125 4310874895091723003128547)
            ·
              refine ⟨6466312342637584504692821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310874895091723003128547 6466312342637584504692821)
              ·
                refine ⟨75777097765284193414369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6466312342637584504692821 75777097765284193414369)
                ·
                  rfl

theorem cell23_3984535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 8].length) (baseStart_3984535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984535 prefixEnd_3984535 := by exact prefixLift 3984535
  have htrace : WordTrace (prefixWord ++ tailWord_3984535) baseStart_3984535 baseEnd_3984535 := by
    simpa [prefixWord, tailWord_3984535, baseEnd_3984535] using wordTrace_append hprefix tailTrace_3984535
  have hstable : (prefixWord ++ tailWord_3984535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984535).length < 2 ^ (prefixWord ++ tailWord_3984535).sum := by decide
  have hdescent : baseEnd_3984535 < baseStart_3984535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984542 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3984542 : Nat := 118140960795 + 3984542 * 2 ^ 59
def prefixEnd_3984542 : Nat := 4983230072969 + 3 ^ 40 * 3984542 * 2
def baseEnd_3984542 : Nat := 2045985234027254694800431

theorem tailTrace_3984542 : CollatzResearch.WordTrace tailWord_3984542 prefixEnd_3984542 2045985234027254694800431 := by
  unfold tailWord_3984542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166023241336539305111485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96885457287128209627261253 18166023241336539305111485)
  ·
    refine ⟨6812258715501202239416807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18166023241336539305111485 6812258715501202239416807)
    ·
      refine ⟨10218388073251803359125211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812258715501202239416807 10218388073251803359125211)
      ·
        refine ⟨15327582109877705038687817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10218388073251803359125211 15327582109877705038687817)
        ·
          refine ⟨11495686582408278779015863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15327582109877705038687817 11495686582408278779015863)
          ·
            refine ⟨17243529873612418168523795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495686582408278779015863 17243529873612418168523795)
            ·
              refine ⟨25865294810418627252785693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17243529873612418168523795 25865294810418627252785693)
              ·
                refine ⟨9699485553906985219794635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25865294810418627252785693 9699485553906985219794635)
                ·
                  refine ⟨14549228330860477829691953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699485553906985219794635 14549228330860477829691953)
                  ·
                    refine ⟨10911921248145358372268965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14549228330860477829691953 10911921248145358372268965)
                    ·
                      refine ⟨2045985234027254694800431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10911921248145358372268965 2045985234027254694800431)
                      ·
                        rfl

theorem cell23_3984542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3984542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984542 prefixEnd_3984542 := by exact prefixLift 3984542
  have htrace : WordTrace (prefixWord ++ tailWord_3984542) baseStart_3984542 baseEnd_3984542 := by
    simpa [prefixWord, tailWord_3984542, baseEnd_3984542] using wordTrace_append hprefix tailTrace_3984542
  have hstable : (prefixWord ++ tailWord_3984542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984542).length < 2 ^ (prefixWord ++ tailWord_3984542).sum := by decide
  have hdescent : baseEnd_3984542 < baseStart_3984542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984546 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3984546 : Nat := 118140960795 + 3984546 * 2 ^ 59
def prefixEnd_3984546 : Nat := 4983230072969 + 3 ^ 40 * 3984546 * 2
def baseEnd_3984546 : Nat := 2045987287949872679150413

theorem tailTrace_3984546 : CollatzResearch.WordTrace tailWord_3984546 prefixEnd_3984546 2045987287949872679150413 := by
  unfold tailWord_3984546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36332082955669455781009373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96885554548451882082691661 36332082955669455781009373)
  ·
    refine ⟨13624531108376045917878515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36332082955669455781009373 13624531108376045917878515)
    ·
      refine ⟨20436796662564068876817773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624531108376045917878515 20436796662564068876817773)
      ·
        refine ⟨7663798748461525828806665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20436796662564068876817773 7663798748461525828806665)
        ·
          refine ⟨5747849061346144371604999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663798748461525828806665 5747849061346144371604999)
          ·
            refine ⟨8621773592019216557407499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747849061346144371604999 8621773592019216557407499)
            ·
              refine ⟨12932660388028824836111249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621773592019216557407499 12932660388028824836111249)
              ·
                refine ⟨9699495291021618627083437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932660388028824836111249 9699495291021618627083437)
                ·
                  refine ⟨3637310734133106985156289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699495291021618627083437 3637310734133106985156289)
                  ·
                    refine ⟨2727983050599830238867217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637310734133106985156289 2727983050599830238867217)
                    ·
                      refine ⟨2045987287949872679150413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2727983050599830238867217 2045987287949872679150413)
                      ·
                        rfl

theorem cell23_3984546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3984546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984546 prefixEnd_3984546 := by exact prefixLift 3984546
  have htrace : WordTrace (prefixWord ++ tailWord_3984546) baseStart_3984546 baseEnd_3984546 := by
    simpa [prefixWord, tailWord_3984546, baseEnd_3984546] using wordTrace_append hprefix tailTrace_3984546
  have hstable : (prefixWord ++ tailWord_3984546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984546).length < 2 ^ (prefixWord ++ tailWord_3984546).sum := by decide
  have hdescent : baseEnd_3984546 < baseStart_3984546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984568 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_3984568 : Nat := 118140960795 + 3984568 * 2 ^ 59
def prefixEnd_3984568 : Nat := 4983230072969 + 3 ^ 40 * 3984568 * 2
def baseEnd_3984568 : Nat := 2045998584524271593075311

theorem tailTrace_3984568 : CollatzResearch.WordTrace tailWord_3984568 prefixEnd_3984568 2045998584524271593075311 := by
  unfold tailWord_3984568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72664567114299060440669179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96886089485732080587558905 72664567114299060440669179)
  ·
    refine ⟨108996850671448590661003769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72664567114299060440669179 108996850671448590661003769)
    ·
      refine ⟨81747638003586442995752827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108996850671448590661003769 81747638003586442995752827)
      ·
        refine ⟨122621457005379664493629241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81747638003586442995752827 122621457005379664493629241)
        ·
          refine ⟨91966092754034748370221931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122621457005379664493629241 91966092754034748370221931)
          ·
            refine ⟨137949139131052122555332897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91966092754034748370221931 137949139131052122555332897)
            ·
              refine ⟨103461854348289091916499673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137949139131052122555332897 103461854348289091916499673)
              ·
                refine ⟨77596390761216818937374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103461854348289091916499673 77596390761216818937374755)
                ·
                  refine ⟨116394586141825228406062133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77596390761216818937374755 116394586141825228406062133)
                  ·
                    refine ⟨10911992450796115163068325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116394586141825228406062133 10911992450796115163068325)
                    ·
                      refine ⟨2045998584524271593075311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10911992450796115163068325 2045998584524271593075311)
                      ·
                        rfl

theorem cell23_3984568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_3984568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984568 prefixEnd_3984568 := by exact prefixLift 3984568
  have htrace : WordTrace (prefixWord ++ tailWord_3984568) baseStart_3984568 baseEnd_3984568 := by
    simpa [prefixWord, tailWord_3984568, baseEnd_3984568] using wordTrace_append hprefix tailTrace_3984568
  have hstable : (prefixWord ++ tailWord_3984568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984568).length < 2 ^ (prefixWord ++ tailWord_3984568).sum := by decide
  have hdescent : baseEnd_3984568 < baseStart_3984568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984596 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3984596 : Nat := 118140960795 + 3984596 * 2 ^ 59
def prefixEnd_3984596 : Nat := 4983230072969 + 3 ^ 40 * 3984596 * 2
def baseEnd_3984596 : Nat := 2046012961982597483525183

theorem tailTrace_3984596 : CollatzResearch.WordTrace tailWord_3984596 prefixEnd_3984596 2046012961982597483525183 := by
  unfold tailWord_3984596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72665077736248340831678821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96886770314997787775571761 72665077736248340831678821)
  ·
    refine ⟨13624702075546563905939779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72665077736248340831678821 13624702075546563905939779)
    ·
      refine ⟨20437053113319845858909669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624702075546563905939779 20437053113319845858909669)
      ·
        refine ⟨3831947458747471098545563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20437053113319845858909669 3831947458747471098545563)
        ·
          refine ⟨5747921188121206647818345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831947458747471098545563 5747921188121206647818345)
          ·
            refine ⟨4310940891090904985863759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747921188121206647818345 4310940891090904985863759)
            ·
              refine ⟨6466411336636357478795639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310940891090904985863759 6466411336636357478795639)
              ·
                refine ⟨9699617004954536218193459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466411336636357478795639 9699617004954536218193459)
                ·
                  refine ⟨14549425507431804327290189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699617004954536218193459 14549425507431804327290189)
                  ·
                    refine ⟨5456034565286926622733821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14549425507431804327290189 5456034565286926622733821)
                    ·
                      refine ⟨2046012961982597483525183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456034565286926622733821 2046012961982597483525183)
                      ·
                        rfl

theorem cell23_3984596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3984596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984596 prefixEnd_3984596 := by exact prefixLift 3984596
  have htrace : WordTrace (prefixWord ++ tailWord_3984596) baseStart_3984596 baseEnd_3984596 := by
    simpa [prefixWord, tailWord_3984596, baseEnd_3984596] using wordTrace_append hprefix tailTrace_3984596
  have hstable : (prefixWord ++ tailWord_3984596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984596).length < 2 ^ (prefixWord ++ tailWord_3984596).sum := by decide
  have hdescent : baseEnd_3984596 < baseStart_3984596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984682 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3984682 : Nat := 118140960795 + 3984682 * 2 ^ 59
def prefixEnd_3984682 : Nat := 4983230072969 + 3 ^ 40 * 3984682 * 2
def baseEnd_3984682 : Nat := 2046057121318884147049787

theorem tailTrace_3984682 : CollatzResearch.WordTrace tailWord_3984682 prefixEnd_3984682 2046057121318884147049787 := by
  unfold tailWord_3984682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333323037546279587747075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96888861433456745567325533 36333323037546279587747075)
  ·
    refine ⟨54499984556319419381620613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36333323037546279587747075 54499984556319419381620613)
    ·
      refine ⟨10218747104309891134053865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54499984556319419381620613 10218747104309891134053865)
      ·
        refine ⟨7664060328232418350540399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10218747104309891134053865 7664060328232418350540399)
        ·
          refine ⟨11496090492348627525810599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664060328232418350540399 11496090492348627525810599)
          ·
            refine ⟨17244135738522941288715899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496090492348627525810599 17244135738522941288715899)
            ·
              refine ⟨25866203607784411933073849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244135738522941288715899 25866203607784411933073849)
              ·
                refine ⟨19399652705838308949805387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25866203607784411933073849 19399652705838308949805387)
                ·
                  refine ⟨29099479058757463424708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19399652705838308949805387 29099479058757463424708081)
                  ·
                    refine ⟨21824609294068097568531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29099479058757463424708081 21824609294068097568531061)
                    ·
                      refine ⟨2046057121318884147049787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21824609294068097568531061 2046057121318884147049787)
                      ·
                        rfl

theorem cell23_3984682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3984682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984682 prefixEnd_3984682 := by exact prefixLift 3984682
  have htrace : WordTrace (prefixWord ++ tailWord_3984682) baseStart_3984682 baseEnd_3984682 := by
    simpa [prefixWord, tailWord_3984682, baseEnd_3984682] using wordTrace_append hprefix tailTrace_3984682
  have hstable : (prefixWord ++ tailWord_3984682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984682).length < 2 ^ (prefixWord ++ tailWord_3984682).sum := by decide
  have hdescent : baseEnd_3984682 < baseStart_3984682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984695 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_3984695 : Nat := 118140960795 + 3984695 * 2 ^ 59
def prefixEnd_3984695 : Nat := 4983230072969 + 3 ^ 40 * 3984695 * 2
def baseEnd_3984695 : Nat := 2046063796567392596187227

theorem tailTrace_3984695 : CollatzResearch.WordTrace tailWord_3984695 prefixEnd_3984695 2046063796567392596187227 := by
  unfold tailWord_3984695
  simp only [CollatzResearch.WordTrace]
  refine ⟨145333766299138021571211539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96889177532758681047474359 145333766299138021571211539)
  ·
    refine ⟨218000649448707032356817309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145333766299138021571211539 218000649448707032356817309)
    ·
      refine ⟨81750243543265137133806491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218000649448707032356817309 81750243543265137133806491)
      ·
        refine ⟨122625365314897705700709737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81750243543265137133806491 122625365314897705700709737)
        ·
          refine ⟨91969023986173279275532303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122625365314897705700709737 91969023986173279275532303)
          ·
            refine ⟨137953535979259918913298455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91969023986173279275532303 137953535979259918913298455)
            ·
              refine ⟨206930303968889878369947683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137953535979259918913298455 206930303968889878369947683)
              ·
                refine ⟨310395455953334817554921525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206930303968889878369947683 310395455953334817554921525)
                ·
                  refine ⟨29099573995625139145773893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310395455953334817554921525 29099573995625139145773893)
                  ·
                    refine ⟨5456170124179713589832605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29099573995625139145773893 5456170124179713589832605)
                    ·
                      refine ⟨2046063796567392596187227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456170124179713589832605 2046063796567392596187227)
                      ·
                        rfl

theorem cell23_3984695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_3984695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984695 prefixEnd_3984695 := by exact prefixLift 3984695
  have htrace : WordTrace (prefixWord ++ tailWord_3984695) baseStart_3984695 baseEnd_3984695 := by
    simpa [prefixWord, tailWord_3984695, baseEnd_3984695] using wordTrace_append hprefix tailTrace_3984695
  have hstable : (prefixWord ++ tailWord_3984695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984695).length < 2 ^ (prefixWord ++ tailWord_3984695).sum := by decide
  have hdescent : baseEnd_3984695 < baseStart_3984695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984736 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 1, 4]
def baseStart_3984736 : Nat := 118140960795 + 3984736 * 2 ^ 59
def prefixEnd_3984736 : Nat := 4983230072969 + 3 ^ 40 * 3984736 * 2
def baseEnd_3984736 : Nat := 682028283091408978591513

theorem tailTrace_3984736 : CollatzResearch.WordTrace tailWord_3984736 prefixEnd_3984736 682028283091408978591513 := by
  unfold tailWord_3984736
  simp only [CollatzResearch.WordTrace]
  refine ⟨72667630845994742786727031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96890174461326323715636041 72667630845994742786727031)
  ·
    refine ⟨109001446268992114180090547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72667630845994742786727031 109001446268992114180090547)
    ·
      refine ⟨163502169403488171270135821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109001446268992114180090547 163502169403488171270135821)
      ·
        refine ⟨61313313526308064226300933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163502169403488171270135821 61313313526308064226300933)
        ·
          refine ⟨11496246286182762042431425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61313313526308064226300933 11496246286182762042431425)
          ·
            refine ⟨8622184714637071531823569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11496246286182762042431425 8622184714637071531823569)
            ·
              refine ⟨6466638535977803648867677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622184714637071531823569 6466638535977803648867677)
              ·
                refine ⟨2424989450991676368325379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6466638535977803648867677 2424989450991676368325379)
                ·
                  refine ⟨3637484176487514552488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424989450991676368325379 3637484176487514552488069)
                  ·
                    refine ⟨682028283091408978591513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637484176487514552488069 682028283091408978591513)
                    ·
                      rfl

theorem cell23_3984736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_3984736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984736 prefixEnd_3984736 := by exact prefixLift 3984736
  have htrace : WordTrace (prefixWord ++ tailWord_3984736) baseStart_3984736 baseEnd_3984736 := by
    simpa [prefixWord, tailWord_3984736, baseEnd_3984736] using wordTrace_append hprefix tailTrace_3984736
  have hstable : (prefixWord ++ tailWord_3984736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984736).length < 2 ^ (prefixWord ++ tailWord_3984736).sum := by decide
  have hdescent : baseEnd_3984736 < baseStart_3984736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984745 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_3984745 : Nat := 118140960795 + 3984745 * 2 ^ 59
def prefixEnd_3984745 : Nat := 4983230072969 + 3 ^ 40 * 3984745 * 2
def baseEnd_3984745 : Nat := 682029823533372466853999

theorem tailTrace_3984745 : CollatzResearch.WordTrace tailWord_3984745 prefixEnd_3984745 682029823533372466853999 := by
  unfold tailWord_3984745
  simp only [CollatzResearch.WordTrace]
  refine ⟨145335589948956880110531689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96890393299304586740354459 145335589948956880110531689)
  ·
    refine ⟨109001692461717660082898767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145335589948956880110531689 109001692461717660082898767)
    ·
      refine ⟨163502538692576490124348151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109001692461717660082898767 163502538692576490124348151)
      ·
        refine ⟨245253808038864735186522227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163502538692576490124348151 245253808038864735186522227)
        ·
          refine ⟨367880712058297102779783341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245253808038864735186522227 367880712058297102779783341)
          ·
            refine ⟨137955267021861413542418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367880712058297102779783341 137955267021861413542418753)
            ·
              refine ⟨103466450266396060156814065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137955267021861413542418753 103466450266396060156814065)
              ·
                refine ⟨77599837699797045117610549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103466450266396060156814065 77599837699797045117610549)
                ·
                  refine ⟨7274984784355972979775989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77599837699797045117610549 7274984784355972979775989)
                  ·
                    refine ⟨682029823533372466853999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7274984784355972979775989 682029823533372466853999)
                    ·
                      rfl

theorem cell23_3984745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_3984745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984745 prefixEnd_3984745 := by exact prefixLift 3984745
  have htrace : WordTrace (prefixWord ++ tailWord_3984745) baseStart_3984745 baseEnd_3984745 := by
    simpa [prefixWord, tailWord_3984745, baseEnd_3984745] using wordTrace_append hprefix tailTrace_3984745
  have hstable : (prefixWord ++ tailWord_3984745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984745).length < 2 ^ (prefixWord ++ tailWord_3984745).sum := by decide
  have hdescent : baseEnd_3984745 < baseStart_3984745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984749 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3984749 : Nat := 118140960795 + 3984749 * 2 ^ 59
def prefixEnd_3984749 : Nat := 4983230072969 + 3 ^ 40 * 3984749 * 2
def baseEnd_3984749 : Nat := 227343502724748376101331

theorem tailTrace_3984749 : CollatzResearch.WordTrace tailWord_3984749 prefixEnd_3984749 227343502724748376101331 := by
  unfold tailWord_3984749
  simp only [CollatzResearch.WordTrace]
  refine ⟨145335735840942388793677301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96890490560628259195784867 145335735840942388793677301)
  ·
    refine ⟨13625225235088348949407247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145335735840942388793677301 13625225235088348949407247)
    ·
      refine ⟨20437837852632523424110871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625225235088348949407247 20437837852632523424110871)
      ·
        refine ⟨30656756778948785136166307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20437837852632523424110871 30656756778948785136166307)
        ·
          refine ⟨45985135168423177704249461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30656756778948785136166307 45985135168423177704249461)
          ·
            refine ⟨4311106422039672909773387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45985135168423177704249461 4311106422039672909773387)
            ·
              refine ⟨6466659633059509364660081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311106422039672909773387 6466659633059509364660081)
              ·
                refine ⟨4849994724794632023495061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466659633059509364660081 4849994724794632023495061)
                ·
                  refine ⟨227343502724748376101331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4849994724794632023495061 227343502724748376101331)
                  ·
                    rfl

theorem cell23_3984749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3984749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984749 prefixEnd_3984749 := by exact prefixLift 3984749
  have htrace : WordTrace (prefixWord ++ tailWord_3984749) baseStart_3984749 baseEnd_3984749 := by
    simpa [prefixWord, tailWord_3984749, baseEnd_3984749] using wordTrace_append hprefix tailTrace_3984749
  have hstable : (prefixWord ++ tailWord_3984749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984749).length < 2 ^ (prefixWord ++ tailWord_3984749).sum := by decide
  have hdescent : baseEnd_3984749 < baseStart_3984749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984759 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_3984759 : Nat := 118140960795 + 3984759 * 2 ^ 59
def prefixEnd_3984759 : Nat := 4983230072969 + 3 ^ 40 * 3984759 * 2
def baseEnd_3984759 : Nat := 2046096659329280345786933

theorem tailTrace_3984759 : CollatzResearch.WordTrace tailWord_3984759 prefixEnd_3984759 2046096659329280345786933 := by
  unfold tailWord_3984759
  simp only [CollatzResearch.WordTrace]
  refine ⟨145336100570906160501541331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96890733713937440334360887 145336100570906160501541331)
  ·
    refine ⟨218004150856359240752311997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145336100570906160501541331 218004150856359240752311997)
    ·
      refine ⟨81751556571134715282116999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218004150856359240752311997 81751556571134715282116999)
      ·
        refine ⟨122627334856702072923175499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81751556571134715282116999 122627334856702072923175499)
        ·
          refine ⟨183941002285053109384763249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122627334856702072923175499 183941002285053109384763249)
          ·
            refine ⟨137955751713789832038572437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183941002285053109384763249 137955751713789832038572437)
            ·
              refine ⟨6466675861583898376808083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137955751713789832038572437 6466675861583898376808083)
              ·
                refine ⟨9700013792375847565212125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466675861583898376808083 9700013792375847565212125)
                ·
                  refine ⟨3637505172140942836954547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9700013792375847565212125 3637505172140942836954547)
                  ·
                    refine ⟨5456257758211414255431821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637505172140942836954547 5456257758211414255431821)
                    ·
                      refine ⟨2046096659329280345786933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456257758211414255431821 2046096659329280345786933)
                      ·
                        rfl

theorem cell23_3984759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_3984759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984759 prefixEnd_3984759 := by exact prefixLift 3984759
  have htrace : WordTrace (prefixWord ++ tailWord_3984759) baseStart_3984759 baseEnd_3984759 := by
    simpa [prefixWord, tailWord_3984759, baseEnd_3984759] using wordTrace_append hprefix tailTrace_3984759
  have hstable : (prefixWord ++ tailWord_3984759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984759).length < 2 ^ (prefixWord ++ tailWord_3984759).sum := by decide
  have hdescent : baseEnd_3984759 < baseStart_3984759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984793 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 1, 1, 3]
def baseStart_3984793 : Nat := 118140960795 + 3984793 * 2 ^ 59
def prefixEnd_3984793 : Nat := 4983230072969 + 3 ^ 40 * 3984793 * 2
def baseEnd_3984793 : Nat := 2046114117671533212761777

theorem tailTrace_3984793 : CollatzResearch.WordTrace tailWord_3984793 prefixEnd_3984793 2046114117671533212761777 := by
  unfold tailWord_3984793
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337340652782984308279033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96891560435188656205519355 145337340652782984308279033)
  ·
    refine ⟨109003005489587238231209275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145337340652782984308279033 109003005489587238231209275)
    ·
      refine ⟨163504508234380857346813913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109003005489587238231209275 163504508234380857346813913)
      ·
        refine ⟨122628381175785643010110435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163504508234380857346813913 122628381175785643010110435)
        ·
          refine ⟨183942571763678464515165653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122628381175785643010110435 183942571763678464515165653)
          ·
            refine ⟨4311154025711214012074195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 183942571763678464515165653 4311154025711214012074195)
            ·
              refine ⟨6466731038566821018111293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311154025711214012074195 6466731038566821018111293)
              ·
                refine ⟨2425024139462557881791735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6466731038566821018111293 2425024139462557881791735)
                ·
                  refine ⟨3637536209193836822687603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425024139462557881791735 3637536209193836822687603)
                  ·
                    refine ⟨5456304313790755234031405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637536209193836822687603 5456304313790755234031405)
                    ·
                      refine ⟨2046114117671533212761777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456304313790755234031405 2046114117671533212761777)
                      ·
                        rfl

theorem cell23_3984793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_3984793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984793 prefixEnd_3984793 := by exact prefixLift 3984793
  have htrace : WordTrace (prefixWord ++ tailWord_3984793) baseStart_3984793 baseEnd_3984793 := by
    simpa [prefixWord, tailWord_3984793, baseEnd_3984793] using wordTrace_append hprefix tailTrace_3984793
  have hstable : (prefixWord ++ tailWord_3984793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984793).length < 2 ^ (prefixWord ++ tailWord_3984793).sum := by decide
  have hdescent : baseEnd_3984793 < baseStart_3984793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_3984795 : Nat := 118140960795 + 3984795 * 2 ^ 59
def prefixEnd_3984795 : Nat := 4983230072969 + 3 ^ 40 * 3984795 * 2
def baseEnd_3984795 : Nat := 2046115144632842204936767

theorem tailTrace_3984795 : CollatzResearch.WordTrace tailWord_3984795 prefixEnd_3984795 2046115144632842204936767 := by
  unfold tailWord_3984795
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337413598775738649851839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96891609065850492433234559 145337413598775738649851839)
  ·
    refine ⟨218006120398163607974777759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145337413598775738649851839 218006120398163607974777759)
    ·
      refine ⟨327009180597245411962166639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218006120398163607974777759 327009180597245411962166639)
      ·
        refine ⟨490513770895868117943249959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327009180597245411962166639 490513770895868117943249959)
        ·
          refine ⟨735770656343802176914874939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490513770895868117943249959 735770656343802176914874939)
          ·
            refine ⟨1103655984515703265372312409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735770656343802176914874939 1103655984515703265372312409)
            ·
              refine ⟨827741988386777449029234307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103655984515703265372312409 827741988386777449029234307)
              ·
                refine ⟨1241612982580166173543851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827741988386777449029234307 1241612982580166173543851461)
                ·
                  refine ⟨232802434233781157539472149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241612982580166173543851461 232802434233781157539472149)
                  ·
                    refine ⟨10912614104708491759662757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232802434233781157539472149 10912614104708491759662757)
                    ·
                      refine ⟨2046115144632842204936767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10912614104708491759662757 2046115144632842204936767)
                      ·
                        rfl

theorem cell23_3984795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_3984795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984795 prefixEnd_3984795 := by exact prefixLift 3984795
  have htrace : WordTrace (prefixWord ++ tailWord_3984795) baseStart_3984795 baseEnd_3984795 := by
    simpa [prefixWord, tailWord_3984795, baseEnd_3984795] using wordTrace_append hprefix tailTrace_3984795
  have hstable : (prefixWord ++ tailWord_3984795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984795).length < 2 ^ (prefixWord ++ tailWord_3984795).sum := by decide
  have hdescent : baseEnd_3984795 < baseStart_3984795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984799 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3984799 : Nat := 118140960795 + 3984799 * 2 ^ 59
def prefixEnd_3984799 : Nat := 4983230072969 + 3 ^ 40 * 3984799 * 2
def baseEnd_3984799 : Nat := 2046117198555460189286749

theorem tailTrace_3984799 : CollatzResearch.WordTrace tailWord_3984799 prefixEnd_3984799 2046117198555460189286749 := by
  unfold tailWord_3984799
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337559490761247332997451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96891706327174164888664967 145337559490761247332997451)
  ·
    refine ⟨218006339236141870999496177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145337559490761247332997451 218006339236141870999496177)
    ·
      refine ⟨163504754427106403249622133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218006339236141870999496177 163504754427106403249622133)
      ·
        refine ⟨15328570727541225304652075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163504754427106403249622133 15328570727541225304652075)
        ·
          refine ⟨22992856091311837956978113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15328570727541225304652075 22992856091311837956978113)
          ·
            refine ⟨17244642068483878467733585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22992856091311837956978113 17244642068483878467733585)
            ·
              refine ⟨12933481551362908850800189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17244642068483878467733585 12933481551362908850800189)
              ·
                refine ⟨4850055581761090819050071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12933481551362908850800189 4850055581761090819050071)
                ·
                  refine ⟨7275083372641636228575107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850055581761090819050071 7275083372641636228575107)
                  ·
                    refine ⟨10912625058962454342862661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275083372641636228575107 10912625058962454342862661)
                    ·
                      refine ⟨2046117198555460189286749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10912625058962454342862661 2046117198555460189286749)
                      ·
                        rfl

theorem cell23_3984799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3984799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984799 prefixEnd_3984799 := by exact prefixLift 3984799
  have htrace : WordTrace (prefixWord ++ tailWord_3984799) baseStart_3984799 baseEnd_3984799 := by
    simpa [prefixWord, tailWord_3984799, baseEnd_3984799] using wordTrace_append hprefix tailTrace_3984799
  have hstable : (prefixWord ++ tailWord_3984799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984799).length < 2 ^ (prefixWord ++ tailWord_3984799).sum := by decide
  have hdescent : baseEnd_3984799 < baseStart_3984799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984836 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3984836 : Nat := 118140960795 + 3984836 * 2 ^ 59
def prefixEnd_3984836 : Nat := 4983230072969 + 3 ^ 40 * 3984836 * 2
def baseEnd_3984836 : Nat := 2046136197339676544524079

theorem tailTrace_3984836 : CollatzResearch.WordTrace tailWord_3984836 prefixEnd_3984836 2046136197339676544524079 := by
  unfold tailWord_3984836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72669454495813601326047181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96892605994418135101396241 72669454495813601326047181)
  ·
    refine ⟨27251045435930100497267693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72669454495813601326047181 27251045435930100497267693)
    ·
      refine ⟨10219142038473787686475385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27251045435930100497267693 10219142038473787686475385)
      ·
        refine ⟨7664356528855340764856539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10219142038473787686475385 7664356528855340764856539)
        ·
          refine ⟨11496534793283011147284809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664356528855340764856539 11496534793283011147284809)
          ·
            refine ⟨8622401094962258360463607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11496534793283011147284809 8622401094962258360463607)
            ·
              refine ⟨12933601642443387540695411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622401094962258360463607 12933601642443387540695411)
              ·
                refine ⟨19400402463665081311043117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933601642443387540695411 19400402463665081311043117)
                ·
                  refine ⟨7275150923874405491641169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19400402463665081311043117 7275150923874405491641169)
                  ·
                    refine ⟨5456363192905804118730877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275150923874405491641169 5456363192905804118730877)
                    ·
                      refine ⟨2046136197339676544524079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456363192905804118730877 2046136197339676544524079)
                      ·
                        rfl

theorem cell23_3984836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3984836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984836 prefixEnd_3984836 := by exact prefixLift 3984836
  have htrace : WordTrace (prefixWord ++ tailWord_3984836) baseStart_3984836 baseEnd_3984836 := by
    simpa [prefixWord, tailWord_3984836, baseEnd_3984836] using wordTrace_append hprefix tailTrace_3984836
  have hstable : (prefixWord ++ tailWord_3984836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984836).length < 2 ^ (prefixWord ++ tailWord_3984836).sum := by decide
  have hdescent : baseEnd_3984836 < baseStart_3984836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984867 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3984867 : Nat := 118140960795 + 3984867 * 2 ^ 59
def prefixEnd_3984867 : Nat := 4983230072969 + 3 ^ 40 * 3984867 * 2
def baseEnd_3984867 : Nat := 2046152115239965923236437

theorem tailTrace_3984867 : CollatzResearch.WordTrace tailWord_3984867 prefixEnd_3984867 2046152115239965923236437 := by
  unfold tailWord_3984867
  simp only [CollatzResearch.WordTrace]
  refine ⟨145340039654514894946472855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96893359769676596630981903 145340039654514894946472855)
  ·
    refine ⟨218010059481772342419709283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145340039654514894946472855 218010059481772342419709283)
    ·
      refine ⟨327015089222658513629563925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218010059481772342419709283 327015089222658513629563925)
      ·
        refine ⟨15328832307312117826385809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 327015089222658513629563925 15328832307312117826385809)
        ·
          refine ⟨11496624230484088369789357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15328832307312117826385809 11496624230484088369789357)
          ·
            refine ⟨4311234086431533138671009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11496624230484088369789357 4311234086431533138671009)
            ·
              refine ⟨3233425564823649854003257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311234086431533138671009 3233425564823649854003257)
              ·
                refine ⟨2425069173617737390502443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233425564823649854003257 2425069173617737390502443)
                ·
                  refine ⟨3637603760426606085753665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425069173617737390502443 3637603760426606085753665)
                  ·
                    refine ⟨2728202820319954564315249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637603760426606085753665 2728202820319954564315249)
                    ·
                      refine ⟨2046152115239965923236437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728202820319954564315249 2046152115239965923236437)
                      ·
                        rfl

theorem cell23_3984867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3984867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984867 prefixEnd_3984867 := by exact prefixLift 3984867
  have htrace : WordTrace (prefixWord ++ tailWord_3984867) baseStart_3984867 baseEnd_3984867 := by
    simpa [prefixWord, tailWord_3984867, baseEnd_3984867] using wordTrace_append hprefix tailTrace_3984867
  have hstable : (prefixWord ++ tailWord_3984867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984867).length < 2 ^ (prefixWord ++ tailWord_3984867).sum := by decide
  have hdescent : baseEnd_3984867 < baseStart_3984867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984872 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3984872 : Nat := 118140960795 + 3984872 * 2 ^ 59
def prefixEnd_3984872 : Nat := 4983230072969 + 3 ^ 40 * 3984872 * 2
def baseEnd_3984872 : Nat := 2046154682643238403673913

theorem tailTrace_3984872 : CollatzResearch.WordTrace tailWord_3984872 prefixEnd_3984872 2046154682643238403673913 := by
  unfold tailWord_3984872
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670111009748390400202435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96893481346331187200269913 72670111009748390400202435)
  ·
    refine ⟨109005166514622585600303653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72670111009748390400202435 109005166514622585600303653)
    ·
      refine ⟨20438468721491734800056935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109005166514622585600303653 20438468721491734800056935)
      ·
        refine ⟨30657703082237602200085403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438468721491734800056935 30657703082237602200085403)
        ·
          refine ⟨45986554623356403300128105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30657703082237602200085403 45986554623356403300128105)
          ·
            refine ⟨34489915967517302475096079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45986554623356403300128105 34489915967517302475096079)
            ·
              refine ⟨51734873951275953712644119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34489915967517302475096079 51734873951275953712644119)
              ·
                refine ⟨77602310926913930568966179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51734873951275953712644119 77602310926913930568966179)
                ·
                  refine ⟨116403466390370895853449269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77602310926913930568966179 116403466390370895853449269)
                  ·
                    refine ⟨10912824974097271486260869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116403466390370895853449269 10912824974097271486260869)
                    ·
                      refine ⟨2046154682643238403673913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10912824974097271486260869 2046154682643238403673913)
                      ·
                        rfl

theorem cell23_3984872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3984872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984872 prefixEnd_3984872 := by exact prefixLift 3984872
  have htrace : WordTrace (prefixWord ++ tailWord_3984872) baseStart_3984872 baseEnd_3984872 := by
    simpa [prefixWord, tailWord_3984872, baseEnd_3984872] using wordTrace_append hprefix tailTrace_3984872
  have hstable : (prefixWord ++ tailWord_3984872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984872).length < 2 ^ (prefixWord ++ tailWord_3984872).sum := by decide
  have hdescent : baseEnd_3984872 < baseStart_3984872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984892 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_3984892 : Nat := 118140960795 + 3984892 * 2 ^ 59
def prefixEnd_3984892 : Nat := 4983230072969 + 3 ^ 40 * 3984892 * 2
def baseEnd_3984892 : Nat := 2046164952256328325423821

theorem tailTrace_3984892 : CollatzResearch.WordTrace tailWord_3984892 prefixEnd_3984892 2046164952256328325423821 := by
  unfold tailWord_3984892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670475739712162108066465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96893967652949549477421953 72670475739712162108066465)
  ·
    refine ⟨54502856804784121581049849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72670475739712162108066465 54502856804784121581049849)
    ·
      refine ⟨40877142603588091185787387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54502856804784121581049849 40877142603588091185787387)
      ·
        refine ⟨61315713905382136778681081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40877142603588091185787387 61315713905382136778681081)
        ·
          refine ⟨45986785429036602584010811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61315713905382136778681081 45986785429036602584010811)
          ·
            refine ⟨68980178143554903876016217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45986785429036602584010811 68980178143554903876016217)
            ·
              refine ⟨51735133607666177907012163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68980178143554903876016217 51735133607666177907012163)
              ·
                refine ⟨77602700411499266860518245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51735133607666177907012163 77602700411499266860518245)
                ·
                  refine ⟨14550506327156112536347171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77602700411499266860518245 14550506327156112536347171)
                  ·
                    refine ⟨21825759490734168804520757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14550506327156112536347171 21825759490734168804520757)
                    ·
                      refine ⟨2046164952256328325423821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21825759490734168804520757 2046164952256328325423821)
                      ·
                        rfl

theorem cell23_3984892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_3984892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984892 prefixEnd_3984892 := by exact prefixLift 3984892
  have htrace : WordTrace (prefixWord ++ tailWord_3984892) baseStart_3984892 baseEnd_3984892 := by
    simpa [prefixWord, tailWord_3984892, baseEnd_3984892] using wordTrace_append hprefix tailTrace_3984892
  have hstable : (prefixWord ++ tailWord_3984892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984892).length < 2 ^ (prefixWord ++ tailWord_3984892).sum := by decide
  have hdescent : baseEnd_3984892 < baseStart_3984892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984906 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3984906 : Nat := 118140960795 + 3984906 * 2 ^ 59
def prefixEnd_3984906 : Nat := 4983230072969 + 3 ^ 40 * 3984906 * 2
def baseEnd_3984906 : Nat := 2046172140985491270648757

theorem tailTrace_3984906 : CollatzResearch.WordTrace tailWord_3984906 prefixEnd_3984906 2046172140985491270648757 := by
  unfold tailWord_3984906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36335365525343401151785643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96894308067582403071428381 36335365525343401151785643)
  ·
    refine ⟨54503048288015101727678465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36335365525343401151785643 54503048288015101727678465)
    ·
      refine ⟨40877286216011326295758849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54503048288015101727678465 40877286216011326295758849)
      ·
        refine ⟨30657964662008494721819137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40877286216011326295758849 30657964662008494721819137)
        ·
          refine ⟨22993473496506371041364353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30657964662008494721819137 22993473496506371041364353)
          ·
            refine ⟨17245105122379778281023265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22993473496506371041364353 17245105122379778281023265)
            ·
              refine ⟨12933828841784833710767449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17245105122379778281023265 12933828841784833710767449)
              ·
                refine ⟨9700371631338625283075587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12933828841784833710767449 9700371631338625283075587)
                ·
                  refine ⟨14550557447007937924613381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700371631338625283075587 14550557447007937924613381)
                  ·
                    refine ⟨2728229521313988360865009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14550557447007937924613381 2728229521313988360865009)
                    ·
                      refine ⟨2046172140985491270648757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728229521313988360865009 2046172140985491270648757)
                      ·
                        rfl

theorem cell23_3984906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3984906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984906 prefixEnd_3984906 := by exact prefixLift 3984906
  have htrace : WordTrace (prefixWord ++ tailWord_3984906) baseStart_3984906 baseEnd_3984906 := by
    simpa [prefixWord, tailWord_3984906, baseEnd_3984906] using wordTrace_append hprefix tailTrace_3984906
  have hstable : (prefixWord ++ tailWord_3984906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984906).length < 2 ^ (prefixWord ++ tailWord_3984906).sum := by decide
  have hdescent : baseEnd_3984906 < baseStart_3984906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984929 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 7]
def baseStart_3984929 : Nat := 118140960795 + 3984929 * 2 ^ 59
def prefixEnd_3984929 : Nat := 4983230072969 + 3 ^ 40 * 3984929 * 2
def baseEnd_3984929 : Nat := 227353772337838297851239

theorem tailTrace_3984929 : CollatzResearch.WordTrace tailWord_3984929 prefixEnd_3984929 227353772337838297851239 := by
  unfold tailWord_3984929
  simp only [CollatzResearch.WordTrace]
  refine ⟨145342300980290279535229841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96894867320193519690153227 145342300980290279535229841)
  ·
    refine ⟨109006725735217709651422381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145342300980290279535229841 109006725735217709651422381)
    ·
      refine ⟨40877522150706641119283393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109006725735217709651422381 40877522150706641119283393)
      ·
        refine ⟨30658141613029980839462545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40877522150706641119283393 30658141613029980839462545)
        ·
          refine ⟨22993606209772485629596909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30658141613029980839462545 22993606209772485629596909)
          ·
            refine ⟨8622602328664682111098841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22993606209772485629596909 8622602328664682111098841)
            ·
              refine ⟨6466951746498511583324131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622602328664682111098841 6466951746498511583324131)
              ·
                refine ⟨9700427619747767374986197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466951746498511583324131 9700427619747767374986197)
                ·
                  refine ⟨227353772337838297851239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9700427619747767374986197 227353772337838297851239)
                  ·
                    rfl

theorem cell23_3984929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_3984929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984929 prefixEnd_3984929 := by exact prefixLift 3984929
  have htrace : WordTrace (prefixWord ++ tailWord_3984929) baseStart_3984929 baseEnd_3984929 := by
    simpa [prefixWord, tailWord_3984929, baseEnd_3984929] using wordTrace_append hprefix tailTrace_3984929
  have hstable : (prefixWord ++ tailWord_3984929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984929).length < 2 ^ (prefixWord ++ tailWord_3984929).sum := by decide
  have hdescent : baseEnd_3984929 < baseStart_3984929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984979 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 6, 2]
def baseStart_3984979 : Nat := 118140960795 + 3984979 * 2 ^ 59
def prefixEnd_3984979 : Nat := 4983230072969 + 3 ^ 40 * 3984979 * 2
def baseEnd_3984979 : Nat := 2046209625073269485035921

theorem tailTrace_3984979 : CollatzResearch.WordTrace tailWord_3984979 prefixEnd_3984979 2046209625073269485035921 := by
  unfold tailWord_3984979
  simp only [CollatzResearch.WordTrace]
  refine ⟨145344124630109138074549991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96896083086739425383033327 145344124630109138074549991)
  ·
    refine ⟨218016186945163707111824987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145344124630109138074549991 218016186945163707111824987)
    ·
      refine ⟨327024280417745560667737481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218016186945163707111824987 327024280417745560667737481)
      ·
        refine ⟨245268210313309170500803111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327024280417745560667737481 245268210313309170500803111)
        ·
          refine ⟨367902315469963755751204667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245268210313309170500803111 367902315469963755751204667)
          ·
            refine ⟨551853473204945633626807001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367902315469963755751204667 551853473204945633626807001)
            ·
              refine ⟨413890104903709225220105251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551853473204945633626807001 413890104903709225220105251)
              ·
                refine ⟨620835157355563837830157877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413890104903709225220105251 620835157355563837830157877)
                ·
                  refine ⟨58203296002084109796577301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 620835157355563837830157877 58203296002084109796577301)
                  ·
                    refine ⟨2728279500097692646714561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58203296002084109796577301 2728279500097692646714561)
                    ·
                      refine ⟨2046209625073269485035921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728279500097692646714561 2046209625073269485035921)
                      ·
                        rfl

theorem cell23_3984979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6, 2].length) (baseStart_3984979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984979 prefixEnd_3984979 := by exact prefixLift 3984979
  have htrace : WordTrace (prefixWord ++ tailWord_3984979) baseStart_3984979 baseEnd_3984979 := by
    simpa [prefixWord, tailWord_3984979, baseEnd_3984979] using wordTrace_append hprefix tailTrace_3984979
  have hstable : (prefixWord ++ tailWord_3984979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984979).length < 2 ^ (prefixWord ++ tailWord_3984979).sum := by decide
  have hdescent : baseEnd_3984979 < baseStart_3984979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984999 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3984999 : Nat := 118140960795 + 3984999 * 2 ^ 59
def prefixEnd_3984999 : Nat := 4983230072969 + 3 ^ 40 * 3984999 * 2
def baseEnd_3984999 : Nat := 2046219894686359406785829

theorem tailTrace_3984999 : CollatzResearch.WordTrace tailWord_3984999 prefixEnd_3984999 2046219894686359406785829 := by
  unfold tailWord_3984999
  simp only [CollatzResearch.WordTrace]
  refine ⟨145344854090036681490278051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96896569393357787660185367 145344854090036681490278051)
  ·
    refine ⟨218017281135055022235417077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145344854090036681490278051 218017281135055022235417077)
    ·
      refine ⟨20439120106411408334570351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218017281135055022235417077 20439120106411408334570351)
      ·
        refine ⟨30658680159617112501855527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20439120106411408334570351 30658680159617112501855527)
        ·
          refine ⟨45988020239425668752783291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658680159617112501855527 45988020239425668752783291)
          ·
            refine ⟨68982030359138503129174937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45988020239425668752783291 68982030359138503129174937)
            ·
              refine ⟨51736522769353877346881203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68982030359138503129174937 51736522769353877346881203)
              ·
                refine ⟨77604784154030816020321805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51736522769353877346881203 77604784154030816020321805)
                ·
                  refine ⟨29101794057761556007620677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77604784154030816020321805 29101794057761556007620677)
                  ·
                    refine ⟨5456586385830291751428877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29101794057761556007620677 5456586385830291751428877)
                    ·
                      refine ⟨2046219894686359406785829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456586385830291751428877 2046219894686359406785829)
                      ·
                        rfl

theorem cell23_3984999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3984999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3984999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3984999 prefixEnd_3984999 := by exact prefixLift 3984999
  have htrace : WordTrace (prefixWord ++ tailWord_3984999) baseStart_3984999 baseEnd_3984999 := by
    simpa [prefixWord, tailWord_3984999, baseEnd_3984999] using wordTrace_append hprefix tailTrace_3984999
  have hstable : (prefixWord ++ tailWord_3984999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984999).length < 2 ^ (prefixWord ++ tailWord_3984999).sum := by decide
  have hdescent : baseEnd_3984999 < baseStart_3984999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985013 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3985013 : Nat := 118140960795 + 3985013 * 2 ^ 59
def prefixEnd_3985013 : Nat := 4983230072969 + 3 ^ 40 * 3985013 * 2
def baseEnd_3985013 : Nat := 2046227083415522352010765

theorem tailTrace_3985013 : CollatzResearch.WordTrace tailWord_3985013 prefixEnd_3985013 2046227083415522352010765 := by
  unfold tailWord_3985013
  simp only [CollatzResearch.WordTrace]
  refine ⟨145345364711985961881287693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96896909807990641254191795 145345364711985961881287693)
  ·
    refine ⟨54504511766994735705482885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145345364711985961881287693 54504511766994735705482885)
    ·
      refine ⟨10219595956311512944778041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54504511766994735705482885 10219595956311512944778041)
      ·
        refine ⟨7664696967233634708583531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10219595956311512944778041 7664696967233634708583531)
        ·
          refine ⟨11497045450850452062875297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664696967233634708583531 11497045450850452062875297)
          ·
            refine ⟨8622784088137839047156473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11497045450850452062875297 8622784088137839047156473)
            ·
              refine ⟨6467088066103379285367355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8622784088137839047156473 6467088066103379285367355)
              ·
                refine ⟨9700632099155068928051033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6467088066103379285367355 9700632099155068928051033)
                ·
                  refine ⟨7275474074366301696038275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9700632099155068928051033 7275474074366301696038275)
                  ·
                    refine ⟨10913211111549452544057413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275474074366301696038275 10913211111549452544057413)
                    ·
                      refine ⟨2046227083415522352010765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10913211111549452544057413 2046227083415522352010765)
                      ·
                        rfl

theorem cell23_3985013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3985013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985013 prefixEnd_3985013 := by exact prefixLift 3985013
  have htrace : WordTrace (prefixWord ++ tailWord_3985013) baseStart_3985013 baseEnd_3985013 := by
    simpa [prefixWord, tailWord_3985013, baseEnd_3985013] using wordTrace_append hprefix tailTrace_3985013
  have hstable : (prefixWord ++ tailWord_3985013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985013).length < 2 ^ (prefixWord ++ tailWord_3985013).sum := by decide
  have hdescent : baseEnd_3985013 < baseStart_3985013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985064 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3985064 : Nat := 118140960795 + 3985064 * 2 ^ 59
def prefixEnd_3985064 : Nat := 4983230072969 + 3 ^ 40 * 3985064 * 2
def baseEnd_3985064 : Nat := 2046253270928901652473031

theorem tailTrace_3985064 : CollatzResearch.WordTrace tailWord_3985064 prefixEnd_3985064 2046253270928901652473031 := by
  unfold tailWord_3985064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72673612417400598795697123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96898149889867465060929497 72673612417400598795697123)
  ·
    refine ⟨109010418626100898193545685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72673612417400598795697123 109010418626100898193545685)
    ·
      refine ⟨2554931686549239801411227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 109010418626100898193545685 2554931686549239801411227)
      ·
        refine ⟨3832397529823859702116841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554931686549239801411227 3832397529823859702116841)
        ·
          refine ⟨2874298147367894776587631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832397529823859702116841 2874298147367894776587631)
          ·
            refine ⟨4311447221051842164881447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874298147367894776587631 4311447221051842164881447)
            ·
              refine ⟨6467170831577763247322171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311447221051842164881447 6467170831577763247322171)
              ·
                refine ⟨9700756247366644870983257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6467170831577763247322171 9700756247366644870983257)
                ·
                  refine ⟨7275567185524983653237443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9700756247366644870983257 7275567185524983653237443)
                  ·
                    refine ⟨10913350778287475479856165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275567185524983653237443 10913350778287475479856165)
                    ·
                      refine ⟨2046253270928901652473031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10913350778287475479856165 2046253270928901652473031)
                      ·
                        rfl

theorem cell23_3985064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3985064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985064 prefixEnd_3985064 := by exact prefixLift 3985064
  have htrace : WordTrace (prefixWord ++ tailWord_3985064) baseStart_3985064 baseEnd_3985064 := by
    simpa [prefixWord, tailWord_3985064, baseEnd_3985064] using wordTrace_append hprefix tailTrace_3985064
  have hstable : (prefixWord ++ tailWord_3985064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985064).length < 2 ^ (prefixWord ++ tailWord_3985064).sum := by decide
  have hdescent : baseEnd_3985064 < baseStart_3985064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985096 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_3985096 : Nat := 118140960795 + 3985096 * 2 ^ 59
def prefixEnd_3985096 : Nat := 4983230072969 + 3 ^ 40 * 3985096 * 2
def baseEnd_3985096 : Nat := 682089900769948509090961

theorem tailTrace_3985096 : CollatzResearch.WordTrace tailWord_3985096 prefixEnd_3985096 682089900769948509090961 := by
  unfold tailWord_3985096
  simp only [CollatzResearch.WordTrace]
  refine ⟨72674195985342633528279571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96898927980456844704372761 72674195985342633528279571)
  ·
    refine ⟨109011293978013950292419357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72674195985342633528279571 109011293978013950292419357)
    ·
      refine ⟨40879235241755231359657259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109011293978013950292419357 40879235241755231359657259)
      ·
        refine ⟨61318852862632847039485889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40879235241755231359657259 61318852862632847039485889)
        ·
          refine ⟨45989139646974635279614417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61318852862632847039485889 45989139646974635279614417)
          ·
            refine ⟨34491854735230976459710813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45989139646974635279614417 34491854735230976459710813)
            ·
              refine ⟨12934445525711616172391555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34491854735230976459710813 12934445525711616172391555)
              ·
                refine ⟨19401668288567424258587333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934445525711616172391555 19401668288567424258587333)
                ·
                  refine ⟨3637812804106392048485125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19401668288567424258587333 3637812804106392048485125)
                  ·
                    refine ⟨682089900769948509090961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637812804106392048485125 682089900769948509090961)
                    ·
                      rfl

theorem cell23_3985096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_3985096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985096 prefixEnd_3985096 := by exact prefixLift 3985096
  have htrace : WordTrace (prefixWord ++ tailWord_3985096) baseStart_3985096 baseEnd_3985096 := by
    simpa [prefixWord, tailWord_3985096, baseEnd_3985096] using wordTrace_append hprefix tailTrace_3985096
  have hstable : (prefixWord ++ tailWord_3985096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985096).length < 2 ^ (prefixWord ++ tailWord_3985096).sum := by decide
  have hdescent : baseEnd_3985096 < baseStart_3985096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985099 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_3985099 : Nat := 118140960795 + 3985099 * 2 ^ 59
def prefixEnd_3985099 : Nat := 4983230072969 + 3 ^ 40 * 3985099 * 2
def baseEnd_3985099 : Nat := 2046271242751809015535369

theorem tailTrace_3985099 : CollatzResearch.WordTrace tailWord_3985099 prefixEnd_3985099 2046271242751809015535369 := by
  unfold tailWord_3985099
  simp only [CollatzResearch.WordTrace]
  refine ⟨145348501389674398568918351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96899000926449599045945567 145348501389674398568918351)
  ·
    refine ⟨218022752084511597853377527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145348501389674398568918351 218022752084511597853377527)
    ·
      refine ⟨327034128126767396780066291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218022752084511597853377527 327034128126767396780066291)
      ·
        refine ⟨490551192190151095170099437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327034128126767396780066291 490551192190151095170099437)
        ·
          refine ⟨183956697071306660688787289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490551192190151095170099437 183956697071306660688787289)
          ·
            refine ⟨137967522803479995516590467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183956697071306660688787289 137967522803479995516590467)
            ·
              refine ⟨206951284205219993274885701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137967522803479995516590467 206951284205219993274885701)
              ·
                refine ⟨38803365788478748739041069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206951284205219993274885701 38803365788478748739041069)
                ·
                  refine ⟨14551262170679530777140401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38803365788478748739041069 14551262170679530777140401)
                  ·
                    refine ⟨10913446628009648082855301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14551262170679530777140401 10913446628009648082855301)
                    ·
                      refine ⟨2046271242751809015535369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10913446628009648082855301 2046271242751809015535369)
                      ·
                        rfl

theorem cell23_3985099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_3985099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985099 prefixEnd_3985099 := by exact prefixLift 3985099
  have htrace : WordTrace (prefixWord ++ tailWord_3985099) baseStart_3985099 baseEnd_3985099 := by
    simpa [prefixWord, tailWord_3985099, baseEnd_3985099] using wordTrace_append hprefix tailTrace_3985099
  have hstable : (prefixWord ++ tailWord_3985099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985099).length < 2 ^ (prefixWord ++ tailWord_3985099).sum := by decide
  have hdescent : baseEnd_3985099 < baseStart_3985099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985106 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3985106 : Nat := 118140960795 + 3985106 * 2 ^ 59
def prefixEnd_3985106 : Nat := 4983230072969 + 3 ^ 40 * 3985106 * 2
def baseEnd_3985106 : Nat := 2046274837116390488147837

theorem tailTrace_3985106 : CollatzResearch.WordTrace tailWord_3985106 prefixEnd_3985106 2046274837116390488147837 := by
  unfold tailWord_3985106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337189175162259691105793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96899171133766025842948781 36337189175162259691105793)
  ·
    refine ⟨27252891881371694768329345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36337189175162259691105793 27252891881371694768329345)
    ·
      refine ⟨20439668911028771076247009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27252891881371694768329345 20439668911028771076247009)
      ·
        refine ⟨15329751683271578307185257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20439668911028771076247009 15329751683271578307185257)
        ·
          refine ⟨11497313762453683730388943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15329751683271578307185257 11497313762453683730388943)
          ·
            refine ⟨17245970643680525595583415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497313762453683730388943 17245970643680525595583415)
            ·
              refine ⟨25868955965520788393375123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17245970643680525595583415 25868955965520788393375123)
              ·
                refine ⟨38803433948281182590062685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25868955965520788393375123 38803433948281182590062685)
                ·
                  refine ⟨14551287730605443471273507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38803433948281182590062685 14551287730605443471273507)
                  ·
                    refine ⟨21826931595908165206910261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14551287730605443471273507 21826931595908165206910261)
                    ·
                      refine ⟨2046274837116390488147837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21826931595908165206910261 2046274837116390488147837)
                      ·
                        rfl

theorem cell23_3985106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3985106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985106 prefixEnd_3985106 := by exact prefixLift 3985106
  have htrace : WordTrace (prefixWord ++ tailWord_3985106) baseStart_3985106 baseEnd_3985106 := by
    simpa [prefixWord, tailWord_3985106, baseEnd_3985106] using wordTrace_append hprefix tailTrace_3985106
  have hstable : (prefixWord ++ tailWord_3985106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985106).length < 2 ^ (prefixWord ++ tailWord_3985106).sum := by decide
  have hdescent : baseEnd_3985106 < baseStart_3985106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985137 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_3985137 : Nat := 118140960795 + 3985137 * 2 ^ 59
def prefixEnd_3985137 : Nat := 4983230072969 + 3 ^ 40 * 3985137 * 2
def baseEnd_3985137 : Nat := 2046290755016679866860195

theorem tailTrace_3985137 : CollatzResearch.WordTrace tailWord_3985137 prefixEnd_3985137 2046290755016679866860195 := by
  unfold tailWord_3985137
  simp only [CollatzResearch.WordTrace]
  refine ⟨145349887363536731058801665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96899924909024487372534443 145349887363536731058801665)
  ·
    refine ⟨109012415522652548294101249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145349887363536731058801665 109012415522652548294101249)
    ·
      refine ⟨81759311641989411220575937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109012415522652548294101249 81759311641989411220575937)
      ·
        refine ⟨61319483731492058415431953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81759311641989411220575937 61319483731492058415431953)
        ·
          refine ⟨45989612798619043811573965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61319483731492058415431953 45989612798619043811573965)
          ·
            refine ⟨17246104799482141429340237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45989612798619043811573965 17246104799482141429340237)
            ·
              refine ⟨6467289299805803036002589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17246104799482141429340237 6467289299805803036002589)
              ·
                refine ⟨2425233487427176138500971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6467289299805803036002589 2425233487427176138500971)
                ·
                  refine ⟨3637850231140764207751457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425233487427176138500971 3637850231140764207751457)
                  ·
                    refine ⟨2728387673355573155813593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3637850231140764207751457 2728387673355573155813593)
                    ·
                      refine ⟨2046290755016679866860195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728387673355573155813593 2046290755016679866860195)
                      ·
                        rfl

theorem cell23_3985137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_3985137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985137 prefixEnd_3985137 := by exact prefixLift 3985137
  have htrace : WordTrace (prefixWord ++ tailWord_3985137) baseStart_3985137 baseEnd_3985137 := by
    simpa [prefixWord, tailWord_3985137, baseEnd_3985137] using wordTrace_append hprefix tailTrace_3985137
  have hstable : (prefixWord ++ tailWord_3985137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985137).length < 2 ^ (prefixWord ++ tailWord_3985137).sum := by decide
  have hdescent : baseEnd_3985137 < baseStart_3985137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985140 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3985140 : Nat := 118140960795 + 3985140 * 2 ^ 59
def prefixEnd_3985140 : Nat := 4983230072969 + 3 ^ 40 * 3985140 * 2
def baseEnd_3985140 : Nat := 2046292295458643355122681

theorem tailTrace_3985140 : CollatzResearch.WordTrace tailWord_3985140 prefixEnd_3985140 2046292295458643355122681 := by
  unfold tailWord_3985140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72674998391262931285580437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96899997855017241714107249 72674998391262931285580437)
  ·
    refine ⟨3406640549590449904011583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72674998391262931285580437 3406640549590449904011583)
    ·
      refine ⟨5109960824385674856017375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406640549590449904011583 5109960824385674856017375)
      ·
        refine ⟨7664941236578512284026063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109960824385674856017375 7664941236578512284026063)
        ·
          refine ⟨11497411854867768426039095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664941236578512284026063 11497411854867768426039095)
          ·
            refine ⟨17246117782301652639058643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497411854867768426039095 17246117782301652639058643)
            ·
              refine ⟨25869176673452478958587965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246117782301652639058643 25869176673452478958587965)
              ·
                refine ⟨9700941252544679609470487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25869176673452478958587965 9700941252544679609470487)
                ·
                  refine ⟨14551411878817019414205731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700941252544679609470487 14551411878817019414205731)
                  ·
                    refine ⟨21827117818225529121308597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14551411878817019414205731 21827117818225529121308597)
                    ·
                      refine ⟨2046292295458643355122681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21827117818225529121308597 2046292295458643355122681)
                      ·
                        rfl

theorem cell23_3985140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3985140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985140 prefixEnd_3985140 := by exact prefixLift 3985140
  have htrace : WordTrace (prefixWord ++ tailWord_3985140) baseStart_3985140 baseEnd_3985140 := by
    simpa [prefixWord, tailWord_3985140, baseEnd_3985140] using wordTrace_append hprefix tailTrace_3985140
  have hstable : (prefixWord ++ tailWord_3985140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985140).length < 2 ^ (prefixWord ++ tailWord_3985140).sum := by decide
  have hdescent : baseEnd_3985140 < baseStart_3985140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985153 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3985153 : Nat := 118140960795 + 3985153 * 2 ^ 59
def prefixEnd_3985153 : Nat := 4983230072969 + 3 ^ 40 * 3985153 * 2
def baseEnd_3985153 : Nat := 2046298970707151804260121

theorem tailTrace_3985153 : CollatzResearch.WordTrace tailWord_3985153 prefixEnd_3985153 2046298970707151804260121 := by
  unfold tailWord_3985153
  simp only [CollatzResearch.WordTrace]
  refine ⟨145350470931478765791384113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96900313954319177194256075 145350470931478765791384113)
  ·
    refine ⟨109012853198609074343538085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145350470931478765791384113 109012853198609074343538085)
    ·
      refine ⟨20439909974739201439413391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109012853198609074343538085 20439909974739201439413391)
      ·
        refine ⟨30659864962108802159120087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20439909974739201439413391 30659864962108802159120087)
        ·
          refine ⟨45989797443163203238680131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30659864962108802159120087 45989797443163203238680131)
          ·
            refine ⟨68984696164744804858020197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45989797443163203238680131 68984696164744804858020197)
            ·
              refine ⟨12934630530889650910878787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68984696164744804858020197 12934630530889650910878787)
              ·
                refine ⟨19401945796334476366318181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934630530889650910878787 19401945796334476366318181)
                ·
                  refine ⟨3637864836812714318684659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19401945796334476366318181 3637864836812714318684659)
                  ·
                    refine ⟨5456797255219071478026989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637864836812714318684659 5456797255219071478026989)
                    ·
                      refine ⟨2046298970707151804260121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456797255219071478026989 2046298970707151804260121)
                      ·
                        rfl

theorem cell23_3985153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3985153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985153 prefixEnd_3985153 := by exact prefixLift 3985153
  have htrace : WordTrace (prefixWord ++ tailWord_3985153) baseStart_3985153 baseEnd_3985153 := by
    simpa [prefixWord, tailWord_3985153, baseEnd_3985153] using wordTrace_append hprefix tailTrace_3985153
  have hstable : (prefixWord ++ tailWord_3985153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985153).length < 2 ^ (prefixWord ++ tailWord_3985153).sum := by decide
  have hdescent : baseEnd_3985153 < baseStart_3985153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
