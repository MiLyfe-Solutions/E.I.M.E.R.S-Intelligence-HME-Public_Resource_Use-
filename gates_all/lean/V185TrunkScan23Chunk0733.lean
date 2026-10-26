import V185TrunkScan23Chunk0732

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4334928 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2]
def baseStart_4334928 : Nat := 118140960795 + 4334928 * 2 ^ 59
def prefixEnd_4334928 : Nat := 4983230072969 + 3 ^ 40 * 4334928 * 2
def baseEnd_4334928 : Nat := 2225901666633520807964035

theorem tailTrace_4334928 : CollatzResearch.WordTrace tailWord_4334928 prefixEnd_4334928 2225901666633520807964035 := by
  unfold tailWord_4334928
  simp only [CollatzResearch.WordTrace]
  refine ⟨79053906619651838802746719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105405208826202451736995625 79053906619651838802746719)
  ·
    refine ⟨118580859929477758204120079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79053906619651838802746719 118580859929477758204120079)
    ·
      refine ⟨177871289894216637306180119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118580859929477758204120079 177871289894216637306180119)
      ·
        refine ⟨266806934841324955959270179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177871289894216637306180119 266806934841324955959270179)
        ·
          refine ⟨400210402261987433938905269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266806934841324955959270179 400210402261987433938905269)
          ·
            refine ⟨37519725212061321931772369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 400210402261987433938905269 37519725212061321931772369)
            ·
              refine ⟨28139793909045991448829277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37519725212061321931772369 28139793909045991448829277)
              ·
                refine ⟨10552422715892246793310979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28139793909045991448829277 10552422715892246793310979)
                ·
                  refine ⟨15828634073838370189966469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10552422715892246793310979 15828634073838370189966469)
                  ·
                    refine ⟨2967868888844694410618713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15828634073838370189966469 2967868888844694410618713)
                    ·
                      refine ⟨2225901666633520807964035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967868888844694410618713 2225901666633520807964035)
                      ·
                        rfl

theorem cell23_4334928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2].length) (baseStart_4334928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334928 prefixEnd_4334928 := by exact prefixLift 4334928
  have htrace : WordTrace (prefixWord ++ tailWord_4334928) baseStart_4334928 baseEnd_4334928 := by
    simpa [prefixWord, tailWord_4334928, baseEnd_4334928] using wordTrace_append hprefix tailTrace_4334928
  have hstable : (prefixWord ++ tailWord_4334928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334928).length < 2 ^ (prefixWord ++ tailWord_4334928).sum := by decide
  have hdescent : baseEnd_4334928 < baseStart_4334928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334962 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4334962 : Nat := 118140960795 + 4334962 * 2 ^ 59
def prefixEnd_4334962 : Nat := 4983230072969 + 3 ^ 40 * 4334962 * 2
def baseEnd_4334962 : Nat := 2225919124975773674938879

theorem tailTrace_4334962 : CollatzResearch.WordTrace tailWord_4334962 prefixEnd_4334962 2225919124975773674938879 := by
  unfold tailWord_4334962
  simp only [CollatzResearch.WordTrace]
  refine ⟨39527263330295125353057785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105406035547453667608154093 39527263330295125353057785)
  ·
    refine ⟨29645447497721344014793339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39527263330295125353057785 29645447497721344014793339)
    ·
      refine ⟨44468171246582016022190009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29645447497721344014793339 44468171246582016022190009)
      ·
        refine ⟨33351128434936512016642507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44468171246582016022190009 33351128434936512016642507)
        ·
          refine ⟨50026692652404768024963761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33351128434936512016642507 50026692652404768024963761)
          ·
            refine ⟨37520019489303576018722821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50026692652404768024963761 37520019489303576018722821)
            ·
              refine ⟨7035003654244420503510529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37520019489303576018722821 7035003654244420503510529)
              ·
                refine ⟨5276252740683315377632897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035003654244420503510529 5276252740683315377632897)
                ·
                  refine ⟨3957189555512486533224673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5276252740683315377632897 3957189555512486533224673)
                  ·
                    refine ⟨2967892166634364899918505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957189555512486533224673 2967892166634364899918505)
                    ·
                      refine ⟨2225919124975773674938879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967892166634364899918505 2225919124975773674938879)
                      ·
                        rfl

theorem cell23_4334962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4334962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334962 prefixEnd_4334962 := by exact prefixLift 4334962
  have htrace : WordTrace (prefixWord ++ tailWord_4334962) baseStart_4334962 baseEnd_4334962 := by
    simpa [prefixWord, tailWord_4334962, baseEnd_4334962] using wordTrace_append hprefix tailTrace_4334962
  have hstable : (prefixWord ++ tailWord_4334962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334962).length < 2 ^ (prefixWord ++ tailWord_4334962).sum := by decide
  have hdescent : baseEnd_4334962 < baseStart_4334962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334981 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_4334981 : Nat := 118140960795 + 4334981 * 2 ^ 59
def prefixEnd_4334981 : Nat := 4983230072969 + 3 ^ 40 * 4334981 * 2
def baseEnd_4334981 : Nat := 741976293702736366867097

theorem tailTrace_4334981 : CollatzResearch.WordTrace tailWord_4334981 prefixEnd_4334981 741976293702736366867097 := by
  unfold tailWord_4334981
  simp only [CollatzResearch.WordTrace]
  refine ⟨158109746308111667657172797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105406497538741111771448531 158109746308111667657172797)
  ·
    refine ⟨59291154865541875371439799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158109746308111667657172797 59291154865541875371439799)
    ·
      refine ⟨88936732298312813057159699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59291154865541875371439799 88936732298312813057159699)
      ·
        refine ⟨133405098447469219585739549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88936732298312813057159699 133405098447469219585739549)
        ·
          refine ⟨50026911917800957344652331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133405098447469219585739549 50026911917800957344652331)
          ·
            refine ⟨75040367876701436016978497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50026911917800957344652331 75040367876701436016978497)
            ·
              refine ⟨56280275907526077012733873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75040367876701436016978497 56280275907526077012733873)
              ·
                refine ⟨42210206930644557759550405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56280275907526077012733873 42210206930644557759550405)
                ·
                  refine ⟨7914413799495854579915701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42210206930644557759550405 7914413799495854579915701)
                  ·
                    refine ⟨741976293702736366867097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7914413799495854579915701 741976293702736366867097)
                    ·
                      rfl

theorem cell23_4334981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_4334981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334981 prefixEnd_4334981 := by exact prefixLift 4334981
  have htrace : WordTrace (prefixWord ++ tailWord_4334981) baseStart_4334981 baseEnd_4334981 := by
    simpa [prefixWord, tailWord_4334981, baseEnd_4334981] using wordTrace_append hprefix tailTrace_4334981
  have hstable : (prefixWord ++ tailWord_4334981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334981).length < 2 ^ (prefixWord ++ tailWord_4334981).sum := by decide
  have hdescent : baseEnd_4334981 < baseStart_4334981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4334988 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_4334988 : Nat := 118140960795 + 4334988 * 2 ^ 59
def prefixEnd_4334988 : Nat := 4983230072969 + 3 ^ 40 * 4334988 * 2
def baseEnd_4334988 : Nat := 2225932475472790573213759

theorem tailTrace_4334988 : CollatzResearch.WordTrace tailWord_4334988 prefixEnd_4334988 2225932475472790573213759 := by
  unfold tailWord_4334988
  simp only [CollatzResearch.WordTrace]
  refine ⟨79055000809543153926338809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105406667746057538568451745 79055000809543153926338809)
  ·
    refine ⟨59291250607157365444754107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79055000809543153926338809 59291250607157365444754107)
    ·
      refine ⟨88936875910736048167131161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59291250607157365444754107 88936875910736048167131161)
      ·
        refine ⟨66702656933052036125348371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88936875910736048167131161 66702656933052036125348371)
        ·
          refine ⟨100053985399578054188022557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66702656933052036125348371 100053985399578054188022557)
          ·
            refine ⟨37520244524841770320508459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100053985399578054188022557 37520244524841770320508459)
            ·
              refine ⟨56280366787262655480762689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37520244524841770320508459 56280366787262655480762689)
              ·
                refine ⟨42210275090446991610572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56280366787262655480762689 42210275090446991610572017)
                ·
                  refine ⟨31657706317835243707929013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42210275090446991610572017 31657706317835243707929013)
                  ·
                    refine ⟨2967909967297054097618345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31657706317835243707929013 2967909967297054097618345)
                    ·
                      refine ⟨2225932475472790573213759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2967909967297054097618345 2225932475472790573213759)
                      ·
                        rfl

theorem cell23_4334988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_4334988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4334988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4334988 prefixEnd_4334988 := by exact prefixLift 4334988
  have htrace : WordTrace (prefixWord ++ tailWord_4334988) baseStart_4334988 baseEnd_4334988 := by
    simpa [prefixWord, tailWord_4334988, baseEnd_4334988] using wordTrace_append hprefix tailTrace_4334988
  have hstable : (prefixWord ++ tailWord_4334988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4334988).length < 2 ^ (prefixWord ++ tailWord_4334988).sum := by decide
  have hdescent : baseEnd_4334988 < baseStart_4334988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4334988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335031 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_4335031 : Nat := 118140960795 + 4335031 * 2 ^ 59
def prefixEnd_4335031 : Nat := 4983230072969 + 3 ^ 40 * 4335031 * 2
def baseEnd_4335031 : Nat := 2225954555140933904976061

theorem tailTrace_4335031 : CollatzResearch.WordTrace tailWord_4335031 prefixEnd_4335031 2225954555140933904976061 := by
  unfold tailWord_4335031
  simp only [CollatzResearch.WordTrace]
  refine ⟨158111569957930526196492947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105407713305287017464328631 158111569957930526196492947)
  ·
    refine ⟨237167354936895789294739421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158111569957930526196492947 237167354936895789294739421)
    ·
      refine ⟨88937758101335920985527283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237167354936895789294739421 88937758101335920985527283)
      ·
        refine ⟨133406637152003881478290925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88937758101335920985527283 133406637152003881478290925)
        ·
          refine ⟨50027488932001455554359097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133406637152003881478290925 50027488932001455554359097)
          ·
            refine ⟨37520616699001091665769323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50027488932001455554359097 37520616699001091665769323)
            ·
              refine ⟨56280925048501637498653985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37520616699001091665769323 56280925048501637498653985)
              ·
                refine ⟨42210693786376228123990489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56280925048501637498653985 42210693786376228123990489)
                ·
                  refine ⟨31658020339782171092992867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42210693786376228123990489 31658020339782171092992867)
                  ·
                    refine ⟨47487030509673256639489301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31658020339782171092992867 47487030509673256639489301)
                    ·
                      refine ⟨2225954555140933904976061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47487030509673256639489301 2225954555140933904976061)
                      ·
                        rfl

theorem cell23_4335031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_4335031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335031 prefixEnd_4335031 := by exact prefixLift 4335031
  have htrace : WordTrace (prefixWord ++ tailWord_4335031) baseStart_4335031 baseEnd_4335031 := by
    simpa [prefixWord, tailWord_4335031, baseEnd_4335031] using wordTrace_append hprefix tailTrace_4335031
  have hstable : (prefixWord ++ tailWord_4335031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335031).length < 2 ^ (prefixWord ++ tailWord_4335031).sum := by decide
  have hdescent : baseEnd_4335031 < baseStart_4335031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335079 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 1, 4]
def baseStart_4335079 : Nat := 118140960795 + 4335079 * 2 ^ 59
def prefixEnd_4335079 : Nat := 4983230072969 + 3 ^ 40 * 4335079 * 2
def baseEnd_4335079 : Nat := 741993067404116572391947

theorem tailTrace_4335079 : CollatzResearch.WordTrace tailWord_4335079 prefixEnd_4335079 741993067404116572391947 := by
  unfold tailWord_4335079
  simp only [CollatzResearch.WordTrace]
  refine ⟨158113320661756630394240291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105408880441171086929493527 158113320661756630394240291)
  ·
    refine ⟨237169980992634945591360437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158113320661756630394240291 237169980992634945591360437)
    ·
      refine ⟨22234685718059526149190041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237169980992634945591360437 22234685718059526149190041)
      ·
        refine ⟨16676014288544644611892531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22234685718059526149190041 16676014288544644611892531)
        ·
          refine ⟨25014021432816966917838797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16676014288544644611892531 25014021432816966917838797)
          ·
            refine ⟨9380258037306362594189549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25014021432816966917838797 9380258037306362594189549)
            ·
              refine ⟨3517596763989885972821081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9380258037306362594189549 3517596763989885972821081)
              ·
                refine ⟨2638197572992414479615811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517596763989885972821081 2638197572992414479615811)
                ·
                  refine ⟨3957296359488621719423717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638197572992414479615811 3957296359488621719423717)
                  ·
                    refine ⟨741993067404116572391947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957296359488621719423717 741993067404116572391947)
                    ·
                      rfl

theorem cell23_4335079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_4335079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335079 prefixEnd_4335079 := by exact prefixLift 4335079
  have htrace : WordTrace (prefixWord ++ tailWord_4335079) baseStart_4335079 baseEnd_4335079 := by
    simpa [prefixWord, tailWord_4335079, baseEnd_4335079] using wordTrace_append hprefix tailTrace_4335079
  have hstable : (prefixWord ++ tailWord_4335079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335079).length < 2 ^ (prefixWord ++ tailWord_4335079).sum := by decide
  have hdescent : baseEnd_4335079 < baseStart_4335079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335105 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4335105 : Nat := 118140960795 + 4335105 * 2 ^ 59
def prefixEnd_4335105 : Nat := 4983230072969 + 3 ^ 40 * 4335105 * 2
def baseEnd_4335105 : Nat := 741997517569788871816907

theorem tailTrace_4335105 : CollatzResearch.WordTrace tailWord_4335105 prefixEnd_4335105 741997517569788871816907 := by
  unfold tailWord_4335105
  simp only [CollatzResearch.WordTrace]
  refine ⟨158114268959662436834686769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105409512639774957889791179 158114268959662436834686769)
  ·
    refine ⟨118585701719746827626015077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158114268959662436834686769 118585701719746827626015077)
    ·
      refine ⟨22234819072452530179877827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118585701719746827626015077 22234819072452530179877827)
      ·
        refine ⟨33352228608678795269816741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22234819072452530179877827 33352228608678795269816741)
        ·
          refine ⟨6253542864127274113090639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33352228608678795269816741 6253542864127274113090639)
          ·
            refine ⟨9380314296190911169635959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6253542864127274113090639 9380314296190911169635959)
            ·
              refine ⟨14070471444286366754453939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9380314296190911169635959 14070471444286366754453939)
              ·
                refine ⟨21105707166429550131680909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14070471444286366754453939 21105707166429550131680909)
                ·
                  refine ⟨7914640187411081299380341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21105707166429550131680909 7914640187411081299380341)
                  ·
                    refine ⟨741997517569788871816907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7914640187411081299380341 741997517569788871816907)
                    ·
                      rfl

theorem cell23_4335105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4335105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335105 prefixEnd_4335105 := by exact prefixLift 4335105
  have htrace : WordTrace (prefixWord ++ tailWord_4335105) baseStart_4335105 baseEnd_4335105 := by
    simpa [prefixWord, tailWord_4335105, baseEnd_4335105] using wordTrace_append hprefix tailTrace_4335105
  have hstable : (prefixWord ++ tailWord_4335105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335105).length < 2 ^ (prefixWord ++ tailWord_4335105).sum := by decide
  have hdescent : baseEnd_4335105 < baseStart_4335105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335135 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 2, 4]
def baseStart_4335135 : Nat := 118140960795 + 4335135 * 2 ^ 59
def prefixEnd_4335135 : Nat := 4983230072969 + 3 ^ 40 * 4335135 * 2
def baseEnd_4335135 : Nat := 742002652376333832691861

theorem tailTrace_4335135 : CollatzResearch.WordTrace tailWord_4335135 prefixEnd_4335135 742002652376333832691861 := by
  unfold tailWord_4335135
  simp only [CollatzResearch.WordTrace]
  refine ⟨158115363149553751958278859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105410242099702501305519239 158115363149553751958278859)
  ·
    refine ⟨237173044724330627937418289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158115363149553751958278859 237173044724330627937418289)
    ·
      refine ⟨177879783543247970953063717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237173044724330627937418289 177879783543247970953063717)
      ·
        refine ⟨33352459414358994553699447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177879783543247970953063717 33352459414358994553699447)
        ·
          refine ⟨50028689121538491830549171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33352459414358994553699447 50028689121538491830549171)
          ·
            refine ⟨75043033682307737745823757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50028689121538491830549171 75043033682307737745823757)
            ·
              refine ⟨28141137630865401654683909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75043033682307737745823757 28141137630865401654683909)
              ·
                refine ⟨5276463305787262810253233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28141137630865401654683909 5276463305787262810253233)
                ·
                  refine ⟨3957347479340447107689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5276463305787262810253233 3957347479340447107689925)
                  ·
                    refine ⟨742002652376333832691861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957347479340447107689925 742002652376333832691861)
                    ·
                      rfl

theorem cell23_4335135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_4335135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335135 prefixEnd_4335135 := by exact prefixLift 4335135
  have htrace : WordTrace (prefixWord ++ tailWord_4335135) baseStart_4335135 baseEnd_4335135 := by
    simpa [prefixWord, tailWord_4335135, baseEnd_4335135] using wordTrace_append hprefix tailTrace_4335135
  have hstable : (prefixWord ++ tailWord_4335135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335135).length < 2 ^ (prefixWord ++ tailWord_4335135).sum := by decide
  have hdescent : baseEnd_4335135 < baseStart_4335135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335136 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4335136 : Nat := 118140960795 + 4335136 * 2 ^ 59
def prefixEnd_4335136 : Nat := 4983230072969 + 3 ^ 40 * 4335136 * 2
def baseEnd_4335136 : Nat := 2226008470609655994163079

theorem tailTrace_4335136 : CollatzResearch.WordTrace tailWord_4335136 prefixEnd_4335136 2226008470609655994163079 := by
  unfold tailWord_4335136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79057699811275064564532631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105410266415033419419376841 79057699811275064564532631)
  ·
    refine ⟨118586549716912596846798947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79057699811275064564532631 118586549716912596846798947)
    ·
      refine ⟨177879824575368895270198421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118586549716912596846798947 177879824575368895270198421)
      ·
        refine ⟨8338116776970416965790551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177879824575368895270198421 8338116776970416965790551)
        ·
          refine ⟨12507175165455625448685827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338116776970416965790551 12507175165455625448685827)
          ·
            refine ⟨18760762748183438173028741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12507175165455625448685827 18760762748183438173028741)
            ·
              refine ⟨3517643015284394657442889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18760762748183438173028741 3517643015284394657442889)
              ·
                refine ⟨2638232261463295993082167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517643015284394657442889 2638232261463295993082167)
                ·
                  refine ⟨3957348392194943989623251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638232261463295993082167 3957348392194943989623251)
                  ·
                    refine ⟨5936022588292415984434877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957348392194943989623251 5936022588292415984434877)
                    ·
                      refine ⟨2226008470609655994163079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5936022588292415984434877 2226008470609655994163079)
                      ·
                        rfl

theorem cell23_4335136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4335136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335136 prefixEnd_4335136 := by exact prefixLift 4335136
  have htrace : WordTrace (prefixWord ++ tailWord_4335136) baseStart_4335136 baseEnd_4335136 := by
    simpa [prefixWord, tailWord_4335136, baseEnd_4335136] using wordTrace_append hprefix tailTrace_4335136
  have hstable : (prefixWord ++ tailWord_4335136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335136).length < 2 ^ (prefixWord ++ tailWord_4335136).sum := by decide
  have hdescent : baseEnd_4335136 < baseStart_4335136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335138 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4335138 : Nat := 118140960795 + 4335138 * 2 ^ 59
def prefixEnd_4335138 : Nat := 4983230072969 + 3 ^ 40 * 4335138 * 2
def baseEnd_4335138 : Nat := 2226009497570964986338069

theorem tailTrace_4335138 : CollatzResearch.WordTrace tailWord_4335138 prefixEnd_4335138 2226009497570964986338069 := by
  unfold tailWord_4335138
  simp only [CollatzResearch.WordTrace]
  refine ⟨39528868142135720867659517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105410315045695255647092045 39528868142135720867659517)
  ·
    refine ⟨14823325553300895325372319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39528868142135720867659517 14823325553300895325372319)
    ·
      refine ⟨22234988329951342988058479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14823325553300895325372319 22234988329951342988058479)
      ·
        refine ⟨33352482494927014482087719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22234988329951342988058479 33352482494927014482087719)
        ·
          refine ⟨50028723742390521723131579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33352482494927014482087719 50028723742390521723131579)
          ·
            refine ⟨75043085613585782584697369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50028723742390521723131579 75043085613585782584697369)
            ·
              refine ⟨56282314210189336938523027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75043085613585782584697369 56282314210189336938523027)
              ·
                refine ⟨84423471315284005407784541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56282314210189336938523027 84423471315284005407784541)
                ·
                  refine ⟨31658801743231502027919203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84423471315284005407784541 31658801743231502027919203)
                  ·
                    refine ⟨47488202614847253041878805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31658801743231502027919203 47488202614847253041878805)
                    ·
                      refine ⟨2226009497570964986338069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47488202614847253041878805 2226009497570964986338069)
                      ·
                        rfl

theorem cell23_4335138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4335138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335138 prefixEnd_4335138 := by exact prefixLift 4335138
  have htrace : WordTrace (prefixWord ++ tailWord_4335138) baseStart_4335138 baseEnd_4335138 := by
    simpa [prefixWord, tailWord_4335138, baseEnd_4335138] using wordTrace_append hprefix tailTrace_4335138
  have hstable : (prefixWord ++ tailWord_4335138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335138).length < 2 ^ (prefixWord ++ tailWord_4335138).sum := by decide
  have hdescent : baseEnd_4335138 < baseStart_4335138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335155 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4]
def baseStart_4335155 : Nat := 118140960795 + 4335155 * 2 ^ 59
def prefixEnd_4335155 : Nat := 4983230072969 + 3 ^ 40 * 4335155 * 2
def baseEnd_4335155 : Nat := 2226018226742091419825491

theorem tailTrace_4335155 : CollatzResearch.WordTrace tailWord_4335155 prefixEnd_4335155 2226018226742091419825491 := by
  unfold tailWord_4335155
  simp only [CollatzResearch.WordTrace]
  refine ⟨158116092609481295374006919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105410728406320863582671279 158116092609481295374006919)
  ·
    refine ⟨237174138914221943061010379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158116092609481295374006919 237174138914221943061010379)
    ·
      refine ⟨355761208371332914591515569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237174138914221943061010379 355761208371332914591515569)
      ·
        refine ⟨266820906278499685943636677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355761208371332914591515569 266820906278499685943636677)
        ·
          refine ⟨50028919927218691114431877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266820906278499685943636677 50028919927218691114431877)
          ·
            refine ⟨9380422486353504583955977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50028919927218691114431877 9380422486353504583955977)
            ·
              refine ⟨7035316864765128437966983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9380422486353504583955977 7035316864765128437966983)
              ·
                refine ⟨10552975297147692656950475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7035316864765128437966983 10552975297147692656950475)
                ·
                  refine ⟨15829462945721538985425713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10552975297147692656950475 15829462945721538985425713)
                  ·
                    refine ⟨11872097209291154239069285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15829462945721538985425713 11872097209291154239069285)
                    ·
                      refine ⟨2226018226742091419825491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11872097209291154239069285 2226018226742091419825491)
                      ·
                        rfl

theorem cell23_4335155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_4335155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335155 prefixEnd_4335155 := by exact prefixLift 4335155
  have htrace : WordTrace (prefixWord ++ tailWord_4335155) baseStart_4335155 baseEnd_4335155 := by
    simpa [prefixWord, tailWord_4335155, baseEnd_4335155] using wordTrace_append hprefix tailTrace_4335155
  have hstable : (prefixWord ++ tailWord_4335155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335155).length < 2 ^ (prefixWord ++ tailWord_4335155).sum := by decide
  have hdescent : baseEnd_4335155 < baseStart_4335155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335232 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2]
def baseStart_4335232 : Nat := 118140960795 + 4335232 * 2 ^ 59
def prefixEnd_4335232 : Nat := 4983230072969 + 3 ^ 40 * 4335232 * 2
def baseEnd_4335232 : Nat := 2226057764752487618562637

theorem tailTrace_4335232 : CollatzResearch.WordTrace tailWord_4335232 prefixEnd_4335232 2226057764752487618562637 := by
  unfold tailWord_4335232
  simp only [CollatzResearch.WordTrace]
  refine ⟨79059450515101168762279975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105412600686801558349706633 79059450515101168762279975)
  ·
    refine ⟨118589175772651753143419963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79059450515101168762279975 118589175772651753143419963)
    ·
      refine ⟨177883763658977629715129945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118589175772651753143419963 177883763658977629715129945)
      ·
        refine ⟨133412822744233222286347459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177883763658977629715129945 133412822744233222286347459)
        ·
          refine ⟨200119234116349833429521189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133412822744233222286347459 200119234116349833429521189)
          ·
            refine ⟨37522356396815593768035223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200119234116349833429521189 37522356396815593768035223)
            ·
              refine ⟨56283534595223390652052835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37522356396815593768035223 56283534595223390652052835)
              ·
                refine ⟨84425301892835085978079253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56283534595223390652052835 84425301892835085978079253)
                ·
                  refine ⟨3957436026226644655222465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84425301892835085978079253 3957436026226644655222465)
                  ·
                    refine ⟨2968077019669983491416849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957436026226644655222465 2968077019669983491416849)
                    ·
                      refine ⟨2226057764752487618562637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968077019669983491416849 2226057764752487618562637)
                      ·
                        rfl

theorem cell23_4335232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_4335232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335232 prefixEnd_4335232 := by exact prefixLift 4335232
  have htrace : WordTrace (prefixWord ++ tailWord_4335232) baseStart_4335232 baseEnd_4335232 := by
    simpa [prefixWord, tailWord_4335232, baseEnd_4335232] using wordTrace_append hprefix tailTrace_4335232
  have hstable : (prefixWord ++ tailWord_4335232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335232).length < 2 ^ (prefixWord ++ tailWord_4335232).sum := by decide
  have hdescent : baseEnd_4335232 < baseStart_4335232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335255 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 7]
def baseStart_4335255 : Nat := 118140960795 + 4335255 * 2 ^ 59
def prefixEnd_4335255 : Nat := 4983230072969 + 3 ^ 40 * 4335255 * 2
def baseEnd_4335255 : Nat := 247341063867504558730559

theorem tailTrace_4335255 : CollatzResearch.WordTrace tailWord_4335255 prefixEnd_4335255 247341063867504558730559 := by
  unfold tailWord_4335255
  simp only [CollatzResearch.WordTrace]
  refine ⟨158119739909119012452647219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105413159939412674968431479 158119739909119012452647219)
  ·
    refine ⟨237179609863678518678970829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158119739909119012452647219 237179609863678518678970829)
    ·
      refine ⟨88942353698879444504614061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237179609863678518678970829 88942353698879444504614061)
      ·
        refine ⟨33353382637079791689230273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88942353698879444504614061 33353382637079791689230273)
        ·
          refine ⟨25015036977809843766922705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33353382637079791689230273 25015036977809843766922705)
          ·
            refine ⟨18761277733357382825192029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25015036977809843766922705 18761277733357382825192029)
            ·
              refine ⟨7035479150009018559447011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18761277733357382825192029 7035479150009018559447011)
              ·
                refine ⟨10553218725013527839170517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7035479150009018559447011 10553218725013527839170517)
                ·
                  refine ⟨247341063867504558730559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10553218725013527839170517 247341063867504558730559)
                  ·
                    rfl

theorem cell23_4335255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 7].length) (baseStart_4335255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335255 prefixEnd_4335255 := by exact prefixLift 4335255
  have htrace : WordTrace (prefixWord ++ tailWord_4335255) baseStart_4335255 baseEnd_4335255 := by
    simpa [prefixWord, tailWord_4335255, baseEnd_4335255] using wordTrace_append hprefix tailTrace_4335255
  have hstable : (prefixWord ++ tailWord_4335255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335255).length < 2 ^ (prefixWord ++ tailWord_4335255).sum := by decide
  have hdescent : baseEnd_4335255 < baseStart_4335255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335306 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_4335306 : Nat := 118140960795 + 4335306 * 2 ^ 59
def prefixEnd_4335306 : Nat := 4983230072969 + 3 ^ 40 * 4335306 * 2
def baseEnd_4335306 : Nat := 247343973591213369893033

theorem tailTrace_4335306 : CollatzResearch.WordTrace tailWord_4335306 prefixEnd_4335306 247343973591213369893033 := by
  unfold tailWord_4335306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39530400007983562040688443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105414400021289498775169181 39530400007983562040688443)
  ·
    refine ⟨59295600011975343061032665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39530400007983562040688443 59295600011975343061032665)
    ·
      refine ⟨44471700008981507295774499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59295600011975343061032665 44471700008981507295774499)
      ·
        refine ⟨66707550013472260943661749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44471700008981507295774499 66707550013472260943661749)
        ·
          refine ⟨6253832813763024463468289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66707550013472260943661749 6253832813763024463468289)
          ·
            refine ⟨4690374610322268347601217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6253832813763024463468289 4690374610322268347601217)
            ·
              refine ⟨3517780957741701260700913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4690374610322268347601217 3517780957741701260700913)
              ·
                refine ⟨2638335718306275945525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517780957741701260700913 2638335718306275945525685)
                ·
                  refine ⟨247343973591213369893033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638335718306275945525685 247343973591213369893033)
                  ·
                    rfl

theorem cell23_4335306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_4335306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335306 prefixEnd_4335306 := by exact prefixLift 4335306
  have htrace : WordTrace (prefixWord ++ tailWord_4335306) baseStart_4335306 baseEnd_4335306 := by
    simpa [prefixWord, tailWord_4335306, baseEnd_4335306] using wordTrace_append hprefix tailTrace_4335306
  have hstable : (prefixWord ++ tailWord_4335306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335306).length < 2 ^ (prefixWord ++ tailWord_4335306).sum := by decide
  have hdescent : baseEnd_4335306 < baseStart_4335306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335322 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_4335322 : Nat := 118140960795 + 4335322 * 2 ^ 59
def prefixEnd_4335322 : Nat := 4983230072969 + 3 ^ 40 * 4335322 * 2
def baseEnd_4335322 : Nat := 2226103978011392266437223

theorem tailTrace_4335322 : CollatzResearch.WordTrace tailWord_4335322 prefixEnd_4335322 2226103978011392266437223 := by
  unfold tailWord_4335322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39530545899969070723834055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105414789066584188596890813 39530545899969070723834055)
  ·
    refine ⟨59295818849953606085751083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39530545899969070723834055 59295818849953606085751083)
    ·
      refine ⟨88943728274930409128626625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59295818849953606085751083 88943728274930409128626625)
      ·
        refine ⟨66707796206197806846469969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88943728274930409128626625 66707796206197806846469969)
        ·
          refine ⟨50030847154648355134852477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66707796206197806846469969 50030847154648355134852477)
          ·
            refine ⟨18761567682993133175569679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50030847154648355134852477 18761567682993133175569679)
            ·
              refine ⟨28142351524489699763354519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18761567682993133175569679 28142351524489699763354519)
              ·
                refine ⟨42213527286734549645031779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28142351524489699763354519 42213527286734549645031779)
                ·
                  refine ⟨63320290930101824467547669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42213527286734549645031779 63320290930101824467547669)
                  ·
                    refine ⟨2968138637348523021916297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63320290930101824467547669 2968138637348523021916297)
                    ·
                      refine ⟨2226103978011392266437223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968138637348523021916297 2226103978011392266437223)
                      ·
                        rfl

theorem cell23_4335322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_4335322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335322 prefixEnd_4335322 := by exact prefixLift 4335322
  have htrace : WordTrace (prefixWord ++ tailWord_4335322) baseStart_4335322 baseEnd_4335322 := by
    simpa [prefixWord, tailWord_4335322, baseEnd_4335322] using wordTrace_append hprefix tailTrace_4335322
  have hstable : (prefixWord ++ tailWord_4335322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335322).length < 2 ^ (prefixWord ++ tailWord_4335322).sum := by decide
  have hdescent : baseEnd_4335322 < baseStart_4335322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335332 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_4335332 : Nat := 118140960795 + 4335332 * 2 ^ 59
def prefixEnd_4335332 : Nat := 4983230072969 + 3 ^ 40 * 4335332 * 2
def baseEnd_4335332 : Nat := 742036370939312409104059

theorem tailTrace_4335332 : CollatzResearch.WordTrace tailWord_4335332 prefixEnd_4335332 742036370939312409104059 := by
  unfold tailWord_4335332
  simp only [CollatzResearch.WordTrace]
  refine ⟨79061274164920027301600125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105415032219893369735466833 79061274164920027301600125)
  ·
    refine ⟨29647977811845010238100047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79061274164920027301600125 29647977811845010238100047)
    ·
      refine ⟨44471966717767515357150071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29647977811845010238100047 44471966717767515357150071)
      ·
        refine ⟨66707950076651273035725107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44471966717767515357150071 66707950076651273035725107)
        ·
          refine ⟨100061925114976909553587661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66707950076651273035725107 100061925114976909553587661)
          ·
            refine ⟨37523221918116341082595373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100061925114976909553587661 37523221918116341082595373)
            ·
              refine ⟨14071208219293627905973265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37523221918116341082595373 14071208219293627905973265)
              ·
                refine ⟨10553406164470220929479949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14071208219293627905973265 10553406164470220929479949)
                ·
                  refine ⟨3957527311676332848554981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10553406164470220929479949 3957527311676332848554981)
                  ·
                    refine ⟨742036370939312409104059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957527311676332848554981 742036370939312409104059)
                    ·
                      rfl

theorem cell23_4335332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_4335332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335332 prefixEnd_4335332 := by exact prefixLift 4335332
  have htrace : WordTrace (prefixWord ++ tailWord_4335332) baseStart_4335332 baseEnd_4335332 := by
    simpa [prefixWord, tailWord_4335332, baseEnd_4335332] using wordTrace_append hprefix tailTrace_4335332
  have hstable : (prefixWord ++ tailWord_4335332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335332).length < 2 ^ (prefixWord ++ tailWord_4335332).sum := by decide
  have hdescent : baseEnd_4335332 < baseStart_4335332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335342 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_4335342 : Nat := 118140960795 + 4335342 * 2 ^ 59
def prefixEnd_4335342 : Nat := 4983230072969 + 3 ^ 40 * 4335342 * 2
def baseEnd_4335342 : Nat := 2226114247624482188187131

theorem tailTrace_4335342 : CollatzResearch.WordTrace tailWord_4335342 prefixEnd_4335342 2226114247624482188187131 := by
  unfold tailWord_4335342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765364132475478288883035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105415275373202550874042853 19765364132475478288883035)
  ·
    refine ⟨29648046198713217433324553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19765364132475478288883035 29648046198713217433324553)
    ·
      refine ⟨22236034649034913074993415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29648046198713217433324553 22236034649034913074993415)
      ·
        refine ⟨33354051973552369612490123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22236034649034913074993415 33354051973552369612490123)
        ·
          refine ⟨50031077960328554418735185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33354051973552369612490123 50031077960328554418735185)
          ·
            refine ⟨37523308470246415814051389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50031077960328554418735185 37523308470246415814051389)
            ·
              refine ⟨14071240676342405930269271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37523308470246415814051389 14071240676342405930269271)
              ·
                refine ⟨21106861014513608895403907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14071240676342405930269271 21106861014513608895403907)
                ·
                  refine ⟨31660291521770413343105861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21106861014513608895403907 31660291521770413343105861)
                  ·
                    refine ⟨5936304660331952501832349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31660291521770413343105861 5936304660331952501832349)
                    ·
                      refine ⟨2226114247624482188187131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5936304660331952501832349 2226114247624482188187131)
                      ·
                        rfl

theorem cell23_4335342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_4335342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335342 prefixEnd_4335342 := by exact prefixLift 4335342
  have htrace : WordTrace (prefixWord ++ tailWord_4335342) baseStart_4335342 baseEnd_4335342 := by
    simpa [prefixWord, tailWord_4335342, baseEnd_4335342] using wordTrace_append hprefix tailTrace_4335342
  have hstable : (prefixWord ++ tailWord_4335342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335342).length < 2 ^ (prefixWord ++ tailWord_4335342).sum := by decide
  have hdescent : baseEnd_4335342 < baseStart_4335342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335362 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_4335362 : Nat := 118140960795 + 4335362 * 2 ^ 59
def prefixEnd_4335362 : Nat := 4983230072969 + 3 ^ 40 * 4335362 * 2
def baseEnd_4335362 : Nat := 247347168581952456659671

theorem tailTrace_4335362 : CollatzResearch.WordTrace tailWord_4335362 prefixEnd_4335362 247347168581952456659671 := by
  unfold tailWord_4335362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39530910629932842431698085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105415761679820913151194893 39530910629932842431698085)
  ·
    refine ⟨7412045743112407955943391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39530910629932842431698085 7412045743112407955943391)
    ·
      refine ⟨11118068614668611933915087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412045743112407955943391 11118068614668611933915087)
      ·
        refine ⟨16677102922002917900872631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11118068614668611933915087 16677102922002917900872631)
        ·
          refine ⟨25015654383004376851308947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16677102922002917900872631 25015654383004376851308947)
          ·
            refine ⟨37523481574506565276963421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25015654383004376851308947 37523481574506565276963421)
            ·
              refine ⟨14071305590439961978861283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37523481574506565276963421 14071305590439961978861283)
              ·
                refine ⟨21106958385659942968291925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14071305590439961978861283 21106958385659942968291925)
                ·
                  refine ⟨247347168581952456659671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21106958385659942968291925 247347168581952456659671)
                  ·
                    rfl

theorem cell23_4335362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_4335362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335362 prefixEnd_4335362 := by exact prefixLift 4335362
  have htrace : WordTrace (prefixWord ++ tailWord_4335362) baseStart_4335362 baseEnd_4335362 := by
    simpa [prefixWord, tailWord_4335362, baseEnd_4335362] using wordTrace_append hprefix tailTrace_4335362
  have hstable : (prefixWord ++ tailWord_4335362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335362).length < 2 ^ (prefixWord ++ tailWord_4335362).sum := by decide
  have hdescent : baseEnd_4335362 < baseStart_4335362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335375 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 3, 5]
def baseStart_4335375 : Nat := 118140960795 + 4335375 * 2 ^ 59
def prefixEnd_4335375 : Nat := 4983230072969 + 3 ^ 40 * 4335375 * 2
def baseEnd_4335375 : Nat := 742043730828693519691493

theorem tailTrace_4335375 : CollatzResearch.WordTrace tailWord_4335375 prefixEnd_4335375 742043730828693519691493 := by
  unfold tailWord_4335375
  simp only [CollatzResearch.WordTrace]
  refine ⟨158124116668684272947015579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105416077779122848631343719 158124116668684272947015579)
  ·
    refine ⟨237186175003026409420523369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158124116668684272947015579 237186175003026409420523369)
    ·
      refine ⟨177889631252269807065392527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237186175003026409420523369 177889631252269807065392527)
      ·
        refine ⟨266834446878404710598088791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177889631252269807065392527 266834446878404710598088791)
        ·
          refine ⟨400251670317607065897133187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266834446878404710598088791 400251670317607065897133187)
          ·
            refine ⟨600377505476410598845699781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400251670317607065897133187 600377505476410598845699781)
            ·
              refine ⟨112570782276826987283568709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 600377505476410598845699781 112570782276826987283568709)
              ·
                refine ⟨21107021676905060115669133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112570782276826987283568709 21107021676905060115669133)
                ·
                  refine ⟨7915133128839397543375925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21107021676905060115669133 7915133128839397543375925)
                  ·
                    refine ⟨742043730828693519691493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7915133128839397543375925 742043730828693519691493)
                    ·
                      rfl

theorem cell23_4335375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_4335375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335375 prefixEnd_4335375 := by exact prefixLift 4335375
  have htrace : WordTrace (prefixWord ++ tailWord_4335375) baseStart_4335375 baseEnd_4335375 := by
    simpa [prefixWord, tailWord_4335375, baseEnd_4335375] using wordTrace_append hprefix tailTrace_4335375
  have hstable : (prefixWord ++ tailWord_4335375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335375).length < 2 ^ (prefixWord ++ tailWord_4335375).sum := by decide
  have hdescent : baseEnd_4335375 < baseStart_4335375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335423 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 3, 1, 3]
def baseStart_4335423 : Nat := 118140960795 + 4335423 * 2 ^ 59
def prefixEnd_4335423 : Nat := 4983230072969 + 3 ^ 40 * 4335423 * 2
def baseEnd_4335423 : Nat := 2226155839557496371274259

theorem tailTrace_4335423 : CollatzResearch.WordTrace tailWord_4335423 prefixEnd_4335423 2226155839557496371274259 := by
  unfold tailWord_4335423
  simp only [CollatzResearch.WordTrace]
  refine ⟨158125867372510377144762923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105417244915006918096508615 158125867372510377144762923)
  ·
    refine ⟨237188801058765565717144385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158125867372510377144762923 237188801058765565717144385)
    ·
      refine ⟨177891600794074174287858289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237188801058765565717144385 177891600794074174287858289)
      ·
        refine ⟨133418700595555630715893717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177891600794074174287858289 133418700595555630715893717)
        ·
          refine ⟨3127000795208335094903759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 133418700595555630715893717 3127000795208335094903759)
          ·
            refine ⟨4690501192812502642355639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127000795208335094903759 4690501192812502642355639)
            ·
              refine ⟨7035751789218753963533459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690501192812502642355639 7035751789218753963533459)
              ·
                refine ⟨10553627683828130945300189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7035751789218753963533459 10553627683828130945300189)
                ·
                  refine ⟨3957610381435549104487571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10553627683828130945300189 3957610381435549104487571)
                  ·
                    refine ⟨5936415572153323656731357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957610381435549104487571 5936415572153323656731357)
                    ·
                      refine ⟨2226155839557496371274259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5936415572153323656731357 2226155839557496371274259)
                      ·
                        rfl

theorem cell23_4335423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_4335423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335423 prefixEnd_4335423 := by exact prefixLift 4335423
  have htrace : WordTrace (prefixWord ++ tailWord_4335423) baseStart_4335423 baseEnd_4335423 := by
    simpa [prefixWord, tailWord_4335423, baseEnd_4335423] using wordTrace_append hprefix tailTrace_4335423
  have hstable : (prefixWord ++ tailWord_4335423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335423).length < 2 ^ (prefixWord ++ tailWord_4335423).sum := by decide
  have hdescent : baseEnd_4335423 < baseStart_4335423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335432 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_4335432 : Nat := 118140960795 + 4335432 * 2 ^ 59
def prefixEnd_4335432 : Nat := 4983230072969 + 3 ^ 40 * 4335432 * 2
def baseEnd_4335432 : Nat := 2226160460883386836061717

theorem tailTrace_4335432 : CollatzResearch.WordTrace tailWord_4335432 prefixEnd_4335432 2226160460883386836061717 := by
  unfold tailWord_4335432
  simp only [CollatzResearch.WordTrace]
  refine ⟨79063097814738885840920275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105417463752985181121227033 79063097814738885840920275)
  ·
    refine ⟨118594646722108328761380413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79063097814738885840920275 118594646722108328761380413)
    ·
      refine ⟨44472992520790623285517655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118594646722108328761380413 44472992520790623285517655)
      ·
        refine ⟨66709488781185934928276483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44472992520790623285517655 66709488781185934928276483)
        ·
          refine ⟨100064233171778902392414725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66709488781185934928276483 100064233171778902392414725)
          ·
            refine ⟨18762043719708544198577761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100064233171778902392414725 18762043719708544198577761)
            ·
              refine ⟨14071532789781408148933321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18762043719708544198577761 14071532789781408148933321)
              ·
                refine ⟨10553649592336056111699991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14071532789781408148933321 10553649592336056111699991)
                ·
                  refine ⟨15830474388504084167549987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10553649592336056111699991 15830474388504084167549987)
                  ·
                    refine ⟨23745711582756126251324981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15830474388504084167549987 23745711582756126251324981)
                    ·
                      refine ⟨2226160460883386836061717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23745711582756126251324981 2226160460883386836061717)
                      ·
                        rfl

theorem cell23_4335432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_4335432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335432 prefixEnd_4335432 := by exact prefixLift 4335432
  have htrace : WordTrace (prefixWord ++ tailWord_4335432) baseStart_4335432 baseEnd_4335432 := by
    simpa [prefixWord, tailWord_4335432, baseEnd_4335432] using wordTrace_append hprefix tailTrace_4335432
  have hstable : (prefixWord ++ tailWord_4335432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335432).length < 2 ^ (prefixWord ++ tailWord_4335432).sum := by decide
  have hdescent : baseEnd_4335432 < baseStart_4335432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335442 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4335442 : Nat := 118140960795 + 4335442 * 2 ^ 59
def prefixEnd_4335442 : Nat := 4983230072969 + 3 ^ 40 * 4335442 * 2
def baseEnd_4335442 : Nat := 2226165595689931796936671

theorem tailTrace_4335442 : CollatzResearch.WordTrace tailWord_4335442 prefixEnd_4335442 2226165595689931796936671 := by
  unfold tailWord_4335442
  simp only [CollatzResearch.WordTrace]
  refine ⟨39531640089860385847426145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105417706906294362259803053 39531640089860385847426145)
  ·
    refine ⟨29648730067395289385569609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39531640089860385847426145 29648730067395289385569609)
    ·
      refine ⟨22236547550546467039177207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29648730067395289385569609 22236547550546467039177207)
      ·
        refine ⟨33354821325819700558765811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22236547550546467039177207 33354821325819700558765811)
        ·
          refine ⟨50032231988729550838148717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33354821325819700558765811 50032231988729550838148717)
          ·
            refine ⟨18762086995773581564305769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50032231988729550838148717 18762086995773581564305769)
            ·
              refine ⟨14071565246830186173229327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18762086995773581564305769 14071565246830186173229327)
              ·
                refine ⟨21107347870245279259843991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14071565246830186173229327 21107347870245279259843991)
                ·
                  refine ⟨31661021805367918889765987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21107347870245279259843991 31661021805367918889765987)
                  ·
                    refine ⟨47491532708051878334648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31661021805367918889765987 47491532708051878334648981)
                    ·
                      refine ⟨2226165595689931796936671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47491532708051878334648981 2226165595689931796936671)
                      ·
                        rfl

theorem cell23_4335442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4335442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335442 prefixEnd_4335442 := by exact prefixLift 4335442
  have htrace : WordTrace (prefixWord ++ tailWord_4335442) baseStart_4335442 baseEnd_4335442 := by
    simpa [prefixWord, tailWord_4335442, baseEnd_4335442] using wordTrace_append hprefix tailTrace_4335442
  have hstable : (prefixWord ++ tailWord_4335442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335442).length < 2 ^ (prefixWord ++ tailWord_4335442).sum := by decide
  have hdescent : baseEnd_4335442 < baseStart_4335442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335459 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4]
def baseStart_4335459 : Nat := 118140960795 + 4335459 * 2 ^ 59
def prefixEnd_4335459 : Nat := 4983230072969 + 3 ^ 40 * 4335459 * 2
def baseEnd_4335459 : Nat := 2226174324861058230424093

theorem tailTrace_4335459 : CollatzResearch.WordTrace tailWord_4335459 prefixEnd_4335459 2226174324861058230424093 := by
  unfold tailWord_4335459
  simp only [CollatzResearch.WordTrace]
  refine ⟨158127180400379955293073431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105418120266919970195382287 158127180400379955293073431)
  ·
    refine ⟨237190770600569932939610147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158127180400379955293073431 237190770600569932939610147)
    ·
      refine ⟨355786155900854899409415221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237190770600569932939610147 355786155900854899409415221)
      ·
        refine ⟨33354952115705146819632677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 355786155900854899409415221 33354952115705146819632677)
        ·
          refine ⟨6254053521694715028681127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33354952115705146819632677 6254053521694715028681127)
          ·
            refine ⟨9381080282542072543021691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254053521694715028681127 9381080282542072543021691)
            ·
              refine ⟨14071620423813108814532537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9381080282542072543021691 14071620423813108814532537)
              ·
                refine ⟨10553715317859831610899403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14071620423813108814532537 10553715317859831610899403)
                ·
                  refine ⟨15830572976789747416349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10553715317859831610899403 15830572976789747416349105)
                  ·
                    refine ⟨11872929732592310562261829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15830572976789747416349105 11872929732592310562261829)
                    ·
                      refine ⟨2226174324861058230424093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11872929732592310562261829 2226174324861058230424093)
                      ·
                        rfl

theorem cell23_4335459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_4335459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335459 prefixEnd_4335459 := by exact prefixLift 4335459
  have htrace : WordTrace (prefixWord ++ tailWord_4335459) baseStart_4335459 baseEnd_4335459 := by
    simpa [prefixWord, tailWord_4335459, baseEnd_4335459] using wordTrace_append hprefix tailTrace_4335459
  have hstable : (prefixWord ++ tailWord_4335459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335459).length < 2 ^ (prefixWord ++ tailWord_4335459).sum := by decide
  have hdescent : baseEnd_4335459 < baseStart_4335459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335463 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_4335463 : Nat := 118140960795 + 4335463 * 2 ^ 59
def prefixEnd_4335463 : Nat := 4983230072969 + 3 ^ 40 * 4335463 * 2
def baseEnd_4335463 : Nat := 2226176378783676214774075

theorem tailTrace_4335463 : CollatzResearch.WordTrace tailWord_4335463 prefixEnd_4335463 2226176378783676214774075 := by
  unfold tailWord_4335463
  simp only [CollatzResearch.WordTrace]
  refine ⟨158127326292365463976219043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105418217528243642650812695 158127326292365463976219043)
  ·
    refine ⟨237190989438548195964328565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158127326292365463976219043 237190989438548195964328565)
    ·
      refine ⟨22236655259863893371655803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237190989438548195964328565 22236655259863893371655803)
      ·
        refine ⟨33354982889795840057483705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22236655259863893371655803 33354982889795840057483705)
        ·
          refine ⟨25016237167346880043112779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33354982889795840057483705 25016237167346880043112779)
          ·
            refine ⟨37524355751020320064669169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25016237167346880043112779 37524355751020320064669169)
            ·
              refine ⟨28143266813265240048501877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37524355751020320064669169 28143266813265240048501877)
              ·
                refine ⟨2638431263743616254547051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28143266813265240048501877 2638431263743616254547051)
                ·
                  refine ⟨3957646895615424381820577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638431263743616254547051 3957646895615424381820577)
                  ·
                    refine ⟨2968235171711568286365433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957646895615424381820577 2968235171711568286365433)
                    ·
                      refine ⟨2226176378783676214774075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968235171711568286365433 2226176378783676214774075)
                      ·
                        rfl

theorem cell23_4335463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_4335463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335463 prefixEnd_4335463 := by exact prefixLift 4335463
  have htrace : WordTrace (prefixWord ++ tailWord_4335463) baseStart_4335463 baseEnd_4335463 := by
    simpa [prefixWord, tailWord_4335463, baseEnd_4335463] using wordTrace_append hprefix tailTrace_4335463
  have hstable : (prefixWord ++ tailWord_4335463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335463).length < 2 ^ (prefixWord ++ tailWord_4335463).sum := by decide
  have hdescent : baseEnd_4335463 < baseStart_4335463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335465 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_4335465 : Nat := 118140960795 + 4335465 * 2 ^ 59
def prefixEnd_4335465 : Nat := 4983230072969 + 3 ^ 40 * 4335465 * 2
def baseEnd_4335465 : Nat := 742059135248328402316355

theorem tailTrace_4335465 : CollatzResearch.WordTrace tailWord_4335465 prefixEnd_4335465 742059135248328402316355 := by
  unfold tailWord_4335465
  simp only [CollatzResearch.WordTrace]
  refine ⟨158127399238358218317791849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105418266158905478878527899 158127399238358218317791849)
  ·
    refine ⟨118595549428768663738343887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158127399238358218317791849 118595549428768663738343887)
    ·
      refine ⟨177893324143152995607515831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118595549428768663738343887 177893324143152995607515831)
      ·
        refine ⟨266839986214729493411273747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177893324143152995607515831 266839986214729493411273747)
        ·
          refine ⟨400259979322094240116910621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266839986214729493411273747 400259979322094240116910621)
          ·
            refine ⟨150097492245785340043841483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400259979322094240116910621 150097492245785340043841483)
            ·
              refine ⟨225146238368678010065762225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150097492245785340043841483 225146238368678010065762225)
              ·
                refine ⟨168859678776508507549321669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225146238368678010065762225 168859678776508507549321669)
                ·
                  refine ⟨31661189770595345165497813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168859678776508507549321669 31661189770595345165497813)
                  ·
                    refine ⟨742059135248328402316355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31661189770595345165497813 742059135248328402316355)
                    ·
                      rfl

theorem cell23_4335465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_4335465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335465 prefixEnd_4335465 := by exact prefixLift 4335465
  have htrace : WordTrace (prefixWord ++ tailWord_4335465) baseStart_4335465 baseEnd_4335465 := by
    simpa [prefixWord, tailWord_4335465, baseEnd_4335465] using wordTrace_append hprefix tailTrace_4335465
  have hstable : (prefixWord ++ tailWord_4335465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335465).length < 2 ^ (prefixWord ++ tailWord_4335465).sum := by decide
  have hdescent : baseEnd_4335465 < baseStart_4335465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335486 : List Nat := [4, 2, 3, 1, 1, 3, 1, 8]
def baseStart_4335486 : Nat := 118140960795 + 4335486 * 2 ^ 59
def prefixEnd_4335486 : Nat := 4983230072969 + 3 ^ 40 * 4335486 * 2
def baseEnd_4335486 : Nat := 82451414401434430547647

theorem tailTrace_4335486 : CollatzResearch.WordTrace tailWord_4335486 prefixEnd_4335486 82451414401434430547647 := by
  unfold tailWord_4335486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19766020646410267363038289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105418776780854759269537541 19766020646410267363038289)
  ·
    refine ⟨14824515484807700522278717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19766020646410267363038289 14824515484807700522278717)
    ·
      refine ⟨5559193306802887695854519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14824515484807700522278717 5559193306802887695854519)
      ·
        refine ⟨8338789960204331543781779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5559193306802887695854519 8338789960204331543781779)
        ·
          refine ⟨12508184940306497315672669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338789960204331543781779 12508184940306497315672669)
          ·
            refine ⟨4690569352614936493377251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12508184940306497315672669 4690569352614936493377251)
            ·
              refine ⟨7035854028922404740065877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690569352614936493377251 7035854028922404740065877)
              ·
                refine ⟨82451414401434430547647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7035854028922404740065877 82451414401434430547647)
                ·
                  rfl

theorem cell23_4335486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_4335486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335486 prefixEnd_4335486 := by exact prefixLift 4335486
  have htrace : WordTrace (prefixWord ++ tailWord_4335486) baseStart_4335486 baseEnd_4335486 := by
    simpa [prefixWord, tailWord_4335486, baseEnd_4335486] using wordTrace_append hprefix tailTrace_4335486
  have hstable : (prefixWord ++ tailWord_4335486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335486).length < 2 ^ (prefixWord ++ tailWord_4335486).sum := by decide
  have hdescent : baseEnd_4335486 < baseStart_4335486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335496 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4335496 : Nat := 118140960795 + 4335496 * 2 ^ 59
def prefixEnd_4335496 : Nat := 4983230072969 + 3 ^ 40 * 4335496 * 2
def baseEnd_4335496 : Nat := 2226193323645274585661423

theorem tailTrace_4335496 : CollatzResearch.WordTrace tailWord_4335496 prefixEnd_4335496 2226193323645274585661423 := by
  unfold tailWord_4335496
  simp only [CollatzResearch.WordTrace]
  refine ⟨79064264950622955306085171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105419019934163940408113561 79064264950622955306085171)
  ·
    refine ⟨118596397425934432959127757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79064264950622955306085171 118596397425934432959127757)
    ·
      refine ⟨44473649034725412359672909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118596397425934432959127757 44473649034725412359672909)
      ·
        refine ⟨16677618388022029634877341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44473649034725412359672909 16677618388022029634877341)
        ·
          refine ⟨6254106895508261113079003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16677618388022029634877341 6254106895508261113079003)
          ·
            refine ⟨9381160343262391669618505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254106895508261113079003 9381160343262391669618505)
            ·
              refine ⟨7035870257446793752213879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9381160343262391669618505 7035870257446793752213879)
              ·
                refine ⟨10553805386170190628320819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7035870257446793752213879 10553805386170190628320819)
                ·
                  refine ⟨15830708079255285942481229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10553805386170190628320819 15830708079255285942481229)
                  ·
                    refine ⟨5936515529720732228430461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15830708079255285942481229 5936515529720732228430461)
                    ·
                      refine ⟨2226193323645274585661423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5936515529720732228430461 2226193323645274585661423)
                      ·
                        rfl

theorem cell23_4335496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4335496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335496 prefixEnd_4335496 := by exact prefixLift 4335496
  have htrace : WordTrace (prefixWord ++ tailWord_4335496) baseStart_4335496 baseEnd_4335496 := by
    simpa [prefixWord, tailWord_4335496, baseEnd_4335496] using wordTrace_append hprefix tailTrace_4335496
  have hstable : (prefixWord ++ tailWord_4335496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335496).length < 2 ^ (prefixWord ++ tailWord_4335496).sum := by decide
  have hdescent : baseEnd_4335496 < baseStart_4335496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335549 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4335549 : Nat := 118140960795 + 4335549 * 2 ^ 59
def prefixEnd_4335549 : Nat := 4983230072969 + 3 ^ 40 * 4335549 * 2
def baseEnd_4335549 : Nat := 2226220538119962878298679

theorem tailTrace_4335549 : CollatzResearch.WordTrace tailWord_4335549 prefixEnd_4335549 2226220538119962878298679 := by
  unfold tailWord_4335549
  simp only [CollatzResearch.WordTrace]
  refine ⟨158130462970053900663849701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105420308646702600442566467 158130462970053900663849701)
  ·
    refine ⟨29649461806885106374471819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158130462970053900663849701 29649461806885106374471819)
    ·
      refine ⟨44474192710327659561707729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29649461806885106374471819 44474192710327659561707729)
      ·
        refine ⟨33355644532745744671280797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44474192710327659561707729 33355644532745744671280797)
        ·
          refine ⟨12508366699779654251730299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33355644532745744671280797 12508366699779654251730299)
          ·
            refine ⟨18762550049669481377595449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12508366699779654251730299 18762550049669481377595449)
            ·
              refine ⟨14071912537252111033196587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18762550049669481377595449 14071912537252111033196587)
              ·
                refine ⟨21107868805878166549794881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14071912537252111033196587 21107868805878166549794881)
                ·
                  refine ⟨15830901604408624912346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21107868805878166549794881 15830901604408624912346161)
                  ·
                    refine ⟨11873176203306468684259621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15830901604408624912346161 11873176203306468684259621)
                    ·
                      refine ⟨2226220538119962878298679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11873176203306468684259621 2226220538119962878298679)
                      ·
                        rfl

theorem cell23_4335549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4335549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335549 prefixEnd_4335549 := by exact prefixLift 4335549
  have htrace : WordTrace (prefixWord ++ tailWord_4335549) baseStart_4335549 baseEnd_4335549 := by
    simpa [prefixWord, tailWord_4335549, baseEnd_4335549] using wordTrace_append hprefix tailTrace_4335549
  have hstable : (prefixWord ++ tailWord_4335549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335549).length < 2 ^ (prefixWord ++ tailWord_4335549).sum := by decide
  have hdescent : baseEnd_4335549 < baseStart_4335549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335619 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 3, 4]
def baseStart_4335619 : Nat := 118140960795 + 4335619 * 2 ^ 59
def prefixEnd_4335619 : Nat := 4983230072969 + 3 ^ 40 * 4335619 * 2
def baseEnd_4335619 : Nat := 742085493921925868141119

theorem tailTrace_4335619 : CollatzResearch.WordTrace tailWord_4335619 prefixEnd_4335619 742085493921925868141119 := by
  unfold tailWord_4335619
  simp only [CollatzResearch.WordTrace]
  refine ⟨158133016079800302618897911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105422010719866868412598607 158133016079800302618897911)
  ·
    refine ⟨237199524119700453928346867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158133016079800302618897911 237199524119700453928346867)
    ·
      refine ⟨355799286179550680892520301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237199524119700453928346867 355799286179550680892520301)
      ·
        refine ⟨133424732317331505334695113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 355799286179550680892520301 133424732317331505334695113)
        ·
          refine ⟨100068549237998629001021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133424732317331505334695113 100068549237998629001021335)
          ·
            refine ⟨150102823856997943501532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100068549237998629001021335 150102823856997943501532003)
            ·
              refine ⟨225154235785496915252298005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150102823856997943501532003 225154235785496915252298005)
              ·
                refine ⟨10554104802445167902451469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225154235785496915252298005 10554104802445167902451469)
                ·
                  refine ⟨3957789300916937963419301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10554104802445167902451469 3957789300916937963419301)
                  ·
                    refine ⟨742085493921925868141119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957789300916937963419301 742085493921925868141119)
                    ·
                      rfl

theorem cell23_4335619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 4].length) (baseStart_4335619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335619 prefixEnd_4335619 := by exact prefixLift 4335619
  have htrace : WordTrace (prefixWord ++ tailWord_4335619) baseStart_4335619 baseEnd_4335619 := by
    simpa [prefixWord, tailWord_4335619, baseEnd_4335619] using wordTrace_append hprefix tailTrace_4335619
  have hstable : (prefixWord ++ tailWord_4335619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335619).length < 2 ^ (prefixWord ++ tailWord_4335619).sum := by decide
  have hdescent : baseEnd_4335619 < baseStart_4335619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335653 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_4335653 : Nat := 118140960795 + 4335653 * 2 ^ 59
def prefixEnd_4335653 : Nat := 4983230072969 + 3 ^ 40 * 4335653 * 2
def baseEnd_4335653 : Nat := 742091313369343490466067

theorem tailTrace_4335653 : CollatzResearch.WordTrace tailWord_4335653 prefixEnd_4335653 742091313369343490466067 := by
  unfold tailWord_4335653
  simp only [CollatzResearch.WordTrace]
  refine ⟨158134256161677126425635613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105422837441118084283757075 158134256161677126425635613)
  ·
    refine ⟨59300346060628922409613355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158134256161677126425635613 59300346060628922409613355)
    ·
      refine ⟨88950519090943383614420033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59300346060628922409613355 88950519090943383614420033)
      ·
        refine ⟨66712889318207537710815025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88950519090943383614420033 66712889318207537710815025)
        ·
          refine ⟨50034666988655653283111269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66712889318207537710815025 50034666988655653283111269)
          ·
            refine ⟨9381500060372934990583363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50034666988655653283111269 9381500060372934990583363)
            ·
              refine ⟨14072250090559402485875045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9381500060372934990583363 14072250090559402485875045)
              ·
                refine ⟨2638546891979887966101571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14072250090559402485875045 2638546891979887966101571)
                ·
                  refine ⟨3957820337969831949152357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638546891979887966101571 3957820337969831949152357)
                  ·
                    refine ⟨742091313369343490466067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957820337969831949152357 742091313369343490466067)
                    ·
                      rfl

theorem cell23_4335653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_4335653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335653 prefixEnd_4335653 := by exact prefixLift 4335653
  have htrace : WordTrace (prefixWord ++ tailWord_4335653) baseStart_4335653 baseEnd_4335653 := by
    simpa [prefixWord, tailWord_4335653, baseEnd_4335653] using wordTrace_append hprefix tailTrace_4335653
  have hstable : (prefixWord ++ tailWord_4335653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335653).length < 2 ^ (prefixWord ++ tailWord_4335653).sum := by decide
  have hdescent : baseEnd_4335653 < baseStart_4335653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335679 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 3, 5]
def baseStart_4335679 : Nat := 118140960795 + 4335679 * 2 ^ 59
def prefixEnd_4335679 : Nat := 4983230072969 + 3 ^ 40 * 4335679 * 2
def baseEnd_4335679 : Nat := 742095763535015789891027

theorem tailTrace_4335679 : CollatzResearch.WordTrace tailWord_4335679 prefixEnd_4335679 742095763535015789891027 := by
  unfold tailWord_4335679
  simp only [CollatzResearch.WordTrace]
  refine ⟨158135204459582932866082091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105423469639721955244054727 158135204459582932866082091)
  ·
    refine ⟨237202806689374399299123137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158135204459582932866082091 237202806689374399299123137)
    ·
      refine ⟨177902105017030799474342353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237202806689374399299123137 177902105017030799474342353)
      ·
        refine ⟨133426578762773099605756765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177902105017030799474342353 133426578762773099605756765)
        ·
          refine ⟨50034967036039912352158787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133426578762773099605756765 50034967036039912352158787)
          ·
            refine ⟨75052450554059868528238181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50034967036039912352158787 75052450554059868528238181)
            ·
              refine ⟨14072334478886225349044659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75052450554059868528238181 14072334478886225349044659)
              ·
                refine ⟨21108501718329338023566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14072334478886225349044659 21108501718329338023566989)
                ·
                  refine ⟨7915688144373501758837621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21108501718329338023566989 7915688144373501758837621)
                  ·
                    refine ⟨742095763535015789891027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7915688144373501758837621 742095763535015789891027)
                    ·
                      rfl

theorem cell23_4335679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_4335679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335679 prefixEnd_4335679 := by exact prefixLift 4335679
  have htrace : WordTrace (prefixWord ++ tailWord_4335679) baseStart_4335679 baseEnd_4335679 := by
    simpa [prefixWord, tailWord_4335679, baseEnd_4335679] using wordTrace_append hprefix tailTrace_4335679
  have hstable : (prefixWord ++ tailWord_4335679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335679).length < 2 ^ (prefixWord ++ tailWord_4335679).sum := by decide
  have hdescent : baseEnd_4335679 < baseStart_4335679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335693 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4335693 : Nat := 118140960795 + 4335693 * 2 ^ 59
def prefixEnd_4335693 : Nat := 4983230072969 + 3 ^ 40 * 4335693 * 2
def baseEnd_4335693 : Nat := 2226294479334210314898017

theorem tailTrace_4335693 : CollatzResearch.WordTrace tailWord_4335693 prefixEnd_4335693 2226294479334210314898017 := by
  unfold tailWord_4335693
  simp only [CollatzResearch.WordTrace]
  refine ⟨158135715081532213257091733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105423810054354808838061155 158135715081532213257091733)
  ·
    refine ⟨7412611644446822496426175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158135715081532213257091733 7412611644446822496426175)
    ·
      refine ⟨11118917466670233744639263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412611644446822496426175 11118917466670233744639263)
      ·
        refine ⟨16678376200005350616958895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11118917466670233744639263 16678376200005350616958895)
        ·
          refine ⟨25017564300008025925438343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16678376200005350616958895 25017564300008025925438343)
          ·
            refine ⟨37526346450012038888157515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25017564300008025925438343 37526346450012038888157515)
            ·
              refine ⟨56289519675018058332236273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37526346450012038888157515 56289519675018058332236273)
              ·
                refine ⟨42217139756263543749177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56289519675018058332236273 42217139756263543749177205)
                ·
                  refine ⟨3957856852149707226485363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42217139756263543749177205 3957856852149707226485363)
                  ·
                    refine ⟨5936785278224560839728045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957856852149707226485363 5936785278224560839728045)
                    ·
                      refine ⟨2226294479334210314898017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5936785278224560839728045 2226294479334210314898017)
                      ·
                        rfl

theorem cell23_4335693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4335693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335693 prefixEnd_4335693 := by exact prefixLift 4335693
  have htrace : WordTrace (prefixWord ++ tailWord_4335693) baseStart_4335693 baseEnd_4335693 := by
    simpa [prefixWord, tailWord_4335693, baseEnd_4335693] using wordTrace_append hprefix tailTrace_4335693
  have hstable : (prefixWord ++ tailWord_4335693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335693).length < 2 ^ (prefixWord ++ tailWord_4335693).sum := by decide
  have hdescent : baseEnd_4335693 < baseStart_4335693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335729 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_4335729 : Nat := 118140960795 + 4335729 * 2 ^ 59
def prefixEnd_4335729 : Nat := 4983230072969 + 3 ^ 40 * 4335729 * 2
def baseEnd_4335729 : Nat := 2226312964637772174047851

theorem tailTrace_4335729 : CollatzResearch.WordTrace tailWord_4335729 prefixEnd_4335729 2226312964637772174047851 := by
  unfold tailWord_4335729
  simp only [CollatzResearch.WordTrace]
  refine ⟨158137028109401791405402241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105424685406267860936934827 158137028109401791405402241)
  ·
    refine ⟨118602771082051343554051681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158137028109401791405402241 118602771082051343554051681)
    ·
      refine ⟨88952078311538507665538761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118602771082051343554051681 88952078311538507665538761)
      ·
        refine ⟨66714058733653880749154071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88952078311538507665538761 66714058733653880749154071)
        ·
          refine ⟨100071088100480821123731107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66714058733653880749154071 100071088100480821123731107)
          ·
            refine ⟨150106632150721231685596661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100071088100480821123731107 150106632150721231685596661)
            ·
              refine ⟨14072496764130115470524687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150106632150721231685596661 14072496764130115470524687)
              ·
                refine ⟨21108745146195173205787031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14072496764130115470524687 21108745146195173205787031)
                ·
                  refine ⟨31663117719292759808680547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21108745146195173205787031 31663117719292759808680547)
                  ·
                    refine ⟨47494676578939139713020821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31663117719292759808680547 47494676578939139713020821)
                    ·
                      refine ⟨2226312964637772174047851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47494676578939139713020821 2226312964637772174047851)
                      ·
                        rfl

theorem cell23_4335729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_4335729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335729 prefixEnd_4335729 := by exact prefixLift 4335729
  have htrace : WordTrace (prefixWord ++ tailWord_4335729) baseStart_4335729 baseEnd_4335729 := by
    simpa [prefixWord, tailWord_4335729, baseEnd_4335729] using wordTrace_append hprefix tailTrace_4335729
  have hstable : (prefixWord ++ tailWord_4335729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335729).length < 2 ^ (prefixWord ++ tailWord_4335729).sum := by decide
  have hdescent : baseEnd_4335729 < baseStart_4335729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335767 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_4335767 : Nat := 118140960795 + 4335767 * 2 ^ 59
def prefixEnd_4335767 : Nat := 4983230072969 + 3 ^ 40 * 4335767 * 2
def baseEnd_4335767 : Nat := 2226332476902643025372677

theorem tailTrace_4335767 : CollatzResearch.WordTrace tailWord_4335767 prefixEnd_4335767 2226332476902643025372677 := by
  unfold tailWord_4335767
  simp only [CollatzResearch.WordTrace]
  refine ⟨158138414083264123895285555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105425609388842749263523703 158138414083264123895285555)
  ·
    refine ⟨237207621124896185842928333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158138414083264123895285555 237207621124896185842928333)
    ·
      refine ⟨88952857921836069691098125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237207621124896185842928333 88952857921836069691098125)
      ·
        refine ⟨33357321720688526134161797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88952857921836069691098125 33357321720688526134161797)
        ·
          refine ⟨6254497822629098650155337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33357321720688526134161797 6254497822629098650155337)
          ·
            refine ⟨4690873366971823987616503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254497822629098650155337 4690873366971823987616503)
            ·
              refine ⟨7036310050457735981424755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690873366971823987616503 7036310050457735981424755)
              ·
                refine ⟨10554465075686603972137133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7036310050457735981424755 10554465075686603972137133)
                ·
                  refine ⟨3957924403382476489551425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10554465075686603972137133 3957924403382476489551425)
                  ·
                    refine ⟨2968443302536857367163569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957924403382476489551425 2968443302536857367163569)
                    ·
                      refine ⟨2226332476902643025372677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968443302536857367163569 2226332476902643025372677)
                      ·
                        rfl

theorem cell23_4335767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_4335767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335767 prefixEnd_4335767 := by exact prefixLift 4335767
  have htrace : WordTrace (prefixWord ++ tailWord_4335767) baseStart_4335767 baseEnd_4335767 := by
    simpa [prefixWord, tailWord_4335767, baseEnd_4335767] using wordTrace_append hprefix tailTrace_4335767
  have hstable : (prefixWord ++ tailWord_4335767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335767).length < 2 ^ (prefixWord ++ tailWord_4335767).sum := by decide
  have hdescent : baseEnd_4335767 < baseStart_4335767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335840 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2]
def baseStart_4335840 : Nat := 118140960795 + 4335840 * 2 ^ 59
def prefixEnd_4335840 : Nat := 4983230072969 + 3 ^ 40 * 4335840 * 2
def baseEnd_4335840 : Nat := 2226369960990421239759841

theorem tailTrace_4335840 : CollatzResearch.WordTrace tailWord_4335840 prefixEnd_4335840 2226369960990421239759841 := by
  unfold tailWord_4335840
  simp only [CollatzResearch.WordTrace]
  refine ⟨79070538305999828681346487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105427384407999771575128649 79070538305999828681346487)
  ·
    refine ⟨118605807458999743022019731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79070538305999828681346487 118605807458999743022019731)
    ·
      refine ⟨177908711188499614533029597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118605807458999743022019731 177908711188499614533029597)
      ·
        refine ⟨66715766695687355449886099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177908711188499614533029597 66715766695687355449886099)
        ·
          refine ⟨100073650043531033174829149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66715766695687355449886099 100073650043531033174829149)
          ·
            refine ⟨37527618766324137440560931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100073650043531033174829149 37527618766324137440560931)
            ·
              refine ⟨56291428149486206160841397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37527618766324137440560931 56291428149486206160841397)
              ·
                refine ⟨5277321389014331827578881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56291428149486206160841397 5277321389014331827578881)
                ·
                  refine ⟨3957991041760748870684161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5277321389014331827578881 3957991041760748870684161)
                  ·
                    refine ⟨2968493281320561653013121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957991041760748870684161 2968493281320561653013121)
                    ·
                      refine ⟨2226369960990421239759841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968493281320561653013121 2226369960990421239759841)
                      ·
                        rfl

theorem cell23_4335840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_4335840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335840 prefixEnd_4335840 := by exact prefixLift 4335840
  have htrace : WordTrace (prefixWord ++ tailWord_4335840) baseStart_4335840 baseEnd_4335840 := by
    simpa [prefixWord, tailWord_4335840, baseEnd_4335840] using wordTrace_append hprefix tailTrace_4335840
  have hstable : (prefixWord ++ tailWord_4335840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335840).length < 2 ^ (prefixWord ++ tailWord_4335840).sum := by decide
  have hdescent : baseEnd_4335840 < baseStart_4335840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335849 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_4335849 : Nat := 118140960795 + 4335849 * 2 ^ 59
def prefixEnd_4335849 : Nat := 4983230072969 + 3 ^ 40 * 4335849 * 2
def baseEnd_4335849 : Nat := 2226374582316311704547299

theorem tailTrace_4335849 : CollatzResearch.WordTrace tailWord_4335849 prefixEnd_4335849 2226374582316311704547299 := by
  unfold tailWord_4335849
  simp only [CollatzResearch.WordTrace]
  refine ⟨158141404868967051899770601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105427603245978034599847067 158141404868967051899770601)
  ·
    refine ⟨118606053651725288924827951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158141404868967051899770601 118606053651725288924827951)
    ·
      refine ⟨177909080477587933387241927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118606053651725288924827951 177909080477587933387241927)
      ·
        refine ⟨266863620716381900080862891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177909080477587933387241927 266863620716381900080862891)
        ·
          refine ⟨400295431074572850121294337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266863620716381900080862891 400295431074572850121294337)
          ·
            refine ⟨300221573305929637590970753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400295431074572850121294337 300221573305929637590970753)
            ·
              refine ⟨225166179979447228193228065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300221573305929637590970753 225166179979447228193228065)
              ·
                refine ⟨168874634984585421144921049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225166179979447228193228065 168874634984585421144921049)
                ·
                  refine ⟨126655976238439065858690787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168874634984585421144921049 126655976238439065858690787)
                  ·
                    refine ⟨189983964357658598788036181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126655976238439065858690787 189983964357658598788036181)
                    ·
                      refine ⟨2226374582316311704547299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189983964357658598788036181 2226374582316311704547299)
                      ·
                        rfl

theorem cell23_4335849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_4335849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335849 prefixEnd_4335849 := by exact prefixLift 4335849
  have htrace : WordTrace (prefixWord ++ tailWord_4335849) baseStart_4335849 baseEnd_4335849 := by
    simpa [prefixWord, tailWord_4335849, baseEnd_4335849] using wordTrace_append hprefix tailTrace_4335849
  have hstable : (prefixWord ++ tailWord_4335849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335849).length < 2 ^ (prefixWord ++ tailWord_4335849).sum := by decide
  have hdescent : baseEnd_4335849 < baseStart_4335849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335874 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4335874 : Nat := 118140960795 + 4335874 * 2 ^ 59
def prefixEnd_4335874 : Nat := 4983230072969 + 3 ^ 40 * 4335874 * 2
def baseEnd_4335874 : Nat := 2226387419332674106734685

theorem tailTrace_4335874 : CollatzResearch.WordTrace tailWord_4335874 prefixEnd_4335874 2226387419332674106734685 := by
  unfold tailWord_4335874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39535579173469120292357669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105428211129250987446287117 39535579173469120292357669)
  ·
    refine ⟨7412921095025460054817063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39535579173469120292357669 7412921095025460054817063)
    ·
      refine ⟨11119381642538190082225595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412921095025460054817063 11119381642538190082225595)
      ·
        refine ⟨16679072463807285123338393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11119381642538190082225595 16679072463807285123338393)
        ·
          refine ⟨12509304347855463842503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16679072463807285123338393 12509304347855463842503795)
          ·
            refine ⟨18763956521783195763755693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12509304347855463842503795 18763956521783195763755693)
            ·
              refine ⟨7036483695668698411408385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18763956521783195763755693 7036483695668698411408385)
              ·
                refine ⟨5277362771751523808556289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7036483695668698411408385 5277362771751523808556289)
                ·
                  refine ⟨3958022078813642856417217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5277362771751523808556289 3958022078813642856417217)
                  ·
                    refine ⟨2968516559110232142312913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958022078813642856417217 2968516559110232142312913)
                    ·
                      refine ⟨2226387419332674106734685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968516559110232142312913 2226387419332674106734685)
                      ·
                        rfl

theorem cell23_4335874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4335874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335874 prefixEnd_4335874 := by exact prefixLift 4335874
  have htrace : WordTrace (prefixWord ++ tailWord_4335874) baseStart_4335874 baseEnd_4335874 := by
    simpa [prefixWord, tailWord_4335874, baseEnd_4335874] using wordTrace_append hprefix tailTrace_4335874
  have hstable : (prefixWord ++ tailWord_4335874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335874).length < 2 ^ (prefixWord ++ tailWord_4335874).sum := by decide
  have hdescent : baseEnd_4335874 < baseStart_4335874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335886 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4335886 : Nat := 118140960795 + 4335886 * 2 ^ 59
def prefixEnd_4335886 : Nat := 4983230072969 + 3 ^ 40 * 4335886 * 2
def baseEnd_4335886 : Nat := 2226393581100528059784629

theorem tailTrace_4335886 : CollatzResearch.WordTrace tailWord_4335886 prefixEnd_4335886 2226393581100528059784629 := by
  unfold tailWord_4335886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767844296229125902358439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105428502913222004812578341 19767844296229125902358439)
  ·
    refine ⟨29651766444343688853537659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19767844296229125902358439 29651766444343688853537659)
    ·
      refine ⟨44477649666515533280306489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29651766444343688853537659 44477649666515533280306489)
      ·
        refine ⟨33358237249886649960229867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44477649666515533280306489 33358237249886649960229867)
        ·
          refine ⟨50037355874829974940344801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33358237249886649960229867 50037355874829974940344801)
          ·
            refine ⟨37528016906122481205258601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50037355874829974940344801 37528016906122481205258601)
            ·
              refine ⟨28146012679591860903943951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37528016906122481205258601 28146012679591860903943951)
              ·
                refine ⟨42219019019387791355915927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28146012679591860903943951 42219019019387791355915927)
                ·
                  refine ⟨63328528529081687033873891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42219019019387791355915927 63328528529081687033873891)
                  ·
                    refine ⟨94992792793622530550810837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63328528529081687033873891 94992792793622530550810837)
                    ·
                      refine ⟨2226393581100528059784629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94992792793622530550810837 2226393581100528059784629)
                      ·
                        rfl

theorem cell23_4335886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4335886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335886 prefixEnd_4335886 := by exact prefixLift 4335886
  have htrace : WordTrace (prefixWord ++ tailWord_4335886) baseStart_4335886 baseEnd_4335886 := by
    simpa [prefixWord, tailWord_4335886, baseEnd_4335886] using wordTrace_append hprefix tailTrace_4335886
  have hstable : (prefixWord ++ tailWord_4335886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335886).length < 2 ^ (prefixWord ++ tailWord_4335886).sum := by decide
  have hdescent : baseEnd_4335886 < baseStart_4335886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335896 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4335896 : Nat := 118140960795 + 4335896 * 2 ^ 59
def prefixEnd_4335896 : Nat := 4983230072969 + 3 ^ 40 * 4335896 * 2
def baseEnd_4335896 : Nat := 2226398715907073020659583

theorem tailTrace_4335896 : CollatzResearch.WordTrace tailWord_4335896 prefixEnd_4335896 2226398715907073020659583 := by
  unfold tailWord_4335896
  simp only [CollatzResearch.WordTrace]
  refine ⟨79071559549898389463365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105428746066531185951154361 79071559549898389463365771)
  ·
    refine ⟨118607339324847584195048657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79071559549898389463365771 118607339324847584195048657)
    ·
      refine ⟨88955504493635688146286493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118607339324847584195048657 88955504493635688146286493)
      ·
        refine ⟨33358314185113383054857435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88955504493635688146286493 33358314185113383054857435)
        ·
          refine ⟨50037471277670074582286153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33358314185113383054857435 50037471277670074582286153)
          ·
            refine ⟨37528103458252555936714615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50037471277670074582286153 37528103458252555936714615)
            ·
              refine ⟨56292155187378833905071923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37528103458252555936714615 56292155187378833905071923)
              ·
                refine ⟨84438232781068250857607885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56292155187378833905071923 84438232781068250857607885)
                ·
                  refine ⟨31664337292900594071602957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84438232781068250857607885 31664337292900594071602957)
                  ·
                    refine ⟨11874126484837722776851109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31664337292900594071602957 11874126484837722776851109)
                    ·
                      refine ⟨2226398715907073020659583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11874126484837722776851109 2226398715907073020659583)
                      ·
                        rfl

theorem cell23_4335896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4335896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335896 prefixEnd_4335896 := by exact prefixLift 4335896
  have htrace : WordTrace (prefixWord ++ tailWord_4335896) baseStart_4335896 baseEnd_4335896 := by
    simpa [prefixWord, tailWord_4335896, baseEnd_4335896] using wordTrace_append hprefix tailTrace_4335896
  have hstable : (prefixWord ++ tailWord_4335896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335896).length < 2 ^ (prefixWord ++ tailWord_4335896).sum := by decide
  have hdescent : baseEnd_4335896 < baseStart_4335896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335914 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_4335914 : Nat := 118140960795 + 4335914 * 2 ^ 59
def prefixEnd_4335914 : Nat := 4983230072969 + 3 ^ 40 * 4335914 * 2
def baseEnd_4335914 : Nat := 247378662062094883359389

theorem tailTrace_4335914 : CollatzResearch.WordTrace tailWord_4335914 prefixEnd_4335914 247378662062094883359389 := by
  unfold tailWord_4335914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39535943903432892000221699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105429183742487712000591197 39535943903432892000221699)
  ·
    refine ⟨59303915855149338000332549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39535943903432892000221699 59303915855149338000332549)
    ·
      refine ⟨11119484222840500875062353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59303915855149338000332549 11119484222840500875062353)
      ·
        refine ⟨8339613167130375656296765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11119484222840500875062353 8339613167130375656296765)
        ·
          refine ⟨3127354937673890871111287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8339613167130375656296765 3127354937673890871111287)
          ·
            refine ⟨4691032406510836306666931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127354937673890871111287 4691032406510836306666931)
            ·
              refine ⟨7036548609766254460000397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691032406510836306666931 7036548609766254460000397)
              ·
                refine ⟨2638705728662345422500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7036548609766254460000397 2638705728662345422500149)
                ·
                  refine ⟨247378662062094883359389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638705728662345422500149 247378662062094883359389)
                  ·
                    rfl

theorem cell23_4335914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_4335914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335914 prefixEnd_4335914 := by exact prefixLift 4335914
  have htrace : WordTrace (prefixWord ++ tailWord_4335914) baseStart_4335914 baseEnd_4335914 := by
    simpa [prefixWord, tailWord_4335914, baseEnd_4335914] using wordTrace_append hprefix tailTrace_4335914
  have hstable : (prefixWord ++ tailWord_4335914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335914).length < 2 ^ (prefixWord ++ tailWord_4335914).sum := by decide
  have hdescent : baseEnd_4335914 < baseStart_4335914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4335953 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 6]
def baseStart_4335953 : Nat := 118140960795 + 4335953 * 2 ^ 59
def prefixEnd_4335953 : Nat := 4983230072969 + 3 ^ 40 * 4335953 * 2
def baseEnd_4335953 : Nat := 247380887144931033071869

theorem tailTrace_4335953 : CollatzResearch.WordTrace tailWord_4335953 prefixEnd_4335953 247380887144931033071869 := by
  unfold tailWord_4335953
  simp only [CollatzResearch.WordTrace]
  refine ⟨158145198060590277661556513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105430132040393518441037675 158145198060590277661556513)
  ·
    refine ⟨118608898545442708246167385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158145198060590277661556513 118608898545442708246167385)
    ·
      refine ⟨88956673909082031184625539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118608898545442708246167385 88956673909082031184625539)
      ·
        refine ⟨133435010863623046776938309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88956673909082031184625539 133435010863623046776938309)
        ·
          refine ⟨25019064536929321270675933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133435010863623046776938309 25019064536929321270675933)
          ·
            refine ⟨9382149201348495476503475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25019064536929321270675933 9382149201348495476503475)
            ·
              refine ⟨14073223802022743214755213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9382149201348495476503475 14073223802022743214755213)
              ·
                refine ⟨5277458925758528705533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14073223802022743214755213 5277458925758528705533205)
                ·
                  refine ⟨247380887144931033071869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5277458925758528705533205 247380887144931033071869)
                  ·
                    rfl

theorem cell23_4335953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_4335953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4335953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4335953 prefixEnd_4335953 := by exact prefixLift 4335953
  have htrace : WordTrace (prefixWord ++ tailWord_4335953) baseStart_4335953 baseEnd_4335953 := by
    simpa [prefixWord, tailWord_4335953, baseEnd_4335953] using wordTrace_append hprefix tailTrace_4335953
  have hstable : (prefixWord ++ tailWord_4335953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4335953).length < 2 ^ (prefixWord ++ tailWord_4335953).sum := by decide
  have hdescent : baseEnd_4335953 < baseStart_4335953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4335953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336024 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4336024 : Nat := 118140960795 + 4336024 * 2 ^ 59
def prefixEnd_4336024 : Nat := 4983230072969 + 3 ^ 40 * 4336024 * 2
def baseEnd_4336024 : Nat := 2226464441430848519858995

theorem tailTrace_4336024 : CollatzResearch.WordTrace tailWord_4336024 prefixEnd_4336024 2226464441430848519858995 := by
  unfold tailWord_4336024
  simp only [CollatzResearch.WordTrace]
  refine ⟨79073893821666528393695563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105431858428888704524927417 79073893821666528393695563)
  ·
    refine ⟨118610840732499792590543345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79073893821666528393695563 118610840732499792590543345)
    ·
      refine ⟨88958130549374844442907509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118610840732499792590543345 88958130549374844442907509)
      ·
        refine ⟨8339824739003891666522579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88958130549374844442907509 8339824739003891666522579)
        ·
          refine ⟨12509737108505837499783869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8339824739003891666522579 12509737108505837499783869)
          ·
            refine ⟨4691151415689689062418951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12509737108505837499783869 4691151415689689062418951)
            ·
              refine ⟨7036727123534533593628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691151415689689062418951 7036727123534533593628427)
              ·
                refine ⟨10555090685301800390442641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7036727123534533593628427 10555090685301800390442641)
                ·
                  refine ⟨7916318013976350292831981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10555090685301800390442641 7916318013976350292831981)
                  ·
                    refine ⟨2968619255241131359811993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7916318013976350292831981 2968619255241131359811993)
                    ·
                      refine ⟨2226464441430848519858995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968619255241131359811993 2226464441430848519858995)
                      ·
                        rfl

theorem cell23_4336024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4336024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336024 prefixEnd_4336024 := by exact prefixLift 4336024
  have htrace : WordTrace (prefixWord ++ tailWord_4336024) baseStart_4336024 baseEnd_4336024 := by
    simpa [prefixWord, tailWord_4336024, baseEnd_4336024] using wordTrace_append hprefix tailTrace_4336024
  have hstable : (prefixWord ++ tailWord_4336024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336024).length < 2 ^ (prefixWord ++ tailWord_4336024).sum := by decide
  have hdescent : baseEnd_4336024 < baseStart_4336024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336097 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_4336097 : Nat := 118140960795 + 4336097 * 2 ^ 59
def prefixEnd_4336097 : Nat := 4983230072969 + 3 ^ 40 * 4336097 * 2
def baseEnd_4336097 : Nat := 2226501925518626734246159

theorem tailTrace_4336097 : CollatzResearch.WordTrace tailWord_4336097 prefixEnd_4336097 2226501925518626734246159 := by
  unfold tailWord_4336097
  simp only [CollatzResearch.WordTrace]
  refine ⟨158150450172068590254798545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105433633448045726836532363 158150450172068590254798545)
  ·
    refine ⟨118612837629051442691098909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158150450172068590254798545 118612837629051442691098909)
    ·
      refine ⟨44479814110894291009162091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118612837629051442691098909 44479814110894291009162091)
      ·
        refine ⟨66719721166341436513743137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44479814110894291009162091 66719721166341436513743137)
        ·
          refine ⟨50039790874756077385307353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66719721166341436513743137 50039790874756077385307353)
          ·
            refine ⟨37529843156067058038980515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50039790874756077385307353 37529843156067058038980515)
            ·
              refine ⟨56294764734100587058470773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37529843156067058038980515 56294764734100587058470773)
              ·
                refine ⟨5277634193821930036731635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56294764734100587058470773 5277634193821930036731635)
                ·
                  refine ⟨7916451290732895055097453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5277634193821930036731635 7916451290732895055097453)
                  ·
                    refine ⟨2968669234024835645661545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7916451290732895055097453 2968669234024835645661545)
                    ·
                      refine ⟨2226501925518626734246159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968669234024835645661545 2226501925518626734246159)
                      ·
                        rfl

theorem cell23_4336097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_4336097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336097 prefixEnd_4336097 := by exact prefixLift 4336097
  have htrace : WordTrace (prefixWord ++ tailWord_4336097) baseStart_4336097 baseEnd_4336097 := by
    simpa [prefixWord, tailWord_4336097, baseEnd_4336097] using wordTrace_append hprefix tailTrace_4336097
  have hstable : (prefixWord ++ tailWord_4336097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336097).length < 2 ^ (prefixWord ++ tailWord_4336097).sum := by decide
  have hdescent : baseEnd_4336097 < baseStart_4336097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336113 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_4336113 : Nat := 118140960795 + 4336113 * 2 ^ 59
def prefixEnd_4336113 : Nat := 4983230072969 + 3 ^ 40 * 4336113 * 2
def baseEnd_4336113 : Nat := 2226510141209098671646085

theorem tailTrace_4336113 : CollatzResearch.WordTrace tailWord_4336113 prefixEnd_4336113 2226510141209098671646085 := by
  unfold tailWord_4336113
  simp only [CollatzResearch.WordTrace]
  refine ⟨158151033740010624987380993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105434022493340416658253995 158151033740010624987380993)
  ·
    refine ⟨118613275305007968740535745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158151033740010624987380993 118613275305007968740535745)
    ·
      refine ⟨88959956478755976555401809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118613275305007968740535745 88959956478755976555401809)
      ·
        refine ⟨66719967359066982416551357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88959956478755976555401809 66719967359066982416551357)
        ·
          refine ⟨25019987759650118406206759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66719967359066982416551357 25019987759650118406206759)
          ·
            refine ⟨37529981639475177609310139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25019987759650118406206759 37529981639475177609310139)
            ·
              refine ⟨56294972459212766413965209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37529981639475177609310139 56294972459212766413965209)
              ·
                refine ⟨42221229344409574810473907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56294972459212766413965209 42221229344409574810473907)
                ·
                  refine ⟨63331844016614362215710861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42221229344409574810473907 63331844016614362215710861)
                  ·
                    refine ⟨23749441506230385830891573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63331844016614362215710861 23749441506230385830891573)
                    ·
                      refine ⟨2226510141209098671646085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23749441506230385830891573 2226510141209098671646085)
                      ·
                        rfl

theorem cell23_4336113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_4336113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336113 prefixEnd_4336113 := by exact prefixLift 4336113
  have htrace : WordTrace (prefixWord ++ tailWord_4336113) baseStart_4336113 baseEnd_4336113 := by
    simpa [prefixWord, tailWord_4336113, baseEnd_4336113] using wordTrace_append hprefix tailTrace_4336113
  have hstable : (prefixWord ++ tailWord_4336113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336113).length < 2 ^ (prefixWord ++ tailWord_4336113).sum := by decide
  have hdescent : baseEnd_4336113 < baseStart_4336113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336133 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 7]
def baseStart_4336133 : Nat := 118140960795 + 4336133 * 2 ^ 59
def prefixEnd_4336133 : Nat := 4983230072969 + 3 ^ 40 * 4336133 * 2
def baseEnd_4336133 : Nat := 247391156758020954821777

theorem tailTrace_4336133 : CollatzResearch.WordTrace tailWord_4336133 prefixEnd_4336133 247391156758020954821777 := by
  unfold tailWord_4336133
  simp only [CollatzResearch.WordTrace]
  refine ⟨158151763199938168403109053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105434508799958778935406035 158151763199938168403109053)
  ·
    refine ⟨59306911199976813151165895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158151763199938168403109053 59306911199976813151165895)
    ·
      refine ⟨88960366799965219726748843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59306911199976813151165895 88960366799965219726748843)
      ·
        refine ⟨133440550199947829590123265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88960366799965219726748843 133440550199947829590123265)
        ·
          refine ⟨100080412649960872192592449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133440550199947829590123265 100080412649960872192592449)
          ·
            refine ⟨75060309487470654144444337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100080412649960872192592449 75060309487470654144444337)
            ·
              refine ⟨56295232115602990608333253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75060309487470654144444337 56295232115602990608333253)
              ·
                refine ⟨10555356021675560739062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56295232115602990608333253 10555356021675560739062485)
                ·
                  refine ⟨247391156758020954821777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10555356021675560739062485 247391156758020954821777)
                  ·
                    rfl

theorem cell23_4336133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_4336133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336133 prefixEnd_4336133 := by exact prefixLift 4336133
  have htrace : WordTrace (prefixWord ++ tailWord_4336133) baseStart_4336133 baseEnd_4336133 := by
    simpa [prefixWord, tailWord_4336133, baseEnd_4336133] using wordTrace_append hprefix tailTrace_4336133
  have hstable : (prefixWord ++ tailWord_4336133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336133).length < 2 ^ (prefixWord ++ tailWord_4336133).sum := by decide
  have hdescent : baseEnd_4336133 < baseStart_4336133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336148 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4336148 : Nat := 118140960795 + 4336148 * 2 ^ 59
def prefixEnd_4336148 : Nat := 4983230072969 + 3 ^ 40 * 4336148 * 2
def baseEnd_4336148 : Nat := 2226528113032006034708425

theorem tailTrace_4336148 : CollatzResearch.WordTrace tailWord_4336148 prefixEnd_4336148 2226528113032006034708425 := by
  unfold tailWord_4336148
  simp only [CollatzResearch.WordTrace]
  refine ⟨79076155147441912982452549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105434873529922550643270065 79076155147441912982452549)
  ·
    refine ⟨14826779090145358684209853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79076155147441912982452549 14826779090145358684209853)
    ·
      refine ⟨5560042158804509506578695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14826779090145358684209853 5560042158804509506578695)
      ·
        refine ⟨8340063238206764259868043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560042158804509506578695 8340063238206764259868043)
        ·
          refine ⟨12510094857310146389802065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340063238206764259868043 12510094857310146389802065)
          ·
            refine ⟨9382571142982609792351549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12510094857310146389802065 9382571142982609792351549)
            ·
              refine ⟨3518464178618478672131831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9382571142982609792351549 3518464178618478672131831)
              ·
                refine ⟨5277696267927718008197747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518464178618478672131831 5277696267927718008197747)
                ·
                  refine ⟨7916544401891577012296621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5277696267927718008197747 7916544401891577012296621)
                  ·
                    refine ⟨2968704150709341379611233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7916544401891577012296621 2968704150709341379611233)
                    ·
                      refine ⟨2226528113032006034708425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968704150709341379611233 2226528113032006034708425)
                      ·
                        rfl

theorem cell23_4336148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4336148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336148 prefixEnd_4336148 := by exact prefixLift 4336148
  have htrace : WordTrace (prefixWord ++ tailWord_4336148) baseStart_4336148 baseEnd_4336148 := by
    simpa [prefixWord, tailWord_4336148, baseEnd_4336148] using wordTrace_append hprefix tailTrace_4336148
  have hstable : (prefixWord ++ tailWord_4336148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336148).length < 2 ^ (prefixWord ++ tailWord_4336148).sum := by decide
  have hdescent : baseEnd_4336148 < baseStart_4336148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336197 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_4336197 : Nat := 118140960795 + 4336197 * 2 ^ 59
def prefixEnd_4336197 : Nat := 4983230072969 + 3 ^ 40 * 4336197 * 2
def baseEnd_4336197 : Nat := 742184424528025447665233

theorem tailTrace_4336197 : CollatzResearch.WordTrace tailWord_4336197 prefixEnd_4336197 742184424528025447665233 := by
  unfold tailWord_4336197
  simp only [CollatzResearch.WordTrace]
  refine ⟨158154097471706307333438845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105436064981137538222292563 158154097471706307333438845)
  ·
    refine ⟨59307786551889865250039567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158154097471706307333438845 59307786551889865250039567)
    ·
      refine ⟨88961679827834797875059351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59307786551889865250039567 88961679827834797875059351)
      ·
        refine ⟨133442519741752196812589027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88961679827834797875059351 133442519741752196812589027)
        ·
          refine ⟨200163779612628295218883541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133442519741752196812589027 200163779612628295218883541)
          ·
            refine ⟨4691338584670975669192583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200163779612628295218883541 4691338584670975669192583)
            ·
              refine ⟨7037007877006463503788875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691338584670975669192583 7037007877006463503788875)
              ·
                refine ⟨10555511815509695255683313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037007877006463503788875 10555511815509695255683313)
                ·
                  refine ⟨7916633861632271441762485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10555511815509695255683313 7916633861632271441762485)
                  ·
                    refine ⟨742184424528025447665233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7916633861632271441762485 742184424528025447665233)
                    ·
                      rfl

theorem cell23_4336197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_4336197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336197 prefixEnd_4336197 := by exact prefixLift 4336197
  have htrace : WordTrace (prefixWord ++ tailWord_4336197) baseStart_4336197 baseEnd_4336197 := by
    simpa [prefixWord, tailWord_4336197, baseEnd_4336197] using wordTrace_append hprefix tailTrace_4336197
  have hstable : (prefixWord ++ tailWord_4336197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336197).length < 2 ^ (prefixWord ++ tailWord_4336197).sum := by decide
  have hdescent : baseEnd_4336197 < baseStart_4336197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336227 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 3, 4]
def baseStart_4336227 : Nat := 118140960795 + 4336227 * 2 ^ 59
def prefixEnd_4336227 : Nat := 4983230072969 + 3 ^ 40 * 4336227 * 2
def baseEnd_4336227 : Nat := 742189559334570408540187

theorem tailTrace_4336227 : CollatzResearch.WordTrace tailWord_4336227 prefixEnd_4336227 742189559334570408540187 := by
  unfold tailWord_4336227
  simp only [CollatzResearch.WordTrace]
  refine ⟨158155191661597622457030935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105436794441065081638020623 158155191661597622457030935)
  ·
    refine ⟨237232787492396433685546403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158155191661597622457030935 237232787492396433685546403)
    ·
      refine ⟨355849181238594650528319605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237232787492396433685546403 355849181238594650528319605)
      ·
        refine ⟨33360860741118248487029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 355849181238594650528319605 33360860741118248487029963)
        ·
          refine ⟨50041291111677372730544945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33360860741118248487029963 50041291111677372730544945)
          ·
            refine ⟨37530968333758029547908709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50041291111677372730544945 37530968333758029547908709)
            ·
              refine ⟨7037056562579630540232883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37530968333758029547908709 7037056562579630540232883)
              ·
                refine ⟨10555584843869445810349325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037056562579630540232883 10555584843869445810349325)
                ·
                  refine ⟨3958344316451042178880997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10555584843869445810349325 3958344316451042178880997)
                  ·
                    refine ⟨742189559334570408540187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958344316451042178880997 742189559334570408540187)
                    ·
                      rfl

theorem cell23_4336227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 4].length) (baseStart_4336227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336227 prefixEnd_4336227 := by exact prefixLift 4336227
  have htrace : WordTrace (prefixWord ++ tailWord_4336227) baseStart_4336227 baseEnd_4336227 := by
    simpa [prefixWord, tailWord_4336227, baseEnd_4336227] using wordTrace_append hprefix tailTrace_4336227
  have hstable : (prefixWord ++ tailWord_4336227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336227).length < 2 ^ (prefixWord ++ tailWord_4336227).sum := by decide
  have hdescent : baseEnd_4336227 < baseStart_4336227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336237 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4336237 : Nat := 118140960795 + 4336237 * 2 ^ 59
def prefixEnd_4336237 : Nat := 4983230072969 + 3 ^ 40 * 4336237 * 2
def baseEnd_4336237 : Nat := 2226573812810256186495515

theorem tailTrace_4336237 : CollatzResearch.WordTrace tailWord_4336237 prefixEnd_4336237 2226573812810256186495515 := by
  unfold tailWord_4336237
  simp only [CollatzResearch.WordTrace]
  refine ⟨158155556391561394164894965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105437037594374262776596643 158155556391561394164894965)
  ·
    refine ⟨14827083411708880702958903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158155556391561394164894965 14827083411708880702958903)
    ·
      refine ⟨22240625117563321054438355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14827083411708880702958903 22240625117563321054438355)
      ·
        refine ⟨33360937676344981581657533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22240625117563321054438355 33360937676344981581657533)
        ·
          refine ⟨12510351628629368093121575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33360937676344981581657533 12510351628629368093121575)
          ·
            refine ⟨18765527442944052139682363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12510351628629368093121575 18765527442944052139682363)
            ·
              refine ⟨28148291164416078209523545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18765527442944052139682363 28148291164416078209523545)
              ·
                refine ⟨21111218373312058657142659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28148291164416078209523545 21111218373312058657142659)
                ·
                  refine ⟨31666827559968087985713989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21111218373312058657142659 31666827559968087985713989)
                  ·
                    refine ⟨5937530167494016497321373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31666827559968087985713989 5937530167494016497321373)
                    ·
                      refine ⟨2226573812810256186495515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5937530167494016497321373 2226573812810256186495515)
                      ·
                        rfl

theorem cell23_4336237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4336237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336237 prefixEnd_4336237 := by exact prefixLift 4336237
  have htrace : WordTrace (prefixWord ++ tailWord_4336237) baseStart_4336237 baseEnd_4336237 := by
    simpa [prefixWord, tailWord_4336237, baseEnd_4336237] using wordTrace_append hprefix tailTrace_4336237
  have hstable : (prefixWord ++ tailWord_4336237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336237).length < 2 ^ (prefixWord ++ tailWord_4336237).sum := by decide
  have hdescent : baseEnd_4336237 < baseStart_4336237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336261 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_4336261 : Nat := 118140960795 + 4336261 * 2 ^ 59
def prefixEnd_4336261 : Nat := 4983230072969 + 3 ^ 40 * 4336261 * 2
def baseEnd_4336261 : Nat := 742195378781988030865135

theorem tailTrace_4336261 : CollatzResearch.WordTrace tailWord_4336261 prefixEnd_4336261 742195378781988030865135 := by
  unfold tailWord_4336261
  simp only [CollatzResearch.WordTrace]
  refine ⟨158156431743474446263768637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105437621162316297509179091 158156431743474446263768637)
  ·
    refine ⟨59308661903802917348913239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158156431743474446263768637 59308661903802917348913239)
    ·
      refine ⟨88962992855704376023369859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59308661903802917348913239 88962992855704376023369859)
      ·
        refine ⟨133444489283556564035054789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88962992855704376023369859 133444489283556564035054789)
        ·
          refine ⟨25020841740666855756572773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133444489283556564035054789 25020841740666855756572773)
          ·
            refine ⟨4691407826375035454357395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25020841740666855756572773 4691407826375035454357395)
            ·
              refine ⟨7037111739562553181536093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691407826375035454357395 7037111739562553181536093)
              ·
                refine ⟨2638916902335957443076035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7037111739562553181536093 2638916902335957443076035)
                ·
                  refine ⟨3958375353503936164614053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638916902335957443076035 3958375353503936164614053)
                  ·
                    refine ⟨742195378781988030865135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958375353503936164614053 742195378781988030865135)
                    ·
                      rfl

theorem cell23_4336261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_4336261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336261 prefixEnd_4336261 := by exact prefixLift 4336261
  have htrace : WordTrace (prefixWord ++ tailWord_4336261) baseStart_4336261 baseEnd_4336261 := by
    simpa [prefixWord, tailWord_4336261, baseEnd_4336261] using wordTrace_append hprefix tailTrace_4336261
  have hstable : (prefixWord ++ tailWord_4336261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336261).length < 2 ^ (prefixWord ++ tailWord_4336261).sum := by decide
  have hdescent : baseEnd_4336261 < baseStart_4336261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336307 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4]
def baseStart_4336307 : Nat := 118140960795 + 4336307 * 2 ^ 59
def prefixEnd_4336307 : Nat := 4983230072969 + 3 ^ 40 * 4336307 * 2
def baseEnd_4336307 : Nat := 2226609756456070912620193

theorem tailTrace_4336307 : CollatzResearch.WordTrace tailWord_4336307 prefixEnd_4336307 2226609756456070912620193 := by
  unfold tailWord_4336307
  simp only [CollatzResearch.WordTrace]
  refine ⟨158158109501307796119943175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105438739667538530746628783 158158109501307796119943175)
  ·
    refine ⟨237237164251961694179914763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158158109501307796119943175 237237164251961694179914763)
    ·
      refine ⟨355855746377942541269872145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237237164251961694179914763 355855746377942541269872145)
      ·
        refine ⟨266891809783456905952404109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355855746377942541269872145 266891809783456905952404109)
        ·
          refine ⟨100084428668796339732151541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266891809783456905952404109 100084428668796339732151541)
          ·
            refine ⟨9382915187699656849889207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100084428668796339732151541 9382915187699656849889207)
            ·
              refine ⟨14074372781549485274833811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9382915187699656849889207 14074372781549485274833811)
              ·
                refine ⟨21111559172324227912250717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14074372781549485274833811 21111559172324227912250717)
                ·
                  refine ⟨7916834689621585467094019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21111559172324227912250717 7916834689621585467094019)
                  ·
                    refine ⟨11875252034432378200641029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7916834689621585467094019 11875252034432378200641029)
                    ·
                      refine ⟨2226609756456070912620193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11875252034432378200641029 2226609756456070912620193)
                      ·
                        rfl

theorem cell23_4336307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_4336307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336307 prefixEnd_4336307 := by exact prefixLift 4336307
  have htrace : WordTrace (prefixWord ++ tailWord_4336307) baseStart_4336307 baseEnd_4336307 := by
    simpa [prefixWord, tailWord_4336307, baseEnd_4336307] using wordTrace_append hprefix tailTrace_4336307
  have hstable : (prefixWord ++ tailWord_4336307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336307).length < 2 ^ (prefixWord ++ tailWord_4336307).sum := by decide
  have hdescent : baseEnd_4336307 < baseStart_4336307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336311 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_4336311 : Nat := 118140960795 + 4336311 * 2 ^ 59
def prefixEnd_4336311 : Nat := 4983230072969 + 3 ^ 40 * 4336311 * 2
def baseEnd_4336311 : Nat := 2226611810378688896970175

theorem tailTrace_4336311 : CollatzResearch.WordTrace tailWord_4336311 prefixEnd_4336311 2226611810378688896970175 := by
  unfold tailWord_4336311
  simp only [CollatzResearch.WordTrace]
  refine ⟨158158255393293304803088787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105438836928862203202059191 158158255393293304803088787)
  ·
    refine ⟨237237383089939957204633181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158158255393293304803088787 237237383089939957204633181)
    ·
      refine ⟨88964018658727483951737443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237237383089939957204633181 88964018658727483951737443)
      ·
        refine ⟨133446027988091225927606165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88964018658727483951737443 133446027988091225927606165)
        ·
          refine ⟨6255282561941776215356539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133446027988091225927606165 6255282561941776215356539)
          ·
            refine ⟨9382923842912664323034809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6255282561941776215356539 9382923842912664323034809)
            ·
              refine ⟨7037192882184498242276107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9382923842912664323034809 7037192882184498242276107)
              ·
                refine ⟨10555789323276747363414161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037192882184498242276107 10555789323276747363414161)
                ·
                  refine ⟨7916841992457560522560621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10555789323276747363414161 7916841992457560522560621)
                  ·
                    refine ⟨2968815747171585195960233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7916841992457560522560621 2968815747171585195960233)
                    ·
                      refine ⟨2226611810378688896970175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968815747171585195960233 2226611810378688896970175)
                      ·
                        rfl

theorem cell23_4336311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_4336311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336311 prefixEnd_4336311 := by exact prefixLift 4336311
  have htrace : WordTrace (prefixWord ++ tailWord_4336311) baseStart_4336311 baseEnd_4336311 := by
    simpa [prefixWord, tailWord_4336311, baseEnd_4336311] using wordTrace_append hprefix tailTrace_4336311
  have hstable : (prefixWord ++ tailWord_4336311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336311).length < 2 ^ (prefixWord ++ tailWord_4336311).sum := by decide
  have hdescent : baseEnd_4336311 < baseStart_4336311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336317 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_4336317 : Nat := 118140960795 + 4336317 * 2 ^ 59
def prefixEnd_4336317 : Nat := 4983230072969 + 3 ^ 40 * 4336317 * 2
def baseEnd_4336317 : Nat := 742204963754205291165049

theorem tailTrace_4336317 : CollatzResearch.WordTrace tailWord_4336317 prefixEnd_4336317 742204963754205291165049 := by
  unfold tailWord_4336317
  simp only [CollatzResearch.WordTrace]
  refine ⟨158158474231271567827807205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105438982820847711885204803 158158474231271567827807205)
  ·
    refine ⟨29654713918363418967713851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158158474231271567827807205 29654713918363418967713851)
    ·
      refine ⟨44482070877545128451570777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29654713918363418967713851 44482070877545128451570777)
      ·
        refine ⟨33361553158158846338678083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44482070877545128451570777 33361553158158846338678083)
        ·
          refine ⟨50042329737238269508017125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33361553158158846338678083 50042329737238269508017125)
          ·
            refine ⟨9382936825732175532753211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50042329737238269508017125 9382936825732175532753211)
            ·
              refine ⟨14074405238598263299129817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9382936825732175532753211 14074405238598263299129817)
              ·
                refine ⟨10555803928948697474347363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14074405238598263299129817 10555803928948697474347363)
                ·
                  refine ⟨15833705893423046211521045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10555803928948697474347363 15833705893423046211521045)
                  ·
                    refine ⟨742204963754205291165049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15833705893423046211521045 742204963754205291165049)
                    ·
                      rfl

theorem cell23_4336317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_4336317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336317 prefixEnd_4336317 := by exact prefixLift 4336317
  have htrace : WordTrace (prefixWord ++ tailWord_4336317) baseStart_4336317 baseEnd_4336317 := by
    simpa [prefixWord, tailWord_4336317, baseEnd_4336317] using wordTrace_append hprefix tailTrace_4336317
  have hstable : (prefixWord ++ tailWord_4336317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336317).length < 2 ^ (prefixWord ++ tailWord_4336317).sum := by decide
  have hdescent : baseEnd_4336317 < baseStart_4336317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336330 : List Nat := [3, 1, 2, 1, 4, 12]
def baseStart_4336330 : Nat := 118140960795 + 4336330 * 2 ^ 59
def prefixEnd_4336330 : Nat := 4983230072969 + 3 ^ 40 * 4336330 * 2
def baseEnd_4336330 : Nat := 9163051714037548652809

theorem tailTrace_4336330 : CollatzResearch.WordTrace tailWord_4336330 prefixEnd_4336330 9163051714037548652809 := by
  unfold tailWord_4336330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39539737095056117762007611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105439298920149647365353629 39539737095056117762007611)
  ·
    refine ⟨59309605642584176643011417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39539737095056117762007611 59309605642584176643011417)
    ·
      refine ⟨44482204231938132482258563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59309605642584176643011417 44482204231938132482258563)
      ·
        refine ⟨66723306347907198723387845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44482204231938132482258563 66723306347907198723387845)
        ·
          refine ⟨12510619940232599760635221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66723306347907198723387845 12510619940232599760635221)
          ·
            refine ⟨9163051714037548652809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12510619940232599760635221 9163051714037548652809)
            ·
              rfl

theorem cell23_4336330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 12].length) (baseStart_4336330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336330 prefixEnd_4336330 := by exact prefixLift 4336330
  have htrace : WordTrace (prefixWord ++ tailWord_4336330) baseStart_4336330 baseEnd_4336330 := by
    simpa [prefixWord, tailWord_4336330, baseEnd_4336330] using wordTrace_append hprefix tailTrace_4336330
  have hstable : (prefixWord ++ tailWord_4336330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336330).length < 2 ^ (prefixWord ++ tailWord_4336330).sum := by decide
  have hdescent : baseEnd_4336330 < baseStart_4336330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336334 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_4336334 : Nat := 118140960795 + 4336334 * 2 ^ 59
def prefixEnd_4336334 : Nat := 4983230072969 + 3 ^ 40 * 4336334 * 2
def baseEnd_4336334 : Nat := 742207873477914102327523

theorem tailTrace_4336334 : CollatzResearch.WordTrace tailWord_4336334 prefixEnd_4336334 742207873477914102327523 := by
  unfold tailWord_4336334
  simp only [CollatzResearch.WordTrace]
  refine ⟨19769886784026247466397007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105439396181473319820784037 19769886784026247466397007)
  ·
    refine ⟨29654830176039371199595511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19769886784026247466397007 29654830176039371199595511)
    ·
      refine ⟨44482245264059056799393267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29654830176039371199595511 44482245264059056799393267)
      ·
        refine ⟨66723367896088585199089901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44482245264059056799393267 66723367896088585199089901)
        ·
          refine ⟨25021262961033219449658713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66723367896088585199089901 25021262961033219449658713)
          ·
            refine ⟨18765947220774914587244035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25021262961033219449658713 18765947220774914587244035)
            ·
              refine ⟨28148920831162371880866053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18765947220774914587244035 28148920831162371880866053)
              ·
                refine ⟨5277922655842944727662385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28148920831162371880866053 5277922655842944727662385)
                ·
                  refine ⟨3958441991882208545746789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5277922655842944727662385 3958441991882208545746789)
                  ·
                    refine ⟨742207873477914102327523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958441991882208545746789 742207873477914102327523)
                    ·
                      rfl

theorem cell23_4336334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_4336334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336334 prefixEnd_4336334 := by exact prefixLift 4336334
  have htrace : WordTrace (prefixWord ++ tailWord_4336334) baseStart_4336334 baseEnd_4336334 := by
    simpa [prefixWord, tailWord_4336334, baseEnd_4336334] using wordTrace_append hprefix tailTrace_4336334
  have hstable : (prefixWord ++ tailWord_4336334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336334).length < 2 ^ (prefixWord ++ tailWord_4336334).sum := by decide
  have hdescent : baseEnd_4336334 < baseStart_4336334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336372 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4336372 : Nat := 118140960795 + 4336372 * 2 ^ 59
def prefixEnd_4336372 : Nat := 4983230072969 + 3 ^ 40 * 4336372 * 2
def baseEnd_4336372 : Nat := 742214377566204386102465

theorem tailTrace_4336372 : CollatzResearch.WordTrace tailWord_4336372 prefixEnd_4336372 742214377566204386102465 := by
  unfold tailWord_4336372
  simp only [CollatzResearch.WordTrace]
  refine ⟨79080240123036156110529685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105440320164048208147372913 79080240123036156110529685)
  ·
    refine ⟨3706886255767319817681079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79080240123036156110529685 3706886255767319817681079)
    ·
      refine ⟨5560329383650979726521619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706886255767319817681079 5560329383650979726521619)
      ·
        refine ⟨8340494075476469589782429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560329383650979726521619 8340494075476469589782429)
        ·
          refine ⟨3127685278303676096168411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8340494075476469589782429 3127685278303676096168411)
          ·
            refine ⟨4691527917455514144252617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127685278303676096168411 4691527917455514144252617)
            ·
              refine ⟨3518645938091635608189463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691527917455514144252617 3518645938091635608189463)
              ·
                refine ⟨5277968907137453412284195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518645938091635608189463 5277968907137453412284195)
                ·
                  refine ⟨7916953360706180118426293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5277968907137453412284195 7916953360706180118426293)
                  ·
                    refine ⟨742214377566204386102465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7916953360706180118426293 742214377566204386102465)
                    ·
                      rfl

theorem cell23_4336372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4336372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336372 prefixEnd_4336372 := by exact prefixLift 4336372
  have htrace : WordTrace (prefixWord ++ tailWord_4336372) baseStart_4336372 baseEnd_4336372 := by
    simpa [prefixWord, tailWord_4336372, baseEnd_4336372] using wordTrace_append hprefix tailTrace_4336372
  have hstable : (prefixWord ++ tailWord_4336372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336372).length < 2 ^ (prefixWord ++ tailWord_4336372).sum := by decide
  have hdescent : baseEnd_4336372 < baseStart_4336372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336374 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4336374 : Nat := 118140960795 + 4336374 * 2 ^ 59
def prefixEnd_4336374 : Nat := 4983230072969 + 3 ^ 40 * 4336374 * 2
def baseEnd_4336374 : Nat := 2226644159659922150482385

theorem tailTrace_4336374 : CollatzResearch.WordTrace tailWord_4336374 prefixEnd_4336374 2226644159659922150482385 := by
  unfold tailWord_4336374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9885034574504066660164511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105440368794710044375088117 9885034574504066660164511)
  ·
    refine ⟨14827551861756099990246767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9885034574504066660164511 14827551861756099990246767)
    ·
      refine ⟨22241327792634149985370151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14827551861756099990246767 22241327792634149985370151)
      ·
        refine ⟨33361991688951224978055227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22241327792634149985370151 33361991688951224978055227)
        ·
          refine ⟨50042987533426837467082841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33361991688951224978055227 50042987533426837467082841)
          ·
            refine ⟨37532240650070128100312131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50042987533426837467082841 37532240650070128100312131)
            ·
              refine ⟨56298360975105192150468197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37532240650070128100312131 56298360975105192150468197)
              ·
                refine ⟨10555942682832223528212787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56298360975105192150468197 10555942682832223528212787)
                ·
                  refine ⟨15833914024248335292319181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10555942682832223528212787 15833914024248335292319181)
                  ·
                    refine ⟨5937717759093125734619693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15833914024248335292319181 5937717759093125734619693)
                    ·
                      refine ⟨2226644159659922150482385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5937717759093125734619693 2226644159659922150482385)
                      ·
                        rfl

theorem cell23_4336374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4336374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336374 prefixEnd_4336374 := by exact prefixLift 4336374
  have htrace : WordTrace (prefixWord ++ tailWord_4336374) baseStart_4336374 baseEnd_4336374 := by
    simpa [prefixWord, tailWord_4336374, baseEnd_4336374] using wordTrace_append hprefix tailTrace_4336374
  have hstable : (prefixWord ++ tailWord_4336374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336374).length < 2 ^ (prefixWord ++ tailWord_4336374).sum := by decide
  have hdescent : baseEnd_4336374 < baseStart_4336374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336391 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4336391 : Nat := 118140960795 + 4336391 * 2 ^ 59
def prefixEnd_4336391 : Nat := 4983230072969 + 3 ^ 40 * 4336391 * 2
def baseEnd_4336391 : Nat := 2226652888831048583969807

theorem tailTrace_4336391 : CollatzResearch.WordTrace tailWord_4336391 prefixEnd_4336391 2226652888831048583969807 := by
  unfold tailWord_4336391
  simp only [CollatzResearch.WordTrace]
  refine ⟨158161173233003478466001027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105440782155335652310667351 158161173233003478466001027)
  ·
    refine ⟨237241759849505217699001541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158161173233003478466001027 237241759849505217699001541)
    ·
      refine ⟨44482829971782228318562789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237241759849505217699001541 44482829971782228318562789)
      ·
        refine ⟨8340530619709167809730523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44482829971782228318562789 8340530619709167809730523)
        ·
          refine ⟨12510795929563751714595785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340530619709167809730523 12510795929563751714595785)
          ·
            refine ⟨9383096947172813785946839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12510795929563751714595785 9383096947172813785946839)
            ·
              refine ⟨14074645420759220678920259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383096947172813785946839 14074645420759220678920259)
              ·
                refine ⟨21111968131138831018380389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14074645420759220678920259 21111968131138831018380389)
                ·
                  refine ⟨3958494024588530815946323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21111968131138831018380389 3958494024588530815946323)
                  ·
                    refine ⟨5937741036882796223919485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3958494024588530815946323 5937741036882796223919485)
                    ·
                      refine ⟨2226652888831048583969807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5937741036882796223919485 2226652888831048583969807)
                      ·
                        rfl

theorem cell23_4336391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4336391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336391 prefixEnd_4336391 := by exact prefixLift 4336391
  have htrace : WordTrace (prefixWord ++ tailWord_4336391) baseStart_4336391 baseEnd_4336391 := by
    simpa [prefixWord, tailWord_4336391, baseEnd_4336391] using wordTrace_append hprefix tailTrace_4336391
  have hstable : (prefixWord ++ tailWord_4336391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336391).length < 2 ^ (prefixWord ++ tailWord_4336391).sum := by decide
  have hdescent : baseEnd_4336391 < baseStart_4336391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336417 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4336417 : Nat := 118140960795 + 4336417 * 2 ^ 59
def prefixEnd_4336417 : Nat := 4983230072969 + 3 ^ 40 * 4336417 * 2
def baseEnd_4336417 : Nat := 2226666239328065482244687

theorem tailTrace_4336417 : CollatzResearch.WordTrace tailWord_4336417 prefixEnd_4336417 2226666239328065482244687 := by
  unfold tailWord_4336417
  simp only [CollatzResearch.WordTrace]
  refine ⟨158162121530909284906447505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105441414353939523270965003 158162121530909284906447505)
  ·
    refine ⟨118621591148181963679835629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158162121530909284906447505 118621591148181963679835629)
    ·
      refine ⟨44483096680568236379938361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118621591148181963679835629 44483096680568236379938361)
      ·
        refine ⟨33362322510426177284953771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44483096680568236379938361 33362322510426177284953771)
        ·
          refine ⟨50043483765639265927430657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33362322510426177284953771 50043483765639265927430657)
          ·
            refine ⟨37532612824229449445572993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50043483765639265927430657 37532612824229449445572993)
            ·
              refine ⟨28149459618172087084179745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37532612824229449445572993 28149459618172087084179745)
              ·
                refine ⟨21112094713629065313134809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28149459618172087084179745 21112094713629065313134809)
                ·
                  refine ⟨15834071035221798984851107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21112094713629065313134809 15834071035221798984851107)
                  ·
                    refine ⟨23751106552832698477276661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15834071035221798984851107 23751106552832698477276661)
                    ·
                      refine ⟨2226666239328065482244687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23751106552832698477276661 2226666239328065482244687)
                      ·
                        rfl

theorem cell23_4336417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4336417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336417 prefixEnd_4336417 := by exact prefixLift 4336417
  have htrace : WordTrace (prefixWord ++ tailWord_4336417) baseStart_4336417 baseEnd_4336417 := by
    simpa [prefixWord, tailWord_4336417, baseEnd_4336417] using wordTrace_append hprefix tailTrace_4336417
  have hstable : (prefixWord ++ tailWord_4336417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336417).length < 2 ^ (prefixWord ++ tailWord_4336417).sum := by decide
  have hdescent : baseEnd_4336417 < baseStart_4336417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336418 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_4336418 : Nat := 118140960795 + 4336418 * 2 ^ 59
def prefixEnd_4336418 : Nat := 4983230072969 + 3 ^ 40 * 4336418 * 2
def baseEnd_4336418 : Nat := 2226666752808719978332183

theorem tailTrace_4336418 : CollatzResearch.WordTrace tailWord_4336418 prefixEnd_4336418 2226666752808719978332183 := by
  unfold tailWord_4336418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540539500976415519308477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105441438669270441384822605 39540539500976415519308477)
  ·
    refine ⟨14827702312866155819740679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39540539500976415519308477 14827702312866155819740679)
    ·
      refine ⟨22241553469299233729611019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14827702312866155819740679 22241553469299233729611019)
      ·
        refine ⟨33362330203948850594416529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22241553469299233729611019 33362330203948850594416529)
        ·
          refine ⟨25021747652961637945812397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33362330203948850594416529 25021747652961637945812397)
          ·
            refine ⟨9383155369860614229679649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25021747652961637945812397 9383155369860614229679649)
            ·
              refine ⟨7037366527395460672259737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9383155369860614229679649 7037366527395460672259737)
              ·
                refine ⟨5278024895546595504194803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037366527395460672259737 5278024895546595504194803)
                ·
                  refine ⟨7917037343319893256292205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278024895546595504194803 7917037343319893256292205)
                  ·
                    refine ⟨2968889003744959971109577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7917037343319893256292205 2968889003744959971109577)
                    ·
                      refine ⟨2226666752808719978332183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968889003744959971109577 2226666752808719978332183)
                      ·
                        rfl

theorem cell23_4336418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_4336418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336418 prefixEnd_4336418 := by exact prefixLift 4336418
  have htrace : WordTrace (prefixWord ++ tailWord_4336418) baseStart_4336418 baseEnd_4336418 := by
    simpa [prefixWord, tailWord_4336418, baseEnd_4336418] using wordTrace_append hprefix tailTrace_4336418
  have hstable : (prefixWord ++ tailWord_4336418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336418).length < 2 ^ (prefixWord ++ tailWord_4336418).sum := by decide
  have hdescent : baseEnd_4336418 < baseStart_4336418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336484 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_4336484 : Nat := 118140960795 + 4336484 * 2 ^ 59
def prefixEnd_4336484 : Nat := 4983230072969 + 3 ^ 40 * 4336484 * 2
def baseEnd_4336484 : Nat := 742233547510638906702293

theorem tailTrace_4336484 : CollatzResearch.WordTrace tailWord_4336484 prefixEnd_4336484 742233547510638906702293 := by
  unfold tailWord_4336484
  simp only [CollatzResearch.WordTrace]
  refine ⟨79082282610833277674568253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105443043481111036899424337 79082282610833277674568253)
  ·
    refine ⟨29655855979062479127963095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79082282610833277674568253 29655855979062479127963095)
    ·
      refine ⟨44483783968593718691944643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29655855979062479127963095 44483783968593718691944643)
      ·
        refine ⟨66725675952890578037916965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44483783968593718691944643 66725675952890578037916965)
        ·
          refine ⟨12511064241166983382109431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66725675952890578037916965 12511064241166983382109431)
          ·
            refine ⟨18766596361750475073164147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511064241166983382109431 18766596361750475073164147)
            ·
              refine ⟨28149894542625712609746221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18766596361750475073164147 28149894542625712609746221)
              ·
                refine ⟨10556210453484642228654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28149894542625712609746221 10556210453484642228654833)
                ·
                  refine ⟨7917157840113481671491125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10556210453484642228654833 7917157840113481671491125)
                  ·
                    refine ⟨742233547510638906702293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917157840113481671491125 742233547510638906702293)
                    ·
                      rfl

theorem cell23_4336484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_4336484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336484 prefixEnd_4336484 := by exact prefixLift 4336484
  have htrace : WordTrace (prefixWord ++ tailWord_4336484) baseStart_4336484 baseEnd_4336484 := by
    simpa [prefixWord, tailWord_4336484, baseEnd_4336484] using wordTrace_append hprefix tailTrace_4336484
  have hstable : (prefixWord ++ tailWord_4336484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336484).length < 2 ^ (prefixWord ++ tailWord_4336484).sum := by decide
  have hdescent : baseEnd_4336484 < baseStart_4336484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336521 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 2, 4, 2]
def baseStart_4336521 : Nat := 118140960795 + 4336521 * 2 ^ 59
def prefixEnd_4336521 : Nat := 4983230072969 + 3 ^ 40 * 4336521 * 2
def baseEnd_4336521 : Nat := 2226719641316133075344209

theorem tailTrace_4336521 : CollatzResearch.WordTrace tailWord_4336521 prefixEnd_4336521 2226719641316133075344209 := by
  unfold tailWord_4336521
  simp only [CollatzResearch.WordTrace]
  refine ⟨158165914722532510668233417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105443943148355007112155611 158165914722532510668233417)
  ·
    refine ⟨118624436041899383001175063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158165914722532510668233417 118624436041899383001175063)
    ·
      refine ⟨177936654062849074501762595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118624436041899383001175063 177936654062849074501762595)
      ·
        refine ⟨266904981094273611752643893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177936654062849074501762595 266904981094273611752643893)
        ·
          refine ⟨25022341977588151101810365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 266904981094273611752643893 25022341977588151101810365)
          ·
            refine ⟨9383378241595556663178887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25022341977588151101810365 9383378241595556663178887)
            ·
              refine ⟨14075067362393334994768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383378241595556663178887 14075067362393334994768331)
              ·
                refine ⟨21112601043590002492152497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14075067362393334994768331 21112601043590002492152497)
                ·
                  refine ⟨15834450782692501869114373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21112601043590002492152497 15834450782692501869114373)
                  ·
                    refine ⟨2968959521754844100458945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15834450782692501869114373 2968959521754844100458945)
                    ·
                      refine ⟨2226719641316133075344209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2968959521754844100458945 2226719641316133075344209)
                      ·
                        rfl

theorem cell23_4336521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4, 2].length) (baseStart_4336521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336521 prefixEnd_4336521 := by exact prefixLift 4336521
  have htrace : WordTrace (prefixWord ++ tailWord_4336521) baseStart_4336521 baseEnd_4336521 := by
    simpa [prefixWord, tailWord_4336521, baseEnd_4336521] using wordTrace_append hprefix tailTrace_4336521
  have hstable : (prefixWord ++ tailWord_4336521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336521).length < 2 ^ (prefixWord ++ tailWord_4336521).sum := by decide
  have hdescent : baseEnd_4336521 < baseStart_4336521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336524 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4336524 : Nat := 118140960795 + 4336524 * 2 ^ 59
def prefixEnd_4336524 : Nat := 4983230072969 + 3 ^ 40 * 4336524 * 2
def baseEnd_4336524 : Nat := 2226721181758096563606695

theorem tailTrace_4336524 : CollatzResearch.WordTrace tailWord_4336524 prefixEnd_4336524 2226721181758096563606695 := by
  unfold tailWord_4336524
  simp only [CollatzResearch.WordTrace]
  refine ⟨79083012070760821090296313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105444016094347761453728417 79083012070760821090296313)
  ·
    refine ⟨59312259053070615817722235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79083012070760821090296313 59312259053070615817722235)
    ·
      refine ⟨88968388579605923726583353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59312259053070615817722235 88968388579605923726583353)
      ·
        refine ⟨66726291434704442794937515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88968388579605923726583353 66726291434704442794937515)
        ·
          refine ⟨100089437152056664192406273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66726291434704442794937515 100089437152056664192406273)
          ·
            refine ⟨75067077864042498144304705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100089437152056664192406273 75067077864042498144304705)
            ·
              refine ⟨56300308398031873608228529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75067077864042498144304705 56300308398031873608228529)
              ·
                refine ⟨42225231298523905206171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56300308398031873608228529 42225231298523905206171397)
                ·
                  refine ⟨7917230868473232226157137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42225231298523905206171397 7917230868473232226157137)
                  ·
                    refine ⟨5937923151354924169617853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7917230868473232226157137 5937923151354924169617853)
                    ·
                      refine ⟨2226721181758096563606695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5937923151354924169617853 2226721181758096563606695)
                      ·
                        rfl

theorem cell23_4336524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4336524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336524 prefixEnd_4336524 := by exact prefixLift 4336524
  have htrace : WordTrace (prefixWord ++ tailWord_4336524) baseStart_4336524 baseEnd_4336524 := by
    simpa [prefixWord, tailWord_4336524, baseEnd_4336524] using wordTrace_append hprefix tailTrace_4336524
  have hstable : (prefixWord ++ tailWord_4336524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336524).length < 2 ^ (prefixWord ++ tailWord_4336524).sum := by decide
  have hdescent : baseEnd_4336524 < baseStart_4336524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336538 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4336538 : Nat := 118140960795 + 4336538 * 2 ^ 59
def prefixEnd_4336538 : Nat := 4983230072969 + 3 ^ 40 * 4336538 * 2
def baseEnd_4336538 : Nat := 2226728370487259508831631

theorem tailTrace_4336538 : CollatzResearch.WordTrace tailWord_4336538 prefixEnd_4336538 2226728370487259508831631 := by
  unfold tailWord_4336538
  simp only [CollatzResearch.WordTrace]
  refine ⟨39541633690867730642900567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105444356508980615047734845 39541633690867730642900567)
  ·
    refine ⟨59312450536301595964350851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39541633690867730642900567 59312450536301595964350851)
    ·
      refine ⟨88968675804452393946526277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59312450536301595964350851 88968675804452393946526277)
      ·
        refine ⟨16681626713334823864973677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88968675804452393946526277 16681626713334823864973677)
        ·
          refine ⟨6255610017500558949365129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16681626713334823864973677 6255610017500558949365129)
          ·
            refine ⟨4691707513125419212023847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6255610017500558949365129 4691707513125419212023847)
            ·
              refine ⟨7037561269688128818035771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691707513125419212023847 7037561269688128818035771)
              ·
                refine ⟨10556341904532193227053657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037561269688128818035771 10556341904532193227053657)
                ·
                  refine ⟨7917256428399144920290243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10556341904532193227053657 7917256428399144920290243)
                  ·
                    refine ⟨11875884642598717380435365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7917256428399144920290243 11875884642598717380435365)
                    ·
                      refine ⟨2226728370487259508831631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11875884642598717380435365 2226728370487259508831631)
                      ·
                        rfl

theorem cell23_4336538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4336538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336538 prefixEnd_4336538 := by exact prefixLift 4336538
  have htrace : WordTrace (prefixWord ++ tailWord_4336538) baseStart_4336538 baseEnd_4336538 := by
    simpa [prefixWord, tailWord_4336538, baseEnd_4336538] using wordTrace_append hprefix tailTrace_4336538
  have hstable : (prefixWord ++ tailWord_4336538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336538).length < 2 ^ (prefixWord ++ tailWord_4336538).sum := by decide
  have hdescent : baseEnd_4336538 < baseStart_4336538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336548 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_4336548 : Nat := 118140960795 + 4336548 * 2 ^ 59
def prefixEnd_4336548 : Nat := 4983230072969 + 3 ^ 40 * 4336548 * 2
def baseEnd_4336548 : Nat := 742244501764601489902195

theorem tailTrace_4336548 : CollatzResearch.WordTrace tailWord_4336548 prefixEnd_4336548 742244501764601489902195 := by
  unfold tailWord_4336548
  simp only [CollatzResearch.WordTrace]
  refine ⟨79083449746717347139733149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105444599662289796186310865 79083449746717347139733149)
  ·
    refine ⟨29656293655019005177399931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79083449746717347139733149 29656293655019005177399931)
    ·
      refine ⟨44484440482528507766099897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29656293655019005177399931 44484440482528507766099897)
      ·
        refine ⟨33363330361896380824574923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44484440482528507766099897 33363330361896380824574923)
        ·
          refine ⟨50044995542844571236862385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33363330361896380824574923 50044995542844571236862385)
          ·
            refine ⟨37533746657133428427646789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50044995542844571236862385 37533746657133428427646789)
            ·
              refine ⟨7037577498212517830183773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37533746657133428427646789 7037577498212517830183773)
              ·
                refine ⟨2639091561829694186318915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7037577498212517830183773 2639091561829694186318915)
                ·
                  refine ⟨3958637342744541279478373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639091561829694186318915 3958637342744541279478373)
                  ·
                    refine ⟨742244501764601489902195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958637342744541279478373 742244501764601489902195)
                    ·
                      rfl

theorem cell23_4336548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_4336548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336548 prefixEnd_4336548 := by exact prefixLift 4336548
  have htrace : WordTrace (prefixWord ++ tailWord_4336548) baseStart_4336548 baseEnd_4336548 := by
    simpa [prefixWord, tailWord_4336548, baseEnd_4336548] using wordTrace_append hprefix tailTrace_4336548
  have hstable : (prefixWord ++ tailWord_4336548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336548).length < 2 ^ (prefixWord ++ tailWord_4336548).sum := by decide
  have hdescent : baseEnd_4336548 < baseStart_4336548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336591 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 1, 5]
def baseStart_4336591 : Nat := 118140960795 + 4336591 * 2 ^ 59
def prefixEnd_4336591 : Nat := 4983230072969 + 3 ^ 40 * 4336591 * 2
def baseEnd_4336591 : Nat := 742251861653982600489629

theorem tailTrace_4336591 : CollatzResearch.WordTrace tailWord_4336591 prefixEnd_4336591 742251861653982600489629 := by
  unfold tailWord_4336591
  simp only [CollatzResearch.WordTrace]
  refine ⟨158168467832278912623281627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105445645221519275082187751 158168467832278912623281627)
  ·
    refine ⟨237252701748418368934922441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158168467832278912623281627 237252701748418368934922441)
    ·
      refine ⟨177939526311313776701191831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237252701748418368934922441 177939526311313776701191831)
      ·
        refine ⟨266909289466970665051787747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177939526311313776701191831 266909289466970665051787747)
        ·
          refine ⟨400363934200455997577681621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266909289466970665051787747 400363934200455997577681621)
          ·
            refine ⟨9383529707823187443226913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 400363934200455997577681621 9383529707823187443226913)
            ·
              refine ⟨7037647280867390582420185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9383529707823187443226913 7037647280867390582420185)
              ·
                refine ⟨5278235460650542936815139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037647280867390582420185 5278235460650542936815139)
                ·
                  refine ⟨7917353190975814405222709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278235460650542936815139 7917353190975814405222709)
                  ·
                    refine ⟨742251861653982600489629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917353190975814405222709 742251861653982600489629)
                    ·
                      rfl

theorem cell23_4336591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_4336591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336591 prefixEnd_4336591 := by exact prefixLift 4336591
  have htrace : WordTrace (prefixWord ++ tailWord_4336591) baseStart_4336591 baseEnd_4336591 := by
    simpa [prefixWord, tailWord_4336591, baseEnd_4336591] using wordTrace_append hprefix tailTrace_4336591
  have hstable : (prefixWord ++ tailWord_4336591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336591).length < 2 ^ (prefixWord ++ tailWord_4336591).sum := by decide
  have hdescent : baseEnd_4336591 < baseStart_4336591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336611 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4336611 : Nat := 118140960795 + 4336611 * 2 ^ 59
def prefixEnd_4336611 : Nat := 4983230072969 + 3 ^ 40 * 4336611 * 2
def baseEnd_4336611 : Nat := 2226765854575037723218795

theorem tailTrace_4336611 : CollatzResearch.WordTrace tailWord_4336611 prefixEnd_4336611 2226765854575037723218795 := by
  unfold tailWord_4336611
  simp only [CollatzResearch.WordTrace]
  refine ⟨158169197292206456039009687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105446131528137637359339791 158169197292206456039009687)
  ·
    refine ⟨237253795938309684058514531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158169197292206456039009687 237253795938309684058514531)
    ·
      refine ⟨355880693907464526087771797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237253795938309684058514531 355880693907464526087771797)
      ·
        refine ⟨16681907526912399660364303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 355880693907464526087771797 16681907526912399660364303)
        ·
          refine ⟨25022861290368599490546455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16681907526912399660364303 25022861290368599490546455)
          ·
            refine ⟨37534291935552899235819683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25022861290368599490546455 37534291935552899235819683)
            ·
              refine ⟨56301437903329348853729525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37534291935552899235819683 56301437903329348853729525)
              ·
                refine ⟨5278259803437126455037143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56301437903329348853729525 5278259803437126455037143)
                ·
                  refine ⟨7917389705155689682555715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278259803437126455037143 7917389705155689682555715)
                  ·
                    refine ⟨11876084557733534523833573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7917389705155689682555715 11876084557733534523833573)
                    ·
                      refine ⟨2226765854575037723218795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11876084557733534523833573 2226765854575037723218795)
                      ·
                        rfl

theorem cell23_4336611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4336611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336611 prefixEnd_4336611 := by exact prefixLift 4336611
  have htrace : WordTrace (prefixWord ++ tailWord_4336611) baseStart_4336611 baseEnd_4336611 := by
    simpa [prefixWord, tailWord_4336611, baseEnd_4336611] using wordTrace_append hprefix tailTrace_4336611
  have hstable : (prefixWord ++ tailWord_4336611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336611).length < 2 ^ (prefixWord ++ tailWord_4336611).sum := by decide
  have hdescent : baseEnd_4336611 < baseStart_4336611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336622 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_4336622 : Nat := 118140960795 + 4336622 * 2 ^ 59
def prefixEnd_4336622 : Nat := 4983230072969 + 3 ^ 40 * 4336622 * 2
def baseEnd_4336622 : Nat := 2226771502862237180181245

theorem tailTrace_4336622 : CollatzResearch.WordTrace tailWord_4336622 prefixEnd_4336622 2226771502862237180181245 := by
  unfold tailWord_4336622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771199811895825614707515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105446398996777736611773413 19771199811895825614707515)
  ·
    refine ⟨29656799717843738422061273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19771199811895825614707515 29656799717843738422061273)
    ·
      refine ⟨22242599788382803816545955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29656799717843738422061273 22242599788382803816545955)
      ·
        refine ⟨33363899682574205724818933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22242599788382803816545955 33363899682574205724818933)
        ·
          refine ⟨3127865595241331786701775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33363899682574205724818933 3127865595241331786701775)
          ·
            refine ⟨4691798392861997680052663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127865595241331786701775 4691798392861997680052663)
            ·
              refine ⟨7037697589292996520078995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691798392861997680052663 7037697589292996520078995)
              ·
                refine ⟨10556546383939494780118493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037697589292996520078995 10556546383939494780118493)
                ·
                  refine ⟨3958704893977310542544435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10556546383939494780118493 3958704893977310542544435)
                  ·
                    refine ⟨5938057340965965813816653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3958704893977310542544435 5938057340965965813816653)
                    ·
                      refine ⟨2226771502862237180181245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938057340965965813816653 2226771502862237180181245)
                      ·
                        rfl

theorem cell23_4336622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_4336622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336622 prefixEnd_4336622 := by exact prefixLift 4336622
  have htrace : WordTrace (prefixWord ++ tailWord_4336622) baseStart_4336622 baseEnd_4336622 := by
    simpa [prefixWord, tailWord_4336622, baseEnd_4336622] using wordTrace_append hprefix tailTrace_4336622
  have hstable : (prefixWord ++ tailWord_4336622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336622).length < 2 ^ (prefixWord ++ tailWord_4336622).sum := by decide
  have hdescent : baseEnd_4336622 < baseStart_4336622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336642 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4336642 : Nat := 118140960795 + 4336642 * 2 ^ 59
def prefixEnd_4336642 : Nat := 4983230072969 + 3 ^ 40 * 4336642 * 2
def baseEnd_4336642 : Nat := 742260590825109033977051

theorem tailTrace_4336642 : CollatzResearch.WordTrace tailWord_4336642 prefixEnd_4336642 742260590825109033977051 := by
  unfold tailWord_4336642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39542581988773537083347045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105446885303396098888925453 39542581988773537083347045)
  ·
    refine ⟨7414234122895038203127571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39542581988773537083347045 7414234122895038203127571)
    ·
      refine ⟨11121351184342557304691357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414234122895038203127571 11121351184342557304691357)
      ·
        refine ⟨4170506694128458989259259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11121351184342557304691357 4170506694128458989259259)
        ·
          refine ⟨6255760041192688483888889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4170506694128458989259259 6255760041192688483888889)
          ·
            refine ⟨4691820030894516362916667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6255760041192688483888889 4691820030894516362916667)
            ·
              refine ⟨7037730046341774544375001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691820030894516362916667 7037730046341774544375001)
              ·
                refine ⟨5278297534756330908281251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037730046341774544375001 5278297534756330908281251)
                ·
                  refine ⟨7917446302134496362421877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278297534756330908281251 7917446302134496362421877)
                  ·
                    refine ⟨742260590825109033977051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917446302134496362421877 742260590825109033977051)
                    ·
                      rfl

theorem cell23_4336642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4336642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336642 prefixEnd_4336642 := by exact prefixLift 4336642
  have htrace : WordTrace (prefixWord ++ tailWord_4336642) baseStart_4336642 baseEnd_4336642 := by
    simpa [prefixWord, tailWord_4336642, baseEnd_4336642] using wordTrace_append hprefix tailTrace_4336642
  have hstable : (prefixWord ++ tailWord_4336642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336642).length < 2 ^ (prefixWord ++ tailWord_4336642).sum := by decide
  have hdescent : baseEnd_4336642 < baseStart_4336642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336648 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_4336648 : Nat := 118140960795 + 4336648 * 2 ^ 59
def prefixEnd_4336648 : Nat := 4983230072969 + 3 ^ 40 * 4336648 * 2
def baseEnd_4336648 : Nat := 2226784853359254078456125

theorem tailTrace_4336648 : CollatzResearch.WordTrace tailWord_4336648 prefixEnd_4336648 2226784853359254078456125 := by
  unfold tailWord_4336648
  simp only [CollatzResearch.WordTrace]
  refine ⟨79085273396536205679053299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105447031195381607572071065 79085273396536205679053299)
  ·
    refine ⟨118627910094804308518579949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79085273396536205679053299 118627910094804308518579949)
    ·
      refine ⟨44485466285551615694467481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118627910094804308518579949 44485466285551615694467481)
      ·
        refine ⟨33364099714163711770850611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44485466285551615694467481 33364099714163711770850611)
        ·
          refine ⟨50046149571245567656275917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33364099714163711770850611 50046149571245567656275917)
          ·
            refine ⟨18767306089217087871103469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50046149571245567656275917 18767306089217087871103469)
            ·
              refine ⟨7037739783456407951663801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18767306089217087871103469 7037739783456407951663801)
              ·
                refine ⟨5278304837592305963747851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037739783456407951663801 5278304837592305963747851)
                ·
                  refine ⟨7917457256388458945621777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278304837592305963747851 7917457256388458945621777)
                  ·
                    refine ⟨5938092942291344209216333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7917457256388458945621777 5938092942291344209216333)
                    ·
                      refine ⟨2226784853359254078456125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938092942291344209216333 2226784853359254078456125)
                      ·
                        rfl

theorem cell23_4336648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_4336648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336648 prefixEnd_4336648 := by exact prefixLift 4336648
  have htrace : WordTrace (prefixWord ++ tailWord_4336648) baseStart_4336648 baseEnd_4336648 := by
    simpa [prefixWord, tailWord_4336648, baseEnd_4336648] using wordTrace_append hprefix tailTrace_4336648
  have hstable : (prefixWord ++ tailWord_4336648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336648).length < 2 ^ (prefixWord ++ tailWord_4336648).sum := by decide
  have hdescent : baseEnd_4336648 < baseStart_4336648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336661 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_4336661 : Nat := 118140960795 + 4336661 * 2 ^ 59
def prefixEnd_4336661 : Nat := 4983230072969 + 3 ^ 40 * 4336661 * 2
def baseEnd_4336661 : Nat := 2226791528607762527593565

theorem tailTrace_4336661 : CollatzResearch.WordTrace tailWord_4336661 prefixEnd_4336661 2226791528607762527593565 := by
  unfold tailWord_4336661
  simp only [CollatzResearch.WordTrace]
  refine ⟨158171020942025314578329837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105447347294683543052219891 158171020942025314578329837)
  ·
    refine ⟨59314132853259492966873689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158171020942025314578329837 59314132853259492966873689)
    ·
      refine ⟨44485599639944619725155267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59314132853259492966873689 44485599639944619725155267)
      ·
        refine ⟨66728399459916929587732901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44485599639944619725155267 66728399459916929587732901)
        ·
          refine ⟨12511574898734424297699919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66728399459916929587732901 12511574898734424297699919)
          ·
            refine ⟨18767362348101636446549879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511574898734424297699919 18767362348101636446549879)
            ·
              refine ⟨28151043522152454669824819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18767362348101636446549879 28151043522152454669824819)
              ·
                refine ⟨42226565283228682004737229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28151043522152454669824819 42226565283228682004737229)
                ·
                  refine ⟨15834961981210755751776461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42226565283228682004737229 15834961981210755751776461)
                  ·
                    refine ⟨5938110742954033406916173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15834961981210755751776461 5938110742954033406916173)
                    ·
                      refine ⟨2226791528607762527593565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938110742954033406916173 2226791528607762527593565)
                      ·
                        rfl

theorem cell23_4336661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_4336661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336661 prefixEnd_4336661 := by exact prefixLift 4336661
  have htrace : WordTrace (prefixWord ++ tailWord_4336661) baseStart_4336661 baseEnd_4336661 := by
    simpa [prefixWord, tailWord_4336661, baseEnd_4336661] using wordTrace_append hprefix tailTrace_4336661
  have hstable : (prefixWord ++ tailWord_4336661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336661).length < 2 ^ (prefixWord ++ tailWord_4336661).sum := by decide
  have hdescent : baseEnd_4336661 < baseStart_4336661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336679 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4336679 : Nat := 118140960795 + 4336679 * 2 ^ 59
def prefixEnd_4336679 : Nat := 4983230072969 + 3 ^ 40 * 4336679 * 2
def baseEnd_4336679 : Nat := 2226800771259543457168483

theorem tailTrace_4336679 : CollatzResearch.WordTrace tailWord_4336679 prefixEnd_4336679 2226800771259543457168483 := by
  unfold tailWord_4336679
  simp only [CollatzResearch.WordTrace]
  refine ⟨158171677455960103652485091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105447784970640069101656727 158171677455960103652485091)
  ·
    refine ⟨237257516183940155478727637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158171677455960103652485091 237257516183940155478727637)
    ·
      refine ⟨5560723035561097394032679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 237257516183940155478727637 5560723035561097394032679)
      ·
        refine ⟨8341084553341646091049019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560723035561097394032679 8341084553341646091049019)
        ·
          refine ⟨12511626830012469136573529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341084553341646091049019 12511626830012469136573529)
          ·
            refine ⟨9383720122509351852430147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12511626830012469136573529 9383720122509351852430147)
            ·
              refine ⟨14075580183764027778645221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383720122509351852430147 14075580183764027778645221)
              ·
                refine ⟨2639171284455755208495979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14075580183764027778645221 2639171284455755208495979)
                ·
                  refine ⟨3958756926683632812743969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639171284455755208495979 3958756926683632812743969)
                  ·
                    refine ⟨2969067695012724609557977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958756926683632812743969 2969067695012724609557977)
                    ·
                      refine ⟨2226800771259543457168483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969067695012724609557977 2226800771259543457168483)
                      ·
                        rfl

theorem cell23_4336679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4336679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336679 prefixEnd_4336679 := by exact prefixLift 4336679
  have htrace : WordTrace (prefixWord ++ tailWord_4336679) baseStart_4336679 baseEnd_4336679 := by
    simpa [prefixWord, tailWord_4336679, baseEnd_4336679] using wordTrace_append hprefix tailTrace_4336679
  have hstable : (prefixWord ++ tailWord_4336679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336679).length < 2 ^ (prefixWord ++ tailWord_4336679).sum := by decide
  have hdescent : baseEnd_4336679 < baseStart_4336679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336684 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_4336684 : Nat := 118140960795 + 4336684 * 2 ^ 59
def prefixEnd_4336684 : Nat := 4983230072969 + 3 ^ 40 * 4336684 * 2
def baseEnd_4336684 : Nat := 2226803338662815937605959

theorem tailTrace_4336684 : CollatzResearch.WordTrace tailWord_4336684 prefixEnd_4336684 2226803338662815937605959 := by
  unfold tailWord_4336684
  simp only [CollatzResearch.WordTrace]
  refine ⟨79085929910470994753208553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105447906547294659670944737 79085929910470994753208553)
  ·
    refine ⟨59314447432853246064906415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79085929910470994753208553 59314447432853246064906415)
    ·
      refine ⟨88971671149279869097359623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59314447432853246064906415 88971671149279869097359623)
      ·
        refine ⟨133457506723919803646039435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88971671149279869097359623 133457506723919803646039435)
        ·
          refine ⟨200186260085879705469059153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133457506723919803646039435 200186260085879705469059153)
          ·
            refine ⟨150139695064409779101794365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200186260085879705469059153 150139695064409779101794365)
            ·
              refine ⟨56302385649153667163172887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150139695064409779101794365 56302385649153667163172887)
              ·
                refine ⟨84453578473730500744759331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56302385649153667163172887 84453578473730500744759331)
                ·
                  refine ⟨126680367710595751117138997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84453578473730500744759331 126680367710595751117138997)
                  ·
                    refine ⟨11876284472868351667231781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126680367710595751117138997 11876284472868351667231781)
                    ·
                      refine ⟨2226803338662815937605959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11876284472868351667231781 2226803338662815937605959)
                      ·
                        rfl

theorem cell23_4336684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_4336684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336684 prefixEnd_4336684 := by exact prefixLift 4336684
  have htrace : WordTrace (prefixWord ++ tailWord_4336684) baseStart_4336684 baseEnd_4336684 := by
    simpa [prefixWord, tailWord_4336684, baseEnd_4336684] using wordTrace_append hprefix tailTrace_4336684
  have hstable : (prefixWord ++ tailWord_4336684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336684).length < 2 ^ (prefixWord ++ tailWord_4336684).sum := by decide
  have hdescent : baseEnd_4336684 < baseStart_4336684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336718 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_4336718 : Nat := 118140960795 + 4336718 * 2 ^ 59
def prefixEnd_4336718 : Nat := 4983230072969 + 3 ^ 40 * 4336718 * 2
def baseEnd_4336718 : Nat := 2226820797005068804580803

theorem tailTrace_4336718 : CollatzResearch.WordTrace tailWord_4336718 prefixEnd_4336718 2226820797005068804580803 := by
  unfold tailWord_4336718
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771637487852351664144351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105448733268545875542103205 19771637487852351664144351)
  ·
    refine ⟨29657456231778527496216527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19771637487852351664144351 29657456231778527496216527)
    ·
      refine ⟨44486184347667791244324791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29657456231778527496216527 44486184347667791244324791)
      ·
        refine ⟨66729276521501686866487187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44486184347667791244324791 66729276521501686866487187)
        ·
          refine ⟨100093914782252530299730781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66729276521501686866487187 100093914782252530299730781)
          ·
            refine ⟨37535218043344698862399043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100093914782252530299730781 37535218043344698862399043)
            ·
              refine ⟨56302827065017048293598565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37535218043344698862399043 56302827065017048293598565)
              ·
                refine ⟨10556780074690696555049731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56302827065017048293598565 10556780074690696555049731)
                ·
                  refine ⟨15835170112036044832574597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10556780074690696555049731 15835170112036044832574597)
                  ·
                    refine ⟨2969094396006758406107737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15835170112036044832574597 2969094396006758406107737)
                    ·
                      refine ⟨2226820797005068804580803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969094396006758406107737 2226820797005068804580803)
                      ·
                        rfl

theorem cell23_4336718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_4336718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336718 prefixEnd_4336718 := by exact prefixLift 4336718
  have htrace : WordTrace (prefixWord ++ tailWord_4336718) baseStart_4336718 baseEnd_4336718 := by
    simpa [prefixWord, tailWord_4336718, baseEnd_4336718] using wordTrace_append hprefix tailTrace_4336718
  have hstable : (prefixWord ++ tailWord_4336718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336718).length < 2 ^ (prefixWord ++ tailWord_4336718).sum := by decide
  have hdescent : baseEnd_4336718 < baseStart_4336718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336722 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_4336722 : Nat := 118140960795 + 4336722 * 2 ^ 59
def prefixEnd_4336722 : Nat := 4983230072969 + 3 ^ 40 * 4336722 * 2
def baseEnd_4336722 : Nat := 2226822850927686788930785

theorem tailTrace_4336722 : CollatzResearch.WordTrace tailWord_4336722 prefixEnd_4336722 2226822850927686788930785 := by
  unfold tailWord_4336722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39543311448701080499075105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105448830529869547997533613 39543311448701080499075105)
  ·
    refine ⟨29657483586525810374306329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39543311448701080499075105 29657483586525810374306329)
    ·
      refine ⟨22243112689894357780729747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29657483586525810374306329 22243112689894357780729747)
      ·
        refine ⟨33364669034841536671094621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22243112689894357780729747 33364669034841536671094621)
        ·
          refine ⟨12511750888065576251660483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33364669034841536671094621 12511750888065576251660483)
          ·
            refine ⟨18767626332098364377490725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511750888065576251660483 18767626332098364377490725)
            ·
              refine ⟨3518929937268443320779511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18767626332098364377490725 3518929937268443320779511)
              ·
                refine ⟨5278394905902664981169267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518929937268443320779511 5278394905902664981169267)
                ·
                  refine ⟨7917592358853997471753901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278394905902664981169267 7917592358853997471753901)
                  ·
                    refine ⟨2969097134570249051907713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7917592358853997471753901 2969097134570249051907713)
                    ·
                      refine ⟨2226822850927686788930785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969097134570249051907713 2226822850927686788930785)
                      ·
                        rfl

theorem cell23_4336722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_4336722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336722 prefixEnd_4336722 := by exact prefixLift 4336722
  have htrace : WordTrace (prefixWord ++ tailWord_4336722) baseStart_4336722 baseEnd_4336722 := by
    simpa [prefixWord, tailWord_4336722, baseEnd_4336722] using wordTrace_append hprefix tailTrace_4336722
  have hstable : (prefixWord ++ tailWord_4336722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336722).length < 2 ^ (prefixWord ++ tailWord_4336722).sum := by decide
  have hdescent : baseEnd_4336722 < baseStart_4336722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336741 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 7]
def baseStart_4336741 : Nat := 118140960795 + 4336741 * 2 ^ 59
def prefixEnd_4336741 : Nat := 4983230072969 + 3 ^ 40 * 4336741 * 2
def baseEnd_4336741 : Nat := 247425845228902468288133

theorem tailTrace_4336741 : CollatzResearch.WordTrace tailWord_4336741 prefixEnd_4336741 247425845228902468288133 := by
  unfold tailWord_4336741
  simp only [CollatzResearch.WordTrace]
  refine ⟨158173938781735488241242077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105449292521156992160828051 158173938781735488241242077)
  ·
    refine ⟨59315227043150808090465779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158173938781735488241242077 59315227043150808090465779)
    ·
      refine ⟨88972840564726212135698669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59315227043150808090465779 88972840564726212135698669)
      ·
        refine ⟨33364815211772329550887001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88972840564726212135698669 33364815211772329550887001)
        ·
          refine ⟨25023611408829247163165251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33364815211772329550887001 25023611408829247163165251)
          ·
            refine ⟨37535417113243870744747877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25023611408829247163165251 37535417113243870744747877)
            ·
              refine ⟨7037890708733225764640227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37535417113243870744747877 7037890708733225764640227)
              ·
                refine ⟨10556836063099838646960341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037890708733225764640227 10556836063099838646960341)
                ·
                  refine ⟨247425845228902468288133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10556836063099838646960341 247425845228902468288133)
                  ·
                    rfl

theorem cell23_4336741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_4336741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336741 prefixEnd_4336741 := by exact prefixLift 4336741
  have htrace : WordTrace (prefixWord ++ tailWord_4336741) baseStart_4336741 baseEnd_4336741 := by
    simpa [prefixWord, tailWord_4336741, baseEnd_4336741] using wordTrace_append hprefix tailTrace_4336741
  have hstable : (prefixWord ++ tailWord_4336741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336741).length < 2 ^ (prefixWord ++ tailWord_4336741).sum := by decide
  have hdescent : baseEnd_4336741 < baseStart_4336741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336751 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_4336751 : Nat := 118140960795 + 4336751 * 2 ^ 59
def prefixEnd_4336751 : Nat := 4983230072969 + 3 ^ 40 * 4336751 * 2
def baseEnd_4336751 : Nat := 2226837741866667175468151

theorem tailTrace_4336751 : CollatzResearch.WordTrace tailWord_4336751 prefixEnd_4336751 2226837741866667175468151 := by
  unfold tailWord_4336751
  simp only [CollatzResearch.WordTrace]
  refine ⟨158174303511699259949106107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105449535674466173299404071 158174303511699259949106107)
  ·
    refine ⟨237261455267548889923659161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158174303511699259949106107 237261455267548889923659161)
    ·
      refine ⟨177946091450661667442744371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237261455267548889923659161 177946091450661667442744371)
      ·
        refine ⟨266919137175992501164116557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177946091450661667442744371 266919137175992501164116557)
        ·
          refine ⟨100094676440997187936543709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266919137175992501164116557 100094676440997187936543709)
          ·
            refine ⟨37535503665373945476203891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100094676440997187936543709 37535503665373945476203891)
            ·
              refine ⟨56303255498060918214305837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37535503665373945476203891 56303255498060918214305837)
              ·
                refine ⟨21113720811772844330364689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56303255498060918214305837 21113720811772844330364689)
                ·
                  refine ⟨15835290608829633247773517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21113720811772844330364689 15835290608829633247773517)
                  ·
                    refine ⟨5938233978311112467915069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15835290608829633247773517 5938233978311112467915069)
                    ·
                      refine ⟨2226837741866667175468151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938233978311112467915069 2226837741866667175468151)
                      ·
                        rfl

theorem cell23_4336751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_4336751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336751 prefixEnd_4336751 := by exact prefixLift 4336751
  have htrace : WordTrace (prefixWord ++ tailWord_4336751) baseStart_4336751 baseEnd_4336751 := by
    simpa [prefixWord, tailWord_4336751, baseEnd_4336751] using wordTrace_append hprefix tailTrace_4336751
  have hstable : (prefixWord ++ tailWord_4336751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336751).length < 2 ^ (prefixWord ++ tailWord_4336751).sum := by decide
  have hdescent : baseEnd_4336751 < baseStart_4336751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336752 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2]
def baseStart_4336752 : Nat := 118140960795 + 4336752 * 2 ^ 59
def prefixEnd_4336752 : Nat := 4983230072969 + 3 ^ 40 * 4336752 * 2
def baseEnd_4336752 : Nat := 2226838255347321671555647

theorem tailTrace_4336752 : CollatzResearch.WordTrace tailWord_4336752 prefixEnd_4336752 2226838255347321671555647 := by
  unfold tailWord_4336752
  simp only [CollatzResearch.WordTrace]
  refine ⟨79087169992347818559946255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105449559989797091413261673 79087169992347818559946255)
  ·
    refine ⟨118630754988521727839919383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79087169992347818559946255 118630754988521727839919383)
    ·
      refine ⟨177946132482782591759879075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118630754988521727839919383 177946132482782591759879075)
      ·
        refine ⟨266919198724173887639818613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177946132482782591759879075 266919198724173887639818613)
        ·
          refine ⟨25023674880391301966232995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 266919198724173887639818613 25023674880391301966232995)
          ·
            refine ⟨37535512320586952949349493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25023674880391301966232995 37535512320586952949349493)
            ·
              refine ⟨3518954280055026839001515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37535512320586952949349493 3518954280055026839001515)
              ·
                refine ⟨5278431420082540258502273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518954280055026839001515 5278431420082540258502273)
                ·
                  refine ⟨3958823565061905193876705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278431420082540258502273 3958823565061905193876705)
                  ·
                    refine ⟨2969117673796428895407529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958823565061905193876705 2969117673796428895407529)
                    ·
                      refine ⟨2226838255347321671555647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969117673796428895407529 2226838255347321671555647)
                      ·
                        rfl

theorem cell23_4336752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2].length) (baseStart_4336752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336752 prefixEnd_4336752 := by exact prefixLift 4336752
  have htrace : WordTrace (prefixWord ++ tailWord_4336752) baseStart_4336752 baseEnd_4336752 := by
    simpa [prefixWord, tailWord_4336752, baseEnd_4336752] using wordTrace_append hprefix tailTrace_4336752
  have hstable : (prefixWord ++ tailWord_4336752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336752).length < 2 ^ (prefixWord ++ tailWord_4336752).sum := by decide
  have hdescent : baseEnd_4336752 < baseStart_4336752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336771 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 2, 5]
def baseStart_4336771 : Nat := 118140960795 + 4336771 * 2 ^ 59
def prefixEnd_4336771 : Nat := 4983230072969 + 3 ^ 40 * 4336771 * 2
def baseEnd_4336771 : Nat := 742282670493252365739353

theorem tailTrace_4336771 : CollatzResearch.WordTrace tailWord_4336771 prefixEnd_4336771 742282670493252365739353 := by
  unfold tailWord_4336771
  simp only [CollatzResearch.WordTrace]
  refine ⟨158175032971626803364834167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105450021981084535576556111 158175032971626803364834167)
  ·
    refine ⟨237262549457440205047251251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158175032971626803364834167 237262549457440205047251251)
    ·
      refine ⟨355893824186160307570876877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237262549457440205047251251 355893824186160307570876877)
      ·
        refine ⟨133460184069810115339078829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 355893824186160307570876877 133460184069810115339078829)
        ·
          refine ⟨50047569026178793252154561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133460184069810115339078829 50047569026178793252154561)
          ·
            refine ⟨37535676769634094939115921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50047569026178793252154561 37535676769634094939115921)
            ·
              refine ⟨28151757577225571204336941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37535676769634094939115921 28151757577225571204336941)
              ·
                refine ⟨10556909091459589201626353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28151757577225571204336941 10556909091459589201626353)
                ·
                  refine ⟨7917681818594691901219765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10556909091459589201626353 7917681818594691901219765)
                  ·
                    refine ⟨742282670493252365739353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917681818594691901219765 742282670493252365739353)
                    ·
                      rfl

theorem cell23_4336771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].length) (baseStart_4336771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336771 prefixEnd_4336771 := by exact prefixLift 4336771
  have htrace : WordTrace (prefixWord ++ tailWord_4336771) baseStart_4336771 baseEnd_4336771 := by
    simpa [prefixWord, tailWord_4336771, baseEnd_4336771] using wordTrace_append hprefix tailTrace_4336771
  have hstable : (prefixWord ++ tailWord_4336771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336771).length < 2 ^ (prefixWord ++ tailWord_4336771).sum := by decide
  have hdescent : baseEnd_4336771 < baseStart_4336771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336798 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4336798 : Nat := 118140960795 + 4336798 * 2 ^ 59
def prefixEnd_4336798 : Nat := 4983230072969 + 3 ^ 40 * 4336798 * 2
def baseEnd_4336798 : Nat := 2226861875457428491580435

theorem tailTrace_4336798 : CollatzResearch.WordTrace tailWord_4336798 prefixEnd_4336798 2226861875457428491580435 := by
  unfold tailWord_4336798
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772002217816123372008381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105450678495019324650711365 19772002217816123372008381)
  ·
    refine ⟨7414500831681046264503143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19772002217816123372008381 7414500831681046264503143)
    ·
      refine ⟨11121751247521569396754715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414500831681046264503143 11121751247521569396754715)
      ·
        refine ⟨16682626871282354095132073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11121751247521569396754715 16682626871282354095132073)
        ·
          refine ⟨12511970153461765571349055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16682626871282354095132073 12511970153461765571349055)
          ·
            refine ⟨18767955230192648357023583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511970153461765571349055 18767955230192648357023583)
            ·
              refine ⟨28151932845288972535535375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18767955230192648357023583 28151932845288972535535375)
              ·
                refine ⟨42227899267933458803303063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28151932845288972535535375 42227899267933458803303063)
                ·
                  refine ⟨63341848901900188204954595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42227899267933458803303063 63341848901900188204954595)
                  ·
                    refine ⟨95012773352850282307431893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63341848901900188204954595 95012773352850282307431893)
                    ·
                      refine ⟨2226861875457428491580435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95012773352850282307431893 2226861875457428491580435)
                      ·
                        rfl

theorem cell23_4336798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4336798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336798 prefixEnd_4336798 := by exact prefixLift 4336798
  have htrace : WordTrace (prefixWord ++ tailWord_4336798) baseStart_4336798 baseEnd_4336798 := by
    simpa [prefixWord, tailWord_4336798, baseEnd_4336798] using wordTrace_append hprefix tailTrace_4336798
  have hstable : (prefixWord ++ tailWord_4336798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336798).length < 2 ^ (prefixWord ++ tailWord_4336798).sum := by decide
  have hdescent : baseEnd_4336798 < baseStart_4336798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336841 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_4336841 : Nat := 118140960795 + 4336841 * 2 ^ 59
def prefixEnd_4336841 : Nat := 4983230072969 + 3 ^ 40 * 4336841 * 2
def baseEnd_4336841 : Nat := 2226883955125571823342737

theorem tailTrace_4336841 : CollatzResearch.WordTrace tailWord_4336841 prefixEnd_4336841 2226883955125571823342737 := by
  unfold tailWord_4336841
  simp only [CollatzResearch.WordTrace]
  refine ⟨158177586081373205319882377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105451724054248803546588251 158177586081373205319882377)
  ·
    refine ⟨118633189561029903989911783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158177586081373205319882377 118633189561029903989911783)
    ·
      refine ⟨177949784341544855984867675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118633189561029903989911783 177949784341544855984867675)
      ·
        refine ⟨266924676512317283977301513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177949784341544855984867675 266924676512317283977301513)
        ·
          refine ⟨200193507384237962982976135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266924676512317283977301513 200193507384237962982976135)
          ·
            refine ⟨300290261076356944474464203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200193507384237962982976135 300290261076356944474464203)
            ·
              refine ⟨450435391614535416711696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300290261076356944474464203 450435391614535416711696305)
              ·
                refine ⟨337826543710901562533772229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450435391614535416711696305 337826543710901562533772229)
                ·
                  refine ⟨63342476945794042975082293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337826543710901562533772229 63342476945794042975082293)
                  ·
                    refine ⟨5938357213668191528913965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63342476945794042975082293 5938357213668191528913965)
                    ·
                      refine ⟨2226883955125571823342737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938357213668191528913965 2226883955125571823342737)
                      ·
                        rfl

theorem cell23_4336841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_4336841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336841 prefixEnd_4336841 := by exact prefixLift 4336841
  have htrace : WordTrace (prefixWord ++ tailWord_4336841) baseStart_4336841 baseEnd_4336841 := by
    simpa [prefixWord, tailWord_4336841, baseEnd_4336841] using wordTrace_append hprefix tailTrace_4336841
  have hstable : (prefixWord ++ tailWord_4336841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336841).length < 2 ^ (prefixWord ++ tailWord_4336841).sum := by decide
  have hdescent : baseEnd_4336841 < baseStart_4336841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336875 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 3]
def baseStart_4336875 : Nat := 118140960795 + 4336875 * 2 ^ 59
def prefixEnd_4336875 : Nat := 4983230072969 + 3 ^ 40 * 4336875 * 2
def baseEnd_4336875 : Nat := 2226901413467824690317581

theorem tailTrace_4336875 : CollatzResearch.WordTrace tailWord_4336875 prefixEnd_4336875 2226901413467824690317581 := by
  unfold tailWord_4336875
  simp only [CollatzResearch.WordTrace]
  refine ⟨158178826163250029126620079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105452550775500019417746719 158178826163250029126620079)
  ·
    refine ⟨237268239244875043689930119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158178826163250029126620079 237268239244875043689930119)
    ·
      refine ⟨355902358867312565534895179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237268239244875043689930119 355902358867312565534895179)
      ·
        refine ⟨533853538300968848302342769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355902358867312565534895179 533853538300968848302342769)
        ·
          refine ⟨400390153725726636226757077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533853538300968848302342769 400390153725726636226757077)
          ·
            refine ⟨9384144227946718036564619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 400390153725726636226757077 9384144227946718036564619)
            ·
              refine ⟨14076216341920077054846929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384144227946718036564619 14076216341920077054846929)
              ·
                refine ⟨10557162256440057791135197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14076216341920077054846929 10557162256440057791135197)
                ·
                  refine ⟨3958935846165021671675699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10557162256440057791135197 3958935846165021671675699)
                  ·
                    refine ⟨5938403769247532507513549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3958935846165021671675699 5938403769247532507513549)
                    ·
                      refine ⟨2226901413467824690317581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938403769247532507513549 2226901413467824690317581)
                      ·
                        rfl

theorem cell23_4336875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 3].length) (baseStart_4336875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336875 prefixEnd_4336875 := by exact prefixLift 4336875
  have htrace : WordTrace (prefixWord ++ tailWord_4336875) baseStart_4336875 baseEnd_4336875 := by
    simpa [prefixWord, tailWord_4336875, baseEnd_4336875] using wordTrace_append hprefix tailTrace_4336875
  have hstable : (prefixWord ++ tailWord_4336875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336875).length < 2 ^ (prefixWord ++ tailWord_4336875).sum := by decide
  have hdescent : baseEnd_4336875 < baseStart_4336875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336878 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4336878 : Nat := 118140960795 + 4336878 * 2 ^ 59
def prefixEnd_4336878 : Nat := 4983230072969 + 3 ^ 40 * 4336878 * 2
def baseEnd_4336878 : Nat := 742300984636596059526689

theorem tailTrace_4336878 : CollatzResearch.WordTrace tailWord_4336878 prefixEnd_4336878 742300984636596059526689 := by
  unfold tailWord_4336878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19772366947779895079872411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105452623721492773759319525 19772366947779895079872411)
  ·
    refine ⟨29658550421669842619808617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19772366947779895079872411 29658550421669842619808617)
    ·
      refine ⟨22243912816252381964856463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29658550421669842619808617 22243912816252381964856463)
      ·
        refine ⟨33365869224378572947284695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22243912816252381964856463 33365869224378572947284695)
        ·
          refine ⟨50048803836567859420927043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33365869224378572947284695 50048803836567859420927043)
          ·
            refine ⟨75073205754851789131390565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50048803836567859420927043 75073205754851789131390565)
            ·
              refine ⟨14076226079034710462135731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75073205754851789131390565 14076226079034710462135731)
              ·
                refine ⟨21114339118552065693203597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14076226079034710462135731 21114339118552065693203597)
                ·
                  refine ⟨7917877169457024634951349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21114339118552065693203597 7917877169457024634951349)
                  ·
                    refine ⟨742300984636596059526689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917877169457024634951349 742300984636596059526689)
                    ·
                      rfl

theorem cell23_4336878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4336878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336878 prefixEnd_4336878 := by exact prefixLift 4336878
  have htrace : WordTrace (prefixWord ++ tailWord_4336878) baseStart_4336878 baseEnd_4336878 := by
    simpa [prefixWord, tailWord_4336878, baseEnd_4336878] using wordTrace_append hprefix tailTrace_4336878
  have hstable : (prefixWord ++ tailWord_4336878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336878).length < 2 ^ (prefixWord ++ tailWord_4336878).sum := by decide
  have hdescent : baseEnd_4336878 < baseStart_4336878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336895 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 1, 5]
def baseStart_4336895 : Nat := 118140960795 + 4336895 * 2 ^ 59
def prefixEnd_4336895 : Nat := 4983230072969 + 3 ^ 40 * 4336895 * 2
def baseEnd_4336895 : Nat := 742303894360304870689163

theorem tailTrace_4336895 : CollatzResearch.WordTrace tailWord_4336895 prefixEnd_4336895 742303894360304870689163 := by
  unfold tailWord_4336895
  simp only [CollatzResearch.WordTrace]
  refine ⟨158179555623177572542348139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105453037082118381694898759 158179555623177572542348139)
  ·
    refine ⟨237269333434766358813522209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158179555623177572542348139 237269333434766358813522209)
    ·
      refine ⟨177952000076074769110141657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237269333434766358813522209 177952000076074769110141657)
      ·
        refine ⟨133464000057056076832606243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177952000076074769110141657 133464000057056076832606243)
        ·
          refine ⟨200196000085584115248909365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133464000057056076832606243 200196000085584115248909365)
          ·
            refine ⟨18768375008023510804585253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200196000085584115248909365 18768375008023510804585253)
            ·
              refine ⟨3519070314004408275859735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18768375008023510804585253 3519070314004408275859735)
              ·
                refine ⟨5278605471006612413789603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519070314004408275859735 5278605471006612413789603)
                ·
                  refine ⟨7917908206509918620684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278605471006612413789603 7917908206509918620684405)
                  ·
                    refine ⟨742303894360304870689163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917908206509918620684405 742303894360304870689163)
                    ·
                      rfl

theorem cell23_4336895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_4336895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336895 prefixEnd_4336895 := by exact prefixLift 4336895
  have htrace : WordTrace (prefixWord ++ tailWord_4336895) baseStart_4336895 baseEnd_4336895 := by
    simpa [prefixWord, tailWord_4336895, baseEnd_4336895] using wordTrace_append hprefix tailTrace_4336895
  have hstable : (prefixWord ++ tailWord_4336895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336895).length < 2 ^ (prefixWord ++ tailWord_4336895).sum := by decide
  have hdescent : baseEnd_4336895 < baseStart_4336895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336911 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_4336911 : Nat := 118140960795 + 4336911 * 2 ^ 59
def prefixEnd_4336911 : Nat := 4983230072969 + 3 ^ 40 * 4336911 * 2
def baseEnd_4336911 : Nat := 2226919898771386549467415

theorem tailTrace_4336911 : CollatzResearch.WordTrace tailWord_4336911 prefixEnd_4336911 2226919898771386549467415 := by
  unfold tailWord_4336911
  simp only [CollatzResearch.WordTrace]
  refine ⟨158180139191119607274930587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105453426127413071516620391 158180139191119607274930587)
  ·
    refine ⟨237270208786679410912395881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158180139191119607274930587 237270208786679410912395881)
    ·
      refine ⟨177952656590009558184296911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237270208786679410912395881 177952656590009558184296911)
      ·
        refine ⟨266928984885014337276445367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177952656590009558184296911 266928984885014337276445367)
        ·
          refine ⟨400393477327521505914668051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266928984885014337276445367 400393477327521505914668051)
          ·
            refine ⟨600590215991282258872002077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400393477327521505914668051 600590215991282258872002077)
            ·
              refine ⟨225221330996730847077000779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600590215991282258872002077 225221330996730847077000779)
              ·
                refine ⟨337831996495096270615501169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225221330996730847077000779 337831996495096270615501169)
                ·
                  refine ⟨253373997371322202961625877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337831996495096270615501169 253373997371322202961625877)
                  ·
                    refine ⟨11876906126780728263826213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 253373997371322202961625877 11876906126780728263826213)
                    ·
                      refine ⟨2226919898771386549467415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11876906126780728263826213 2226919898771386549467415)
                      ·
                        rfl

theorem cell23_4336911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_4336911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336911 prefixEnd_4336911 := by exact prefixLift 4336911
  have htrace : WordTrace (prefixWord ++ tailWord_4336911) baseStart_4336911 baseEnd_4336911 := by
    simpa [prefixWord, tailWord_4336911, baseEnd_4336911] using wordTrace_append hprefix tailTrace_4336911
  have hstable : (prefixWord ++ tailWord_4336911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336911).length < 2 ^ (prefixWord ++ tailWord_4336911).sum := by decide
  have hdescent : baseEnd_4336911 < baseStart_4336911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336925 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_4336925 : Nat := 118140960795 + 4336925 * 2 ^ 59
def prefixEnd_4336925 : Nat := 4983230072969 + 3 ^ 40 * 4336925 * 2
def baseEnd_4336925 : Nat := 742309029166849831564117

theorem tailTrace_4336925 : CollatzResearch.WordTrace tailWord_4336925 prefixEnd_4336925 742309029166849831564117 := by
  unfold tailWord_4336925
  simp only [CollatzResearch.WordTrace]
  refine ⟨158180649813068887665940229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105453766542045925110626819 158180649813068887665940229)
  ·
    refine ⟨29658871839950416437363793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158180649813068887665940229 29658871839950416437363793)
    ·
      refine ⟨22244153879962812328022845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29658871839950416437363793 22244153879962812328022845)
      ·
        refine ⟨8341557704986054623008567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22244153879962812328022845 8341557704986054623008567)
        ·
          refine ⟨12512336557479081934512851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341557704986054623008567 12512336557479081934512851)
          ·
            refine ⟨18768504836218622901769277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12512336557479081934512851 18768504836218622901769277)
            ·
              refine ⟨7038189313581983588163479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18768504836218622901769277 7038189313581983588163479)
              ·
                refine ⟨10557283970372975382245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038189313581983588163479 10557283970372975382245219)
                ·
                  refine ⟨15835925955559463073367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10557283970372975382245219 15835925955559463073367829)
                  ·
                    refine ⟨742309029166849831564117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15835925955559463073367829 742309029166849831564117)
                    ·
                      rfl

theorem cell23_4336925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_4336925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336925 prefixEnd_4336925 := by exact prefixLift 4336925
  have htrace : WordTrace (prefixWord ++ tailWord_4336925) baseStart_4336925 baseEnd_4336925 := by
    simpa [prefixWord, tailWord_4336925, baseEnd_4336925] using wordTrace_append hprefix tailTrace_4336925
  have hstable : (prefixWord ++ tailWord_4336925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336925).length < 2 ^ (prefixWord ++ tailWord_4336925).sum := by decide
  have hdescent : baseEnd_4336925 < baseStart_4336925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336932 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_4336932 : Nat := 118140960795 + 4336932 * 2 ^ 59
def prefixEnd_4336932 : Nat := 4983230072969 + 3 ^ 40 * 4336932 * 2
def baseEnd_4336932 : Nat := 2226930681865130967304819

theorem tailTrace_4336932 : CollatzResearch.WordTrace tailWord_4336932 prefixEnd_4336932 2226930681865130967304819 := by
  unfold tailWord_4336932
  simp only [CollatzResearch.WordTrace]
  refine ⟨79090452562021763930722525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105453936749362351907630033 79090452562021763930722525)
  ·
    refine ⟨29658919710758161474020947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79090452562021763930722525 29658919710758161474020947)
    ·
      refine ⟨44488379566137242211031421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29658919710758161474020947 44488379566137242211031421)
      ·
        refine ⟨16683142337301465829136783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44488379566137242211031421 16683142337301465829136783)
        ·
          refine ⟨25024713505952198743705175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16683142337301465829136783 25024713505952198743705175)
          ·
            refine ⟨37537070258928298115557763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25024713505952198743705175 37537070258928298115557763)
            ·
              refine ⟨56305605388392447173336645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37537070258928298115557763 56305605388392447173336645)
              ·
                refine ⟨10557301010323583845000621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56305605388392447173336645 10557301010323583845000621)
                ·
                  refine ⟨3958987878871343941875233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10557301010323583845000621 3958987878871343941875233)
                  ·
                    refine ⟨2969240909153507956406425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958987878871343941875233 2969240909153507956406425)
                    ·
                      refine ⟨2226930681865130967304819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969240909153507956406425 2226930681865130967304819)
                      ·
                        rfl

theorem cell23_4336932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_4336932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336932 prefixEnd_4336932 := by exact prefixLift 4336932
  have htrace : WordTrace (prefixWord ++ tailWord_4336932) baseStart_4336932 baseEnd_4336932 := by
    simpa [prefixWord, tailWord_4336932, baseEnd_4336932] using wordTrace_append hprefix tailTrace_4336932
  have hstable : (prefixWord ++ tailWord_4336932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336932).length < 2 ^ (prefixWord ++ tailWord_4336932).sum := by decide
  have hdescent : baseEnd_4336932 < baseStart_4336932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336951 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 9]
def baseStart_4336951 : Nat := 118140960795 + 4336951 * 2 ^ 59
def prefixEnd_4336951 : Nat := 4983230072969 + 3 ^ 40 * 4336951 * 2
def baseEnd_4336951 : Nat := 742313479332522130989077

theorem tailTrace_4336951 : CollatzResearch.WordTrace tailWord_4336951 prefixEnd_4336951 742313479332522130989077 := by
  unfold tailWord_4336951
  simp only [CollatzResearch.WordTrace]
  refine ⟨158181598110974694106386707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105454398740649796070924471 158181598110974694106386707)
  ·
    refine ⟨237272397166462041159580061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158181598110974694106386707 237272397166462041159580061)
    ·
      refine ⟨88977148937423265434842523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237272397166462041159580061 88977148937423265434842523)
      ·
        refine ⟨133465723406134898152263785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88977148937423265434842523 133465723406134898152263785)
        ·
          refine ⟨100099292554601173614197839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133465723406134898152263785 100099292554601173614197839)
          ·
            refine ⟨150148938831901760421296759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100099292554601173614197839 150148938831901760421296759)
            ·
              refine ⟨225223408247852640631945139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150148938831901760421296759 225223408247852640631945139)
              ·
                refine ⟨337835112371778960947917709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225223408247852640631945139 337835112371778960947917709)
                ·
                  refine ⟨126688167139417110355469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337835112371778960947917709 126688167139417110355469141)
                  ·
                    refine ⟨742313479332522130989077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126688167139417110355469141 742313479332522130989077)
                    ·
                      rfl

theorem cell23_4336951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_4336951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336951 prefixEnd_4336951 := by exact prefixLift 4336951
  have htrace : WordTrace (prefixWord ++ tailWord_4336951) baseStart_4336951 baseEnd_4336951 := by
    simpa [prefixWord, tailWord_4336951, baseEnd_4336951] using wordTrace_append hprefix tailTrace_4336951
  have hstable : (prefixWord ++ tailWord_4336951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336951).length < 2 ^ (prefixWord ++ tailWord_4336951).sum := by decide
  have hdescent : baseEnd_4336951 < baseStart_4336951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_4336971 : Nat := 118140960795 + 4336971 * 2 ^ 59
def prefixEnd_4336971 : Nat := 4983230072969 + 3 ^ 40 * 4336971 * 2
def baseEnd_4336971 : Nat := 2226950707610656314717139

theorem tailTrace_4336971 : CollatzResearch.WordTrace tailWord_4336971 prefixEnd_4336971 2226950707610656314717139 := by
  unfold tailWord_4336971
  simp only [CollatzResearch.WordTrace]
  refine ⟨158182327570902237522114767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105454885047268158348076511 158182327570902237522114767)
  ·
    refine ⟨237273491356353356283172151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158182327570902237522114767 237273491356353356283172151)
    ·
      refine ⟨355910237034530034424758227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237273491356353356283172151 355910237034530034424758227)
      ·
        refine ⟨533865355551795051637137341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355910237034530034424758227 533865355551795051637137341)
        ·
          refine ⟨200199508331923144363926503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533865355551795051637137341 200199508331923144363926503)
          ·
            refine ⟨300299262497884716545889755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200199508331923144363926503 300299262497884716545889755)
            ·
              refine ⟨450448893746827074818834633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300299262497884716545889755 450448893746827074818834633)
              ·
                refine ⟨337836670310120306114125975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450448893746827074818834633 337836670310120306114125975)
                ·
                  refine ⟨506755005465180459171188963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337836670310120306114125975 506755005465180459171188963)
                  ·
                    refine ⟨760132508197770688756783445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 506755005465180459171188963 760132508197770688756783445)
                    ·
                      refine ⟨2226950707610656314717139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 760132508197770688756783445 2226950707610656314717139)
                      ·
                        rfl

theorem cell23_4336971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_4336971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336971 prefixEnd_4336971 := by exact prefixLift 4336971
  have htrace : WordTrace (prefixWord ++ tailWord_4336971) baseStart_4336971 baseEnd_4336971 := by
    simpa [prefixWord, tailWord_4336971, baseEnd_4336971] using wordTrace_append hprefix tailTrace_4336971
  have hstable : (prefixWord ++ tailWord_4336971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336971).length < 2 ^ (prefixWord ++ tailWord_4336971).sum := by decide
  have hdescent : baseEnd_4336971 < baseStart_4336971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4336992 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2]
def baseStart_4336992 : Nat := 118140960795 + 4336992 * 2 ^ 59
def prefixEnd_4336992 : Nat := 4983230072969 + 3 ^ 40 * 4336992 * 2
def baseEnd_4336992 : Nat := 2226961490704400732554543

theorem tailTrace_4336992 : CollatzResearch.WordTrace tailWord_4336992 prefixEnd_4336992 2226961490704400732554543 := by
  unfold tailWord_4336992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79091546751913079054314615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105455395669217438739086153 79091546751913079054314615)
  ·
    refine ⟨118637320127869618581471923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79091546751913079054314615 118637320127869618581471923)
    ·
      refine ⟨177955980191804427872207885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118637320127869618581471923 177955980191804427872207885)
      ·
        refine ⟨66733492571926660452077957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177955980191804427872207885 66733492571926660452077957)
        ·
          refine ⟨12512529857236248834764617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66733492571926660452077957 12512529857236248834764617)
          ·
            refine ⟨9384397392927186626073463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12512529857236248834764617 9384397392927186626073463)
            ·
              refine ⟨14076596089390779939110195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384397392927186626073463 14076596089390779939110195)
              ·
                refine ⟨21114894134086169908665293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14076596089390779939110195 21114894134086169908665293)
                ·
                  refine ⟨7918085300282313715749485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21114894134086169908665293 7918085300282313715749485)
                  ·
                    refine ⟨2969281987605867643406057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7918085300282313715749485 2969281987605867643406057)
                    ·
                      refine ⟨2226961490704400732554543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969281987605867643406057 2226961490704400732554543)
                      ·
                        rfl

theorem cell23_4336992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_4336992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4336992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4336992 prefixEnd_4336992 := by exact prefixLift 4336992
  have htrace : WordTrace (prefixWord ++ tailWord_4336992) baseStart_4336992 baseEnd_4336992 := by
    simpa [prefixWord, tailWord_4336992, baseEnd_4336992] using wordTrace_append hprefix tailTrace_4336992
  have hstable : (prefixWord ++ tailWord_4336992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4336992).length < 2 ^ (prefixWord ++ tailWord_4336992).sum := by decide
  have hdescent : baseEnd_4336992 < baseStart_4336992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4336992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337008 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_4337008 : Nat := 118140960795 + 4337008 * 2 ^ 59
def prefixEnd_4337008 : Nat := 4983230072969 + 3 ^ 40 * 4337008 * 2
def baseEnd_4337008 : Nat := 2226969706394872669954469

theorem tailTrace_4337008 : CollatzResearch.WordTrace tailWord_4337008 prefixEnd_4337008 2226969706394872669954469 := by
  unfold tailWord_4337008
  simp only [CollatzResearch.WordTrace]
  refine ⟨79091838535884096420605839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105455784714512128560807785 79091838535884096420605839)
  ·
    refine ⟨118637757803826144630908759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79091838535884096420605839 118637757803826144630908759)
    ·
      refine ⟨177956636705739216946363139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118637757803826144630908759 177956636705739216946363139)
      ·
        refine ⟨266934955058608825419544709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177956636705739216946363139 266934955058608825419544709)
        ·
          refine ⟨50050304073489154766164633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266934955058608825419544709 50050304073489154766164633)
          ·
            refine ⟨37537728055116866074623475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50050304073489154766164633 37537728055116866074623475)
            ·
              refine ⟨56306592082675299111935213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37537728055116866074623475 56306592082675299111935213)
              ·
                refine ⟨21114972031003237166975705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56306592082675299111935213 21114972031003237166975705)
                ·
                  refine ⟨15836229023252427875231779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21114972031003237166975705 15836229023252427875231779)
                  ·
                    refine ⟨23754343534878641812847669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15836229023252427875231779 23754343534878641812847669)
                    ·
                      refine ⟨2226969706394872669954469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23754343534878641812847669 2226969706394872669954469)
                      ·
                        rfl

theorem cell23_4337008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_4337008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337008 prefixEnd_4337008 := by exact prefixLift 4337008
  have htrace : WordTrace (prefixWord ++ tailWord_4337008) baseStart_4337008 baseEnd_4337008 := by
    simpa [prefixWord, tailWord_4337008, baseEnd_4337008] using wordTrace_append hprefix tailTrace_4337008
  have hstable : (prefixWord ++ tailWord_4337008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337008).length < 2 ^ (prefixWord ++ tailWord_4337008).sum := by decide
  have hdescent : baseEnd_4337008 < baseStart_4337008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337018 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_4337018 : Nat := 118140960795 + 4337018 * 2 ^ 59
def prefixEnd_4337018 : Nat := 4983230072969 + 3 ^ 40 * 4337018 * 2
def baseEnd_4337018 : Nat := 2226974841201417630829423

theorem tailTrace_4337018 : CollatzResearch.WordTrace tailWord_4337018 prefixEnd_4337018 2226974841201417630829423 := by
  unfold tailWord_4337018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39546010450432991137268927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105456027867821309699383805 39546010450432991137268927)
  ·
    refine ⟨59319015675649486705903391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39546010450432991137268927 59319015675649486705903391)
    ·
      refine ⟨88978523513474230058855087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59319015675649486705903391 88978523513474230058855087)
      ·
        refine ⟨133467785270211345088282631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88978523513474230058855087 133467785270211345088282631)
        ·
          refine ⟨200201677905317017632423947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133467785270211345088282631 200201677905317017632423947)
          ·
            refine ⟨300302516857975526448635921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200201677905317017632423947 300302516857975526448635921)
            ·
              refine ⟨225226887643481644836476941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300302516857975526448635921 225226887643481644836476941)
              ·
                refine ⟨84460082866305616813678853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225226887643481644836476941 84460082866305616813678853)
                ·
                  refine ⟨15836265537432303152564785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84460082866305616813678853 15836265537432303152564785)
                  ·
                    refine ⟨11877199153074227364423589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15836265537432303152564785 11877199153074227364423589)
                    ·
                      refine ⟨2226974841201417630829423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11877199153074227364423589 2226974841201417630829423)
                      ·
                        rfl

theorem cell23_4337018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_4337018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337018 prefixEnd_4337018 := by exact prefixLift 4337018
  have htrace : WordTrace (prefixWord ++ tailWord_4337018) baseStart_4337018 baseEnd_4337018 := by
    simpa [prefixWord, tailWord_4337018, baseEnd_4337018] using wordTrace_append hprefix tailTrace_4337018
  have hstable : (prefixWord ++ tailWord_4337018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337018).length < 2 ^ (prefixWord ++ tailWord_4337018).sum := by decide
  have hdescent : baseEnd_4337018 < baseStart_4337018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337068 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_4337068 : Nat := 118140960795 + 4337068 * 2 ^ 59
def prefixEnd_4337068 : Nat := 4983230072969 + 3 ^ 40 * 4337068 * 2
def baseEnd_4337068 : Nat := 2227000515234142435204193

theorem tailTrace_4337068 : CollatzResearch.WordTrace tailWord_4337068 prefixEnd_4337068 2227000515234142435204193 := by
  unfold tailWord_4337068
  simp only [CollatzResearch.WordTrace]
  refine ⟨79092932725775411544197929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105457243634367215392263905 79092932725775411544197929)
  ·
    refine ⟨59319699544331558658148447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79092932725775411544197929 59319699544331558658148447)
    ·
      refine ⟨88979549316497337987222671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59319699544331558658148447 88979549316497337987222671)
      ·
        refine ⟨133469323974746006980834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88979549316497337987222671 133469323974746006980834007)
        ·
          refine ⟨200203985962119010471251011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133469323974746006980834007 200203985962119010471251011)
          ·
            refine ⟨300305978943178515706876517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200203985962119010471251011 300305978943178515706876517)
            ·
              refine ⟨56307371051845971695039347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300305978943178515706876517 56307371051845971695039347)
              ·
                refine ⟨84461056577768957542559021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56307371051845971695039347 84461056577768957542559021)
                ·
                  refine ⟨31672896216663359078459633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84461056577768957542559021 31672896216663359078459633)
                  ·
                    refine ⟨23754672162497519308844725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31672896216663359078459633 23754672162497519308844725)
                    ·
                      refine ⟨2227000515234142435204193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23754672162497519308844725 2227000515234142435204193)
                      ·
                        rfl

theorem cell23_4337068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_4337068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337068 prefixEnd_4337068 := by exact prefixLift 4337068
  have htrace : WordTrace (prefixWord ++ tailWord_4337068) baseStart_4337068 baseEnd_4337068 := by
    simpa [prefixWord, tailWord_4337068, baseEnd_4337068] using wordTrace_append hprefix tailTrace_4337068
  have hstable : (prefixWord ++ tailWord_4337068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337068).length < 2 ^ (prefixWord ++ tailWord_4337068).sum := by decide
  have hdescent : baseEnd_4337068 < baseStart_4337068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337202 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_4337202 : Nat := 118140960795 + 4337202 * 2 ^ 59
def prefixEnd_4337202 : Nat := 4983230072969 + 3 ^ 40 * 4337202 * 2
def baseEnd_4337202 : Nat := 2227069321641844910928577

theorem tailTrace_4337202 : CollatzResearch.WordTrace tailWord_4337202 prefixEnd_4337202 2227069321641844910928577 := by
  unfold tailWord_4337202
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547688208266340993443465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105460501888710242649182573 39547688208266340993443465)
  ·
    refine ⟨29660766156199755745082599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39547688208266340993443465 29660766156199755745082599)
    ·
      refine ⟨44491149234299633617623899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29660766156199755745082599 44491149234299633617623899)
      ·
        refine ⟨66736723851449450426435849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44491149234299633617623899 66736723851449450426435849)
        ·
          refine ⟨50052542888587087819826887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66736723851449450426435849 50052542888587087819826887)
          ·
            refine ⟨75078814332880631729740331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50052542888587087819826887 75078814332880631729740331)
            ·
              refine ⟨112618221499320947594610497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75078814332880631729740331 112618221499320947594610497)
              ·
                refine ⟨84463666124490710695957873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112618221499320947594610497 84463666124490710695957873)
                ·
                  refine ⟨63347749593368033021968405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84463666124490710695957873 63347749593368033021968405)
                  ·
                    refine ⟨2969425762189126547904769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63347749593368033021968405 2969425762189126547904769)
                    ·
                      refine ⟨2227069321641844910928577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969425762189126547904769 2227069321641844910928577)
                      ·
                        rfl

theorem cell23_4337202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_4337202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337202 prefixEnd_4337202 := by exact prefixLift 4337202
  have htrace : WordTrace (prefixWord ++ tailWord_4337202) baseStart_4337202 baseEnd_4337202 := by
    simpa [prefixWord, tailWord_4337202, baseEnd_4337202] using wordTrace_append hprefix tailTrace_4337202
  have hstable : (prefixWord ++ tailWord_4337202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337202).length < 2 ^ (prefixWord ++ tailWord_4337202).sum := by decide
  have hdescent : baseEnd_4337202 < baseStart_4337202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337223 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_4337223 : Nat := 118140960795 + 4337223 * 2 ^ 59
def prefixEnd_4337223 : Nat := 4983230072969 + 3 ^ 40 * 4337223 * 2
def baseEnd_4337223 : Nat := 2227080104735589328765981

theorem tailTrace_4337223 : CollatzResearch.WordTrace tailWord_4337223 prefixEnd_4337223 2227080104735589328765981 := by
  unfold tailWord_4337223
  simp only [CollatzResearch.WordTrace]
  refine ⟨158191518765989284560288323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105461012510659523040192215 158191518765989284560288323)
  ·
    refine ⟨237287278148983926840432485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158191518765989284560288323 237287278148983926840432485)
    ·
      refine ⟨44491364652934486282581091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237287278148983926840432485 44491364652934486282581091)
      ·
        refine ⟨66737046979401729423871637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44491364652934486282581091 66737046979401729423871637)
        ·
          refine ⟨3128299077159456066743983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66737046979401729423871637 3128299077159456066743983)
          ·
            refine ⟨4692448615739184100115975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128299077159456066743983 4692448615739184100115975)
            ·
              refine ⟨7038672923608776150173963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692448615739184100115975 7038672923608776150173963)
              ·
                refine ⟨10558009385413164225260945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038672923608776150173963 10558009385413164225260945)
                ·
                  refine ⟨7918507039059873168945709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10558009385413164225260945 7918507039059873168945709)
                  ·
                    refine ⟨2969440139647452438354641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7918507039059873168945709 2969440139647452438354641)
                    ·
                      refine ⟨2227080104735589328765981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969440139647452438354641 2227080104735589328765981)
                      ·
                        rfl

theorem cell23_4337223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_4337223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337223 prefixEnd_4337223 := by exact prefixLift 4337223
  have htrace : WordTrace (prefixWord ++ tailWord_4337223) baseStart_4337223 baseEnd_4337223 := by
    simpa [prefixWord, tailWord_4337223, baseEnd_4337223] using wordTrace_append hprefix tailTrace_4337223
  have hstable : (prefixWord ++ tailWord_4337223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337223).length < 2 ^ (prefixWord ++ tailWord_4337223).sum := by decide
  have hdescent : baseEnd_4337223 < baseStart_4337223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337239 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_4337239 : Nat := 118140960795 + 4337239 * 2 ^ 59
def prefixEnd_4337239 : Nat := 4983230072969 + 3 ^ 40 * 4337239 * 2
def baseEnd_4337239 : Nat := 2227088320426061266165907

theorem tailTrace_4337239 : CollatzResearch.WordTrace tailWord_4337239 prefixEnd_4337239 2227088320426061266165907 := by
  unfold tailWord_4337239
  simp only [CollatzResearch.WordTrace]
  refine ⟨158192102333931319292870771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105461401555954212861913847 158192102333931319292870771)
  ·
    refine ⟨237288153500896978939306157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158192102333931319292870771 237288153500896978939306157)
    ·
      refine ⟨88983057562836367102239809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237288153500896978939306157 88983057562836367102239809)
      ·
        refine ⟨66737293172127275326679857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88983057562836367102239809 66737293172127275326679857)
        ·
          refine ⟨50052969879095456495009893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66737293172127275326679857 50052969879095456495009893)
          ·
            refine ⟨9384931852330398092814355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50052969879095456495009893 9384931852330398092814355)
            ·
              refine ⟨14077397778495597139221533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384931852330398092814355 14077397778495597139221533)
              ·
                refine ⟨5279024166935848927208075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14077397778495597139221533 5279024166935848927208075)
                ·
                  refine ⟨7918536250403773390812113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5279024166935848927208075 7918536250403773390812113)
                  ·
                    refine ⟨5938902187802830043109085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7918536250403773390812113 5938902187802830043109085)
                    ·
                      refine ⟨2227088320426061266165907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5938902187802830043109085 2227088320426061266165907)
                      ·
                        rfl

theorem cell23_4337239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_4337239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337239 prefixEnd_4337239 := by exact prefixLift 4337239
  have htrace : WordTrace (prefixWord ++ tailWord_4337239) baseStart_4337239 baseEnd_4337239 := by
    simpa [prefixWord, tailWord_4337239, baseEnd_4337239] using wordTrace_append hprefix tailTrace_4337239
  have hstable : (prefixWord ++ tailWord_4337239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337239).length < 2 ^ (prefixWord ++ tailWord_4337239).sum := by decide
  have hdescent : baseEnd_4337239 < baseStart_4337239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337253 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4337253 : Nat := 118140960795 + 4337253 * 2 ^ 59
def prefixEnd_4337253 : Nat := 4983230072969 + 3 ^ 40 * 4337253 * 2
def baseEnd_4337253 : Nat := 2227095509155224211390843

theorem tailTrace_4337253 : CollatzResearch.WordTrace tailWord_4337253 prefixEnd_4337253 2227095509155224211390843 := by
  unfold tailWord_4337253
  simp only [CollatzResearch.WordTrace]
  refine ⟨158192612955880599683880413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105461741970587066455920275 158192612955880599683880413)
  ·
    refine ⟨59322229858455224881455155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158192612955880599683880413 59322229858455224881455155)
    ·
      refine ⟨88983344787682837322182733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59322229858455224881455155 88983344787682837322182733)
      ·
        refine ⟨33368754295381063995818525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88983344787682837322182733 33368754295381063995818525)
        ·
          refine ⟨12513282860767898998431947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33368754295381063995818525 12513282860767898998431947)
          ·
            refine ⟨18769924291151848497647921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12513282860767898998431947 18769924291151848497647921)
            ·
              refine ⟨14077443218363886373235941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18769924291151848497647921 14077443218363886373235941)
              ·
                refine ⟨2639520603443228694981739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14077443218363886373235941 2639520603443228694981739)
                ·
                  refine ⟨3959280905164843042472609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639520603443228694981739 3959280905164843042472609)
                  ·
                    refine ⟨2969460678873632281854457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959280905164843042472609 2969460678873632281854457)
                    ·
                      refine ⟨2227095509155224211390843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969460678873632281854457 2227095509155224211390843)
                      ·
                        rfl

theorem cell23_4337253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4337253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337253 prefixEnd_4337253 := by exact prefixLift 4337253
  have htrace : WordTrace (prefixWord ++ tailWord_4337253) baseStart_4337253 baseEnd_4337253 := by
    simpa [prefixWord, tailWord_4337253, baseEnd_4337253] using wordTrace_append hprefix tailTrace_4337253
  have hstable : (prefixWord ++ tailWord_4337253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337253).length < 2 ^ (prefixWord ++ tailWord_4337253).sum := by decide
  have hdescent : baseEnd_4337253 < baseStart_4337253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337255 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4337255 : Nat := 118140960795 + 4337255 * 2 ^ 59
def prefixEnd_4337255 : Nat := 4983230072969 + 3 ^ 40 * 4337255 * 2
def baseEnd_4337255 : Nat := 742365512038844401188611

theorem tailTrace_4337255 : CollatzResearch.WordTrace tailWord_4337255 prefixEnd_4337255 742365512038844401188611 := by
  unfold tailWord_4337255
  simp only [CollatzResearch.WordTrace]
  refine ⟨158192685901873354025453219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105461790601248902683635479 158192685901873354025453219)
  ·
    refine ⟨237289028852810031038179829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158192685901873354025453219 237289028852810031038179829)
    ·
      refine ⟨22245846454950940409829359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237289028852810031038179829 22245846454950940409829359)
      ·
        refine ⟨33368769682426410614744039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22245846454950940409829359 33368769682426410614744039)
        ·
          refine ⟨50053154523639615922116059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33368769682426410614744039 50053154523639615922116059)
          ·
            refine ⟨75079731785459423883174089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50053154523639615922116059 75079731785459423883174089)
            ·
              refine ⟨56309798839094567912380567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75079731785459423883174089 56309798839094567912380567)
              ·
                refine ⟨84464698258641851868570851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56309798839094567912380567 84464698258641851868570851)
                ·
                  refine ⟨126697047387962777802856277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84464698258641851868570851 126697047387962777802856277)
                  ·
                    refine ⟨742365512038844401188611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126697047387962777802856277 742365512038844401188611)
                    ·
                      rfl

theorem cell23_4337255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4337255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337255 prefixEnd_4337255 := by exact prefixLift 4337255
  have htrace : WordTrace (prefixWord ++ tailWord_4337255) baseStart_4337255 baseEnd_4337255 := by
    simpa [prefixWord, tailWord_4337255, baseEnd_4337255] using wordTrace_append hprefix tailTrace_4337255
  have hstable : (prefixWord ++ tailWord_4337255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337255).length < 2 ^ (prefixWord ++ tailWord_4337255).sum := by decide
  have hdescent : baseEnd_4337255 < baseStart_4337255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337265 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_4337265 : Nat := 118140960795 + 4337265 * 2 ^ 59
def prefixEnd_4337265 : Nat := 4983230072969 + 3 ^ 40 * 4337265 * 2
def baseEnd_4337265 : Nat := 2227101670923078164440787

theorem tailTrace_4337265 : CollatzResearch.WordTrace tailWord_4337265 prefixEnd_4337265 2227101670923078164440787 := by
  unfold tailWord_4337265
  simp only [CollatzResearch.WordTrace]
  refine ⟨158193050631837125733317249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105462033754558083822211499 158193050631837125733317249)
  ·
    refine ⟨118644787973877844299987937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158193050631837125733317249 118644787973877844299987937)
    ·
      refine ⟨88983590980408383224990953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118644787973877844299987937 88983590980408383224990953)
      ·
        refine ⟨66737693235306287418743215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88983590980408383224990953 66737693235306287418743215)
        ·
          refine ⟨100106539852959431128114823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66737693235306287418743215 100106539852959431128114823)
          ·
            refine ⟨150159809779439146692172235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100106539852959431128114823 150159809779439146692172235)
            ·
              refine ⟨225239714669158720038258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150159809779439146692172235 225239714669158720038258353)
              ·
                refine ⟨168929786001869040028693765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225239714669158720038258353 168929786001869040028693765)
                ·
                  refine ⟨31674334875350445005380081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168929786001869040028693765 31674334875350445005380081)
                  ·
                    refine ⟨23755751156512833754035061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31674334875350445005380081 23755751156512833754035061)
                    ·
                      refine ⟨2227101670923078164440787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23755751156512833754035061 2227101670923078164440787)
                      ·
                        rfl

theorem cell23_4337265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_4337265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337265 prefixEnd_4337265 := by exact prefixLift 4337265
  have htrace : WordTrace (prefixWord ++ tailWord_4337265) baseStart_4337265 baseEnd_4337265 := by
    simpa [prefixWord, tailWord_4337265, baseEnd_4337265] using wordTrace_append hprefix tailTrace_4337265
  have hstable : (prefixWord ++ tailWord_4337265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337265).length < 2 ^ (prefixWord ++ tailWord_4337265).sum := by decide
  have hdescent : baseEnd_4337265 < baseStart_4337265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337305 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_4337305 : Nat := 118140960795 + 4337305 * 2 ^ 59
def prefixEnd_4337305 : Nat := 4983230072969 + 3 ^ 40 * 4337305 * 2
def baseEnd_4337305 : Nat := 2227122210149258007940603

theorem tailTrace_4337305 : CollatzResearch.WordTrace tailWord_4337305 prefixEnd_4337305 2227122210149258007940603 := by
  unfold tailWord_4337305
  simp only [CollatzResearch.WordTrace]
  refine ⟨158194509551692212564773369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105463006367794808376515579 158194509551692212564773369)
  ·
    refine ⟨118645882163769159423580027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158194509551692212564773369 118645882163769159423580027)
    ·
      refine ⟨177968823245653739135370041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118645882163769159423580027 177968823245653739135370041)
      ·
        refine ⟨133476617434240304351527531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177968823245653739135370041 133476617434240304351527531)
        ·
          refine ⟨200214926151360456527291297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133476617434240304351527531 200214926151360456527291297)
          ·
            refine ⟨150161194613520342395468473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200214926151360456527291297 150161194613520342395468473)
            ·
              refine ⟨112620895960140256796601355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150161194613520342395468473 112620895960140256796601355)
              ·
                refine ⟨168931343940210385194902033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112620895960140256796601355 168931343940210385194902033)
                ·
                  refine ⟨126698507955157788896176525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168931343940210385194902033 126698507955157788896176525)
                  ·
                    refine ⟨47511940483184170836066197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126698507955157788896176525 47511940483184170836066197)
                    ·
                      refine ⟨2227122210149258007940603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47511940483184170836066197 2227122210149258007940603)
                      ·
                        rfl

theorem cell23_4337305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_4337305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337305 prefixEnd_4337305 := by exact prefixLift 4337305
  have htrace : WordTrace (prefixWord ++ tailWord_4337305) baseStart_4337305 baseEnd_4337305 := by
    simpa [prefixWord, tailWord_4337305, baseEnd_4337305] using wordTrace_append hprefix tailTrace_4337305
  have hstable : (prefixWord ++ tailWord_4337305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337305).length < 2 ^ (prefixWord ++ tailWord_4337305).sum := by decide
  have hdescent : baseEnd_4337305 < baseStart_4337305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337369 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 5, 2]
def baseStart_4337369 : Nat := 118140960795 + 4337369 * 2 ^ 59
def prefixEnd_4337369 : Nat := 4983230072969 + 3 ^ 40 * 4337369 * 2
def baseEnd_4337369 : Nat := 2227155072911145757540309

theorem tailTrace_4337369 : CollatzResearch.WordTrace tailWord_4337369 prefixEnd_4337369 2227155072911145757540309 := by
  unfold tailWord_4337369
  simp only [CollatzResearch.WordTrace]
  refine ⟨158196843823460351495103161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105464562548973567663402107 158196843823460351495103161)
  ·
    refine ⟨118647632867595263621327371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158196843823460351495103161 118647632867595263621327371)
    ·
      refine ⟨177971449301392895431991057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118647632867595263621327371 177971449301392895431991057)
      ·
        refine ⟨133478586976044671573993293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177971449301392895431991057 133478586976044671573993293)
        ·
          refine ⟨50054470116016751840247485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133478586976044671573993293 50054470116016751840247485)
          ·
            refine ⟨18770426293506281940092807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50054470116016751840247485 18770426293506281940092807)
            ·
              refine ⟨28155639440259422910139211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18770426293506281940092807 28155639440259422910139211)
              ·
                refine ⟨42233459160389134365208817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28155639440259422910139211 42233459160389134365208817)
                ·
                  refine ⟨31675094370291850773906613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42233459160389134365208817 31675094370291850773906613)
                  ·
                    refine ⟨2969540097214861010053745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31675094370291850773906613 2969540097214861010053745)
                    ·
                      refine ⟨2227155072911145757540309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969540097214861010053745 2227155072911145757540309)
                      ·
                        rfl

theorem cell23_4337369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_4337369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337369 prefixEnd_4337369 := by exact prefixLift 4337369
  have htrace : WordTrace (prefixWord ++ tailWord_4337369) baseStart_4337369 baseEnd_4337369 := by
    simpa [prefixWord, tailWord_4337369, baseEnd_4337369] using wordTrace_append hprefix tailTrace_4337369
  have hstable : (prefixWord ++ tailWord_4337369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337369).length < 2 ^ (prefixWord ++ tailWord_4337369).sum := by decide
  have hdescent : baseEnd_4337369 < baseStart_4337369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337399 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_4337399 : Nat := 118140960795 + 4337399 * 2 ^ 59
def prefixEnd_4337399 : Nat := 4983230072969 + 3 ^ 40 * 4337399 * 2
def baseEnd_4337399 : Nat := 2227170477330780640165171

theorem tailTrace_4337399 : CollatzResearch.WordTrace tailWord_4337399 prefixEnd_4337399 2227170477330780640165171 := by
  unfold tailWord_4337399
  simp only [CollatzResearch.WordTrace]
  refine ⟨158197938013351666618695251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105465292008901111079130167 158197938013351666618695251)
  ·
    refine ⟨237296907020027499928042877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158197938013351666618695251 237296907020027499928042877)
    ·
      refine ⟨88986340132510312473016079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237296907020027499928042877 88986340132510312473016079)
      ·
        refine ⟨133479510198765468709524119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88986340132510312473016079 133479510198765468709524119)
        ·
          refine ⟨200219265298148203064286179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133479510198765468709524119 200219265298148203064286179)
          ·
            refine ⟨300328897947222304596429269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200219265298148203064286179 300328897947222304596429269)
            ·
              refine ⟨7038958545638022763978811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 300328897947222304596429269 7038958545638022763978811)
              ·
                refine ⟨10558437818457034145968217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038958545638022763978811 10558437818457034145968217)
                ·
                  refine ⟨7918828363842775609476163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10558437818457034145968217 7918828363842775609476163)
                  ·
                    refine ⟨11878242545764163414214245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7918828363842775609476163 11878242545764163414214245)
                    ·
                      refine ⟨2227170477330780640165171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11878242545764163414214245 2227170477330780640165171)
                      ·
                        rfl

theorem cell23_4337399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_4337399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337399 prefixEnd_4337399 := by exact prefixLift 4337399
  have htrace : WordTrace (prefixWord ++ tailWord_4337399) baseStart_4337399 baseEnd_4337399 := by
    simpa [prefixWord, tailWord_4337399, baseEnd_4337399] using wordTrace_append hprefix tailTrace_4337399
  have hstable : (prefixWord ++ tailWord_4337399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337399).length < 2 ^ (prefixWord ++ tailWord_4337399).sum := by decide
  have hdescent : baseEnd_4337399 < baseStart_4337399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337419 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3]
def baseStart_4337419 : Nat := 118140960795 + 4337419 * 2 ^ 59
def prefixEnd_4337419 : Nat := 4983230072969 + 3 ^ 40 * 4337419 * 2
def baseEnd_4337419 : Nat := 2227180746943870561915079

theorem tailTrace_4337419 : CollatzResearch.WordTrace tailWord_4337419 prefixEnd_4337419 2227180746943870561915079 := by
  unfold tailWord_4337419
  simp only [CollatzResearch.WordTrace]
  refine ⟨158198667473279210034423311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105465778315519473356282207 158198667473279210034423311)
  ·
    refine ⟨237298001209918815051634967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158198667473279210034423311 237298001209918815051634967)
    ·
      refine ⟨355947001814878222577452451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237298001209918815051634967 355947001814878222577452451)
      ·
        refine ⟨533920502722317333866178677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355947001814878222577452451 533920502722317333866178677)
        ·
          refine ⟨50055047130217250049954251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 533920502722317333866178677 50055047130217250049954251)
          ·
            refine ⟨75082570695325875074931377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50055047130217250049954251 75082570695325875074931377)
            ·
              refine ⟨56311928021494406306198533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75082570695325875074931377 56311928021494406306198533)
              ·
                refine ⟨10558486504030201182412225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56311928021494406306198533 10558486504030201182412225)
                ·
                  refine ⟨7918864878022650886809169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10558486504030201182412225 7918864878022650886809169)
                  ·
                    refine ⟨5939148658516988165106877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7918864878022650886809169 5939148658516988165106877)
                    ·
                      refine ⟨2227180746943870561915079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939148658516988165106877 2227180746943870561915079)
                      ·
                        rfl

theorem cell23_4337419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].length) (baseStart_4337419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337419 prefixEnd_4337419 := by exact prefixLift 4337419
  have htrace : WordTrace (prefixWord ++ tailWord_4337419) baseStart_4337419 baseEnd_4337419 := by
    simpa [prefixWord, tailWord_4337419, baseEnd_4337419] using wordTrace_append hprefix tailTrace_4337419
  have hstable : (prefixWord ++ tailWord_4337419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337419).length < 2 ^ (prefixWord ++ tailWord_4337419).sum := by decide
  have hdescent : baseEnd_4337419 < baseStart_4337419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337460 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4337460 : Nat := 118140960795 + 4337460 * 2 ^ 59
def prefixEnd_4337460 : Nat := 4983230072969 + 3 ^ 40 * 4337460 * 2
def baseEnd_4337460 : Nat := 742400599883568300500797

theorem tailTrace_4337460 : CollatzResearch.WordTrace tailWord_4337460 prefixEnd_4337460 742400599883568300500797 := by
  unfold tailWord_4337460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79100081433065337018332917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105466775244087116024443889 79100081433065337018332917)
  ·
    refine ⟨7415632634349875345468711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79100081433065337018332917 7415632634349875345468711)
    ·
      refine ⟨11123448951524813018203067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415632634349875345468711 11123448951524813018203067)
      ·
        refine ⟨16685173427287219527304601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123448951524813018203067 16685173427287219527304601)
        ·
          refine ⟨12513880070465414645478451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16685173427287219527304601 12513880070465414645478451)
          ·
            refine ⟨18770820105698121968217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12513880070465414645478451 18770820105698121968217677)
            ·
              refine ⟨7039057539636795738081629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18770820105698121968217677 7039057539636795738081629)
              ·
                refine ⟨2639646577363798401780611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7039057539636795738081629 2639646577363798401780611)
                ·
                  refine ⟨3959469866045697602670917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639646577363798401780611 3959469866045697602670917)
                  ·
                    refine ⟨742400599883568300500797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959469866045697602670917 742400599883568300500797)
                    ·
                      rfl

theorem cell23_4337460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4337460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337460 prefixEnd_4337460 := by exact prefixLift 4337460
  have htrace : WordTrace (prefixWord ++ tailWord_4337460) baseStart_4337460 baseEnd_4337460 := by
    simpa [prefixWord, tailWord_4337460, baseEnd_4337460] using wordTrace_append hprefix tailTrace_4337460
  have hstable : (prefixWord ++ tailWord_4337460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337460).length < 2 ^ (prefixWord ++ tailWord_4337460).sum := by decide
  have hdescent : baseEnd_4337460 < baseStart_4337460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337534 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4337534 : Nat := 118140960795 + 4337534 * 2 ^ 59
def prefixEnd_4337534 : Nat := 4983230072969 + 3 ^ 40 * 4337534 * 2
def baseEnd_4337534 : Nat := 2227239797219137611977051

theorem tailTrace_4337534 : CollatzResearch.WordTrace tailWord_4337534 prefixEnd_4337534 2227239797219137611977051 := by
  unfold tailWord_4337534
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775357733482823084357457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105468574578575056449906437 19775357733482823084357457)
  ·
    refine ⟨14831518300112117313268093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19775357733482823084357457 14831518300112117313268093)
    ·
      refine ⟨5561819362542043992475535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14831518300112117313268093 5561819362542043992475535)
      ·
        refine ⟨8342729043813065988713303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561819362542043992475535 8342729043813065988713303)
        ·
          refine ⟨12514093565719598983069955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342729043813065988713303 12514093565719598983069955)
          ·
            refine ⟨18771140348579398474604933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514093565719598983069955 18771140348579398474604933)
            ·
              refine ⟨3519588815358637213988425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18771140348579398474604933 3519588815358637213988425)
              ·
                refine ⟨2639691611518977910491319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519588815358637213988425 2639691611518977910491319)
                ·
                  refine ⟨3959537417278466865736979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639691611518977910491319 3959537417278466865736979)
                  ·
                    refine ⟨5939306125917700298605469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959537417278466865736979 5939306125917700298605469)
                    ·
                      refine ⟨2227239797219137611977051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939306125917700298605469 2227239797219137611977051)
                      ·
                        rfl

theorem cell23_4337534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4337534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337534 prefixEnd_4337534 := by exact prefixLift 4337534
  have htrace : WordTrace (prefixWord ++ tailWord_4337534) baseStart_4337534 baseEnd_4337534 := by
    simpa [prefixWord, tailWord_4337534, baseEnd_4337534] using wordTrace_append hprefix tailTrace_4337534
  have hstable : (prefixWord ++ tailWord_4337534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337534).length < 2 ^ (prefixWord ++ tailWord_4337534).sum := by decide
  have hdescent : baseEnd_4337534 < baseStart_4337534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337583 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 1, 3, 2]
def baseStart_4337583 : Nat := 118140960795 + 4337583 * 2 ^ 59
def prefixEnd_4337583 : Nat := 4983230072969 + 3 ^ 40 * 4337583 * 2
def baseEnd_4337583 : Nat := 2227264957771207920264325

theorem tailTrace_4337583 : CollatzResearch.WordTrace tailWord_4337583 prefixEnd_4337583 2227264957771207920264325 := by
  unfold tailWord_4337583
  simp only [CollatzResearch.WordTrace]
  refine ⟨158204649044685066043393403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105469766029790044028928935 158204649044685066043393403)
  ·
    refine ⟨237306973567027599065090105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158204649044685066043393403 237306973567027599065090105)
    ·
      refine ⟨177980230175270699298817579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237306973567027599065090105 177980230175270699298817579)
      ·
        refine ⟨266970345262906048948226369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177980230175270699298817579 266970345262906048948226369)
        ·
          refine ⟨200227758947179536711169777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266970345262906048948226369 200227758947179536711169777)
          ·
            refine ⟨150170819210384652533377333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200227758947179536711169777 150170819210384652533377333)
            ·
              refine ⟨14078514300973561175004125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150170819210384652533377333 14078514300973561175004125)
              ·
                refine ⟨5279442862865085440626547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14078514300973561175004125 5279442862865085440626547)
                ·
                  refine ⟨7919164294297628160939821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5279442862865085440626547 7919164294297628160939821)
                  ·
                    refine ⟨2969686610361610560352433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7919164294297628160939821 2969686610361610560352433)
                    ·
                      refine ⟨2227264957771207920264325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969686610361610560352433 2227264957771207920264325)
                      ·
                        rfl

theorem cell23_4337583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3, 2].length) (baseStart_4337583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337583 prefixEnd_4337583 := by exact prefixLift 4337583
  have htrace : WordTrace (prefixWord ++ tailWord_4337583) baseStart_4337583 baseEnd_4337583 := by
    simpa [prefixWord, tailWord_4337583, baseEnd_4337583] using wordTrace_append hprefix tailTrace_4337583
  have hstable : (prefixWord ++ tailWord_4337583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337583).length < 2 ^ (prefixWord ++ tailWord_4337583).sum := by decide
  have hdescent : baseEnd_4337583 < baseStart_4337583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337659 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_4337659 : Nat := 118140960795 + 4337659 * 2 ^ 59
def prefixEnd_4337659 : Nat := 4983230072969 + 3 ^ 40 * 4337659 * 2
def baseEnd_4337659 : Nat := 2227303982300949622913975

theorem tailTrace_4337659 : CollatzResearch.WordTrace tailWord_4337659 prefixEnd_4337659 2227303982300949622913975 := by
  unfold tailWord_4337659
  simp only [CollatzResearch.WordTrace]
  refine ⟨158207420992409731023160031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105471613994939820682106687 158207420992409731023160031)
  ·
    refine ⟨237311131488614596534740047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158207420992409731023160031 237311131488614596534740047)
    ·
      refine ⟨355966697232921894802110071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237311131488614596534740047 355966697232921894802110071)
      ·
        refine ⟨533950045849382842203165107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355966697232921894802110071 533950045849382842203165107)
        ·
          refine ⟨800925068774074263304747661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533950045849382842203165107 800925068774074263304747661)
          ·
            refine ⟨300346900790277848739280373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800925068774074263304747661 300346900790277848739280373)
            ·
              refine ⟨28157521949088548319307535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300346900790277848739280373 28157521949088548319307535)
              ·
                refine ⟨42236282923632822478961303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28157521949088548319307535 42236282923632822478961303)
                ·
                  refine ⟨63354424385449233718441955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42236282923632822478961303 63354424385449233718441955)
                  ·
                    refine ⟨95031636578173850577662933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63354424385449233718441955 95031636578173850577662933)
                    ·
                      refine ⟨2227303982300949622913975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95031636578173850577662933 2227303982300949622913975)
                      ·
                        rfl

theorem cell23_4337659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_4337659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337659 prefixEnd_4337659 := by exact prefixLift 4337659
  have htrace : WordTrace (prefixWord ++ tailWord_4337659) baseStart_4337659 baseEnd_4337659 := by
    simpa [prefixWord, tailWord_4337659, baseEnd_4337659] using wordTrace_append hprefix tailTrace_4337659
  have hstable : (prefixWord ++ tailWord_4337659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337659).length < 2 ^ (prefixWord ++ tailWord_4337659).sum := by decide
  have hdescent : baseEnd_4337659 < baseStart_4337659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337704 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 5]
def baseStart_4337704 : Nat := 118140960795 + 4337704 * 2 ^ 59
def prefixEnd_4337704 : Nat := 4983230072969 + 3 ^ 40 * 4337704 * 2
def baseEnd_4337704 : Nat := 247480787658933549650141

theorem tailTrace_4337704 : CollatzResearch.WordTrace tailWord_4337704 prefixEnd_4337704 247480787658933549650141 := by
  unfold tailWord_4337704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79104531138623351854274083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105472708184831135805698777 79104531138623351854274083)
  ·
    refine ⟨118656796707935027781411125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79104531138623351854274083 118656796707935027781411125)
    ·
      refine ⟨11124074691368908854507293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118656796707935027781411125 11124074691368908854507293)
      ·
        refine ⟨4171528009263340820440235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11124074691368908854507293 4171528009263340820440235)
        ·
          refine ⟨6257292013895011230660353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171528009263340820440235 6257292013895011230660353)
          ·
            refine ⟨4692969010421258422995265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257292013895011230660353 4692969010421258422995265)
            ·
              refine ⟨3519726757815943817246449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4692969010421258422995265 3519726757815943817246449)
              ·
                refine ⟨2639795068361957862934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519726757815943817246449 2639795068361957862934837)
                ·
                  refine ⟨247480787658933549650141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2639795068361957862934837 247480787658933549650141)
                  ·
                    rfl

theorem cell23_4337704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 5].length) (baseStart_4337704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337704 prefixEnd_4337704 := by exact prefixLift 4337704
  have htrace : WordTrace (prefixWord ++ tailWord_4337704) baseStart_4337704 baseEnd_4337704 := by
    simpa [prefixWord, tailWord_4337704, baseEnd_4337704] using wordTrace_append hprefix tailTrace_4337704
  have hstable : (prefixWord ++ tailWord_4337704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337704).length < 2 ^ (prefixWord ++ tailWord_4337704).sum := by decide
  have hdescent : baseEnd_4337704 < baseStart_4337704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337720 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_4337720 : Nat := 118140960795 + 4337720 * 2 ^ 59
def prefixEnd_4337720 : Nat := 4983230072969 + 3 ^ 40 * 4337720 * 2
def baseEnd_4337720 : Nat := 2227335304620873884251195

theorem tailTrace_4337720 : CollatzResearch.WordTrace tailWord_4337720 prefixEnd_4337720 2227335304620873884251195 := by
  unfold tailWord_4337720
  simp only [CollatzResearch.WordTrace]
  refine ⟨79104822922594369220565307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105473097230125825627420409 79104822922594369220565307)
  ·
    refine ⟨118657234383891553830847961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79104822922594369220565307 118657234383891553830847961)
    ·
      refine ⟨88992925787918665373135971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118657234383891553830847961 88992925787918665373135971)
      ·
        refine ⟨133489388681877998059703957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88992925787918665373135971 133489388681877998059703957)
        ·
          refine ⟨6257315094463031159048623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133489388681877998059703957 6257315094463031159048623)
          ·
            refine ⟨9385972641694546738572935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257315094463031159048623 9385972641694546738572935)
            ·
              refine ⟨14078958962541820107859403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9385972641694546738572935 14078958962541820107859403)
              ·
                refine ⟨21118438443812730161789105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14078958962541820107859403 21118438443812730161789105)
                ·
                  refine ⟨15838828832859547621341829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21118438443812730161789105 15838828832859547621341829)
                  ·
                    refine ⟨2969780406161165179001593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15838828832859547621341829 2969780406161165179001593)
                    ·
                      refine ⟨2227335304620873884251195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969780406161165179001593 2227335304620873884251195)
                      ·
                        rfl

theorem cell23_4337720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_4337720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337720 prefixEnd_4337720 := by exact prefixLift 4337720
  have htrace : WordTrace (prefixWord ++ tailWord_4337720) baseStart_4337720 baseEnd_4337720 := by
    simpa [prefixWord, tailWord_4337720, baseEnd_4337720] using wordTrace_append hprefix tailTrace_4337720
  have hstable : (prefixWord ++ tailWord_4337720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337720).length < 2 ^ (prefixWord ++ tailWord_4337720).sum := by decide
  have hdescent : baseEnd_4337720 < baseStart_4337720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337736 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_4337736 : Nat := 118140960795 + 4337736 * 2 ^ 59
def prefixEnd_4337736 : Nat := 4983230072969 + 3 ^ 40 * 4337736 * 2
def baseEnd_4337736 : Nat := 2227343520311345821651121

theorem tailTrace_4337736 : CollatzResearch.WordTrace tailWord_4337736 prefixEnd_4337736 2227343520311345821651121 := by
  unfold tailWord_4337736
  simp only [CollatzResearch.WordTrace]
  refine ⟨79105114706565386586856531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105473486275420515449142041 79105114706565386586856531)
  ·
    refine ⟨118657672059848079880284797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79105114706565386586856531 118657672059848079880284797)
    ·
      refine ⟨44496627022443029955106799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118657672059848079880284797 44496627022443029955106799)
      ·
        refine ⟨66744940533664544932660199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44496627022443029955106799 66744940533664544932660199)
        ·
          refine ⟨100117410800496817398990299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66744940533664544932660199 100117410800496817398990299)
          ·
            refine ⟨150176116200745226098485449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100117410800496817398990299 150176116200745226098485449)
            ·
              refine ⟨112632087150558919573864087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150176116200745226098485449 112632087150558919573864087)
              ·
                refine ⟨168948130725838379360796131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112632087150558919573864087 168948130725838379360796131)
                ·
                  refine ⟨253422196088757569041194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168948130725838379360796131 253422196088757569041194197)
                  ·
                    refine ⟨5939582720830255524402989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 253422196088757569041194197 5939582720830255524402989)
                    ·
                      refine ⟨2227343520311345821651121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939582720830255524402989 2227343520311345821651121)
                      ·
                        rfl

theorem cell23_4337736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_4337736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337736 prefixEnd_4337736 := by exact prefixLift 4337736
  have htrace : WordTrace (prefixWord ++ tailWord_4337736) baseStart_4337736 baseEnd_4337736 := by
    simpa [prefixWord, tailWord_4337736, baseEnd_4337736] using wordTrace_append hprefix tailTrace_4337736
  have hstable : (prefixWord ++ tailWord_4337736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337736).length < 2 ^ (prefixWord ++ tailWord_4337736).sum := by decide
  have hdescent : baseEnd_4337736 < baseStart_4337736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337750 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4337750 : Nat := 118140960795 + 4337750 * 2 ^ 59
def prefixEnd_4337750 : Nat := 4983230072969 + 3 ^ 40 * 4337750 * 2
def baseEnd_4337750 : Nat := 2227350709040508766876057

theorem tailTrace_4337750 : CollatzResearch.WordTrace tailWord_4337750 prefixEnd_4337750 2227350709040508766876057 := by
  unfold tailWord_4337750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888171252192503347795169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105473826690053369043148469 9888171252192503347795169)
  ·
    refine ⟨7416128439144377510846377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9888171252192503347795169 7416128439144377510846377)
    ·
      refine ⟨5562096329358283133134783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7416128439144377510846377 5562096329358283133134783)
      ·
        refine ⟨8343144494037424699702175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562096329358283133134783 8343144494037424699702175)
        ·
          refine ⟨12514716741056137049553263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343144494037424699702175 12514716741056137049553263)
          ·
            refine ⟨18772075111584205574329895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514716741056137049553263 18772075111584205574329895)
            ·
              refine ⟨28158112667376308361494843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18772075111584205574329895 28158112667376308361494843)
              ·
                refine ⟨42237169001064462542242265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28158112667376308361494843 42237169001064462542242265)
                ·
                  refine ⟨31677876750798346906681699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42237169001064462542242265 31677876750798346906681699)
                  ·
                    refine ⟨47516815126197520360022549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31677876750798346906681699 47516815126197520360022549)
                    ·
                      refine ⟨2227350709040508766876057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47516815126197520360022549 2227350709040508766876057)
                      ·
                        rfl

theorem cell23_4337750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4337750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337750 prefixEnd_4337750 := by exact prefixLift 4337750
  have htrace : WordTrace (prefixWord ++ tailWord_4337750) baseStart_4337750 baseEnd_4337750 := by
    simpa [prefixWord, tailWord_4337750, baseEnd_4337750] using wordTrace_append hprefix tailTrace_4337750
  have hstable : (prefixWord ++ tailWord_4337750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337750).length < 2 ^ (prefixWord ++ tailWord_4337750).sum := by decide
  have hdescent : baseEnd_4337750 < baseStart_4337750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337753 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_4337753 : Nat := 118140960795 + 4337753 * 2 ^ 59
def prefixEnd_4337753 : Nat := 4983230072969 + 3 ^ 40 * 4337753 * 2
def baseEnd_4337753 : Nat := 2227352249482472255138543

theorem tailTrace_4337753 : CollatzResearch.WordTrace tailWord_4337753 prefixEnd_4337753 2227352249482472255138543 := by
  unfold tailWord_4337753
  simp only [CollatzResearch.WordTrace]
  refine ⟨158210849454069185077081913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105473899636046123384721275 158210849454069185077081913)
  ·
    refine ⟨118658137090551888807811435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158210849454069185077081913 118658137090551888807811435)
    ·
      refine ⟨177987205635827833211717153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118658137090551888807811435 177987205635827833211717153)
      ·
        refine ⟨133490404226870874908787865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177987205635827833211717153 133490404226870874908787865)
        ·
          refine ⟨100117803170153156181590899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133490404226870874908787865 100117803170153156181590899)
          ·
            refine ⟨150176704755229734272386349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100117803170153156181590899 150176704755229734272386349)
            ·
              refine ⟨56316264283211150352144881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150176704755229734272386349 56316264283211150352144881)
              ·
                refine ⟨42237198212408362764108661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56316264283211150352144881 42237198212408362764108661)
                ·
                  refine ⟨3959737332413284009135187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42237198212408362764108661 3959737332413284009135187)
                  ·
                    refine ⟨5939605998619926013702781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959737332413284009135187 5939605998619926013702781)
                    ·
                      refine ⟨2227352249482472255138543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939605998619926013702781 2227352249482472255138543)
                      ·
                        rfl

theorem cell23_4337753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_4337753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337753 prefixEnd_4337753 := by exact prefixLift 4337753
  have htrace : WordTrace (prefixWord ++ tailWord_4337753) baseStart_4337753 baseEnd_4337753 := by
    simpa [prefixWord, tailWord_4337753, baseEnd_4337753] using wordTrace_append hprefix tailTrace_4337753
  have hstable : (prefixWord ++ tailWord_4337753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337753).length < 2 ^ (prefixWord ++ tailWord_4337753).sum := by decide
  have hdescent : baseEnd_4337753 < baseStart_4337753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337810 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4337810 : Nat := 118140960795 + 4337810 * 2 ^ 59
def prefixEnd_4337810 : Nat := 4983230072969 + 3 ^ 40 * 4337810 * 2
def baseEnd_4337810 : Nat := 2227381517879778532125781

theorem tailTrace_4337810 : CollatzResearch.WordTrace tailWord_4337810 prefixEnd_4337810 2227381517879778532125781 := by
  unfold tailWord_4337810
  simp only [CollatzResearch.WordTrace]
  refine ⟨39553232103715670952976721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105475285609908455874604589 39553232103715670952976721)
  ·
    refine ⟨29664924077786753214732541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39553232103715670952976721 29664924077786753214732541)
    ·
      refine ⟨11124346529170032455524703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29664924077786753214732541 11124346529170032455524703)
      ·
        refine ⟨16686519793755048683287055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11124346529170032455524703 16686519793755048683287055)
        ·
          refine ⟨25029779690632573024930583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16686519793755048683287055 25029779690632573024930583)
          ·
            refine ⟨37544669535948859537395875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25029779690632573024930583 37544669535948859537395875)
            ·
              refine ⟨56317004303923289306093813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37544669535948859537395875 56317004303923289306093813)
              ·
                refine ⟨5279719153492808372446295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56317004303923289306093813 5279719153492808372446295)
                ·
                  refine ⟨7919578730239212558669443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5279719153492808372446295 7919578730239212558669443)
                  ·
                    refine ⟨11879368095358818838004165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7919578730239212558669443 11879368095358818838004165)
                    ·
                      refine ⟨2227381517879778532125781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11879368095358818838004165 2227381517879778532125781)
                      ·
                        rfl

theorem cell23_4337810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4337810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337810 prefixEnd_4337810 := by exact prefixLift 4337810
  have htrace : WordTrace (prefixWord ++ tailWord_4337810) baseStart_4337810 baseEnd_4337810 := by
    simpa [prefixWord, tailWord_4337810, baseEnd_4337810] using wordTrace_append hprefix tailTrace_4337810
  have hstable : (prefixWord ++ tailWord_4337810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337810).length < 2 ^ (prefixWord ++ tailWord_4337810).sum := by decide
  have hdescent : baseEnd_4337810 < baseStart_4337810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337813 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_4337813 : Nat := 118140960795 + 4337813 * 2 ^ 59
def prefixEnd_4337813 : Nat := 4983230072969 + 3 ^ 40 * 4337813 * 2
def baseEnd_4337813 : Nat := 2227383058321742020388267

theorem tailTrace_4337813 : CollatzResearch.WordTrace tailWord_4337813 prefixEnd_4337813 2227383058321742020388267 := by
  unfold tailWord_4337813
  simp only [CollatzResearch.WordTrace]
  refine ⟨158213037833851815324266093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105475358555901210216177395 158213037833851815324266093)
  ·
    refine ⟨59329889187694430746599785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158213037833851815324266093 59329889187694430746599785)
    ·
      refine ⟨44497416890770823059949839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59329889187694430746599785 44497416890770823059949839)
      ·
        refine ⟨66746125336156234589924759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44497416890770823059949839 66746125336156234589924759)
        ·
          refine ⟨100119188004234351884887139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66746125336156234589924759 100119188004234351884887139)
          ·
            refine ⟨150178782006351527827330709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100119188004234351884887139 150178782006351527827330709)
            ·
              refine ⟨7039630406547727866906127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150178782006351527827330709 7039630406547727866906127)
              ·
                refine ⟨10559445609821591800359191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7039630406547727866906127 10559445609821591800359191)
                ·
                  refine ⟨15839168414732387700538787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10559445609821591800359191 15839168414732387700538787)
                  ·
                    refine ⟨23758752622098581550808181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15839168414732387700538787 23758752622098581550808181)
                    ·
                      refine ⟨2227383058321742020388267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23758752622098581550808181 2227383058321742020388267)
                      ·
                        rfl

theorem cell23_4337813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_4337813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337813 prefixEnd_4337813 := by exact prefixLift 4337813
  have htrace : WordTrace (prefixWord ++ tailWord_4337813) baseStart_4337813 baseEnd_4337813 := by
    simpa [prefixWord, tailWord_4337813, baseEnd_4337813] using wordTrace_append hprefix tailTrace_4337813
  have hstable : (prefixWord ++ tailWord_4337813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337813).length < 2 ^ (prefixWord ++ tailWord_4337813).sum := by decide
  have hdescent : baseEnd_4337813 < baseStart_4337813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337820 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_4337820 : Nat := 118140960795 + 4337820 * 2 ^ 59
def prefixEnd_4337820 : Nat := 4983230072969 + 3 ^ 40 * 4337820 * 2
def baseEnd_4337820 : Nat := 742462217562107831000245

theorem tailTrace_4337820 : CollatzResearch.WordTrace tailWord_4337820 prefixEnd_4337820 742462217562107831000245 := by
  unfold tailWord_4337820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79106646572413227759885457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105475528763217637013180609 79106646572413227759885457)
  ·
    refine ⟨59329984929309920819914093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79106646572413227759885457 59329984929309920819914093)
    ·
      refine ⟨22248744348491220307467785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59329984929309920819914093 22248744348491220307467785)
      ·
        refine ⟨16686558261368415230600839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22248744348491220307467785 16686558261368415230600839)
        ·
          refine ⟨25029837392052622845901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16686558261368415230600839 25029837392052622845901259)
          ·
            refine ⟨37544756088078934268851889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25029837392052622845901259 37544756088078934268851889)
            ·
              refine ⟨28158567066059200701638917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37544756088078934268851889 28158567066059200701638917)
              ·
                refine ⟨5279731324886100131557297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28158567066059200701638917 5279731324886100131557297)
                ·
                  refine ⟨3959798493664575098667973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279731324886100131557297 3959798493664575098667973)
                  ·
                    refine ⟨742462217562107831000245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959798493664575098667973 742462217562107831000245)
                    ·
                      rfl

theorem cell23_4337820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_4337820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337820 prefixEnd_4337820 := by exact prefixLift 4337820
  have htrace : WordTrace (prefixWord ++ tailWord_4337820) baseStart_4337820 baseEnd_4337820 := by
    simpa [prefixWord, tailWord_4337820, baseEnd_4337820] using wordTrace_append hprefix tailTrace_4337820
  have hstable : (prefixWord ++ tailWord_4337820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337820).length < 2 ^ (prefixWord ++ tailWord_4337820).sum := by decide
  have hdescent : baseEnd_4337820 < baseStart_4337820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337823 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4337823 : Nat := 118140960795 + 4337823 * 2 ^ 59
def prefixEnd_4337823 : Nat := 4983230072969 + 3 ^ 40 * 4337823 * 2
def baseEnd_4337823 : Nat := 2227388193128286981263221

theorem tailTrace_4337823 : CollatzResearch.WordTrace tailWord_4337823 prefixEnd_4337823 2227388193128286981263221 := by
  unfold tailWord_4337823
  simp only [CollatzResearch.WordTrace]
  refine ⟨158213402563815587032130123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105475601709210391354753415 158213402563815587032130123)
  ·
    refine ⟨237320103845723380548195185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158213402563815587032130123 237320103845723380548195185)
    ·
      refine ⟨177990077884292535411146389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237320103845723380548195185 177990077884292535411146389)
      ·
        refine ⟨8343284900826212597397487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177990077884292535411146389 8343284900826212597397487)
        ·
          refine ⟨12514927351239318896096231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343284900826212597397487 12514927351239318896096231)
          ·
            refine ⟨18772391026858978344144347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514927351239318896096231 18772391026858978344144347)
            ·
              refine ⟨28158586540288467516216521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18772391026858978344144347 28158586540288467516216521)
              ·
                refine ⟨21118939905216350637162391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28158586540288467516216521 21118939905216350637162391)
                ·
                  refine ⟨31678409857824525955743587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21118939905216350637162391 31678409857824525955743587)
                  ·
                    refine ⟨47517614786736788933615381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31678409857824525955743587 47517614786736788933615381)
                    ·
                      refine ⟨2227388193128286981263221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47517614786736788933615381 2227388193128286981263221)
                      ·
                        rfl

theorem cell23_4337823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4337823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337823 prefixEnd_4337823 := by exact prefixLift 4337823
  have htrace : WordTrace (prefixWord ++ tailWord_4337823) baseStart_4337823 baseEnd_4337823 := by
    simpa [prefixWord, tailWord_4337823, baseEnd_4337823] using wordTrace_append hprefix tailTrace_4337823
  have hstable : (prefixWord ++ tailWord_4337823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337823).length < 2 ^ (prefixWord ++ tailWord_4337823).sum := by decide
  have hdescent : baseEnd_4337823 < baseStart_4337823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337837 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4337837 : Nat := 118140960795 + 4337837 * 2 ^ 59
def prefixEnd_4337837 : Nat := 4983230072969 + 3 ^ 40 * 4337837 * 2
def baseEnd_4337837 : Nat := 742465127285816642162719

theorem tailTrace_4337837 : CollatzResearch.WordTrace tailWord_4337837 prefixEnd_4337837 742465127285816642162719 := by
  unfold tailWord_4337837
  simp only [CollatzResearch.WordTrace]
  refine ⟨158213913185764867423139765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105475942123843244948759843 158213913185764867423139765)
  ·
    refine ⟨14832554361165456320919353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158213913185764867423139765 14832554361165456320919353)
    ·
      refine ⟨11124415770874092240689515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14832554361165456320919353 11124415770874092240689515)
      ·
        refine ⟨16686623656311138361034273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11124415770874092240689515 16686623656311138361034273)
        ·
          refine ⟨12514967742233353770775705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16686623656311138361034273 12514967742233353770775705)
          ·
            refine ⟨9386225806675015328081779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12514967742233353770775705 9386225806675015328081779)
            ·
              refine ⟨14079338710012522992122669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386225806675015328081779 14079338710012522992122669)
              ·
                refine ⟨5279752016254696122046001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14079338710012522992122669 5279752016254696122046001)
                ·
                  refine ⟨3959814012191022091534501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279752016254696122046001 3959814012191022091534501)
                  ·
                    refine ⟨742465127285816642162719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959814012191022091534501 742465127285816642162719)
                    ·
                      rfl

theorem cell23_4337837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4337837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337837 prefixEnd_4337837 := by exact prefixLift 4337837
  have htrace : WordTrace (prefixWord ++ tailWord_4337837) baseStart_4337837 baseEnd_4337837 := by
    simpa [prefixWord, tailWord_4337837, baseEnd_4337837] using wordTrace_append hprefix tailTrace_4337837
  have hstable : (prefixWord ++ tailWord_4337837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337837).length < 2 ^ (prefixWord ++ tailWord_4337837).sum := by decide
  have hdescent : baseEnd_4337837 < baseStart_4337837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337843 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3]
def baseStart_4337843 : Nat := 118140960795 + 4337843 * 2 ^ 59
def prefixEnd_4337843 : Nat := 4983230072969 + 3 ^ 40 * 4337843 * 2
def baseEnd_4337843 : Nat := 2227398462741376903013129

theorem tailTrace_4337843 : CollatzResearch.WordTrace tailWord_4337843 prefixEnd_4337843 2227398462741376903013129 := by
  unfold tailWord_4337843
  simp only [CollatzResearch.WordTrace]
  refine ⟨158214132023743130447858183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105476088015828753631905455 158214132023743130447858183)
  ·
    refine ⟨237321198035614695671787275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158214132023743130447858183 237321198035614695671787275)
    ·
      refine ⟨355981797053422043507680913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237321198035614695671787275 355981797053422043507680913)
      ·
        refine ⟨266986347790066532630760685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355981797053422043507680913 266986347790066532630760685)
        ·
          refine ⟨100119880421274949736535257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266986347790066532630760685 100119880421274949736535257)
          ·
            refine ⟨75089910315956212302401443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100119880421274949736535257 75089910315956212302401443)
            ·
              refine ⟨112634865473934318453602165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75089910315956212302401443 112634865473934318453602165)
              ·
                refine ⟨10559518638181342355025203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112634865473934318453602165 10559518638181342355025203)
                ·
                  refine ⟨15839277957272013532537805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10559518638181342355025203 15839277957272013532537805)
                  ·
                    refine ⟨5939729233977005074701677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15839277957272013532537805 5939729233977005074701677)
                    ·
                      refine ⟨2227398462741376903013129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939729233977005074701677 2227398462741376903013129)
                      ·
                        rfl

theorem cell23_4337843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_4337843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337843 prefixEnd_4337843 := by exact prefixLift 4337843
  have htrace : WordTrace (prefixWord ++ tailWord_4337843) baseStart_4337843 baseEnd_4337843 := by
    simpa [prefixWord, tailWord_4337843, baseEnd_4337843] using wordTrace_append hprefix tailTrace_4337843
  have hstable : (prefixWord ++ tailWord_4337843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337843).length < 2 ^ (prefixWord ++ tailWord_4337843).sum := by decide
  have hdescent : baseEnd_4337843 < baseStart_4337843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337847 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_4337847 : Nat := 118140960795 + 4337847 * 2 ^ 59
def prefixEnd_4337847 : Nat := 4983230072969 + 3 ^ 40 * 4337847 * 2
def baseEnd_4337847 : Nat := 2227400516663994887363111

theorem tailTrace_4337847 : CollatzResearch.WordTrace tailWord_4337847 prefixEnd_4337847 2227400516663994887363111 := by
  unfold tailWord_4337847
  simp only [CollatzResearch.WordTrace]
  refine ⟨158214277915728639131003795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105476185277152426087335863 158214277915728639131003795)
  ·
    refine ⟨237321416873592958696505693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158214277915728639131003795 237321416873592958696505693)
    ·
      refine ⟨88995531327597359511189635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237321416873592958696505693 88995531327597359511189635)
      ·
        refine ⟨133493296991396039266784453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88995531327597359511189635 133493296991396039266784453)
        ·
          refine ⟨25029993185886757362522085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133493296991396039266784453 25029993185886757362522085)
          ·
            refine ⟨4693123722353767005472891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25029993185886757362522085 4693123722353767005472891)
            ·
              refine ⟨7039685583530650508209337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693123722353767005472891 7039685583530650508209337)
              ·
                refine ⟨5279764187647987881157003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7039685583530650508209337 5279764187647987881157003)
                ·
                  refine ⟨7919646281471981821735505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5279764187647987881157003 7919646281471981821735505)
                  ·
                    refine ⟨5939734711103986366301629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7919646281471981821735505 5939734711103986366301629)
                    ·
                      refine ⟨2227400516663994887363111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939734711103986366301629 2227400516663994887363111)
                      ·
                        rfl

theorem cell23_4337847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_4337847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337847 prefixEnd_4337847 := by exact prefixLift 4337847
  have htrace : WordTrace (prefixWord ++ tailWord_4337847) baseStart_4337847 baseEnd_4337847 := by
    simpa [prefixWord, tailWord_4337847, baseEnd_4337847] using wordTrace_append hprefix tailTrace_4337847
  have hstable : (prefixWord ++ tailWord_4337847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337847).length < 2 ^ (prefixWord ++ tailWord_4337847).sum := by decide
  have hdescent : baseEnd_4337847 < baseStart_4337847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337857 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4337857 : Nat := 118140960795 + 4337857 * 2 ^ 59
def prefixEnd_4337857 : Nat := 4983230072969 + 3 ^ 40 * 4337857 * 2
def baseEnd_4337857 : Nat := 2227405651470539848238065

theorem tailTrace_4337857 : CollatzResearch.WordTrace tailWord_4337857 prefixEnd_4337857 2227405651470539848238065 := by
  unfold tailWord_4337857
  simp only [CollatzResearch.WordTrace]
  refine ⟨158214642645692410838867825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105476428430461607225911883 158214642645692410838867825)
  ·
    refine ⟨118660981984269308129150869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158214642645692410838867825 118660981984269308129150869)
    ·
      refine ⟨5562233530512623818553947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118660981984269308129150869 5562233530512623818553947)
      ·
        refine ⟨8343350295768935727830921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562233530512623818553947 8343350295768935727830921)
        ·
          refine ⟨6257512721826701795873191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8343350295768935727830921 6257512721826701795873191)
          ·
            refine ⟨9386269082740052693809787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257512721826701795873191 9386269082740052693809787)
            ·
              refine ⟨14079403624110079040714681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386269082740052693809787 14079403624110079040714681)
              ·
                refine ⟨10559552718082559280536011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14079403624110079040714681 10559552718082559280536011)
                ·
                  refine ⟨15839329077123838920804017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10559552718082559280536011 15839329077123838920804017)
                  ·
                    refine ⟨11879496807842879190603013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15839329077123838920804017 11879496807842879190603013)
                    ·
                      refine ⟨2227405651470539848238065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11879496807842879190603013 2227405651470539848238065)
                      ·
                        rfl

theorem cell23_4337857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4337857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337857 prefixEnd_4337857 := by exact prefixLift 4337857
  have htrace : WordTrace (prefixWord ++ tailWord_4337857) baseStart_4337857 baseEnd_4337857 := by
    simpa [prefixWord, tailWord_4337857, baseEnd_4337857] using wordTrace_append hprefix tailTrace_4337857
  have hstable : (prefixWord ++ tailWord_4337857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337857).length < 2 ^ (prefixWord ++ tailWord_4337857).sum := by decide
  have hdescent : baseEnd_4337857 < baseStart_4337857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337860 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_4337860 : Nat := 118140960795 + 4337860 * 2 ^ 59
def prefixEnd_4337860 : Nat := 4983230072969 + 3 ^ 40 * 4337860 * 2
def baseEnd_4337860 : Nat := 2227407191912503336500551

theorem tailTrace_4337860 : CollatzResearch.WordTrace tailWord_4337860 prefixEnd_4337860 2227407191912503336500551 := by
  unfold tailWord_4337860
  simp only [CollatzResearch.WordTrace]
  refine ⟨79107376032340771175613517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105476501376454361567484689 79107376032340771175613517)
  ·
    refine ⟨29665266012127789190855069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79107376032340771175613517 29665266012127789190855069)
    ·
      refine ⟨11124474754547920946570651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29665266012127789190855069 11124474754547920946570651)
      ·
        refine ⟨16686712131821881419855977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11124474754547920946570651 16686712131821881419855977)
        ·
          refine ⟨12515034098866411064891983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16686712131821881419855977 12515034098866411064891983)
          ·
            refine ⟨18772551148299616597337975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12515034098866411064891983 18772551148299616597337975)
            ·
              refine ⟨28158826722449424896006963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18772551148299616597337975 28158826722449424896006963)
              ·
                refine ⟨42238240083674137344010445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28158826722449424896006963 42238240083674137344010445)
                ·
                  refine ⟨15839340031377801504003917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42238240083674137344010445 15839340031377801504003917)
                  ·
                    refine ⟨5939752511766675564001469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15839340031377801504003917 5939752511766675564001469)
                    ·
                      refine ⟨2227407191912503336500551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939752511766675564001469 2227407191912503336500551)
                      ·
                        rfl

theorem cell23_4337860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_4337860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337860 prefixEnd_4337860 := by exact prefixLift 4337860
  have htrace : WordTrace (prefixWord ++ tailWord_4337860) baseStart_4337860 baseEnd_4337860 := by
    simpa [prefixWord, tailWord_4337860, baseEnd_4337860] using wordTrace_append hprefix tailTrace_4337860
  have hstable : (prefixWord ++ tailWord_4337860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337860).length < 2 ^ (prefixWord ++ tailWord_4337860).sum := by decide
  have hdescent : baseEnd_4337860 < baseStart_4337860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337878 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4337878 : Nat := 118140960795 + 4337878 * 2 ^ 59
def prefixEnd_4337878 : Nat := 4983230072969 + 3 ^ 40 * 4337878 * 2
def baseEnd_4337878 : Nat := 2227416434564284266075469

theorem tailTrace_4337878 : CollatzResearch.WordTrace tailWord_4337878 prefixEnd_4337878 2227416434564284266075469 := by
  unfold tailWord_4337878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888463036163520714086393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105476939052410887616921525 9888463036163520714086393)
  ·
    refine ⟨7416347277122640535564795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9888463036163520714086393 7416347277122640535564795)
    ·
      refine ⟨11124520915683960803347193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7416347277122640535564795 11124520915683960803347193)
      ·
        refine ⟨8343390686762970602510395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11124520915683960803347193 8343390686762970602510395)
        ·
          refine ⟨12515086030144455903765593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343390686762970602510395 12515086030144455903765593)
          ·
            refine ⟨9386314522608341927824195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12515086030144455903765593 9386314522608341927824195)
            ·
              refine ⟨14079471783912512891736293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386314522608341927824195 14079471783912512891736293)
              ·
                refine ⟨2639900959483596167200555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14079471783912512891736293 2639900959483596167200555)
                ·
                  refine ⟨3959851439225394250800833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639900959483596167200555 3959851439225394250800833)
                  ·
                    refine ⟨2969888579419045688100625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959851439225394250800833 2969888579419045688100625)
                    ·
                      refine ⟨2227416434564284266075469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969888579419045688100625 2227416434564284266075469)
                      ·
                        rfl

theorem cell23_4337878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4337878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337878 prefixEnd_4337878 := by exact prefixLift 4337878
  have htrace : WordTrace (prefixWord ++ tailWord_4337878) baseStart_4337878 baseEnd_4337878 := by
    simpa [prefixWord, tailWord_4337878, baseEnd_4337878] using wordTrace_append hprefix tailTrace_4337878
  have hstable : (prefixWord ++ tailWord_4337878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337878).length < 2 ^ (prefixWord ++ tailWord_4337878).sum := by decide
  have hdescent : baseEnd_4337878 < baseStart_4337878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337884 : List Nat := [2, 2, 5, 2, 2, 1, 1, 8]
def baseStart_4337884 : Nat := 118140960795 + 4337884 * 2 ^ 59
def prefixEnd_4337884 : Nat := 4983230072969 + 3 ^ 40 * 4337884 * 2
def baseEnd_4337884 : Nat := 82497019090674490466683

theorem tailTrace_4337884 : CollatzResearch.WordTrace tailWord_4337884 prefixEnd_4337884 82497019090674490466683 := by
  unfold tailWord_4337884
  simp only [CollatzResearch.WordTrace]
  refine ⟨79107813708297297225050353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105477084944396396300067137 79107813708297297225050353)
  ·
    refine ⟨59330860281222972918787765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79107813708297297225050353 59330860281222972918787765)
    ·
      refine ⟨5562268151364653711136353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59330860281222972918787765 5562268151364653711136353)
      ·
        refine ⟨4171701113523490283352265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5562268151364653711136353 4171701113523490283352265)
        ·
          refine ⟨3128775835142617712514199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4171701113523490283352265 3128775835142617712514199)
          ·
            refine ⟨4693163752713926568771299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128775835142617712514199 4693163752713926568771299)
            ·
              refine ⟨7039745629070889853156949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693163752713926568771299 7039745629070889853156949)
              ·
                refine ⟨82497019090674490466683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7039745629070889853156949 82497019090674490466683)
                ·
                  rfl

theorem cell23_4337884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 8].length) (baseStart_4337884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337884 prefixEnd_4337884 := by exact prefixLift 4337884
  have htrace : WordTrace (prefixWord ++ tailWord_4337884) baseStart_4337884 baseEnd_4337884 := by
    simpa [prefixWord, tailWord_4337884, baseEnd_4337884] using wordTrace_append hprefix tailTrace_4337884
  have hstable : (prefixWord ++ tailWord_4337884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337884).length < 2 ^ (prefixWord ++ tailWord_4337884).sum := by decide
  have hdescent : baseEnd_4337884 < baseStart_4337884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337893 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_4337893 : Nat := 118140960795 + 4337893 * 2 ^ 59
def prefixEnd_4337893 : Nat := 4983230072969 + 3 ^ 40 * 4337893 * 2
def baseEnd_4337893 : Nat := 742474712258033902462633

theorem tailTrace_4337893 : CollatzResearch.WordTrace tailWord_4337893 prefixEnd_4337893 742474712258033902462633 := by
  unfold tailWord_4337893
  simp only [CollatzResearch.WordTrace]
  refine ⟨158215955673561988987178333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105477303782374659324785555 158215955673561988987178333)
  ·
    refine ⟨59330983377585745870191875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158215955673561988987178333 59330983377585745870191875)
    ·
      refine ⟨88996475066378618805287813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59330983377585745870191875 88996475066378618805287813)
      ·
        refine ⟨16686839074945991025991465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88996475066378618805287813 16686839074945991025991465)
        ·
          refine ⟨12515129306209493269493599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16686839074945991025991465 12515129306209493269493599)
          ·
            refine ⟨18772693959314239904240399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12515129306209493269493599 18772693959314239904240399)
            ·
              refine ⟨28159040938971359856360599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18772693959314239904240399 28159040938971359856360599)
              ·
                refine ⟨42238561408457039784540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28159040938971359856360599 42238561408457039784540899)
                ·
                  refine ⟨63357842112685559676811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42238561408457039784540899 63357842112685559676811349)
                  ·
                    refine ⟨742474712258033902462633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63357842112685559676811349 742474712258033902462633)
                    ·
                      rfl

theorem cell23_4337893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_4337893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337893 prefixEnd_4337893 := by exact prefixLift 4337893
  have htrace : WordTrace (prefixWord ++ tailWord_4337893) baseStart_4337893 baseEnd_4337893 := by
    simpa [prefixWord, tailWord_4337893, baseEnd_4337893] using wordTrace_append hprefix tailTrace_4337893
  have hstable : (prefixWord ++ tailWord_4337893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337893).length < 2 ^ (prefixWord ++ tailWord_4337893).sum := by decide
  have hdescent : baseEnd_4337893 < baseStart_4337893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337951 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 2, 2, 2]
def baseStart_4337951 : Nat := 118140960795 + 4337951 * 2 ^ 59
def prefixEnd_4337951 : Nat := 4983230072969 + 3 ^ 40 * 4337951 * 2
def baseEnd_4337951 : Nat := 2227453918652062480462633

theorem tailTrace_4337951 : CollatzResearch.WordTrace tailWord_4337951 prefixEnd_4337951 2227453918652062480462633 := by
  unfold tailWord_4337951
  simp only [CollatzResearch.WordTrace]
  refine ⟨158218071107351864892789707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105478714071567909928526471 158218071107351864892789707)
  ·
    refine ⟨237327106661027797339184561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158218071107351864892789707 237327106661027797339184561)
    ·
      refine ⟨177995329995770848004388421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237327106661027797339184561 177995329995770848004388421)
      ·
        refine ⟨33374124374207034000822829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177995329995770848004388421 33374124374207034000822829)
        ·
          refine ⟨12515296640327637750308561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33374124374207034000822829 12515296640327637750308561)
          ·
            refine ⟨9386472480245728312731421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12515296640327637750308561 9386472480245728312731421)
            ·
              refine ⟨3519927180092148117274283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9386472480245728312731421 3519927180092148117274283)
              ·
                refine ⟨5279890770138222175911425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519927180092148117274283 5279890770138222175911425)
                ·
                  refine ⟨3959918077603666631933569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279890770138222175911425 3959918077603666631933569)
                  ·
                    refine ⟨2969938558202749973950177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959918077603666631933569 2969938558202749973950177)
                    ·
                      refine ⟨2227453918652062480462633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2969938558202749973950177 2227453918652062480462633)
                      ·
                        rfl

theorem cell23_4337951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_4337951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337951 prefixEnd_4337951 := by exact prefixLift 4337951
  have htrace : WordTrace (prefixWord ++ tailWord_4337951) baseStart_4337951 baseEnd_4337951 := by
    simpa [prefixWord, tailWord_4337951, baseEnd_4337951] using wordTrace_append hprefix tailTrace_4337951
  have hstable : (prefixWord ++ tailWord_4337951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337951).length < 2 ^ (prefixWord ++ tailWord_4337951).sum := by decide
  have hdescent : baseEnd_4337951 < baseStart_4337951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4337953 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_4337953 : Nat := 118140960795 + 4337953 * 2 ^ 59
def prefixEnd_4337953 : Nat := 4983230072969 + 3 ^ 40 * 4337953 * 2
def baseEnd_4337953 : Nat := 742484981871123824212541

theorem tailTrace_4337953 : CollatzResearch.WordTrace tailWord_4337953 prefixEnd_4337953 742484981871123824212541 := by
  unfold tailWord_4337953
  simp only [CollatzResearch.WordTrace]
  refine ⟨158218144053344619234362513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105478762702229746156241675 158218144053344619234362513)
  ·
    refine ⟨118663608040008464425771885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158218144053344619234362513 118663608040008464425771885)
    ·
      refine ⟨44498853015003174159664457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118663608040008464425771885 44498853015003174159664457)
      ·
        refine ⟨33374139761252380619748343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44498853015003174159664457 33374139761252380619748343)
        ·
          refine ⟨50061209641878570929622515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33374139761252380619748343 50061209641878570929622515)
          ·
            refine ⟨75091814462817856394433773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50061209641878570929622515 75091814462817856394433773)
            ·
              refine ⟨28159430423556696147912665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75091814462817856394433773 28159430423556696147912665)
              ·
                refine ⟨21119572817667522110934499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28159430423556696147912665 21119572817667522110934499)
                ·
                  refine ⟨31679359226501283166401749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21119572817667522110934499 31679359226501283166401749)
                  ·
                    refine ⟨742484981871123824212541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31679359226501283166401749 742484981871123824212541)
                    ·
                      rfl

theorem cell23_4337953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_4337953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4337953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4337953 prefixEnd_4337953 := by exact prefixLift 4337953
  have htrace : WordTrace (prefixWord ++ tailWord_4337953) baseStart_4337953 baseEnd_4337953 := by
    simpa [prefixWord, tailWord_4337953, baseEnd_4337953] using wordTrace_append hprefix tailTrace_4337953
  have hstable : (prefixWord ++ tailWord_4337953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4337953).length < 2 ^ (prefixWord ++ tailWord_4337953).sum := by decide
  have hdescent : baseEnd_4337953 < baseStart_4337953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4337953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338003 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_4338003 : Nat := 118140960795 + 4338003 * 2 ^ 59
def prefixEnd_4338003 : Nat := 4983230072969 + 3 ^ 40 * 4338003 * 2
def baseEnd_4338003 : Nat := 2227480619646096277012393

theorem tailTrace_4338003 : CollatzResearch.WordTrace tailWord_4338003 prefixEnd_4338003 2227480619646096277012393 := by
  unfold tailWord_4338003
  simp only [CollatzResearch.WordTrace]
  refine ⟨158219967703163477773682663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105479978468775651849121775 158219967703163477773682663)
  ·
    refine ⟨237329951554745216660523995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158219967703163477773682663 237329951554745216660523995)
    ·
      refine ⟨355994927332117824990785993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237329951554745216660523995 355994927332117824990785993)
      ·
        refine ⟨266996195499088368743089495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355994927332117824990785993 266996195499088368743089495)
        ·
          refine ⟨400494293248632553114634243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266996195499088368743089495 400494293248632553114634243)
          ·
            refine ⟨600741439872948829671951365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400494293248632553114634243 600741439872948829671951365)
            ·
              refine ⟨112639019976177905563490881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 600741439872948829671951365 112639019976177905563490881)
              ·
                refine ⟨84479264982133429172618161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112639019976177905563490881 84479264982133429172618161)
                ·
                  refine ⟨63359448736600071879463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84479264982133429172618161 63359448736600071879463621)
                  ·
                    refine ⟨11879896638112513477399429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63359448736600071879463621 11879896638112513477399429)
                    ·
                      refine ⟨2227480619646096277012393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11879896638112513477399429 2227480619646096277012393)
                      ·
                        rfl

theorem cell23_4338003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_4338003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338003 prefixEnd_4338003 := by exact prefixLift 4338003
  have htrace : WordTrace (prefixWord ++ tailWord_4338003) baseStart_4338003 baseEnd_4338003 := by
    simpa [prefixWord, tailWord_4338003, baseEnd_4338003] using wordTrace_append hprefix tailTrace_4338003
  have hstable : (prefixWord ++ tailWord_4338003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338003).length < 2 ^ (prefixWord ++ tailWord_4338003).sum := by decide
  have hdescent : baseEnd_4338003 < baseStart_4338003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338010 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_4338010 : Nat := 118140960795 + 4338010 * 2 ^ 59
def prefixEnd_4338010 : Nat := 4983230072969 + 3 ^ 40 * 4338010 * 2
def baseEnd_4338010 : Nat := 2227484214010677749624861

theorem tailTrace_4338010 : CollatzResearch.WordTrace tailWord_4338010 prefixEnd_4338010 2227484214010677749624861 := by
  unfold tailWord_4338010
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555055753534529492296871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105480148676092078646124989 39555055753534529492296871)
  ·
    refine ⟨59332583630301794238445307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39555055753534529492296871 59332583630301794238445307)
    ·
      refine ⟨88998875445452691357667961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59332583630301794238445307 88998875445452691357667961)
      ·
        refine ⟨66749156584089518518250971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88998875445452691357667961 66749156584089518518250971)
        ·
          refine ⟨100123734876134277777376457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66749156584089518518250971 100123734876134277777376457)
          ·
            refine ⟨75092801157100708333032343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100123734876134277777376457 75092801157100708333032343)
            ·
              refine ⟨112639201735651062499548515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75092801157100708333032343 112639201735651062499548515)
              ·
                refine ⟨168958802603476593749322773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112639201735651062499548515 168958802603476593749322773)
                ·
                  refine ⟨7919943872037965331999505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168958802603476593749322773 7919943872037965331999505)
                  ·
                    refine ⟨5939957904028473998999629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7919943872037965331999505 5939957904028473998999629)
                    ·
                      refine ⟨2227484214010677749624861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5939957904028473998999629 2227484214010677749624861)
                      ·
                        rfl

theorem cell23_4338010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_4338010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338010 prefixEnd_4338010 := by exact prefixLift 4338010
  have htrace : WordTrace (prefixWord ++ tailWord_4338010) baseStart_4338010 baseEnd_4338010 := by
    simpa [prefixWord, tailWord_4338010, baseEnd_4338010] using wordTrace_append hprefix tailTrace_4338010
  have hstable : (prefixWord ++ tailWord_4338010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338010).length < 2 ^ (prefixWord ++ tailWord_4338010).sum := by decide
  have hdescent : baseEnd_4338010 < baseStart_4338010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338033 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_4338033 : Nat := 118140960795 + 4338033 * 2 ^ 59
def prefixEnd_4338033 : Nat := 4983230072969 + 3 ^ 40 * 4338033 * 2
def baseEnd_4338033 : Nat := 2227496024065731159637255

theorem tailTrace_4338033 : CollatzResearch.WordTrace tailWord_4338033 prefixEnd_4338033 2227496024065731159637255 := by
  unfold tailWord_4338033
  simp only [CollatzResearch.WordTrace]
  refine ⟨158221061893054792897274753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105480707928703195264849835 158221061893054792897274753)
  ·
    refine ⟨118665796419791094672956065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158221061893054792897274753 118665796419791094672956065)
    ·
      refine ⟨88999347314843321004717049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118665796419791094672956065 88999347314843321004717049)
      ·
        refine ⟨66749510486132490753537787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88999347314843321004717049 66749510486132490753537787)
        ·
          refine ⟨100124265729198736130306681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66749510486132490753537787 100124265729198736130306681)
          ·
            refine ⟨75093199296899052097730011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100124265729198736130306681 75093199296899052097730011)
            ·
              refine ⟨112639798945348578146595017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75093199296899052097730011 112639798945348578146595017)
              ·
                refine ⟨84479849209011433609946263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112639798945348578146595017 84479849209011433609946263)
                ·
                  refine ⟨126719773813517150414919395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84479849209011433609946263 126719773813517150414919395)
                  ·
                    refine ⟨190079660720275725622379093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126719773813517150414919395 190079660720275725622379093)
                    ·
                      refine ⟨2227496024065731159637255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190079660720275725622379093 2227496024065731159637255)
                      ·
                        rfl

theorem cell23_4338033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_4338033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338033 prefixEnd_4338033 := by exact prefixLift 4338033
  have htrace : WordTrace (prefixWord ++ tailWord_4338033) baseStart_4338033 baseEnd_4338033 := by
    simpa [prefixWord, tailWord_4338033, baseEnd_4338033] using wordTrace_append hprefix tailTrace_4338033
  have hstable : (prefixWord ++ tailWord_4338033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338033).length < 2 ^ (prefixWord ++ tailWord_4338033).sum := by decide
  have hdescent : baseEnd_4338033 < baseStart_4338033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338060 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_4338060 : Nat := 118140960795 + 4338060 * 2 ^ 59
def prefixEnd_4338060 : Nat := 4983230072969 + 3 ^ 40 * 4338060 * 2
def baseEnd_4338060 : Nat := 742503296014467517999877

theorem tailTrace_4338060 : CollatzResearch.WordTrace tailWord_4338060 prefixEnd_4338060 742503296014467517999877 := by
  unfold tailWord_4338060
  simp only [CollatzResearch.WordTrace]
  refine ⟨79111023331978488254253817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105481364442637984339005089 79111023331978488254253817)
  ·
    refine ⟨59333267498983866190690363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79111023331978488254253817 59333267498983866190690363)
    ·
      refine ⟨88999901248475799286035545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59333267498983866190690363 88999901248475799286035545)
      ·
        refine ⟨66749925936356849464526659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88999901248475799286035545 66749925936356849464526659)
        ·
          refine ⟨100124888904535274196789989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66749925936356849464526659 100124888904535274196789989)
          ·
            refine ⟨18773416669600363911898123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100124888904535274196789989 18773416669600363911898123)
            ·
              refine ⟨28160125004400545867847185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18773416669600363911898123 28160125004400545867847185)
              ·
                refine ⟨21120093753300409400885389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28160125004400545867847185 21120093753300409400885389)
                ·
                  refine ⟨7920035157487653525332021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21120093753300409400885389 7920035157487653525332021)
                  ·
                    refine ⟨742503296014467517999877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7920035157487653525332021 742503296014467517999877)
                    ·
                      rfl

theorem cell23_4338060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_4338060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338060 prefixEnd_4338060 := by exact prefixLift 4338060
  have htrace : WordTrace (prefixWord ++ tailWord_4338060) baseStart_4338060 baseEnd_4338060 := by
    simpa [prefixWord, tailWord_4338060, baseEnd_4338060] using wordTrace_append hprefix tailTrace_4338060
  have hstable : (prefixWord ++ tailWord_4338060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338060).length < 2 ^ (prefixWord ++ tailWord_4338060).sum := by decide
  have hdescent : baseEnd_4338060 < baseStart_4338060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338074 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4338074 : Nat := 118140960795 + 4338074 * 2 ^ 59
def prefixEnd_4338074 : Nat := 4983230072969 + 3 ^ 40 * 4338074 * 2
def baseEnd_4338074 : Nat := 2227517076772565499224567

theorem tailTrace_4338074 : CollatzResearch.WordTrace tailWord_4338074 prefixEnd_4338074 2227517076772565499224567 := by
  unfold tailWord_4338074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555639321476564224879319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105481704857270837933011517 39555639321476564224879319)
  ·
    refine ⟨59333458982214846337318979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39555639321476564224879319 59333458982214846337318979)
    ·
      refine ⟨89000188473322269505978469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59333458982214846337318979 89000188473322269505978469)
      ·
        refine ⟨16687535338747925532370963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89000188473322269505978469 16687535338747925532370963)
        ·
          refine ⟨25031303008121888298556445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16687535338747925532370963 25031303008121888298556445)
          ·
            refine ⟨9386738628045708111958667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25031303008121888298556445 9386738628045708111958667)
            ·
              refine ⟨14080107942068562167938001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386738628045708111958667 14080107942068562167938001)
              ·
                refine ⟨10560080956551421625953501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14080107942068562167938001 10560080956551421625953501)
                ·
                  refine ⟨3960030358706783109732563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10560080956551421625953501 3960030358706783109732563)
                  ·
                    refine ⟨5940045538060174664598845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960030358706783109732563 5940045538060174664598845)
                    ·
                      refine ⟨2227517076772565499224567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940045538060174664598845 2227517076772565499224567)
                      ·
                        rfl

theorem cell23_4338074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4338074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338074 prefixEnd_4338074 := by exact prefixLift 4338074
  have htrace : WordTrace (prefixWord ++ tailWord_4338074) baseStart_4338074 baseEnd_4338074 := by
    simpa [prefixWord, tailWord_4338074, baseEnd_4338074] using wordTrace_append hprefix tailTrace_4338074
  have hstable : (prefixWord ++ tailWord_4338074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338074).length < 2 ^ (prefixWord ++ tailWord_4338074).sum := by decide
  have hdescent : baseEnd_4338074 < baseStart_4338074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338084 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_4338084 : Nat := 118140960795 + 4338084 * 2 ^ 59
def prefixEnd_4338084 : Nat := 4983230072969 + 3 ^ 40 * 4338084 * 2
def baseEnd_4338084 : Nat := 2227522211579110460099521

theorem tailTrace_4338084 : CollatzResearch.WordTrace tailWord_4338084 prefixEnd_4338084 2227522211579110460099521 := by
  unfold tailWord_4338084
  simp only [CollatzResearch.WordTrace]
  refine ⟨79111461007935014303690653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105481948010580019071587537 79111461007935014303690653)
  ·
    refine ⟨29666797877975630363883995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79111461007935014303690653 29666797877975630363883995)
    ·
      refine ⟨44500196816963445545825993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29666797877975630363883995 44500196816963445545825993)
      ·
        refine ⟨33375147612722584159369495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44500196816963445545825993 33375147612722584159369495)
        ·
          refine ⟨50062721419083876239054243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33375147612722584159369495 50062721419083876239054243)
          ·
            refine ⟨75094082128625814358581365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50062721419083876239054243 75094082128625814358581365)
            ·
              refine ⟨7040070199558670096117003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75094082128625814358581365 7040070199558670096117003)
              ·
                refine ⟨10560105299338005144175505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040070199558670096117003 10560105299338005144175505)
                ·
                  refine ⟨7920078974503503858131629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10560105299338005144175505 7920078974503503858131629)
                  ·
                    refine ⟨2970029615438813946799361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7920078974503503858131629 2970029615438813946799361)
                    ·
                      refine ⟨2227522211579110460099521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970029615438813946799361 2227522211579110460099521)
                      ·
                        rfl

theorem cell23_4338084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_4338084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338084 prefixEnd_4338084 := by exact prefixLift 4338084
  have htrace : WordTrace (prefixWord ++ tailWord_4338084) baseStart_4338084 baseEnd_4338084 := by
    simpa [prefixWord, tailWord_4338084, baseEnd_4338084] using wordTrace_append hprefix tailTrace_4338084
  have hstable : (prefixWord ++ tailWord_4338084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338084).length < 2 ^ (prefixWord ++ tailWord_4338084).sum := by decide
  have hdescent : baseEnd_4338084 < baseStart_4338084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338124 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_4338124 : Nat := 118140960795 + 4338124 * 2 ^ 59
def prefixEnd_4338124 : Nat := 4983230072969 + 3 ^ 40 * 4338124 * 2
def baseEnd_4338124 : Nat := 742514250268430101199779

theorem tailTrace_4338124 : CollatzResearch.WordTrace tailWord_4338124 prefixEnd_4338124 742514250268430101199779 := by
  unfold tailWord_4338124
  simp only [CollatzResearch.WordTrace]
  refine ⟨79112190467862557719418713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105482920623816743625891617 79112190467862557719418713)
  ·
    refine ⟨59334142850896918289564035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79112190467862557719418713 59334142850896918289564035)
    ·
      refine ⟨89001214276345377434346053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59334142850896918289564035 89001214276345377434346053)
      ·
        refine ⟨16687727676814758268939885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89001214276345377434346053 16687727676814758268939885)
        ·
          refine ⟨6257897878805534350852457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16687727676814758268939885 6257897878805534350852457)
          ·
            refine ⟨4693423409104150763139343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257897878805534350852457 4693423409104150763139343)
            ·
              refine ⟨7040135113656226144709015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693423409104150763139343 7040135113656226144709015)
              ·
                refine ⟨10560202670484339217063523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040135113656226144709015 10560202670484339217063523)
                ·
                  refine ⟨15840304005726508825595285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10560202670484339217063523 15840304005726508825595285)
                  ·
                    refine ⟨742514250268430101199779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15840304005726508825595285 742514250268430101199779)
                    ·
                      rfl

theorem cell23_4338124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_4338124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338124 prefixEnd_4338124 := by exact prefixLift 4338124
  have htrace : WordTrace (prefixWord ++ tailWord_4338124) baseStart_4338124 baseEnd_4338124 := by
    simpa [prefixWord, tailWord_4338124, baseEnd_4338124] using wordTrace_append hprefix tailTrace_4338124
  have hstable : (prefixWord ++ tailWord_4338124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338124).length < 2 ^ (prefixWord ++ tailWord_4338124).sum := by decide
  have hdescent : baseEnd_4338124 < baseStart_4338124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338160 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_4338160 : Nat := 118140960795 + 4338160 * 2 ^ 59
def prefixEnd_4338160 : Nat := 4983230072969 + 3 ^ 40 * 4338160 * 2
def baseEnd_4338160 : Nat := 2227561236108852162749171

theorem tailTrace_4338160 : CollatzResearch.WordTrace tailWord_4338160 prefixEnd_4338160 2227561236108852162749171 := by
  unfold tailWord_4338160
  simp only [CollatzResearch.WordTrace]
  refine ⟨79112846981797346793573967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105483795975729795724765289 79112846981797346793573967)
  ·
    refine ⟨118669270472696020190360951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79112846981797346793573967 118669270472696020190360951)
    ·
      refine ⟨178003905709044030285541427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118669270472696020190360951 178003905709044030285541427)
      ·
        refine ⟨267005858563566045428312141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178003905709044030285541427 267005858563566045428312141)
        ·
          refine ⟨100127196961337267035617053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267005858563566045428312141 100127196961337267035617053)
          ·
            refine ⟨37547698860501475138356395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100127196961337267035617053 37547698860501475138356395)
            ·
              refine ⟨56321548290752212707534593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37547698860501475138356395 56321548290752212707534593)
              ·
                refine ⟨42241161218064159530650945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56321548290752212707534593 42241161218064159530650945)
                ·
                  refine ⟨31680870913548119647988209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42241161218064159530650945 31680870913548119647988209)
                  ·
                    refine ⟨23760653185161089735991157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31680870913548119647988209 23760653185161089735991157)
                    ·
                      refine ⟨2227561236108852162749171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23760653185161089735991157 2227561236108852162749171)
                      ·
                        rfl

theorem cell23_4338160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_4338160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338160 prefixEnd_4338160 := by exact prefixLift 4338160
  have htrace : WordTrace (prefixWord ++ tailWord_4338160) baseStart_4338160 baseEnd_4338160 := by
    simpa [prefixWord, tailWord_4338160, baseEnd_4338160] using wordTrace_append hprefix tailTrace_4338160
  have hstable : (prefixWord ++ tailWord_4338160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338160).length < 2 ^ (prefixWord ++ tailWord_4338160).sum := by decide
  have hdescent : baseEnd_4338160 < baseStart_4338160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338165 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4338165 : Nat := 118140960795 + 4338165 * 2 ^ 59
def prefixEnd_4338165 : Nat := 4983230072969 + 3 ^ 40 * 4338165 * 2
def baseEnd_4338165 : Nat := 2227563803512124643186649

theorem tailTrace_4338165 : CollatzResearch.WordTrace tailWord_4338165 prefixEnd_4338165 2227563803512124643186649 := by
  unfold tailWord_4338165
  simp only [CollatzResearch.WordTrace]
  refine ⟨158225876328576579441079949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105483917552384386294053299 158225876328576579441079949)
  ·
    refine ⟨59334703623216217290404981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158225876328576579441079949 59334703623216217290404981)
    ·
      refine ⟨5562628464676520370975467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59334703623216217290404981 5562628464676520370975467)
      ·
        refine ⟨8343942697014780556463201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562628464676520370975467 8343942697014780556463201)
        ·
          refine ⟨6257957022761085417347401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8343942697014780556463201 6257957022761085417347401)
          ·
            refine ⟨4693467767070814063010551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257957022761085417347401 4693467767070814063010551)
            ·
              refine ⟨7040201650606221094515827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693467767070814063010551 7040201650606221094515827)
              ·
                refine ⟨10560302475909331641773741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040201650606221094515827 10560302475909331641773741)
                ·
                  refine ⟨3960113428465999365665153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10560302475909331641773741 3960113428465999365665153)
                  ·
                    refine ⟨2970085071349499524248865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960113428465999365665153 2970085071349499524248865)
                    ·
                      refine ⟨2227563803512124643186649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970085071349499524248865 2227563803512124643186649)
                      ·
                        rfl

theorem cell23_4338165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4338165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338165 prefixEnd_4338165 := by exact prefixLift 4338165
  have htrace : WordTrace (prefixWord ++ tailWord_4338165) baseStart_4338165 baseEnd_4338165 := by
    simpa [prefixWord, tailWord_4338165, baseEnd_4338165] using wordTrace_append hprefix tailTrace_4338165
  have hstable : (prefixWord ++ tailWord_4338165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338165).length < 2 ^ (prefixWord ++ tailWord_4338165).sum := by decide
  have hdescent : baseEnd_4338165 < baseStart_4338165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338181 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_4338181 : Nat := 118140960795 + 4338181 * 2 ^ 59
def prefixEnd_4338181 : Nat := 4983230072969 + 3 ^ 40 * 4338181 * 2
def baseEnd_4338181 : Nat := 2227572019202596580586575

theorem tailTrace_4338181 : CollatzResearch.WordTrace tailWord_4338181 prefixEnd_4338181 2227572019202596580586575 := by
  unfold tailWord_4338181
  simp only [CollatzResearch.WordTrace]
  refine ⟨158226459896518614173662397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105484306597679076115774931 158226459896518614173662397)
  ·
    refine ⟨59334922461194480315123399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158226459896518614173662397 59334922461194480315123399)
    ·
      refine ⟨89002383691791720472685099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59334922461194480315123399 89002383691791720472685099)
      ·
        refine ⟨133503575537687580709027649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89002383691791720472685099 133503575537687580709027649)
        ·
          refine ⟨100127681653265685531770737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133503575537687580709027649 100127681653265685531770737)
          ·
            refine ⟨75095761239949264148828053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100127681653265685531770737 75095761239949264148828053)
            ·
              refine ⟨3520113808122621756976315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75095761239949264148828053 3520113808122621756976315)
              ·
                refine ⟨5280170712183932635464473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520113808122621756976315 5280170712183932635464473)
                ·
                  refine ⟨3960128034137949476598355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5280170712183932635464473 3960128034137949476598355)
                  ·
                    refine ⟨5940192051206924214897533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960128034137949476598355 5940192051206924214897533)
                    ·
                      refine ⟨2227572019202596580586575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940192051206924214897533 2227572019202596580586575)
                      ·
                        rfl

theorem cell23_4338181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_4338181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338181 prefixEnd_4338181 := by exact prefixLift 4338181
  have htrace : WordTrace (prefixWord ++ tailWord_4338181) baseStart_4338181 baseEnd_4338181 := by
    simpa [prefixWord, tailWord_4338181, baseEnd_4338181] using wordTrace_append hprefix tailTrace_4338181
  have hstable : (prefixWord ++ tailWord_4338181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338181).length < 2 ^ (prefixWord ++ tailWord_4338181).sum := by decide
  have hdescent : baseEnd_4338181 < baseStart_4338181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338204 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4338204 : Nat := 118140960795 + 4338204 * 2 ^ 59
def prefixEnd_4338204 : Nat := 4983230072969 + 3 ^ 40 * 4338204 * 2
def baseEnd_4338204 : Nat := 2227583829257649990598969

theorem tailTrace_4338204 : CollatzResearch.WordTrace tailWord_4338204 prefixEnd_4338204 2227583829257649990598969 := by
  unfold tailWord_4338204
  simp only [CollatzResearch.WordTrace]
  refine ⟨79113649387717644550874833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105484865850290192734499777 79113649387717644550874833)
  ·
    refine ⟨59335237040788233413156125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79113649387717644550874833 59335237040788233413156125)
    ·
      refine ⟨22250713890295587529933547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59335237040788233413156125 22250713890295587529933547)
      ·
        refine ⟨33376070835443381294900321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22250713890295587529933547 33376070835443381294900321)
        ·
          refine ⟨25032053126582535971175241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33376070835443381294900321 25032053126582535971175241)
          ·
            refine ⟨18774039844936901978381431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25032053126582535971175241 18774039844936901978381431)
            ·
              refine ⟨28161059767405352967572147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18774039844936901978381431 28161059767405352967572147)
              ·
                refine ⟨42241589651108029451358221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28161059767405352967572147 42241589651108029451358221)
                ·
                  refine ⟨15840596119165511044259333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42241589651108029451358221 15840596119165511044259333)
                  ·
                    refine ⟨2970111772343533320798625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15840596119165511044259333 2970111772343533320798625)
                    ·
                      refine ⟨2227583829257649990598969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970111772343533320798625 2227583829257649990598969)
                      ·
                        rfl

theorem cell23_4338204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4338204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338204 prefixEnd_4338204 := by exact prefixLift 4338204
  have htrace : WordTrace (prefixWord ++ tailWord_4338204) baseStart_4338204 baseEnd_4338204 := by
    simpa [prefixWord, tailWord_4338204, baseEnd_4338204] using wordTrace_append hprefix tailTrace_4338204
  have hstable : (prefixWord ++ tailWord_4338204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338204).length < 2 ^ (prefixWord ++ tailWord_4338204).sum := by decide
  have hdescent : baseEnd_4338204 < baseStart_4338204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338215 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4338215 : Nat := 118140960795 + 4338215 * 2 ^ 59
def prefixEnd_4338215 : Nat := 4983230072969 + 3 ^ 40 * 4338215 * 2
def baseEnd_4338215 : Nat := 2227589477544849447561419

theorem tailTrace_4338215 : CollatzResearch.WordTrace tailWord_4338215 prefixEnd_4338215 2227589477544849447561419 := by
  unfold tailWord_4338215
  simp only [CollatzResearch.WordTrace]
  refine ⟨158227699978395437980400099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105485133318930291986933399 158227699978395437980400099)
  ·
    refine ⟨237341549967593156970600149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158227699978395437980400099 237341549967593156970600149)
    ·
      refine ⟨5562692577365464616498441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 237341549967593156970600149 5562692577365464616498441)
      ·
        refine ⟨4172019433024098462373831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5562692577365464616498441 4172019433024098462373831)
        ·
          refine ⟨6258029149536147693560747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172019433024098462373831 6258029149536147693560747)
          ·
            refine ⟨9387043724304221540341121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6258029149536147693560747 9387043724304221540341121)
            ·
              refine ⟨7040282793228166155255841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9387043724304221540341121 7040282793228166155255841)
              ·
                refine ⟨5280212094921124616441881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7040282793228166155255841 5280212094921124616441881)
                ·
                  refine ⟨3960159071190843462331411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5280212094921124616441881 3960159071190843462331411)
                  ·
                    refine ⟨5940238606786265193497117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960159071190843462331411 5940238606786265193497117)
                    ·
                      refine ⟨2227589477544849447561419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940238606786265193497117 2227589477544849447561419)
                      ·
                        rfl

theorem cell23_4338215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4338215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338215 prefixEnd_4338215 := by exact prefixLift 4338215
  have htrace : WordTrace (prefixWord ++ tailWord_4338215) baseStart_4338215 baseEnd_4338215 := by
    simpa [prefixWord, tailWord_4338215, baseEnd_4338215] using wordTrace_append hprefix tailTrace_4338215
  have hstable : (prefixWord ++ tailWord_4338215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338215).length < 2 ^ (prefixWord ++ tailWord_4338215).sum := by decide
  have hdescent : baseEnd_4338215 < baseStart_4338215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_4338220 : Nat := 118140960795 + 4338220 * 2 ^ 59
def prefixEnd_4338220 : Nat := 4983230072969 + 3 ^ 40 * 4338220 * 2
def baseEnd_4338220 : Nat := 2227592044948121927998895

theorem tailTrace_4338220 : CollatzResearch.WordTrace tailWord_4338220 prefixEnd_4338220 2227592044948121927998895 := by
  unfold tailWord_4338220
  simp only [CollatzResearch.WordTrace]
  refine ⟨79113941171688661917166057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105485254895584882556221409 79113941171688661917166057)
  ·
    refine ⟨59335455878766496437874543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79113941171688661917166057 59335455878766496437874543)
    ·
      refine ⟨89003183818149744656811815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59335455878766496437874543 89003183818149744656811815)
      ·
        refine ⟨133504775727224616985217723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89003183818149744656811815 133504775727224616985217723)
        ·
          refine ⟨200257163590836925477826585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133504775727224616985217723 200257163590836925477826585)
          ·
            refine ⟨150192872693127694108369939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200257163590836925477826585 150192872693127694108369939)
            ·
              refine ⟨225289309039691541162554909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150192872693127694108369939 225289309039691541162554909)
              ·
                refine ⟨84483490889884327935958091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225289309039691541162554909 84483490889884327935958091)
                ·
                  refine ⟨126725236334826491903937137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84483490889884327935958091 126725236334826491903937137)
                  ·
                    refine ⟨95043927251119868927952853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126725236334826491903937137 95043927251119868927952853)
                    ·
                      refine ⟨2227592044948121927998895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95043927251119868927952853 2227592044948121927998895)
                      ·
                        rfl

theorem cell23_4338220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_4338220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338220 prefixEnd_4338220 := by exact prefixLift 4338220
  have htrace : WordTrace (prefixWord ++ tailWord_4338220) baseStart_4338220 baseEnd_4338220 := by
    simpa [prefixWord, tailWord_4338220, baseEnd_4338220] using wordTrace_append hprefix tailTrace_4338220
  have hstable : (prefixWord ++ tailWord_4338220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338220).length < 2 ^ (prefixWord ++ tailWord_4338220).sum := by decide
  have hdescent : baseEnd_4338220 < baseStart_4338220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338257 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_4338257 : Nat := 118140960795 + 4338257 * 2 ^ 59
def prefixEnd_4338257 : Nat := 4983230072969 + 3 ^ 40 * 4338257 * 2
def baseEnd_4338257 : Nat := 742537014577446094412075

theorem tailTrace_4338257 : CollatzResearch.WordTrace tailWord_4338257 prefixEnd_4338257 742537014577446094412075 := by
  unfold tailWord_4338257
  simp only [CollatzResearch.WordTrace]
  refine ⟨158229231844243279153429025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105486154562828852768952683 158229231844243279153429025)
  ·
    refine ⟨118671923883182459365071769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158229231844243279153429025 118671923883182459365071769)
    ·
      refine ⟨89003942912386844523803827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118671923883182459365071769 89003942912386844523803827)
      ·
        refine ⟨133505914368580266785705741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89003942912386844523803827 133505914368580266785705741)
        ·
          refine ⟨50064717888217600044639653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133505914368580266785705741 50064717888217600044639653)
          ·
            refine ⟨9387134604040800008369935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50064717888217600044639653 9387134604040800008369935)
            ·
              refine ⟨14080701906061200012554903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9387134604040800008369935 14080701906061200012554903)
              ·
                refine ⟨21121052859091800018832355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14080701906061200012554903 21121052859091800018832355)
                ·
                  refine ⟨31681579288637700028248533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21121052859091800018832355 31681579288637700028248533)
                  ·
                    refine ⟨742537014577446094412075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31681579288637700028248533 742537014577446094412075)
                    ·
                      rfl

theorem cell23_4338257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_4338257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338257 prefixEnd_4338257 := by exact prefixLift 4338257
  have htrace : WordTrace (prefixWord ++ tailWord_4338257) baseStart_4338257 baseEnd_4338257 := by
    simpa [prefixWord, tailWord_4338257, baseEnd_4338257] using wordTrace_append hprefix tailTrace_4338257
  have hstable : (prefixWord ++ tailWord_4338257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338257).length < 2 ^ (prefixWord ++ tailWord_4338257).sum := by decide
  have hdescent : baseEnd_4338257 < baseStart_4338257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338304 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_4338304 : Nat := 118140960795 + 4338304 * 2 ^ 59
def prefixEnd_4338304 : Nat := 4983230072969 + 3 ^ 40 * 4338304 * 2
def baseEnd_4338304 : Nat := 742545059107699866449503

theorem tailTrace_4338304 : CollatzResearch.WordTrace tailWord_4338304 prefixEnd_4338304 742545059107699866449503 := by
  unfold tailWord_4338304
  simp only [CollatzResearch.WordTrace]
  refine ⟨79115473037536503090194983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105487297383382004120259977 79115473037536503090194983)
  ·
    refine ⟨118673209556304754635292475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79115473037536503090194983 118673209556304754635292475)
    ·
      refine ⟨178009814334457131952938713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118673209556304754635292475 178009814334457131952938713)
      ·
        refine ⟨133507360750842848964704035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178009814334457131952938713 133507360750842848964704035)
        ·
          refine ⟨200261041126264273447056053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133507360750842848964704035 200261041126264273447056053)
          ·
            refine ⟨18774472605587275635661505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200261041126264273447056053 18774472605587275635661505)
            ·
              refine ⟨14080854454190456726746129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18774472605587275635661505 14080854454190456726746129)
              ·
                refine ⟨10560640840642842545059597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14080854454190456726746129 10560640840642842545059597)
                ·
                  refine ⟨3960240315241065954397349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10560640840642842545059597 3960240315241065954397349)
                  ·
                    refine ⟨742545059107699866449503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960240315241065954397349 742545059107699866449503)
                    ·
                      rfl

theorem cell23_4338304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_4338304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338304 prefixEnd_4338304 := by exact prefixLift 4338304
  have htrace : WordTrace (prefixWord ++ tailWord_4338304) baseStart_4338304 baseEnd_4338304 := by
    simpa [prefixWord, tailWord_4338304, baseEnd_4338304] using wordTrace_append hprefix tailTrace_4338304
  have hstable : (prefixWord ++ tailWord_4338304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338304).length < 2 ^ (prefixWord ++ tailWord_4338304).sum := by decide
  have hdescent : baseEnd_4338304 < baseStart_4338304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338334 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4338334 : Nat := 118140960795 + 4338334 * 2 ^ 59
def prefixEnd_4338334 : Nat := 4983230072969 + 3 ^ 40 * 4338334 * 2
def baseEnd_4338334 : Nat := 247516731304748275774819

theorem tailTrace_4338334 : CollatzResearch.WordTrace tailWord_4338334 prefixEnd_4338334 247516731304748275774819 := by
  unfold tailWord_4338334
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779005033120540162997757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105488026843309547535988037 19779005033120540162997757)
  ·
    refine ⟨7417126887420202561124159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19779005033120540162997757 7417126887420202561124159)
    ·
      refine ⟨11125690331130303841686239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7417126887420202561124159 11125690331130303841686239)
      ·
        refine ⟨16688535496695455762529359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125690331130303841686239 16688535496695455762529359)
        ·
          refine ⟨25032803245043183643794039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16688535496695455762529359 25032803245043183643794039)
          ·
            refine ⟨37549204867564775465691059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25032803245043183643794039 37549204867564775465691059)
            ·
              refine ⟨56323807301347163198536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37549204867564775465691059 56323807301347163198536589)
              ·
                refine ⟨21121427738005186199451221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56323807301347163198536589 21121427738005186199451221)
                ·
                  refine ⟨247516731304748275774819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21121427738005186199451221 247516731304748275774819)
                  ·
                    rfl

theorem cell23_4338334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4338334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338334 prefixEnd_4338334 := by exact prefixLift 4338334
  have htrace : WordTrace (prefixWord ++ tailWord_4338334) baseStart_4338334 baseEnd_4338334 := by
    simpa [prefixWord, tailWord_4338334, baseEnd_4338334] using wordTrace_append hprefix tailTrace_4338334
  have hstable : (prefixWord ++ tailWord_4338334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338334).length < 2 ^ (prefixWord ++ tailWord_4338334).sum := by decide
  have hdescent : baseEnd_4338334 < baseStart_4338334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338351 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 6]
def baseStart_4338351 : Nat := 118140960795 + 4338351 * 2 ^ 59
def prefixEnd_4338351 : Nat := 4983230072969 + 3 ^ 40 * 4338351 * 2
def baseEnd_4338351 : Nat := 247517701212651212828977

theorem tailTrace_4338351 : CollatzResearch.WordTrace tailWord_4338351 prefixEnd_4338351 247517701212651212828977 := by
  unfold tailWord_4338351
  simp only [CollatzResearch.WordTrace]
  refine ⟨158232660305902733207350907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105488440203935155471567271 158232660305902733207350907)
  ·
    refine ⟨237348990458854099811026361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158232660305902733207350907 237348990458854099811026361)
    ·
      refine ⟨178011742844140574858269771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237348990458854099811026361 178011742844140574858269771)
      ·
        refine ⟨267017614266210862287404657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178011742844140574858269771 267017614266210862287404657)
        ·
          refine ⟨200263210699658146715553493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267017614266210862287404657 200263210699658146715553493)
          ·
            refine ⟨4693669000773237813645785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200263210699658146715553493 4693669000773237813645785)
            ·
              refine ⟨3520251750579928360234339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693669000773237813645785 3520251750579928360234339)
              ·
                refine ⟨5280377625869892540351509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520251750579928360234339 5280377625869892540351509)
                ·
                  refine ⟨247517701212651212828977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5280377625869892540351509 247517701212651212828977)
                  ·
                    rfl

theorem cell23_4338351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 6].length) (baseStart_4338351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338351 prefixEnd_4338351 := by exact prefixLift 4338351
  have htrace : WordTrace (prefixWord ++ tailWord_4338351) baseStart_4338351 baseEnd_4338351 := by
    simpa [prefixWord, tailWord_4338351, baseEnd_4338351] using wordTrace_append hprefix tailTrace_4338351
  have hstable : (prefixWord ++ tailWord_4338351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338351).length < 2 ^ (prefixWord ++ tailWord_4338351).sum := by decide
  have hdescent : baseEnd_4338351 < baseStart_4338351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338364 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_4338364 : Nat := 118140960795 + 4338364 * 2 ^ 59
def prefixEnd_4338364 : Nat := 4983230072969 + 3 ^ 40 * 4338364 * 2
def baseEnd_4338364 : Nat := 742555328720789788199411

theorem tailTrace_4338364 : CollatzResearch.WordTrace tailWord_4338364 prefixEnd_4338364 742555328720789788199411 := by
  unfold tailWord_4338364
  simp only [CollatzResearch.WordTrace]
  refine ⟨79116567227427818213787073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105488756303237090951716097 79116567227427818213787073)
  ·
    refine ⟨59337425420570863660340305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79116567227427818213787073 59337425420570863660340305)
    ·
      refine ⟨44503069065428147745255229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59337425420570863660340305 44503069065428147745255229)
      ·
        refine ⟨16688650899535555404470711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44503069065428147745255229 16688650899535555404470711)
        ·
          refine ⟨25032976349303333106706067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16688650899535555404470711 25032976349303333106706067)
          ·
            refine ⟨37549464523954999660059101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25032976349303333106706067 37549464523954999660059101)
            ·
              refine ⟨14081049196483124872522163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37549464523954999660059101 14081049196483124872522163)
              ·
                refine ⟨21121573794724687308783245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14081049196483124872522163 21121573794724687308783245)
                ·
                  refine ⟨7920590173021757740793717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21121573794724687308783245 7920590173021757740793717)
                  ·
                    refine ⟨742555328720789788199411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7920590173021757740793717 742555328720789788199411)
                    ·
                      rfl

theorem cell23_4338364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_4338364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338364 prefixEnd_4338364 := by exact prefixLift 4338364
  have htrace : WordTrace (prefixWord ++ tailWord_4338364) baseStart_4338364 baseEnd_4338364 := by
    simpa [prefixWord, tailWord_4338364, baseEnd_4338364] using wordTrace_append hprefix tailTrace_4338364
  have hstable : (prefixWord ++ tailWord_4338364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338364).length < 2 ^ (prefixWord ++ tailWord_4338364).sum := by decide
  have hdescent : baseEnd_4338364 < baseStart_4338364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338384 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2]
def baseStart_4338384 : Nat := 118140960795 + 4338384 * 2 ^ 59
def prefixEnd_4338384 : Nat := 4983230072969 + 3 ^ 40 * 4338384 * 2
def baseEnd_4338384 : Nat := 2227676255775459286348141

theorem tailTrace_4338384 : CollatzResearch.WordTrace tailWord_4338384 prefixEnd_4338384 2227676255775459286348141 := by
  unfold tailWord_4338384
  simp only [CollatzResearch.WordTrace]
  refine ⟨79116931957391589921651103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105489242609855453228868137 79116931957391589921651103)
  ·
    refine ⟨118675397936087384882476655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79116931957391589921651103 118675397936087384882476655)
    ·
      refine ⟨178013096904131077323714983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118675397936087384882476655 178013096904131077323714983)
      ·
        refine ⟨267019645356196615985572475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178013096904131077323714983 267019645356196615985572475)
        ·
          refine ⟨400529468034294923978358713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267019645356196615985572475 400529468034294923978358713)
          ·
            refine ⟨300397101025721192983769035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400529468034294923978358713 300397101025721192983769035)
            ·
              refine ⟨450595651538581789475653553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300397101025721192983769035 450595651538581789475653553)
              ·
                refine ⟨337946738653936342106740165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450595651538581789475653553 337946738653936342106740165)
                ·
                  refine ⟨63365013497613064145013781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337946738653936342106740165 63365013497613064145013781)
                  ·
                    refine ⟨2970235007700612381797521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63365013497613064145013781 2970235007700612381797521)
                    ·
                      refine ⟨2227676255775459286348141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970235007700612381797521 2227676255775459286348141)
                      ·
                        rfl

theorem cell23_4338384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6, 2].length) (baseStart_4338384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338384 prefixEnd_4338384 := by exact prefixLift 4338384
  have htrace : WordTrace (prefixWord ++ tailWord_4338384) baseStart_4338384 baseEnd_4338384 := by
    simpa [prefixWord, tailWord_4338384, baseEnd_4338384] using wordTrace_append hprefix tailTrace_4338384
  have hstable : (prefixWord ++ tailWord_4338384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338384).length < 2 ^ (prefixWord ++ tailWord_4338384).sum := by decide
  have hdescent : baseEnd_4338384 < baseStart_4338384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338389 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_4338389 : Nat := 118140960795 + 4338389 * 2 ^ 59
def prefixEnd_4338389 : Nat := 4983230072969 + 3 ^ 40 * 4338389 * 2
def baseEnd_4338389 : Nat := 742559607726243922261873

theorem tailTrace_4338389 : CollatzResearch.WordTrace tailWord_4338389 prefixEnd_4338389 742559607726243922261873 := by
  unfold tailWord_4338389
  simp only [CollatzResearch.WordTrace]
  refine ⟨158234046279765065697234221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105489364186510043798156147 158234046279765065697234221)
  ·
    refine ⟨59337767354911899636462833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158234046279765065697234221 59337767354911899636462833)
    ·
      refine ⟨44503325516183924727347125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59337767354911899636462833 44503325516183924727347125)
      ·
        refine ⟨4172186767142242943188793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44503325516183924727347125 4172186767142242943188793)
        ·
          refine ⟨3129140075356682207391595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4172186767142242943188793 3129140075356682207391595)
          ·
            refine ⟨4693710113035023311087393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129140075356682207391595 4693710113035023311087393)
            ·
              refine ⟨3520282584776267483315545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693710113035023311087393 3520282584776267483315545)
              ·
                refine ⟨2640211938582200612486659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520282584776267483315545 2640211938582200612486659)
                ·
                  refine ⟨3960317907873300918729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640211938582200612486659 3960317907873300918729989)
                  ·
                    refine ⟨742559607726243922261873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960317907873300918729989 742559607726243922261873)
                    ·
                      rfl

theorem cell23_4338389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_4338389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338389 prefixEnd_4338389 := by exact prefixLift 4338389
  have htrace : WordTrace (prefixWord ++ tailWord_4338389) baseStart_4338389 baseEnd_4338389 := by
    simpa [prefixWord, tailWord_4338389, baseEnd_4338389] using wordTrace_append hprefix tailTrace_4338389
  have hstable : (prefixWord ++ tailWord_4338389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338389).length < 2 ^ (prefixWord ++ tailWord_4338389).sum := by decide
  have hdescent : baseEnd_4338389 < baseStart_4338389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338418 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4338418 : Nat := 118140960795 + 4338418 * 2 ^ 59
def prefixEnd_4338418 : Nat := 4983230072969 + 3 ^ 40 * 4338418 * 2
def baseEnd_4338418 : Nat := 2227693714117712153322985

theorem tailTrace_4338418 : CollatzResearch.WordTrace tailWord_4338418 prefixEnd_4338418 2227693714117712153322985 := by
  unfold tailWord_4338418
  simp only [CollatzResearch.WordTrace]
  refine ⟨39558775999165000912509977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105490069331106669100026605 39558775999165000912509977)
  ·
    refine ⟨29669081999373750684382483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39558775999165000912509977 29669081999373750684382483)
    ·
      refine ⟨44503622999060626026573725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29669081999373750684382483 44503622999060626026573725)
      ·
        refine ⟨16688858624647734759965147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44503622999060626026573725 16688858624647734759965147)
        ·
          refine ⟨25033287936971602139947721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16688858624647734759965147 25033287936971602139947721)
          ·
            refine ⟨18774965952728701604960791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25033287936971602139947721 18774965952728701604960791)
            ·
              refine ⟨28162448929093052407441187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18774965952728701604960791 28162448929093052407441187)
              ·
                refine ⟨42243673393639578611161781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28162448929093052407441187 42243673393639578611161781)
                ·
                  refine ⟨3960344380653710494796417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42243673393639578611161781 3960344380653710494796417)
                  ·
                    refine ⟨2970258285490282871097313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960344380653710494796417 2970258285490282871097313)
                    ·
                      refine ⟨2227693714117712153322985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970258285490282871097313 2227693714117712153322985)
                      ·
                        rfl

theorem cell23_4338418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4338418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338418 prefixEnd_4338418 := by exact prefixLift 4338418
  have htrace : WordTrace (prefixWord ++ tailWord_4338418) baseStart_4338418 baseEnd_4338418 := by
    simpa [prefixWord, tailWord_4338418, baseEnd_4338418] using wordTrace_append hprefix tailTrace_4338418
  have hstable : (prefixWord ++ tailWord_4338418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338418).length < 2 ^ (prefixWord ++ tailWord_4338418).sum := by decide
  have hdescent : baseEnd_4338418 < baseStart_4338418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338424 : List Nat := [2, 1, 2, 1, 1, 2, 7, 7]
def baseStart_4338424 : Nat := 118140960795 + 4338424 * 2 ^ 59
def prefixEnd_4338424 : Nat := 4983230072969 + 3 ^ 40 * 4338424 * 2
def baseEnd_4338424 : Nat := 82507288703764412216591

theorem tailTrace_4338424 : CollatzResearch.WordTrace tailWord_4338424 prefixEnd_4338424 82507288703764412216591 := by
  unfold tailWord_4338424
  simp only [CollatzResearch.WordTrace]
  refine ⟨79117661417319133337379163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105490215223092177783172217 79117661417319133337379163)
  ·
    refine ⟨118676492125978700006068745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79117661417319133337379163 118676492125978700006068745)
    ·
      refine ⟨89007369094484025004551559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118676492125978700006068745 89007369094484025004551559)
      ·
        refine ⟨133511053641726037506827339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89007369094484025004551559 133511053641726037506827339)
        ·
          refine ⟨200266580462589056260241009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133511053641726037506827339 200266580462589056260241009)
          ·
            refine ⟨150199935346941792195180757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200266580462589056260241009 150199935346941792195180757)
            ·
              refine ⟨3520310984693948254574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150199935346941792195180757 3520310984693948254574549)
              ·
                refine ⟨82507288703764412216591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3520310984693948254574549 82507288703764412216591)
                ·
                  rfl

theorem cell23_4338424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 7].length) (baseStart_4338424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338424 prefixEnd_4338424 := by exact prefixLift 4338424
  have htrace : WordTrace (prefixWord ++ tailWord_4338424) baseStart_4338424 baseEnd_4338424 := by
    simpa [prefixWord, tailWord_4338424, baseEnd_4338424] using wordTrace_append hprefix tailTrace_4338424
  have hstable : (prefixWord ++ tailWord_4338424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338424).length < 2 ^ (prefixWord ++ tailWord_4338424).sum := by decide
  have hdescent : baseEnd_4338424 < baseStart_4338424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338427 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_4338427 : Nat := 118140960795 + 4338427 * 2 ^ 59
def prefixEnd_4338427 : Nat := 4983230072969 + 3 ^ 40 * 4338427 * 2
def baseEnd_4338427 : Nat := 2227698335443602618110443

theorem tailTrace_4338427 : CollatzResearch.WordTrace tailWord_4338427 prefixEnd_4338427 2227698335443602618110443 := by
  unfold tailWord_4338427
  simp only [CollatzResearch.WordTrace]
  refine ⟨158235432253627398187117535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105490288169084932124745023 158235432253627398187117535)
  ·
    refine ⟨237353148380441097280676303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158235432253627398187117535 237353148380441097280676303)
    ·
      refine ⟨356029722570661645921014455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237353148380441097280676303 356029722570661645921014455)
      ·
        refine ⟨534044583855992468881521683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356029722570661645921014455 534044583855992468881521683)
        ·
          refine ⟨801066875783988703322282525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534044583855992468881521683 801066875783988703322282525)
          ·
            refine ⟨300400078418995763745855947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 801066875783988703322282525 300400078418995763745855947)
            ·
              refine ⟨450600117628493645618783921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300400078418995763745855947 450600117628493645618783921)
              ·
                refine ⟨337950088221370234214087941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450600117628493645618783921 337950088221370234214087941)
                ·
                  refine ⟨63365641541506918915141489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337950088221370234214087941 63365641541506918915141489)
                  ·
                    refine ⟨47524231156130189186356117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63365641541506918915141489 47524231156130189186356117)
                    ·
                      refine ⟨2227698335443602618110443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47524231156130189186356117 2227698335443602618110443)
                      ·
                        rfl

theorem cell23_4338427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_4338427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338427 prefixEnd_4338427 := by exact prefixLift 4338427
  have htrace : WordTrace (prefixWord ++ tailWord_4338427) baseStart_4338427 baseEnd_4338427 := by
    simpa [prefixWord, tailWord_4338427, baseEnd_4338427] using wordTrace_append hprefix tailTrace_4338427
  have hstable : (prefixWord ++ tailWord_4338427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338427).length < 2 ^ (prefixWord ++ tailWord_4338427).sum := by decide
  have hdescent : baseEnd_4338427 < baseStart_4338427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338451 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 3]
def baseStart_4338451 : Nat := 118140960795 + 4338451 * 2 ^ 59
def prefixEnd_4338451 : Nat := 4983230072969 + 3 ^ 40 * 4338451 * 2
def baseEnd_4338451 : Nat := 2227710658979310524210333

theorem tailTrace_4338451 : CollatzResearch.WordTrace tailWord_4338451 prefixEnd_4338451 2227710658979310524210333 := by
  unfold tailWord_4338451
  simp only [CollatzResearch.WordTrace]
  refine ⟨158236307605540450285991207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105490871737026966857327471 158236307605540450285991207)
  ·
    refine ⟨237354461408310675428986811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158236307605540450285991207 237354461408310675428986811)
    ·
      refine ⟨356031692112466013143480217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237354461408310675428986811 356031692112466013143480217)
      ·
        refine ⟨267023769084349509857610163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356031692112466013143480217 267023769084349509857610163)
        ·
          refine ⟨400535653626524264786415245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267023769084349509857610163 400535653626524264786415245)
          ·
            refine ⟨150200870109946599294905717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400535653626524264786415245 150200870109946599294905717)
            ·
              refine ⟨14081331572807493683897411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150200870109946599294905717 14081331572807493683897411)
              ·
                refine ⟨21121997359211240525846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14081331572807493683897411 21121997359211240525846117)
                ·
                  refine ⟨3960374504852107598596147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21121997359211240525846117 3960374504852107598596147)
                  ·
                    refine ⟨5940561757278161397894221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960374504852107598596147 5940561757278161397894221)
                    ·
                      refine ⟨2227710658979310524210333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940561757278161397894221 2227710658979310524210333)
                      ·
                        rfl

theorem cell23_4338451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_4338451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338451 prefixEnd_4338451 := by exact prefixLift 4338451
  have htrace : WordTrace (prefixWord ++ tailWord_4338451) baseStart_4338451 baseEnd_4338451 := by
    simpa [prefixWord, tailWord_4338451, baseEnd_4338451] using wordTrace_append hprefix tailTrace_4338451
  have hstable : (prefixWord ++ tailWord_4338451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338451).length < 2 ^ (prefixWord ++ tailWord_4338451).sum := by decide
  have hdescent : baseEnd_4338451 < baseStart_4338451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338486 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4338486 : Nat := 118140960795 + 4338486 * 2 ^ 59
def prefixEnd_4338486 : Nat := 4983230072969 + 3 ^ 40 * 4338486 * 2
def baseEnd_4338486 : Nat := 2227728630802217887272673

theorem tailTrace_4338486 : CollatzResearch.WordTrace tailWord_4338486 prefixEnd_4338486 2227728630802217887272673 := by
  unfold tailWord_4338486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889849010025853203969707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105491722773609100842343541 9889849010025853203969707)
  ·
    refine ⟨14834773515038779805954561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889849010025853203969707 14834773515038779805954561)
    ·
      refine ⟨11126080136279084854465921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14834773515038779805954561 11126080136279084854465921)
      ·
        refine ⟨8344560102209313640849441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11126080136279084854465921 8344560102209313640849441)
        ·
          refine ⟨6258420076656985230637081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8344560102209313640849441 6258420076656985230637081)
          ·
            refine ⟨4693815057492738922977811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6258420076656985230637081 4693815057492738922977811)
            ·
              refine ⟨7040722586239108384466717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693815057492738922977811 7040722586239108384466717)
              ·
                refine ⟨2640270969839665644175019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7040722586239108384466717 2640270969839665644175019)
                ·
                  refine ⟨3960406454759498466262529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640270969839665644175019 3960406454759498466262529)
                  ·
                    refine ⟨2970304841069623849696897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960406454759498466262529 2970304841069623849696897)
                    ·
                      refine ⟨2227728630802217887272673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970304841069623849696897 2227728630802217887272673)
                      ·
                        rfl

theorem cell23_4338486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4338486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338486 prefixEnd_4338486 := by exact prefixLift 4338486
  have htrace : WordTrace (prefixWord ++ tailWord_4338486) baseStart_4338486 baseEnd_4338486 := by
    simpa [prefixWord, tailWord_4338486, baseEnd_4338486] using wordTrace_append hprefix tailTrace_4338486
  have hstable : (prefixWord ++ tailWord_4338486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338486).length < 2 ^ (prefixWord ++ tailWord_4338486).sum := by decide
  have hdescent : baseEnd_4338486 < baseStart_4338486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338541 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4338541 : Nat := 118140960795 + 4338541 * 2 ^ 59
def prefixEnd_4338541 : Nat := 4983230072969 + 3 ^ 40 * 4338541 * 2
def baseEnd_4338541 : Nat := 2227756872238215172084919

theorem tailTrace_4338541 : CollatzResearch.WordTrace tailWord_4338541 prefixEnd_4338541 2227756872238215172084919 := by
  unfold tailWord_4338541
  simp only [CollatzResearch.WordTrace]
  refine ⟨158239590175214395656767477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105493060116809597104511651 158239590175214395656767477)
  ·
    refine ⟨14834961578926349592821951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158239590175214395656767477 14834961578926349592821951)
    ·
      refine ⟨22252442368389524389232927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14834961578926349592821951 22252442368389524389232927)
      ·
        refine ⟨33378663552584286583849391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22252442368389524389232927 33378663552584286583849391)
        ·
          refine ⟨50067995328876429875774087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33378663552584286583849391 50067995328876429875774087)
          ·
            refine ⟨75101992993314644813661131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50067995328876429875774087 75101992993314644813661131)
            ·
              refine ⟨112652989489971967220491697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75101992993314644813661131 112652989489971967220491697)
              ·
                refine ⟨84489742117478975415368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112652989489971967220491697 84489742117478975415368773)
                ·
                  refine ⟨15841826647027307890381645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84489742117478975415368773 15841826647027307890381645)
                  ·
                    refine ⟨5940684992635240458893117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15841826647027307890381645 5940684992635240458893117)
                    ·
                      refine ⟨2227756872238215172084919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940684992635240458893117 2227756872238215172084919)
                      ·
                        rfl

theorem cell23_4338541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4338541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338541 prefixEnd_4338541 := by exact prefixLift 4338541
  have htrace : WordTrace (prefixWord ++ tailWord_4338541) baseStart_4338541 baseEnd_4338541 := by
    simpa [prefixWord, tailWord_4338541, baseEnd_4338541] using wordTrace_append hprefix tailTrace_4338541
  have hstable : (prefixWord ++ tailWord_4338541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338541).length < 2 ^ (prefixWord ++ tailWord_4338541).sum := by decide
  have hdescent : baseEnd_4338541 < baseStart_4338541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338544 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_4338544 : Nat := 118140960795 + 4338544 * 2 ^ 59
def prefixEnd_4338544 : Nat := 4983230072969 + 3 ^ 40 * 4338544 * 2
def baseEnd_4338544 : Nat := 742586137560059553449135

theorem tailTrace_4338544 : CollatzResearch.WordTrace tailWord_4338544 prefixEnd_4338544 742586137560059553449135 := by
  unfold tailWord_4338544
  simp only [CollatzResearch.WordTrace]
  refine ⟨79119849797101763584563343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105493133062802351446084457 79119849797101763584563343)
  ·
    refine ⟨118679774695652645376845015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79119849797101763584563343 118679774695652645376845015)
    ·
      refine ⟨178019662043478968065267523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118679774695652645376845015 178019662043478968065267523)
      ·
        refine ⟨267029493065218452097901285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178019662043478968065267523 267029493065218452097901285)
        ·
          refine ⟨50068029949728459768356491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267029493065218452097901285 50068029949728459768356491)
          ·
            refine ⟨75102044924592689652534737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50068029949728459768356491 75102044924592689652534737)
            ·
              refine ⟨56326533693444517239401053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75102044924592689652534737 56326533693444517239401053)
              ·
                refine ⟨21122450135041693964775395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56326533693444517239401053 21122450135041693964775395)
                ·
                  refine ⟨31683675202562540947163093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21122450135041693964775395 31683675202562540947163093)
                  ·
                    refine ⟨742586137560059553449135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31683675202562540947163093 742586137560059553449135)
                    ·
                      rfl

theorem cell23_4338544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_4338544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338544 prefixEnd_4338544 := by exact prefixLift 4338544
  have htrace : WordTrace (prefixWord ++ tailWord_4338544) baseStart_4338544 baseEnd_4338544 := by
    simpa [prefixWord, tailWord_4338544, baseEnd_4338544] using wordTrace_append hprefix tailTrace_4338544
  have hstable : (prefixWord ++ tailWord_4338544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338544).length < 2 ^ (prefixWord ++ tailWord_4338544).sum := by decide
  have hdescent : baseEnd_4338544 < baseStart_4338544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338551 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_4338551 : Nat := 118140960795 + 4338551 * 2 ^ 59
def prefixEnd_4338551 : Nat := 4983230072969 + 3 ^ 40 * 4338551 * 2
def baseEnd_4338551 : Nat := 2227762007044760132959873

theorem tailTrace_4338551 : CollatzResearch.WordTrace tailWord_4338551 prefixEnd_4338551 2227762007044760132959873 := by
  unfold tailWord_4338551
  simp only [CollatzResearch.WordTrace]
  refine ⟨158239954905178167364631507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105493303270118778243087671 158239954905178167364631507)
  ·
    refine ⟨237359932357767251046947261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158239954905178167364631507 237359932357767251046947261)
    ·
      refine ⟨89009974634162719142605223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237359932357767251046947261 89009974634162719142605223)
      ·
        refine ⟨133514961951244078713907835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89009974634162719142605223 133514961951244078713907835)
        ·
          refine ⟨200272442926866118070861753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133514961951244078713907835 200272442926866118070861753)
          ·
            refine ⟨150204332195149588553146315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200272442926866118070861753 150204332195149588553146315)
            ·
              refine ⟨225306498292724382829719473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150204332195149588553146315 225306498292724382829719473)
              ·
                refine ⟨168979873719543287122289605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225306498292724382829719473 168979873719543287122289605)
                ·
                  refine ⟨31683726322414366335429301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168979873719543287122289605 31683726322414366335429301)
                  ·
                    refine ⟨2970349342726346843946497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31683726322414366335429301 2970349342726346843946497)
                    ·
                      refine ⟨2227762007044760132959873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970349342726346843946497 2227762007044760132959873)
                      ·
                        rfl

theorem cell23_4338551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_4338551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338551 prefixEnd_4338551 := by exact prefixLift 4338551
  have htrace : WordTrace (prefixWord ++ tailWord_4338551) baseStart_4338551 baseEnd_4338551 := by
    simpa [prefixWord, tailWord_4338551, baseEnd_4338551] using wordTrace_append hprefix tailTrace_4338551
  have hstable : (prefixWord ++ tailWord_4338551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338551).length < 2 ^ (prefixWord ++ tailWord_4338551).sum := by decide
  have hdescent : baseEnd_4338551 < baseStart_4338551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338565 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 5]
def baseStart_4338565 : Nat := 118140960795 + 4338565 * 2 ^ 59
def prefixEnd_4338565 : Nat := 4983230072969 + 3 ^ 40 * 4338565 * 2
def baseEnd_4338565 : Nat := 247529910641547008687201

theorem tailTrace_4338565 : CollatzResearch.WordTrace tailWord_4338565 prefixEnd_4338565 247529910641547008687201 := by
  unfold tailWord_4338565
  simp only [CollatzResearch.WordTrace]
  refine ⟨158240465527127447755641149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105493643684751631837094099 158240465527127447755641149)
  ·
    refine ⟨59340174572672792908365431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158240465527127447755641149 59340174572672792908365431)
    ·
      refine ⟨89010261859009189362548147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59340174572672792908365431 89010261859009189362548147)
      ·
        refine ⟨133515392788513784043822221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89010261859009189362548147 133515392788513784043822221)
        ·
          refine ⟨50068272295692669016433333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133515392788513784043822221 50068272295692669016433333)
          ·
            refine ⟨4693900527721187720290625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50068272295692669016433333 4693900527721187720290625)
            ·
              refine ⟨3520425395790890790217969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693900527721187720290625 3520425395790890790217969)
              ·
                refine ⟨2640319046843168092663477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520425395790890790217969 2640319046843168092663477)
                ·
                  refine ⟨247529910641547008687201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640319046843168092663477 247529910641547008687201)
                  ·
                    rfl

theorem cell23_4338565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_4338565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338565 prefixEnd_4338565 := by exact prefixLift 4338565
  have htrace : WordTrace (prefixWord ++ tailWord_4338565) baseStart_4338565 baseEnd_4338565 := by
    simpa [prefixWord, tailWord_4338565, baseEnd_4338565] using wordTrace_append hprefix tailTrace_4338565
  have hstable : (prefixWord ++ tailWord_4338565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338565).length < 2 ^ (prefixWord ++ tailWord_4338565).sum := by decide
  have hdescent : baseEnd_4338565 < baseStart_4338565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338568 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4338568 : Nat := 118140960795 + 4338568 * 2 ^ 59
def prefixEnd_4338568 : Nat := 4983230072969 + 3 ^ 40 * 4338568 * 2
def baseEnd_4338568 : Nat := 2227770736215886566447295

theorem tailTrace_4338568 : CollatzResearch.WordTrace tailWord_4338568 prefixEnd_4338568 2227770736215886566447295 := by
  unfold tailWord_4338568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79120287473058289634000179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105493716630744386178666905 79120287473058289634000179)
  ·
    refine ⟨118680431209587434451000269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79120287473058289634000179 118680431209587434451000269)
    ·
      refine ⟨44505161703595287919125101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118680431209587434451000269 44505161703595287919125101)
      ·
        refine ⟨16689435638848232969671913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44505161703595287919125101 16689435638848232969671913)
        ·
          refine ⟨12517076729136174727253935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16689435638848232969671913 12517076729136174727253935)
          ·
            refine ⟨18775615093704262090880903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12517076729136174727253935 18775615093704262090880903)
            ·
              refine ⟨28163422640556393136321355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18775615093704262090880903 28163422640556393136321355)
              ·
                refine ⟨42245133960834589704482033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28163422640556393136321355 42245133960834589704482033)
                ·
                  refine ⟨31683850470625942278361525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42245133960834589704482033 31683850470625942278361525)
                  ·
                    refine ⟨2970360981621182088596393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31683850470625942278361525 2970360981621182088596393)
                    ·
                      refine ⟨2227770736215886566447295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970360981621182088596393 2227770736215886566447295)
                      ·
                        rfl

theorem cell23_4338568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4338568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338568 prefixEnd_4338568 := by exact prefixLift 4338568
  have htrace : WordTrace (prefixWord ++ tailWord_4338568) baseStart_4338568 baseEnd_4338568 := by
    simpa [prefixWord, tailWord_4338568, baseEnd_4338568] using wordTrace_append hprefix tailTrace_4338568
  have hstable : (prefixWord ++ tailWord_4338568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338568).length < 2 ^ (prefixWord ++ tailWord_4338568).sum := by decide
  have hdescent : baseEnd_4338568 < baseStart_4338568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338601 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_4338601 : Nat := 118140960795 + 4338601 * 2 ^ 59
def prefixEnd_4338601 : Nat := 4983230072969 + 3 ^ 40 * 4338601 * 2
def baseEnd_4338601 : Nat := 2227787681077484937334643

theorem tailTrace_4338601 : CollatzResearch.WordTrace tailWord_4338601 prefixEnd_4338601 2227787681077484937334643 := by
  unfold tailWord_4338601
  simp only [CollatzResearch.WordTrace]
  refine ⟨158241778554997025903951657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105494519036664683935967771 158241778554997025903951657)
  ·
    refine ⟨118681333916247769427963743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158241778554997025903951657 118681333916247769427963743)
    ·
      refine ⟨178022000874371654141945615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118681333916247769427963743 178022000874371654141945615)
      ·
        refine ⟨267033001311557481212918423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178022000874371654141945615 267033001311557481212918423)
        ·
          refine ⟨400549501967336221819377635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267033001311557481212918423 400549501967336221819377635)
          ·
            refine ⟨600824252951004332729066453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400549501967336221819377635 600824252951004332729066453)
            ·
              refine ⟨14081818428539164048337495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 600824252951004332729066453 14081818428539164048337495)
              ·
                refine ⟨21122727642808746072506243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14081818428539164048337495 21122727642808746072506243)
                ·
                  refine ⟨31684091464213119108759365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21122727642808746072506243 31684091464213119108759365)
                  ·
                    refine ⟨5940767149539959832892381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31684091464213119108759365 5940767149539959832892381)
                    ·
                      refine ⟨2227787681077484937334643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940767149539959832892381 2227787681077484937334643)
                      ·
                        rfl

theorem cell23_4338601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_4338601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338601 prefixEnd_4338601 := by exact prefixLift 4338601
  have htrace : WordTrace (prefixWord ++ tailWord_4338601) baseStart_4338601 baseEnd_4338601 := by
    simpa [prefixWord, tailWord_4338601, baseEnd_4338601] using wordTrace_append hprefix tailTrace_4338601
  have hstable : (prefixWord ++ tailWord_4338601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338601).length < 2 ^ (prefixWord ++ tailWord_4338601).sum := by decide
  have hdescent : baseEnd_4338601 < baseStart_4338601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338604 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 10]
def baseStart_4338604 : Nat := 118140960795 + 4338604 * 2 ^ 59
def prefixEnd_4338604 : Nat := 4983230072969 + 3 ^ 40 * 4338604 * 2
def baseEnd_4338604 : Nat := 247532135724383158399681

theorem tailTrace_4338604 : CollatzResearch.WordTrace tailWord_4338604 prefixEnd_4338604 247532135724383158399681 := by
  unfold tailWord_4338604
  simp only [CollatzResearch.WordTrace]
  refine ⟨79120943986993078708155433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105494591982657438277540577 79120943986993078708155433)
  ·
    refine ⟨59340707990244809031116575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79120943986993078708155433 59340707990244809031116575)
    ·
      refine ⟨89011061985367213546674863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59340707990244809031116575 89011061985367213546674863)
      ·
        refine ⟨133516592978050820320012295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89011061985367213546674863 133516592978050820320012295)
        ·
          refine ⟨200274889467076230480018443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133516592978050820320012295 200274889467076230480018443)
          ·
            refine ⟨300412334200614345720027665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200274889467076230480018443 300412334200614345720027665)
            ·
              refine ⟨225309250650460759290020749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300412334200614345720027665 225309250650460759290020749)
              ·
                refine ⟨84490968993922784733757781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225309250650460759290020749 84490968993922784733757781)
                ·
                  refine ⟨247532135724383158399681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84490968993922784733757781 247532135724383158399681)
                  ·
                    rfl

theorem cell23_4338604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_4338604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338604 prefixEnd_4338604 := by exact prefixLift 4338604
  have htrace : WordTrace (prefixWord ++ tailWord_4338604) baseStart_4338604 baseEnd_4338604 := by
    simpa [prefixWord, tailWord_4338604, baseEnd_4338604] using wordTrace_append hprefix tailTrace_4338604
  have hstable : (prefixWord ++ tailWord_4338604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338604).length < 2 ^ (prefixWord ++ tailWord_4338604).sum := by decide
  have hdescent : baseEnd_4338604 < baseStart_4338604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338691 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3]
def baseStart_4338691 : Nat := 118140960795 + 4338691 * 2 ^ 59
def prefixEnd_4338691 : Nat := 4983230072969 + 3 ^ 40 * 4338691 * 2
def baseEnd_4338691 : Nat := 2227833894336389585209229

theorem tailTrace_4338691 : CollatzResearch.WordTrace tailWord_4338691 prefixEnd_4338691 2227833894336389585209229 := by
  unfold tailWord_4338691
  simp only [CollatzResearch.WordTrace]
  refine ⟨158245061124670971274727927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105496707416447314183151951 158245061124670971274727927)
  ·
    refine ⟨237367591687006456912091891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158245061124670971274727927 237367591687006456912091891)
    ·
      refine ⟨356051387530509685368137837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237367591687006456912091891 356051387530509685368137837)
      ·
        refine ⟨133519270323941132013051689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356051387530509685368137837 133519270323941132013051689)
        ·
          refine ⟨100139452742955849009788767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133519270323941132013051689 100139452742955849009788767)
          ·
            refine ⟨150209179114433773514683151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100139452742955849009788767 150209179114433773514683151)
            ·
              refine ⟨225313768671650660272024727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150209179114433773514683151 225313768671650660272024727)
              ·
                refine ⟨337970653007475990408037091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225313768671650660272024727 337970653007475990408037091)
                ·
                  refine ⟨506955979511213985612055637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337970653007475990408037091 506955979511213985612055637)
                  ·
                    refine ⟨5940890384897038893891277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 506955979511213985612055637 5940890384897038893891277)
                    ·
                      refine ⟨2227833894336389585209229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940890384897038893891277 2227833894336389585209229)
                      ·
                        rfl

theorem cell23_4338691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_4338691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338691 prefixEnd_4338691 := by exact prefixLift 4338691
  have htrace : WordTrace (prefixWord ++ tailWord_4338691) baseStart_4338691 baseEnd_4338691 := by
    simpa [prefixWord, tailWord_4338691, baseEnd_4338691] using wordTrace_append hprefix tailTrace_4338691
  have hstable : (prefixWord ++ tailWord_4338691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338691).length < 2 ^ (prefixWord ++ tailWord_4338691).sum := by decide
  have hdescent : baseEnd_4338691 < baseStart_4338691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338705 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_4338705 : Nat := 118140960795 + 4338705 * 2 ^ 59
def prefixEnd_4338705 : Nat := 4983230072969 + 3 ^ 40 * 4338705 * 2
def baseEnd_4338705 : Nat := 2227841083065552530434165

theorem tailTrace_4338705 : CollatzResearch.WordTrace tailWord_4338705 prefixEnd_4338705 2227841083065552530434165 := by
  unfold tailWord_4338705
  simp only [CollatzResearch.WordTrace]
  refine ⟨158245571746620251665737569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105497047831080167777158379 158245571746620251665737569)
  ·
    refine ⟨118684178809965188749303177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158245571746620251665737569 118684178809965188749303177)
    ·
      refine ⟨89013134107473891561977383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118684178809965188749303177 89013134107473891561977383)
      ·
        refine ⟨133519701161210837342966075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89013134107473891561977383 133519701161210837342966075)
        ·
          refine ⟨200279551741816256014449113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133519701161210837342966075 200279551741816256014449113)
          ·
            refine ⟨150209663806362192010836835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200279551741816256014449113 150209663806362192010836835)
            ·
              refine ⟨225314495709543288016255253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150209663806362192010836835 225314495709543288016255253)
              ·
                refine ⟨10561616986384841625761965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225314495709543288016255253 10561616986384841625761965)
                ·
                  refine ⟨3960606369894315609660737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10561616986384841625761965 3960606369894315609660737)
                  ·
                    refine ⟨2970454777420736707245553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960606369894315609660737 2970454777420736707245553)
                    ·
                      refine ⟨2227841083065552530434165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970454777420736707245553 2227841083065552530434165)
                      ·
                        rfl

theorem cell23_4338705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_4338705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338705 prefixEnd_4338705 := by exact prefixLift 4338705
  have htrace : WordTrace (prefixWord ++ tailWord_4338705) baseStart_4338705 baseEnd_4338705 := by
    simpa [prefixWord, tailWord_4338705, baseEnd_4338705] using wordTrace_append hprefix tailTrace_4338705
  have hstable : (prefixWord ++ tailWord_4338705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338705).length < 2 ^ (prefixWord ++ tailWord_4338705).sum := by decide
  have hdescent : baseEnd_4338705 < baseStart_4338705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338722 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_4338722 : Nat := 118140960795 + 4338722 * 2 ^ 59
def prefixEnd_4338722 : Nat := 4983230072969 + 3 ^ 40 * 4338722 * 2
def baseEnd_4338722 : Nat := 2227849812236678963921587

theorem tailTrace_4338722 : CollatzResearch.WordTrace tailWord_4338722 prefixEnd_4338722 2227849812236678963921587 := by
  unfold tailWord_4338722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561547946889665892276605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105497461191705775712737613 39561547946889665892276605)
  ·
    refine ⟨14835580480083624709603727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39561547946889665892276605 14835580480083624709603727)
    ·
      refine ⟨22253370720125437064405591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835580480083624709603727 22253370720125437064405591)
      ·
        refine ⟨33380056080188155596608387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22253370720125437064405591 33380056080188155596608387)
        ·
          refine ⟨50070084120282233394912581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33380056080188155596608387 50070084120282233394912581)
          ·
            refine ⟨9388140772552918761546109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50070084120282233394912581 9388140772552918761546109)
            ·
              refine ⟨3520552789707344535579791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9388140772552918761546109 3520552789707344535579791)
              ·
                refine ⟨5280829184561016803369687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520552789707344535579791 5280829184561016803369687)
                ·
                  refine ⟨7921243776841525205054531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5280829184561016803369687 7921243776841525205054531)
                  ·
                    refine ⟨11881865665262287807581797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7921243776841525205054531 11881865665262287807581797)
                    ·
                      refine ⟨2227849812236678963921587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11881865665262287807581797 2227849812236678963921587)
                      ·
                        rfl

theorem cell23_4338722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_4338722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338722 prefixEnd_4338722 := by exact prefixLift 4338722
  have htrace : WordTrace (prefixWord ++ tailWord_4338722) baseStart_4338722 baseEnd_4338722 := by
    simpa [prefixWord, tailWord_4338722, baseEnd_4338722] using wordTrace_append hprefix tailTrace_4338722
  have hstable : (prefixWord ++ tailWord_4338722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338722).length < 2 ^ (prefixWord ++ tailWord_4338722).sum := by decide
  have hdescent : baseEnd_4338722 < baseStart_4338722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338738 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_4338738 : Nat := 118140960795 + 4338738 * 2 ^ 59
def prefixEnd_4338738 : Nat := 4983230072969 + 3 ^ 40 * 4338738 * 2
def baseEnd_4338738 : Nat := 2227858027927150901321513

theorem tailTrace_4338738 : CollatzResearch.WordTrace tailWord_4338738 prefixEnd_4338738 2227858027927150901321513 := by
  unfold tailWord_4338738
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561693838875174575422217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105497850237000465534459245 39561693838875174575422217)
  ·
    refine ⟨29671270379156380931566663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39561693838875174575422217 29671270379156380931566663)
    ·
      refine ⟨44506905568734571397349995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29671270379156380931566663 44506905568734571397349995)
      ·
        refine ⟨66760358353101857096024993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44506905568734571397349995 66760358353101857096024993)
        ·
          refine ⟨50070268764826392822018745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66760358353101857096024993 50070268764826392822018745)
          ·
            refine ⟨37552701573619794616514059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50070268764826392822018745 37552701573619794616514059)
            ·
              refine ⟨56329052360429691924771089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37552701573619794616514059 56329052360429691924771089)
              ·
                refine ⟨42246789270322268943578317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56329052360429691924771089 42246789270322268943578317)
                ·
                  refine ⟨15842545976370850853841869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42246789270322268943578317 15842545976370850853841869)
                  ·
                    refine ⟨5940954741139069070190701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15842545976370850853841869 5940954741139069070190701)
                    ·
                      refine ⟨2227858027927150901321513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940954741139069070190701 2227858027927150901321513)
                      ·
                        rfl

theorem cell23_4338738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_4338738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338738 prefixEnd_4338738 := by exact prefixLift 4338738
  have htrace : WordTrace (prefixWord ++ tailWord_4338738) baseStart_4338738 baseEnd_4338738 := by
    simpa [prefixWord, tailWord_4338738, baseEnd_4338738] using wordTrace_append hprefix tailTrace_4338738
  have hstable : (prefixWord ++ tailWord_4338738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338738).length < 2 ^ (prefixWord ++ tailWord_4338738).sum := by decide
  have hdescent : baseEnd_4338738 < baseStart_4338738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338751 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_4338751 : Nat := 118140960795 + 4338751 * 2 ^ 59
def prefixEnd_4338751 : Nat := 4983230072969 + 3 ^ 40 * 4338751 * 2
def baseEnd_4338751 : Nat := 2227864703175659350458953

theorem tailTrace_4338751 : CollatzResearch.WordTrace tailWord_4338751 prefixEnd_4338751 2227864703175659350458953 := by
  unfold tailWord_4338751
  simp only [CollatzResearch.WordTrace]
  refine ⟨158247249504453601521912107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105498166336302401014608071 158247249504453601521912107)
  ·
    refine ⟨237370874256680402282868161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158247249504453601521912107 237370874256680402282868161)
    ·
      refine ⟨178028155692510301712151121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237370874256680402282868161 178028155692510301712151121)
      ·
        refine ⟨133521116769382726284113341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178028155692510301712151121 133521116769382726284113341)
        ·
          refine ⟨50070418788518522356542503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133521116769382726284113341 50070418788518522356542503)
          ·
            refine ⟨75105628182777783534813755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50070418788518522356542503 75105628182777783534813755)
            ·
              refine ⟨112658442274166675302220633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75105628182777783534813755 112658442274166675302220633)
              ·
                refine ⟨84493831705625006476665475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112658442274166675302220633 84493831705625006476665475)
                ·
                  refine ⟨126740747558437509714998213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84493831705625006476665475 126740747558437509714998213)
                  ·
                    refine ⟨23763890167207033071562165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126740747558437509714998213 23763890167207033071562165)
                    ·
                      refine ⟨2227864703175659350458953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23763890167207033071562165 2227864703175659350458953)
                      ·
                        rfl

theorem cell23_4338751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_4338751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338751 prefixEnd_4338751 := by exact prefixLift 4338751
  have htrace : WordTrace (prefixWord ++ tailWord_4338751) baseStart_4338751 baseEnd_4338751 := by
    simpa [prefixWord, tailWord_4338751, baseEnd_4338751] using wordTrace_append hprefix tailTrace_4338751
  have hstable : (prefixWord ++ tailWord_4338751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338751).length < 2 ^ (prefixWord ++ tailWord_4338751).sum := by decide
  have hdescent : baseEnd_4338751 < baseStart_4338751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338755 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 3]
def baseStart_4338755 : Nat := 118140960795 + 4338755 * 2 ^ 59
def prefixEnd_4338755 : Nat := 4983230072969 + 3 ^ 40 * 4338755 * 2
def baseEnd_4338755 : Nat := 2227866757098277334808935

theorem tailTrace_4338755 : CollatzResearch.WordTrace tailWord_4338755 prefixEnd_4338755 2227866757098277334808935 := by
  unfold tailWord_4338755
  simp only [CollatzResearch.WordTrace]
  refine ⟨158247395396439110205057719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105498263597626073470038479 158247395396439110205057719)
  ·
    refine ⟨237371093094658665307586579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158247395396439110205057719 237371093094658665307586579)
    ·
      refine ⟨356056639641987997961379869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237371093094658665307586579 356056639641987997961379869)
      ·
        refine ⟨133521239865745499235517451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356056639641987997961379869 133521239865745499235517451)
        ·
          refine ⟨200281859798618248853276177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133521239865745499235517451 200281859798618248853276177)
          ·
            refine ⟨150211394848963686639957133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200281859798618248853276177 150211394848963686639957133)
            ·
              refine ⟨56329273068361382489983925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150211394848963686639957133 56329273068361382489983925)
              ·
                refine ⟨5280869350158879608435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56329273068361382489983925 5280869350158879608435993)
                ·
                  refine ⟨3960652012619159706326995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5280869350158879608435993 3960652012619159706326995)
                  ·
                    refine ⟨5940978018928739559490493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960652012619159706326995 5940978018928739559490493)
                    ·
                      refine ⟨2227866757098277334808935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5940978018928739559490493 2227866757098277334808935)
                      ·
                        rfl

theorem cell23_4338755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_4338755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338755 prefixEnd_4338755 := by exact prefixLift 4338755
  have htrace : WordTrace (prefixWord ++ tailWord_4338755) baseStart_4338755 baseEnd_4338755 := by
    simpa [prefixWord, tailWord_4338755, baseEnd_4338755] using wordTrace_append hprefix tailTrace_4338755
  have hstable : (prefixWord ++ tailWord_4338755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338755).length < 2 ^ (prefixWord ++ tailWord_4338755).sum := by decide
  have hdescent : baseEnd_4338755 < baseStart_4338755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 6]
def baseStart_4338771 : Nat := 118140960795 + 4338771 * 2 ^ 59
def prefixEnd_4338771 : Nat := 4983230072969 + 3 ^ 40 * 4338771 * 2
def baseEnd_4338771 : Nat := 742624990929583090736287

theorem tailTrace_4338771 : CollatzResearch.WordTrace tailWord_4338771 prefixEnd_4338771 742624990929583090736287 := by
  unfold tailWord_4338771
  simp only [CollatzResearch.WordTrace]
  refine ⟨158247978964381144937640167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105498652642920763291760111 158247978964381144937640167)
  ·
    refine ⟨237371968446571717406460251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158247978964381144937640167 237371968446571717406460251)
    ·
      refine ⟨356057952669857576109690377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237371968446571717406460251 356057952669857576109690377)
      ·
        refine ⟨267043464502393182082267783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356057952669857576109690377 267043464502393182082267783)
        ·
          refine ⟨400565196753589773123401675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267043464502393182082267783 400565196753589773123401675)
          ·
            refine ⟨600847795130384659685102513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400565196753589773123401675 600847795130384659685102513)
            ·
              refine ⟨450635846347788494763826885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600847795130384659685102513 450635846347788494763826885)
              ·
                refine ⟨84494221190210342768217541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450635846347788494763826885 84494221190210342768217541)
                ·
                  refine ⟨15842666473164439269040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84494221190210342768217541 15842666473164439269040789)
                  ·
                    refine ⟨742624990929583090736287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15842666473164439269040789 742624990929583090736287)
                    ·
                      rfl

theorem cell23_4338771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_4338771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338771 prefixEnd_4338771 := by exact prefixLift 4338771
  have htrace : WordTrace (prefixWord ++ tailWord_4338771) baseStart_4338771 baseEnd_4338771 := by
    simpa [prefixWord, tailWord_4338771, baseEnd_4338771] using wordTrace_append hprefix tailTrace_4338771
  have hstable : (prefixWord ++ tailWord_4338771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338771).length < 2 ^ (prefixWord ++ tailWord_4338771).sum := by decide
  have hdescent : baseEnd_4338771 < baseStart_4338771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338808 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_4338808 : Nat := 118140960795 + 4338808 * 2 ^ 59
def prefixEnd_4338808 : Nat := 4983230072969 + 3 ^ 40 * 4338808 * 2
def baseEnd_4338808 : Nat := 2227893971572965627446191

theorem tailTrace_4338808 : CollatzResearch.WordTrace tailWord_4338808 prefixEnd_4338808 2227893971572965627446191 := by
  unfold tailWord_4338808
  simp only [CollatzResearch.WordTrace]
  refine ⟨79124664232623550128368539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105499552310164733504491385 79124664232623550128368539)
  ·
    refine ⟨118686996348935325192552809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79124664232623550128368539 118686996348935325192552809)
    ·
      refine ⟨89015247261701493894414607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118686996348935325192552809 89015247261701493894414607)
      ·
        refine ⟨133522870892552240841621911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89015247261701493894414607 133522870892552240841621911)
        ·
          refine ⟨200284306338828361262432867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133522870892552240841621911 200284306338828361262432867)
          ·
            refine ⟨300426459508242541893649301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200284306338828361262432867 300426459508242541893649301)
            ·
              refine ⟨14082490289448869151264811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 300426459508242541893649301 14082490289448869151264811)
              ·
                refine ⟨21123735434173303726897217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14082490289448869151264811 21123735434173303726897217)
                ·
                  refine ⟨15842801575629977795172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21123735434173303726897217 15842801575629977795172913)
                  ·
                    refine ⟨11882101181722483346379685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15842801575629977795172913 11882101181722483346379685)
                    ·
                      refine ⟨2227893971572965627446191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11882101181722483346379685 2227893971572965627446191)
                      ·
                        rfl

theorem cell23_4338808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_4338808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338808 prefixEnd_4338808 := by exact prefixLift 4338808
  have htrace : WordTrace (prefixWord ++ tailWord_4338808) baseStart_4338808 baseEnd_4338808 := by
    simpa [prefixWord, tailWord_4338808, baseEnd_4338808] using wordTrace_append hprefix tailTrace_4338808
  have hstable : (prefixWord ++ tailWord_4338808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338808).length < 2 ^ (prefixWord ++ tailWord_4338808).sum := by decide
  have hdescent : baseEnd_4338808 < baseStart_4338808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338811 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_4338811 : Nat := 118140960795 + 4338811 * 2 ^ 59
def prefixEnd_4338811 : Nat := 4983230072969 + 3 ^ 40 * 4338811 * 2
def baseEnd_4338811 : Nat := 2227895512014929115708677

theorem tailTrace_4338811 : CollatzResearch.WordTrace tailWord_4338811 prefixEnd_4338811 2227895512014929115708677 := by
  unfold tailWord_4338811
  simp only [CollatzResearch.WordTrace]
  refine ⟨158249437884236231769096287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105499625256157487846064191 158249437884236231769096287)
  ·
    refine ⟨237374156826354347653644431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158249437884236231769096287 237374156826354347653644431)
    ·
      refine ⟨356061235239531521480466647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237374156826354347653644431 356061235239531521480466647)
      ·
        refine ⟨534091852859297282220699971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356061235239531521480466647 534091852859297282220699971)
        ·
          refine ⟨801137779288945923331049957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534091852859297282220699971 801137779288945923331049957)
          ·
            refine ⟨150213333616677360624571867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 801137779288945923331049957 150213333616677360624571867)
            ·
              refine ⟨225320000425016040936857801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150213333616677360624571867 225320000425016040936857801)
              ·
                refine ⟨168990000318762030702643351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225320000425016040936857801 168990000318762030702643351)
                ·
                  refine ⟨253485000478143046053965027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168990000318762030702643351 253485000478143046053965027)
                  ·
                    refine ⟨380227500717214569080947541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253485000478143046053965027 380227500717214569080947541)
                    ·
                      refine ⟨2227895512014929115708677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 380227500717214569080947541 2227895512014929115708677)
                      ·
                        rfl

theorem cell23_4338811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_4338811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338811 prefixEnd_4338811 := by exact prefixLift 4338811
  have htrace : WordTrace (prefixWord ++ tailWord_4338811) baseStart_4338811 baseEnd_4338811 := by
    simpa [prefixWord, tailWord_4338811, baseEnd_4338811] using wordTrace_append hprefix tailTrace_4338811
  have hstable : (prefixWord ++ tailWord_4338811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338811).length < 2 ^ (prefixWord ++ tailWord_4338811).sum := by decide
  have hdescent : baseEnd_4338811 < baseStart_4338811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338828 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4338828 : Nat := 118140960795 + 4338828 * 2 ^ 59
def prefixEnd_4338828 : Nat := 4983230072969 + 3 ^ 40 * 4338828 * 2
def baseEnd_4338828 : Nat := 2227904241186055549196099

theorem tailTrace_4338828 : CollatzResearch.WordTrace tailWord_4338828 prefixEnd_4338828 2227904241186055549196099 := by
  unfold tailWord_4338828
  simp only [CollatzResearch.WordTrace]
  refine ⟨79125028962587321836232569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105500038616783095781643425 79125028962587321836232569)
  ·
    refine ⟨59343771721940491377174427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79125028962587321836232569 59343771721940491377174427)
    ·
      refine ⟨89015657582910737065761641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59343771721940491377174427 89015657582910737065761641)
      ·
        refine ⟨66761743187183052799321231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89015657582910737065761641 66761743187183052799321231)
        ·
          refine ⟨100142614780774579198981847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66761743187183052799321231 100142614780774579198981847)
          ·
            refine ⟨150213922171161868798472771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100142614780774579198981847 150213922171161868798472771)
            ·
              refine ⟨225320883256742803197709157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150213922171161868798472771 225320883256742803197709157)
              ·
                refine ⟨42247665610639275599570467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225320883256742803197709157 42247665610639275599570467)
                ·
                  refine ⟨63371498415958913399355701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42247665610639275599570467 63371498415958913399355701)
                  ·
                    refine ⟨5941077976496148131189597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63371498415958913399355701 5941077976496148131189597)
                    ·
                      refine ⟨2227904241186055549196099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5941077976496148131189597 2227904241186055549196099)
                      ·
                        rfl

theorem cell23_4338828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4338828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338828 prefixEnd_4338828 := by exact prefixLift 4338828
  have htrace : WordTrace (prefixWord ++ tailWord_4338828) baseStart_4338828 baseEnd_4338828 := by
    simpa [prefixWord, tailWord_4338828, baseEnd_4338828] using wordTrace_append hprefix tailTrace_4338828
  have hstable : (prefixWord ++ tailWord_4338828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338828).length < 2 ^ (prefixWord ++ tailWord_4338828).sum := by decide
  have hdescent : baseEnd_4338828 < baseStart_4338828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338835 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 5]
def baseStart_4338835 : Nat := 118140960795 + 4338835 * 2 ^ 59
def prefixEnd_4338835 : Nat := 4983230072969 + 3 ^ 40 * 4338835 * 2
def baseEnd_4338835 : Nat := 247545315061181891312063

theorem tailTrace_4338835 : CollatzResearch.WordTrace tailWord_4338835 prefixEnd_4338835 247545315061181891312063 := by
  unfold tailWord_4338835
  simp only [CollatzResearch.WordTrace]
  refine ⟨158250313236149283867969959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105500208824099522578646639 158250313236149283867969959)
  ·
    refine ⟨237375469854223925801954939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158250313236149283867969959 237375469854223925801954939)
    ·
      refine ⟨356063204781335888702932409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237375469854223925801954939 356063204781335888702932409)
      ·
        refine ⟨267047403586001916527199307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356063204781335888702932409 267047403586001916527199307)
        ·
          refine ⟨400571105379002874790798961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267047403586001916527199307 400571105379002874790798961)
          ·
            refine ⟨300428329034252156093099221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400571105379002874790798961 300428329034252156093099221)
            ·
              refine ⟨7041288961740284908432013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 300428329034252156093099221 7041288961740284908432013)
              ·
                refine ⟨2640483360652606840662005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7041288961740284908432013 2640483360652606840662005)
                ·
                  refine ⟨247545315061181891312063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640483360652606840662005 247545315061181891312063)
                  ·
                    rfl

theorem cell23_4338835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 5].length) (baseStart_4338835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338835 prefixEnd_4338835 := by exact prefixLift 4338835
  have htrace : WordTrace (prefixWord ++ tailWord_4338835) baseStart_4338835 baseEnd_4338835 := by
    simpa [prefixWord, tailWord_4338835, baseEnd_4338835] using wordTrace_append hprefix tailTrace_4338835
  have hstable : (prefixWord ++ tailWord_4338835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338835).length < 2 ^ (prefixWord ++ tailWord_4338835).sum := by decide
  have hdescent : baseEnd_4338835 < baseStart_4338835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_4338885 : Nat := 118140960795 + 4338885 * 2 ^ 59
def prefixEnd_4338885 : Nat := 4983230072969 + 3 ^ 40 * 4338885 * 2
def baseEnd_4338885 : Nat := 2227933509583361826183337

theorem tailTrace_4338885 : CollatzResearch.WordTrace tailWord_4338885 prefixEnd_4338885 2227933509583361826183337 := by
  unfold tailWord_4338885
  simp only [CollatzResearch.WordTrace]
  refine ⟨158252136885968142407290109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105501424590645428271526739 158252136885968142407290109)
  ·
    refine ⟨59344551332238053402733791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158252136885968142407290109 59344551332238053402733791)
    ·
      refine ⟨89016826998357080104100687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59344551332238053402733791 89016826998357080104100687)
      ·
        refine ⟨133525240497535620156151031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89016826998357080104100687 133525240497535620156151031)
        ·
          refine ⟨200287860746303430234226547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133525240497535620156151031 200287860746303430234226547)
          ·
            refine ⟨300431791119455145351339821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200287860746303430234226547 300431791119455145351339821)
            ·
              refine ⟨112661921669795679506752433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300431791119455145351339821 112661921669795679506752433)
              ·
                refine ⟨84496441252346759630064325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112661921669795679506752433 84496441252346759630064325)
                ·
                  refine ⟨15843082734815017430637061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84496441252346759630064325 15843082734815017430637061)
                  ·
                    refine ⟨2970578012777815768244449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15843082734815017430637061 2970578012777815768244449)
                    ·
                      refine ⟨2227933509583361826183337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970578012777815768244449 2227933509583361826183337)
                      ·
                        rfl

theorem cell23_4338885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_4338885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338885 prefixEnd_4338885 := by exact prefixLift 4338885
  have htrace : WordTrace (prefixWord ++ tailWord_4338885) baseStart_4338885 baseEnd_4338885 := by
    simpa [prefixWord, tailWord_4338885, baseEnd_4338885] using wordTrace_append hprefix tailTrace_4338885
  have hstable : (prefixWord ++ tailWord_4338885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338885).length < 2 ^ (prefixWord ++ tailWord_4338885).sum := by decide
  have hdescent : baseEnd_4338885 < baseStart_4338885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338919 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4338919 : Nat := 118140960795 + 4338919 * 2 ^ 59
def prefixEnd_4338919 : Nat := 4983230072969 + 3 ^ 40 * 4338919 * 2
def baseEnd_4338919 : Nat := 2227950967925614693158181

theorem tailTrace_4338919 : CollatzResearch.WordTrace tailWord_4338919 prefixEnd_4338919 2227950967925614693158181 := by
  unfold tailWord_4338919
  simp only [CollatzResearch.WordTrace]
  refine ⟨158253376967844966214027811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105502251311896644142685207 158253376967844966214027811)
  ·
    refine ⟨237380065451767449321041717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158253376967844966214027811 237380065451767449321041717)
    ·
      refine ⟨22254381136103198373847661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237380065451767449321041717 22254381136103198373847661)
      ·
        refine ⟨8345392926038699390192873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22254381136103198373847661 8345392926038699390192873)
        ·
          refine ⟨6259044694529024542644655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8345392926038699390192873 6259044694529024542644655)
          ·
            refine ⟨9388567041793536813966983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259044694529024542644655 9388567041793536813966983)
            ·
              refine ⟨14082850562690305220950475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9388567041793536813966983 14082850562690305220950475)
              ·
                refine ⟨21124275844035457831425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14082850562690305220950475 21124275844035457831425713)
                ·
                  refine ⟨15843206883026593373569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21124275844035457831425713 15843206883026593373569285)
                  ·
                    refine ⟨2970601290567486257544241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15843206883026593373569285 2970601290567486257544241)
                    ·
                      refine ⟨2227950967925614693158181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970601290567486257544241 2227950967925614693158181)
                      ·
                        rfl

theorem cell23_4338919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4338919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338919 prefixEnd_4338919 := by exact prefixLift 4338919
  have htrace : WordTrace (prefixWord ++ tailWord_4338919) baseStart_4338919 baseEnd_4338919 := by
    simpa [prefixWord, tailWord_4338919, baseEnd_4338919] using wordTrace_append hprefix tailTrace_4338919
  have hstable : (prefixWord ++ tailWord_4338919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338919).length < 2 ^ (prefixWord ++ tailWord_4338919).sum := by decide
  have hdescent : baseEnd_4338919 < baseStart_4338919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338989 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4338989 : Nat := 118140960795 + 4338989 * 2 ^ 59
def prefixEnd_4338989 : Nat := 4983230072969 + 3 ^ 40 * 4338989 * 2
def baseEnd_4338989 : Nat := 742662303857143139760953

theorem tailTrace_4338989 : CollatzResearch.WordTrace tailWord_4338989 prefixEnd_4338989 742662303857143139760953 := by
  unfold tailWord_4338989
  simp only [CollatzResearch.WordTrace]
  refine ⟨158255930077591368169076021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105503953385060912112717347 158255930077591368169076021)
  ·
    refine ⟨14836493444774190765850877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158255930077591368169076021 14836493444774190765850877)
    ·
      refine ⟨5563685041790321537194079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14836493444774190765850877 5563685041790321537194079)
      ·
        refine ⟨8345527562685482305791119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563685041790321537194079 8345527562685482305791119)
        ·
          refine ⟨12518291344028223458686679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345527562685482305791119 12518291344028223458686679)
          ·
            refine ⟨18777437016042335188030019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518291344028223458686679 18777437016042335188030019)
            ·
              refine ⟨28166155524063502782045029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18777437016042335188030019 28166155524063502782045029)
              ·
                refine ⟨5281154160761906771633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28166155524063502782045029 5281154160761906771633443)
                ·
                  refine ⟨7921731241142860157450165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281154160761906771633443 7921731241142860157450165)
                  ·
                    refine ⟨742662303857143139760953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7921731241142860157450165 742662303857143139760953)
                    ·
                      rfl

theorem cell23_4338989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4338989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338989 prefixEnd_4338989 := by exact prefixLift 4338989
  have htrace : WordTrace (prefixWord ++ tailWord_4338989) baseStart_4338989 baseEnd_4338989 := by
    simpa [prefixWord, tailWord_4338989, baseEnd_4338989] using wordTrace_append hprefix tailTrace_4338989
  have hstable : (prefixWord ++ tailWord_4338989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338989).length < 2 ^ (prefixWord ++ tailWord_4338989).sum := by decide
  have hdescent : baseEnd_4338989 < baseStart_4338989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4338992 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_4338992 : Nat := 118140960795 + 4338992 * 2 ^ 59
def prefixEnd_4338992 : Nat := 4983230072969 + 3 ^ 40 * 4338992 * 2
def baseEnd_4338992 : Nat := 2227988452013392907545345

theorem tailTrace_4338992 : CollatzResearch.WordTrace tailWord_4338992 prefixEnd_4338992 2227988452013392907545345 := by
  unfold tailWord_4338992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79128019748290249840717615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105504026331053666454290153 79128019748290249840717615)
  ·
    refine ⟨118692029622435374761076423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79128019748290249840717615 118692029622435374761076423)
    ·
      refine ⟨178038044433653062141614635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118692029622435374761076423 178038044433653062141614635)
      ·
        refine ⟨267057066650479593212421953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178038044433653062141614635 267057066650479593212421953)
        ·
          refine ⟨200292799987859694909316465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267057066650479593212421953 200292799987859694909316465)
          ·
            refine ⟨150219599990894771181987349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200292799987859694909316465 150219599990894771181987349)
            ·
              refine ⟨7041543749573192399155657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150219599990894771181987349 7041543749573192399155657)
              ·
                refine ⟨5281157812179894299366743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041543749573192399155657 5281157812179894299366743)
                ·
                  refine ⟨7921736718269841449050115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281157812179894299366743 7921736718269841449050115)
                  ·
                    refine ⟨11882605077404762173575173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7921736718269841449050115 11882605077404762173575173)
                    ·
                      refine ⟨2227988452013392907545345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11882605077404762173575173 2227988452013392907545345)
                      ·
                        rfl

theorem cell23_4338992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_4338992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4338992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4338992 prefixEnd_4338992 := by exact prefixLift 4338992
  have htrace : WordTrace (prefixWord ++ tailWord_4338992) baseStart_4338992 baseEnd_4338992 := by
    simpa [prefixWord, tailWord_4338992, baseEnd_4338992] using wordTrace_append hprefix tailTrace_4338992
  have hstable : (prefixWord ++ tailWord_4338992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4338992).length < 2 ^ (prefixWord ++ tailWord_4338992).sum := by decide
  have hdescent : baseEnd_4338992 < baseStart_4338992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4338992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339009 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4339009 : Nat := 118140960795 + 4339009 * 2 ^ 59
def prefixEnd_4339009 : Nat := 4983230072969 + 3 ^ 40 * 4339009 * 2
def baseEnd_4339009 : Nat := 2227997181184519341032767

theorem tailTrace_4339009 : CollatzResearch.WordTrace tailWord_4339009 prefixEnd_4339009 2227997181184519341032767 := by
  unfold tailWord_4339009
  simp only [CollatzResearch.WordTrace]
  refine ⟨158256659537518911584804081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105504439691679274389869387 158256659537518911584804081)
  ·
    refine ⟨118692494653139183688603061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158256659537518911584804081 118692494653139183688603061)
    ·
      refine ⟨11127421373731798470806537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118692494653139183688603061 11127421373731798470806537)
      ·
        refine ⟨8345566030298848853104903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11127421373731798470806537 8345566030298848853104903)
        ·
          refine ⟨12518349045448273279657355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345566030298848853104903 12518349045448273279657355)
          ·
            refine ⟨18777523568172409919486033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518349045448273279657355 18777523568172409919486033)
            ·
              refine ⟨14083142676129307439614525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18777523568172409919486033 14083142676129307439614525)
              ·
                refine ⟨5281178503548490289855447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14083142676129307439614525 5281178503548490289855447)
                ·
                  refine ⟨7921767755322735434783171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281178503548490289855447 7921767755322735434783171)
                  ·
                    refine ⟨11882651632984103152174757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7921767755322735434783171 11882651632984103152174757)
                    ·
                      refine ⟨2227997181184519341032767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11882651632984103152174757 2227997181184519341032767)
                      ·
                        rfl

theorem cell23_4339009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4339009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339009 prefixEnd_4339009 := by exact prefixLift 4339009
  have htrace : WordTrace (prefixWord ++ tailWord_4339009) baseStart_4339009 baseEnd_4339009 := by
    simpa [prefixWord, tailWord_4339009, baseEnd_4339009] using wordTrace_append hprefix tailTrace_4339009
  have hstable : (prefixWord ++ tailWord_4339009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339009).length < 2 ^ (prefixWord ++ tailWord_4339009).sum := by decide
  have hdescent : baseEnd_4339009 < baseStart_4339009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339015 : List Nat := [1, 1, 4, 1, 2, 5, 9]
def baseStart_4339015 : Nat := 118140960795 + 4339015 * 2 ^ 59
def prefixEnd_4339015 : Nat := 4983230072969 + 3 ^ 40 * 4339015 * 2
def baseEnd_4339015 : Nat := 27506176074919090340219

theorem tailTrace_4339015 : CollatzResearch.WordTrace tailWord_4339015 prefixEnd_4339015 27506176074919090340219 := by
  unfold tailWord_4339015
  simp only [CollatzResearch.WordTrace]
  refine ⟨158256878375497174609522499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105504585583664783073014999 158256878375497174609522499)
  ·
    refine ⟨237385317563245761914283749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158256878375497174609522499 237385317563245761914283749)
    ·
      refine ⟨44509747043108580358928203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237385317563245761914283749 44509747043108580358928203)
      ·
        refine ⟨66764620564662870538392305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44509747043108580358928203 66764620564662870538392305)
        ·
          refine ⟨50073465423497152903794229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66764620564662870538392305 50073465423497152903794229)
          ·
            refine ⟨4694387383452858084730709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50073465423497152903794229 4694387383452858084730709)
            ·
              refine ⟨27506176074919090340219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4694387383452858084730709 27506176074919090340219)
              ·
                rfl

theorem cell23_4339015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 9].length) (baseStart_4339015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339015 prefixEnd_4339015 := by exact prefixLift 4339015
  have htrace : WordTrace (prefixWord ++ tailWord_4339015) baseStart_4339015 baseEnd_4339015 := by
    simpa [prefixWord, tailWord_4339015, baseEnd_4339015] using wordTrace_append hprefix tailTrace_4339015
  have hstable : (prefixWord ++ tailWord_4339015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339015).length < 2 ^ (prefixWord ++ tailWord_4339015).sum := by decide
  have hdescent : baseEnd_4339015 < baseStart_4339015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339076 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_4339076 : Nat := 118140960795 + 4339076 * 2 ^ 59
def prefixEnd_4339076 : Nat := 4983230072969 + 3 ^ 40 * 4339076 * 2
def baseEnd_4339076 : Nat := 2228031584388370578894959

theorem tailTrace_4339076 : CollatzResearch.WordTrace tailWord_4339076 prefixEnd_4339076 2228031584388370578894959 := by
  unfold tailWord_4339076
  simp only [CollatzResearch.WordTrace]
  refine ⟨79129551614138091013746541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105506068818850788018328721 79129551614138091013746541)
  ·
    refine ⟨29673581855301784130154953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79129551614138091013746541 29673581855301784130154953)
    ·
      refine ⟨22255186391476338097616215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29673581855301784130154953 22255186391476338097616215)
      ·
        refine ⟨33382779587214507146424323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22255186391476338097616215 33382779587214507146424323)
        ·
          refine ⟨50074169380821760719636485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33382779587214507146424323 50074169380821760719636485)
          ·
            refine ⟨9388906758904080134931841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50074169380821760719636485 9388906758904080134931841)
            ·
              refine ⟨7041680069178060101198881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9388906758904080134931841 7041680069178060101198881)
              ·
                refine ⟨5281260051883545075899161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041680069178060101198881 5281260051883545075899161)
                ·
                  refine ⟨3960945038912658806924371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281260051883545075899161 3960945038912658806924371)
                  ·
                    refine ⟨5941417558368988210386557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960945038912658806924371 5941417558368988210386557)
                    ·
                      refine ⟨2228031584388370578894959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5941417558368988210386557 2228031584388370578894959)
                      ·
                        rfl

theorem cell23_4339076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_4339076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339076 prefixEnd_4339076 := by exact prefixLift 4339076
  have htrace : WordTrace (prefixWord ++ tailWord_4339076) baseStart_4339076 baseEnd_4339076 := by
    simpa [prefixWord, tailWord_4339076, baseEnd_4339076] using wordTrace_append hprefix tailTrace_4339076
  have hstable : (prefixWord ++ tailWord_4339076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339076).length < 2 ^ (prefixWord ++ tailWord_4339076).sum := by decide
  have hdescent : baseEnd_4339076 < baseStart_4339076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339092 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4339092 : Nat := 118140960795 + 4339092 * 2 ^ 59
def prefixEnd_4339092 : Nat := 4983230072969 + 3 ^ 40 * 4339092 * 2
def baseEnd_4339092 : Nat := 742679933359614172098295

theorem tailTrace_4339092 : CollatzResearch.WordTrace tailWord_4339092 prefixEnd_4339092 742679933359614172098295 := by
  unfold tailWord_4339092
  simp only [CollatzResearch.WordTrace]
  refine ⟨79129843398109108380037765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105506457864145477840050353 79129843398109108380037765)
  ·
    refine ⟨14836845637145457821257081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79129843398109108380037765 14836845637145457821257081)
    ·
      refine ⟨11127634227859093365942811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14836845637145457821257081 11127634227859093365942811)
      ·
        refine ⟨16691451341788640048914217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11127634227859093365942811 16691451341788640048914217)
        ·
          refine ⟨12518588506341480036685663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16691451341788640048914217 12518588506341480036685663)
          ·
            refine ⟨18777882759512220055028495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518588506341480036685663 18777882759512220055028495)
            ·
              refine ⟨28166824139268330082542743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18777882759512220055028495 28166824139268330082542743)
              ·
                refine ⟨42250236208902495123814115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28166824139268330082542743 42250236208902495123814115)
                ·
                  refine ⟨63375354313353742685721173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42250236208902495123814115 63375354313353742685721173)
                  ·
                    refine ⟨742679933359614172098295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63375354313353742685721173 742679933359614172098295)
                    ·
                      rfl

theorem cell23_4339092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4339092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339092 prefixEnd_4339092 := by exact prefixLift 4339092
  have htrace : WordTrace (prefixWord ++ tailWord_4339092) baseStart_4339092 baseEnd_4339092 := by
    simpa [prefixWord, tailWord_4339092, baseEnd_4339092] using wordTrace_append hprefix tailTrace_4339092
  have hstable : (prefixWord ++ tailWord_4339092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339092).length < 2 ^ (prefixWord ++ tailWord_4339092).sum := by decide
  have hdescent : baseEnd_4339092 < baseStart_4339092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339145 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_4339145 : Nat := 118140960795 + 4339145 * 2 ^ 59
def prefixEnd_4339145 : Nat := 4983230072969 + 3 ^ 40 * 4339145 * 2
def baseEnd_4339145 : Nat := 2228067014553530808932141

theorem tailTrace_4339145 : CollatzResearch.WordTrace tailWord_4339145 prefixEnd_4339145 2228067014553530808932141 := by
  unfold tailWord_4339145
  simp only [CollatzResearch.WordTrace]
  refine ⟨158261619865026206811754889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105507746576684137874503259 158261619865026206811754889)
  ·
    refine ⟨118696214898769655108816167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158261619865026206811754889 118696214898769655108816167)
    ·
      refine ⟨178044322348154482663224251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118696214898769655108816167 178044322348154482663224251)
      ·
        refine ⟨267066483522231723994836377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178044322348154482663224251 267066483522231723994836377)
        ·
          refine ⟨200299862641673792996127283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267066483522231723994836377 200299862641673792996127283)
          ·
            refine ⟨300449793962510689494190925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200299862641673792996127283 300449793962510689494190925)
            ·
              refine ⟨112668672735941508560321597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300449793962510689494190925 112668672735941508560321597)
              ·
                refine ⟨42250752275978065710120599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112668672735941508560321597 42250752275978065710120599)
                ·
                  refine ⟨63376128413967098565180899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42250752275978065710120599 63376128413967098565180899)
                  ·
                    refine ⟨95064192620950647847771349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63376128413967098565180899 95064192620950647847771349)
                    ·
                      refine ⟨2228067014553530808932141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95064192620950647847771349 2228067014553530808932141)
                      ·
                        rfl

theorem cell23_4339145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_4339145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339145 prefixEnd_4339145 := by exact prefixLift 4339145
  have htrace : WordTrace (prefixWord ++ tailWord_4339145) baseStart_4339145 baseEnd_4339145 := by
    simpa [prefixWord, tailWord_4339145, baseEnd_4339145] using wordTrace_append hprefix tailTrace_4339145
  have hstable : (prefixWord ++ tailWord_4339145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339145).length < 2 ^ (prefixWord ++ tailWord_4339145).sum := by decide
  have hdescent : baseEnd_4339145 < baseStart_4339145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339172 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_4339172 : Nat := 118140960795 + 4339172 * 2 ^ 59
def prefixEnd_4339172 : Nat := 4983230072969 + 3 ^ 40 * 4339172 * 2
def baseEnd_4339172 : Nat := 2228080878531202203294517

theorem tailTrace_4339172 : CollatzResearch.WordTrace tailWord_4339172 prefixEnd_4339172 2228080878531202203294517 := by
  unfold tailWord_4339172
  simp only [CollatzResearch.WordTrace]
  refine ⟨79131302317964195211493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105508403090618926948658513 79131302317964195211493885)
  ·
    refine ⟨29674238369236573204310207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79131302317964195211493885 29674238369236573204310207)
    ·
      refine ⟨44511357553854859806465311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29674238369236573204310207 44511357553854859806465311)
      ·
        refine ⟨66767036330782289709697967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44511357553854859806465311 66767036330782289709697967)
        ·
          refine ⟨100150554496173434564546951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66767036330782289709697967 100150554496173434564546951)
          ·
            refine ⟨150225831744260151846820427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100150554496173434564546951 150225831744260151846820427)
            ·
              refine ⟨225338747616390227770230641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150225831744260151846820427 225338747616390227770230641)
              ·
                refine ⟨169004060712292670827672981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225338747616390227770230641 169004060712292670827672981)
                ·
                  refine ⟨7922065345888718945047171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169004060712292670827672981 7922065345888718945047171)
                  ·
                    refine ⟨11883098018833078417570757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7922065345888718945047171 11883098018833078417570757)
                    ·
                      refine ⟨2228080878531202203294517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11883098018833078417570757 2228080878531202203294517)
                      ·
                        rfl

theorem cell23_4339172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_4339172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339172 prefixEnd_4339172 := by exact prefixLift 4339172
  have htrace : WordTrace (prefixWord ++ tailWord_4339172) baseStart_4339172 baseEnd_4339172 := by
    simpa [prefixWord, tailWord_4339172, baseEnd_4339172] using wordTrace_append hprefix tailTrace_4339172
  have hstable : (prefixWord ++ tailWord_4339172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339172).length < 2 ^ (prefixWord ++ tailWord_4339172).sum := by decide
  have hdescent : baseEnd_4339172 < baseStart_4339172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339246 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_4339246 : Nat := 118140960795 + 4339246 * 2 ^ 59
def prefixEnd_4339246 : Nat := 4983230072969 + 3 ^ 40 * 4339246 * 2
def baseEnd_4339246 : Nat := 247568764011070545974353

theorem tailTrace_4339246 : CollatzResearch.WordTrace tailWord_4339246 prefixEnd_4339246 247568764011070545974353 := by
  unfold tailWord_4339246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783162954707537632647699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105510202425106867374121061 19783162954707537632647699)
  ·
    refine ⟨29674744432061306448971549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19783162954707537632647699 29674744432061306448971549)
    ·
      refine ⟨11128029162022989918364331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29674744432061306448971549 11128029162022989918364331)
      ·
        refine ⟨16692043743034484877546497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128029162022989918364331 16692043743034484877546497)
        ·
          refine ⟨12519032807275863658159873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16692043743034484877546497 12519032807275863658159873)
          ·
            refine ⟨9389274605456897743619905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12519032807275863658159873 9389274605456897743619905)
            ·
              refine ⟨7041955954092673307714929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9389274605456897743619905 7041955954092673307714929)
              ·
                refine ⟨5281466965569504980786197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041955954092673307714929 5281466965569504980786197)
                ·
                  refine ⟨247568764011070545974353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5281466965569504980786197 247568764011070545974353)
                  ·
                    rfl

theorem cell23_4339246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_4339246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339246 prefixEnd_4339246 := by exact prefixLift 4339246
  have htrace : WordTrace (prefixWord ++ tailWord_4339246) baseStart_4339246 baseEnd_4339246 := by
    simpa [prefixWord, tailWord_4339246, baseEnd_4339246] using wordTrace_append hprefix tailTrace_4339246
  have hstable : (prefixWord ++ tailWord_4339246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339246).length < 2 ^ (prefixWord ++ tailWord_4339246).sum := by decide
  have hdescent : baseEnd_4339246 < baseStart_4339246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339249 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_4339249 : Nat := 118140960795 + 4339249 * 2 ^ 59
def prefixEnd_4339249 : Nat := 4983230072969 + 3 ^ 40 * 4339249 * 2
def baseEnd_4339249 : Nat := 2228120416541598402031663

theorem tailTrace_4339249 : CollatzResearch.WordTrace tailWord_4339249 prefixEnd_4339249 2228120416541598402031663 := by
  unfold tailWord_4339249
  simp only [CollatzResearch.WordTrace]
  refine ⟨158265413056649432573540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105510275371099621715693867 158265413056649432573540801)
  ·
    refine ⟨118699059792487074430155601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158265413056649432573540801 118699059792487074430155601)
    ·
      refine ⟨89024294844365305822616701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118699059792487074430155601 89024294844365305822616701)
      ·
        refine ⟨33384110566636989683481263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89024294844365305822616701 33384110566636989683481263)
        ·
          refine ⟨50076165849955484525221895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33384110566636989683481263 50076165849955484525221895)
          ·
            refine ⟨75114248774933226787832843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50076165849955484525221895 75114248774933226787832843)
            ·
              refine ⟨112671373162399840181749265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75114248774933226787832843 112671373162399840181749265)
              ·
                refine ⟨84503529871799880136311949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112671373162399840181749265 84503529871799880136311949)
                ·
                  refine ⟨31688823701924955051116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84503529871799880136311949 31688823701924955051116981)
                  ·
                    refine ⟨2970827222055464536042217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31688823701924955051116981 2970827222055464536042217)
                    ·
                      refine ⟨2228120416541598402031663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970827222055464536042217 2228120416541598402031663)
                      ·
                        rfl

theorem cell23_4339249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_4339249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339249 prefixEnd_4339249 := by exact prefixLift 4339249
  have htrace : WordTrace (prefixWord ++ tailWord_4339249) baseStart_4339249 baseEnd_4339249 := by
    simpa [prefixWord, tailWord_4339249, baseEnd_4339249] using wordTrace_append hprefix tailTrace_4339249
  have hstable : (prefixWord ++ tailWord_4339249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339249).length < 2 ^ (prefixWord ++ tailWord_4339249).sum := by decide
  have hdescent : baseEnd_4339249 < baseStart_4339249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339279 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_4339279 : Nat := 118140960795 + 4339279 * 2 ^ 59
def prefixEnd_4339279 : Nat := 4983230072969 + 3 ^ 40 * 4339279 * 2
def baseEnd_4339279 : Nat := 2228135820961233284656525

theorem tailTrace_4339279 : CollatzResearch.WordTrace tailWord_4339279 prefixEnd_4339279 2228135820961233284656525 := by
  unfold tailWord_4339279
  simp only [CollatzResearch.WordTrace]
  refine ⟨158266507246540747697132891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105511004831027165131421927 158266507246540747697132891)
  ·
    refine ⟨237399760869811121545699337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158266507246540747697132891 237399760869811121545699337)
    ·
      refine ⟨178049820652358341159274503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237399760869811121545699337 178049820652358341159274503)
      ·
        refine ⟨267074730978537511738911755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178049820652358341159274503 267074730978537511738911755)
        ·
          refine ⟨400612096467806267608367633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267074730978537511738911755 400612096467806267608367633)
          ·
            refine ⟨300459072350854700706275725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400612096467806267608367633 300459072350854700706275725)
            ·
              refine ⟨112672152131570512764853397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300459072350854700706275725 112672152131570512764853397)
              ·
                refine ⟨5281507131167367785852503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112672152131570512764853397 5281507131167367785852503)
                ·
                  refine ⟨7922260696751051678778755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281507131167367785852503 7922260696751051678778755)
                  ·
                    refine ⟨11883391045126577518168133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7922260696751051678778755 11883391045126577518168133)
                    ·
                      refine ⟨2228135820961233284656525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11883391045126577518168133 2228135820961233284656525)
                      ·
                        rfl

theorem cell23_4339279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_4339279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339279 prefixEnd_4339279 := by exact prefixLift 4339279
  have htrace : WordTrace (prefixWord ++ tailWord_4339279) baseStart_4339279 baseEnd_4339279 := by
    simpa [prefixWord, tailWord_4339279, baseEnd_4339279] using wordTrace_append hprefix tailTrace_4339279
  have hstable : (prefixWord ++ tailWord_4339279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339279).length < 2 ^ (prefixWord ++ tailWord_4339279).sum := by decide
  have hdescent : baseEnd_4339279 < baseStart_4339279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339296 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2]
def baseStart_4339296 : Nat := 118140960795 + 4339296 * 2 ^ 59
def prefixEnd_4339296 : Nat := 4983230072969 + 3 ^ 40 * 4339296 * 2
def baseEnd_4339296 : Nat := 2228144550132359718143947

theorem tailTrace_4339296 : CollatzResearch.WordTrace tailWord_4339296 prefixEnd_4339296 2228144550132359718143947 := by
  unfold tailWord_4339296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79133563643739579800250871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105511418191652773067001161 79133563643739579800250871)
  ·
    refine ⟨118700345465609369700376307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79133563643739579800250871 118700345465609369700376307)
    ·
      refine ⟨178050518198414054550564461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118700345465609369700376307 178050518198414054550564461)
      ·
        refine ⟨66768944324405270456461673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178050518198414054550564461 66768944324405270456461673)
        ·
          refine ⟨50076708243303952842346255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66768944324405270456461673 50076708243303952842346255)
          ·
            refine ⟨75115062364955929263519383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50076708243303952842346255 75115062364955929263519383)
            ·
              refine ⟨112672593547433893895279075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75115062364955929263519383 112672593547433893895279075)
              ·
                refine ⟨169008890321150840842918613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112672593547433893895279075 169008890321150840842918613)
                ·
                  refine ⟨3961145866901972832255905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169008890321150840842918613 3961145866901972832255905)
                  ·
                    refine ⟨2970859400176479624191929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3961145866901972832255905 2970859400176479624191929)
                    ·
                      refine ⟨2228144550132359718143947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970859400176479624191929 2228144550132359718143947)
                      ·
                        rfl

theorem cell23_4339296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_4339296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339296 prefixEnd_4339296 := by exact prefixLift 4339296
  have htrace : WordTrace (prefixWord ++ tailWord_4339296) baseStart_4339296 baseEnd_4339296 := by
    simpa [prefixWord, tailWord_4339296, baseEnd_4339296] using wordTrace_append hprefix tailTrace_4339296
  have hstable : (prefixWord ++ tailWord_4339296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339296).length < 2 ^ (prefixWord ++ tailWord_4339296).sum := by decide
  have hdescent : baseEnd_4339296 < baseStart_4339296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339306 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4339306 : Nat := 118140960795 + 4339306 * 2 ^ 59
def prefixEnd_4339306 : Nat := 4983230072969 + 3 ^ 40 * 4339306 * 2
def baseEnd_4339306 : Nat := 742716561646301559672967

theorem tailTrace_4339306 : CollatzResearch.WordTrace tailWord_4339306 prefixEnd_4339306 742716561646301559672967 := by
  unfold tailWord_4339306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39566873004360732827091443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105511661344961954205577181 39566873004360732827091443)
  ·
    refine ⟨59350309506541099240637165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39566873004360732827091443 59350309506541099240637165)
    ·
      refine ⟨22256366064952912215238937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59350309506541099240637165 22256366064952912215238937)
      ·
        refine ⟨16692274548714684161429203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22256366064952912215238937 16692274548714684161429203)
        ·
          refine ⟨25038411823072026242143805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692274548714684161429203 25038411823072026242143805)
          ·
            refine ⟨9389404433652009840803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25038411823072026242143805 9389404433652009840803927)
            ·
              refine ⟨14084106650478014761205891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9389404433652009840803927 14084106650478014761205891)
              ·
                refine ⟨21126159975717022141808837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14084106650478014761205891 21126159975717022141808837)
                ·
                  refine ⟨3961154995446941651589157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21126159975717022141808837 3961154995446941651589157)
                  ·
                    refine ⟨742716561646301559672967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961154995446941651589157 742716561646301559672967)
                    ·
                      rfl

theorem cell23_4339306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4339306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339306 prefixEnd_4339306 := by exact prefixLift 4339306
  have htrace : WordTrace (prefixWord ++ tailWord_4339306) baseStart_4339306 baseEnd_4339306 := by
    simpa [prefixWord, tailWord_4339306, baseEnd_4339306] using wordTrace_append hprefix tailTrace_4339306
  have hstable : (prefixWord ++ tailWord_4339306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339306).length < 2 ^ (prefixWord ++ tailWord_4339306).sum := by decide
  have hdescent : baseEnd_4339306 < baseStart_4339306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_4339322 : Nat := 118140960795 + 4339322 * 2 ^ 59
def prefixEnd_4339322 : Nat := 4983230072969 + 3 ^ 40 * 4339322 * 2
def baseEnd_4339322 : Nat := 2228157900629376616418827

theorem tailTrace_4339322 : CollatzResearch.WordTrace tailWord_4339322 prefixEnd_4339322 2228157900629376616418827 := by
  unfold tailWord_4339322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39567018896346241510237055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105512050390256644027298813 39567018896346241510237055)
  ·
    refine ⟨59350528344519362265355583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39567018896346241510237055 59350528344519362265355583)
    ·
      refine ⟨89025792516779043398033375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59350528344519362265355583 89025792516779043398033375)
      ·
        refine ⟨133538688775168565097050063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89025792516779043398033375 133538688775168565097050063)
        ·
          refine ⟨200308033162752847645575095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133538688775168565097050063 200308033162752847645575095)
          ·
            refine ⟨300462049744129271468362643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200308033162752847645575095 300462049744129271468362643)
            ·
              refine ⟨450693074616193907202543965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300462049744129271468362643 450693074616193907202543965)
              ·
                refine ⟨169009902981072715200953987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450693074616193907202543965 169009902981072715200953987)
                ·
                  refine ⟨253514854471609072801430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169009902981072715200953987 253514854471609072801430981)
                  ·
                    refine ⟨47534035213426701150268309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253514854471609072801430981 47534035213426701150268309)
                    ·
                      refine ⟨2228157900629376616418827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47534035213426701150268309 2228157900629376616418827)
                      ·
                        rfl

theorem cell23_4339322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_4339322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339322 prefixEnd_4339322 := by exact prefixLift 4339322
  have htrace : WordTrace (prefixWord ++ tailWord_4339322) baseStart_4339322 baseEnd_4339322 := by
    simpa [prefixWord, tailWord_4339322, baseEnd_4339322] using wordTrace_append hprefix tailTrace_4339322
  have hstable : (prefixWord ++ tailWord_4339322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339322).length < 2 ^ (prefixWord ++ tailWord_4339322).sum := by decide
  have hdescent : baseEnd_4339322 < baseStart_4339322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339336 : List Nat := [2, 1, 3, 5, 1, 1, 1, 9]
def baseStart_4339336 : Nat := 118140960795 + 4339336 * 2 ^ 59
def prefixEnd_4339336 : Nat := 4983230072969 + 3 ^ 40 * 4339336 * 2
def baseEnd_4339336 : Nat := 82524632939205168949769

theorem tailTrace_4339336 : CollatzResearch.WordTrace tailWord_4339336 prefixEnd_4339336 82524632939205168949769 := by
  unfold tailWord_4339336
  simp only [CollatzResearch.WordTrace]
  refine ⟨79134293103667123215978931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105512390804889497621305241 79134293103667123215978931)
  ·
    refine ⟨118701439655500684823968397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79134293103667123215978931 118701439655500684823968397)
    ·
      refine ⟨44513039870812756808988149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118701439655500684823968397 44513039870812756808988149)
      ·
        refine ⟨4173097487888695950842639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44513039870812756808988149 4173097487888695950842639)
        ·
          refine ⟨6259646231833043926263959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173097487888695950842639 6259646231833043926263959)
          ·
            refine ⟨9389469347749565889395939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259646231833043926263959 9389469347749565889395939)
            ·
              refine ⟨14084204021624348834093909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9389469347749565889395939 14084204021624348834093909)
              ·
                refine ⟨82524632939205168949769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14084204021624348834093909 82524632939205168949769)
                ·
                  rfl

theorem cell23_4339336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 9].length) (baseStart_4339336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339336 prefixEnd_4339336 := by exact prefixLift 4339336
  have htrace : WordTrace (prefixWord ++ tailWord_4339336) baseStart_4339336 baseEnd_4339336 := by
    simpa [prefixWord, tailWord_4339336, baseEnd_4339336] using wordTrace_append hprefix tailTrace_4339336
  have hstable : (prefixWord ++ tailWord_4339336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339336).length < 2 ^ (prefixWord ++ tailWord_4339336).sum := by decide
  have hdescent : baseEnd_4339336 < baseStart_4339336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339373 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_4339373 : Nat := 118140960795 + 4339373 * 2 ^ 59
def prefixEnd_4339373 : Nat := 4983230072969 + 3 ^ 40 * 4339373 * 2
def baseEnd_4339373 : Nat := 2228184088142755916881093

theorem tailTrace_4339373 : CollatzResearch.WordTrace tailWord_4339373 prefixEnd_4339373 2228184088142755916881093 := by
  unfold tailWord_4339373
  simp only [CollatzResearch.WordTrace]
  refine ⟨158269935708200201751054773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105513290472133467834036515 158269935708200201751054773)
  ·
    refine ⟨14837806472643768914161385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158269935708200201751054773 14837806472643768914161385)
    ·
      refine ⟨11128354854482826685621039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14837806472643768914161385 11128354854482826685621039)
      ·
        refine ⟨16692532281724240028431559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128354854482826685621039 16692532281724240028431559)
        ·
          refine ⟨25038798422586360042647339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692532281724240028431559 25038798422586360042647339)
          ·
            refine ⟨37558197633879540063971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25038798422586360042647339 37558197633879540063971009)
            ·
              refine ⟨28168648225409655047978257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37558197633879540063971009 28168648225409655047978257)
              ·
                refine ⟨21126486169057241285983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28168648225409655047978257 21126486169057241285983693)
                ·
                  refine ⟨7922432313396465482243885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21126486169057241285983693 7922432313396465482243885)
                  ·
                    refine ⟨2970912117523674555841457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7922432313396465482243885 2970912117523674555841457)
                    ·
                      refine ⟨2228184088142755916881093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970912117523674555841457 2228184088142755916881093)
                      ·
                        rfl

theorem cell23_4339373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_4339373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339373 prefixEnd_4339373 := by exact prefixLift 4339373
  have htrace : WordTrace (prefixWord ++ tailWord_4339373) baseStart_4339373 baseEnd_4339373 := by
    simpa [prefixWord, tailWord_4339373, baseEnd_4339373] using wordTrace_append hprefix tailTrace_4339373
  have hstable : (prefixWord ++ tailWord_4339373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339373).length < 2 ^ (prefixWord ++ tailWord_4339373).sum := by decide
  have hdescent : baseEnd_4339373 < baseStart_4339373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339374 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4339374 : Nat := 118140960795 + 4339374 * 2 ^ 59
def prefixEnd_4339374 : Nat := 4983230072969 + 3 ^ 40 * 4339374 * 2
def baseEnd_4339374 : Nat := 742728200541136804322863

theorem tailTrace_4339374 : CollatzResearch.WordTrace tailWord_4339374 prefixEnd_4339374 742728200541136804322863 := by
  unfold tailWord_4339374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783746522649572365230147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105513314787464385947894117 19783746522649572365230147)
  ·
    refine ⟨29675619783974358547845221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19783746522649572365230147 29675619783974358547845221)
    ·
      refine ⟨5564178709495192227720979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29675619783974358547845221 5564178709495192227720979)
      ·
        refine ⟨8346268064242788341581469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564178709495192227720979 8346268064242788341581469)
        ·
          refine ⟨3129850524091045628093051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8346268064242788341581469 3129850524091045628093051)
          ·
            refine ⟨4694775786136568442139577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129850524091045628093051 4694775786136568442139577)
            ·
              refine ⟨3521081839602426331604683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4694775786136568442139577 3521081839602426331604683)
              ·
                refine ⟨5281622759403639497407025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521081839602426331604683 5281622759403639497407025)
                ·
                  refine ⟨3961217069552729623055269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281622759403639497407025 3961217069552729623055269)
                  ·
                    refine ⟨742728200541136804322863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961217069552729623055269 742728200541136804322863)
                    ·
                      rfl

theorem cell23_4339374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4339374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339374 prefixEnd_4339374 := by exact prefixLift 4339374
  have htrace : WordTrace (prefixWord ++ tailWord_4339374) baseStart_4339374 baseEnd_4339374 := by
    simpa [prefixWord, tailWord_4339374, baseEnd_4339374] using wordTrace_append hprefix tailTrace_4339374
  have hstable : (prefixWord ++ tailWord_4339374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339374).length < 2 ^ (prefixWord ++ tailWord_4339374).sum := by decide
  have hdescent : baseEnd_4339374 < baseStart_4339374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339389 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4339389 : Nat := 118140960795 + 4339389 * 2 ^ 59
def prefixEnd_4339389 : Nat := 4983230072969 + 3 ^ 40 * 4339389 * 2
def baseEnd_4339389 : Nat := 2228192303833227854281019

theorem tailTrace_4339389 : CollatzResearch.WordTrace tailWord_4339389 prefixEnd_4339389 2228192303833227854281019 := by
  unfold tailWord_4339389
  simp only [CollatzResearch.WordTrace]
  refine ⟨158270519276142236483637221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105513679517428157655758147 158270519276142236483637221)
  ·
    refine ⟨29675722364276669340681979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158270519276142236483637221 29675722364276669340681979)
    ·
      refine ⟨44513583546415004011022969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29675722364276669340681979 44513583546415004011022969)
      ·
        refine ⟨33385187659811253008267227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44513583546415004011022969 33385187659811253008267227)
        ·
          refine ⟨50077781489716879512400841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33385187659811253008267227 50077781489716879512400841)
          ·
            refine ⟨37558336117287659634300631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50077781489716879512400841 37558336117287659634300631)
            ·
              refine ⟨56337504175931489451450947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37558336117287659634300631 56337504175931489451450947)
              ·
                refine ⟨84506256263897234177176421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56337504175931489451450947 84506256263897234177176421)
                ·
                  refine ⟨15844923049480731408220579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84506256263897234177176421 15844923049480731408220579)
                  ·
                    refine ⟨23767384574221097112330869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15844923049480731408220579 23767384574221097112330869)
                    ·
                      refine ⟨2228192303833227854281019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23767384574221097112330869 2228192303833227854281019)
                      ·
                        rfl

theorem cell23_4339389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4339389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339389 prefixEnd_4339389 := by exact prefixLift 4339389
  have htrace : WordTrace (prefixWord ++ tailWord_4339389) baseStart_4339389 baseEnd_4339389 := by
    simpa [prefixWord, tailWord_4339389, baseEnd_4339389] using wordTrace_append hprefix tailTrace_4339389
  have hstable : (prefixWord ++ tailWord_4339389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339389).length < 2 ^ (prefixWord ++ tailWord_4339389).sum := by decide
  have hdescent : baseEnd_4339389 < baseStart_4339389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339390 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_4339390 : Nat := 118140960795 + 4339390 * 2 ^ 59
def prefixEnd_4339390 : Nat := 4983230072969 + 3 ^ 40 * 4339390 * 2
def baseEnd_4339390 : Nat := 2228192817313882350368515

theorem tailTrace_4339390 : CollatzResearch.WordTrace tailWord_4339390 prefixEnd_4339390 2228192817313882350368515 := by
  unfold tailWord_4339390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783819468642326706802953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105513703832759075769615749 19783819468642326706802953)
  ·
    refine ⟨14837864601481745030102215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783819468642326706802953 14837864601481745030102215)
    ·
      refine ⟨22256796902222617545153323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14837864601481745030102215 22256796902222617545153323)
      ·
        refine ⟨33385195353333926317729985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22256796902222617545153323 33385195353333926317729985)
        ·
          refine ⟨25038896515000444738297489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33385195353333926317729985 25038896515000444738297489)
          ·
            refine ⟨18779172386250333553723117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25038896515000444738297489 18779172386250333553723117)
            ·
              refine ⟨7042189644843875082646169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18779172386250333553723117 7042189644843875082646169)
              ·
                refine ⟨5281642233632906311984627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042189644843875082646169 5281642233632906311984627)
                ·
                  refine ⟨7922463350449359467976941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281642233632906311984627 7922463350449359467976941)
                  ·
                    refine ⟨2970923756418509800491353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7922463350449359467976941 2970923756418509800491353)
                    ·
                      refine ⟨2228192817313882350368515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970923756418509800491353 2228192817313882350368515)
                      ·
                        rfl

theorem cell23_4339390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_4339390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339390 prefixEnd_4339390 := by exact prefixLift 4339390
  have htrace : WordTrace (prefixWord ++ tailWord_4339390) baseStart_4339390 baseEnd_4339390 := by
    simpa [prefixWord, tailWord_4339390, baseEnd_4339390] using wordTrace_append hprefix tailTrace_4339390
  have hstable : (prefixWord ++ tailWord_4339390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339390).length < 2 ^ (prefixWord ++ tailWord_4339390).sum := by decide
  have hdescent : baseEnd_4339390 < baseStart_4339390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339414 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4339414 : Nat := 118140960795 + 4339414 * 2 ^ 59
def prefixEnd_4339414 : Nat := 4983230072969 + 3 ^ 40 * 4339414 * 2
def baseEnd_4339414 : Nat := 2228205140849590256468405

theorem tailTrace_4339414 : CollatzResearch.WordTrace tailWord_4339414 prefixEnd_4339414 2228205140849590256468405 := by
  unfold tailWord_4339414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891964443815729109581081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105514287400701110502198197 9891964443815729109581081)
  ·
    refine ⟨7418973332861796832185811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9891964443815729109581081 7418973332861796832185811)
    ·
      refine ⟨11128459999292695248278717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7418973332861796832185811 11128459999292695248278717)
      ·
        refine ⟨4173172499734760718104519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11128459999292695248278717 4173172499734760718104519)
        ·
          refine ⟨6259758749602141077156779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173172499734760718104519 6259758749602141077156779)
          ·
            refine ⟨9389638124403211615735169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259758749602141077156779 9389638124403211615735169)
            ·
              refine ⟨7042228593302408711801377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9389638124403211615735169 7042228593302408711801377)
              ·
                refine ⟨5281671444976806533851033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042228593302408711801377 5281671444976806533851033)
                ·
                  refine ⟨3961253583732604900388275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281671444976806533851033 3961253583732604900388275)
                  ·
                    refine ⟨5941880375598907350582413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961253583732604900388275 5941880375598907350582413)
                    ·
                      refine ⟨2228205140849590256468405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5941880375598907350582413 2228205140849590256468405)
                      ·
                        rfl

theorem cell23_4339414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4339414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339414 prefixEnd_4339414 := by exact prefixLift 4339414
  have htrace : WordTrace (prefixWord ++ tailWord_4339414) baseStart_4339414 baseEnd_4339414 := by
    simpa [prefixWord, tailWord_4339414, baseEnd_4339414] using wordTrace_append hprefix tailTrace_4339414
  have hstable : (prefixWord ++ tailWord_4339414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339414).length < 2 ^ (prefixWord ++ tailWord_4339414).sum := by decide
  have hdescent : baseEnd_4339414 < baseStart_4339414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339439 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 7]
def baseStart_4339439 : Nat := 118140960795 + 4339439 * 2 ^ 59
def prefixEnd_4339439 : Nat := 4983230072969 + 3 ^ 40 * 4339439 * 2
def baseEnd_4339439 : Nat := 742739325955317552885263

theorem tailTrace_4339439 : CollatzResearch.WordTrace tailWord_4339439 prefixEnd_4339439 742739325955317552885263 := by
  unfold tailWord_4339439
  simp only [CollatzResearch.WordTrace]
  refine ⟨158272342925961095022957371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105514895283974063348638247 158272342925961095022957371)
  ·
    refine ⟨237408514388941642534436057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158272342925961095022957371 237408514388941642534436057)
    ·
      refine ⟨178056385791706231900827043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237408514388941642534436057 178056385791706231900827043)
      ·
        refine ⟨267084578687559347851240565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178056385791706231900827043 267084578687559347851240565)
        ·
          refine ⟨25039179251958688861053803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267084578687559347851240565 25039179251958688861053803)
          ·
            refine ⟨37558768877938033291580705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25039179251958688861053803 37558768877938033291580705)
            ·
              refine ⟨28169076658453524968685529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37558768877938033291580705 28169076658453524968685529)
              ·
                refine ⟨21126807493840143726514147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28169076658453524968685529 21126807493840143726514147)
                ·
                  refine ⟨31690211240760215589771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21126807493840143726514147 31690211240760215589771221)
                  ·
                    refine ⟨742739325955317552885263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31690211240760215589771221 742739325955317552885263)
                    ·
                      rfl

theorem cell23_4339439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_4339439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339439 prefixEnd_4339439 := by exact prefixLift 4339439
  have htrace : WordTrace (prefixWord ++ tailWord_4339439) baseStart_4339439 baseEnd_4339439 := by
    simpa [prefixWord, tailWord_4339439, baseEnd_4339439] using wordTrace_append hprefix tailTrace_4339439
  have hstable : (prefixWord ++ tailWord_4339439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339439).length < 2 ^ (prefixWord ++ tailWord_4339439).sum := by decide
  have hdescent : baseEnd_4339439 < baseStart_4339439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339493 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_4339493 : Nat := 118140960795 + 4339493 * 2 ^ 59
def prefixEnd_4339493 : Nat := 4983230072969 + 3 ^ 40 * 4339493 * 2
def baseEnd_4339493 : Nat := 2228245705821295447380541

theorem tailTrace_4339493 : CollatzResearch.WordTrace tailWord_4339493 prefixEnd_4339493 2228245705821295447380541 := by
  unfold tailWord_4339493
  simp only [CollatzResearch.WordTrace]
  refine ⟨158274312467765462245423133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105516208311843641496948755 158274312467765462245423133)
  ·
    refine ⟨59352867175412048342033675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158274312467765462245423133 59352867175412048342033675)
    ·
      refine ⟨89029300763118072513050513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59352867175412048342033675 89029300763118072513050513)
      ·
        refine ⟨66771975572338554384787885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89029300763118072513050513 66771975572338554384787885)
        ·
          refine ⟨25039490839626957894295457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66771975572338554384787885 25039490839626957894295457)
          ·
            refine ⟨18779618129720218420721593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25039490839626957894295457 18779618129720218420721593)
            ·
              refine ⟨14084713597290163815541195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18779618129720218420721593 14084713597290163815541195)
              ·
                refine ⟨21127070395935245723311793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14084713597290163815541195 21127070395935245723311793)
                ·
                  refine ⟨15845302796951434292483845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21127070395935245723311793 15845302796951434292483845)
                  ·
                    refine ⟨2970994274428393929840721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15845302796951434292483845 2970994274428393929840721)
                    ·
                      refine ⟨2228245705821295447380541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2970994274428393929840721 2228245705821295447380541)
                      ·
                        rfl

theorem cell23_4339493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_4339493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339493 prefixEnd_4339493 := by exact prefixLift 4339493
  have htrace : WordTrace (prefixWord ++ tailWord_4339493) baseStart_4339493 baseEnd_4339493 := by
    simpa [prefixWord, tailWord_4339493, baseEnd_4339493] using wordTrace_append hprefix tailTrace_4339493
  have hstable : (prefixWord ++ tailWord_4339493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339493).length < 2 ^ (prefixWord ++ tailWord_4339493).sum := by decide
  have hdescent : baseEnd_4339493 < baseStart_4339493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339533 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4339533 : Nat := 118140960795 + 4339533 * 2 ^ 59
def prefixEnd_4339533 : Nat := 4983230072969 + 3 ^ 40 * 4339533 * 2
def baseEnd_4339533 : Nat := 247585138338608365653373

theorem tailTrace_4339533 : CollatzResearch.WordTrace tailWord_4339533 prefixEnd_4339533 247585138338608365653373 := by
  unfold tailWord_4339533
  simp only [CollatzResearch.WordTrace]
  refine ⟨158275771387620549076879253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105517180925080366051252835 158275771387620549076879253)
  ·
    refine ⟨7419176783794713237978715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158275771387620549076879253 7419176783794713237978715)
    ·
      refine ⟨11128765175692069856968073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419176783794713237978715 11128765175692069856968073)
      ·
        refine ⟨8346573881769052392726055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11128765175692069856968073 8346573881769052392726055)
        ·
          refine ⟨12519860822653578589089083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346573881769052392726055 12519860822653578589089083)
          ·
            refine ⟨18779791233980367883633625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519860822653578589089083 18779791233980367883633625)
            ·
              refine ⟨14084843425485275912725219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18779791233980367883633625 14084843425485275912725219)
              ·
                refine ⟨21127265138227913869087829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14084843425485275912725219 21127265138227913869087829)
                ·
                  refine ⟨247585138338608365653373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21127265138227913869087829 247585138338608365653373)
                  ·
                    rfl

theorem cell23_4339533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4339533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339533 prefixEnd_4339533 := by exact prefixLift 4339533
  have htrace : WordTrace (prefixWord ++ tailWord_4339533) baseStart_4339533 baseEnd_4339533 := by
    simpa [prefixWord, tailWord_4339533, baseEnd_4339533] using wordTrace_append hprefix tailTrace_4339533
  have hstable : (prefixWord ++ tailWord_4339533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339533).length < 2 ^ (prefixWord ++ tailWord_4339533).sum := by decide
  have hdescent : baseEnd_4339533 < baseStart_4339533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339537 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 1, 4]
def baseStart_4339537 : Nat := 118140960795 + 4339537 * 2 ^ 59
def prefixEnd_4339537 : Nat := 4983230072969 + 3 ^ 40 * 4339537 * 2
def baseEnd_4339537 : Nat := 742756099656697758410113

theorem tailTrace_4339537 : CollatzResearch.WordTrace tailWord_4339537 prefixEnd_4339537 742756099656697758410113 := by
  unfold tailWord_4339537
  simp only [CollatzResearch.WordTrace]
  refine ⟨158275917279606057760024865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105517278186404038506683243 158275917279606057760024865)
  ·
    refine ⟨118706937959704543320018649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158275917279606057760024865 118706937959704543320018649)
    ·
      refine ⟨89030203469778407490013987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118706937959704543320018649 89030203469778407490013987)
      ·
        refine ⟨133545305204667611235020981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89030203469778407490013987 133545305204667611235020981)
        ·
          refine ⟨12519872362937588553283217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133545305204667611235020981 12519872362937588553283217)
          ·
            refine ⟨9389904272203191414962413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12519872362937588553283217 9389904272203191414962413)
            ·
              refine ⟨3521214102076196780610905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9389904272203191414962413 3521214102076196780610905)
              ·
                refine ⟨2640910576557147585458179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521214102076196780610905 2640910576557147585458179)
                ·
                  refine ⟨3961365864835721378187269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640910576557147585458179 3961365864835721378187269)
                  ·
                    refine ⟨742756099656697758410113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961365864835721378187269 742756099656697758410113)
                    ·
                      rfl

theorem cell23_4339537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_4339537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339537 prefixEnd_4339537 := by exact prefixLift 4339537
  have htrace : WordTrace (prefixWord ++ tailWord_4339537) baseStart_4339537 baseEnd_4339537 := by
    simpa [prefixWord, tailWord_4339537, baseEnd_4339537] using wordTrace_append hprefix tailTrace_4339537
  have hstable : (prefixWord ++ tailWord_4339537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339537).length < 2 ^ (prefixWord ++ tailWord_4339537).sum := by decide
  have hdescent : baseEnd_4339537 < baseStart_4339537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339539 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_4339539 : Nat := 118140960795 + 4339539 * 2 ^ 59
def prefixEnd_4339539 : Nat := 4983230072969 + 3 ^ 40 * 4339539 * 2
def baseEnd_4339539 : Nat := 2228269325931402267405329

theorem tailTrace_4339539 : CollatzResearch.WordTrace tailWord_4339539 prefixEnd_4339539 2228269325931402267405329 := by
  unfold tailWord_4339539
  simp only [CollatzResearch.WordTrace]
  refine ⟨158275990225598812101597671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105517326817065874734398447 158275990225598812101597671)
  ·
    refine ⟨237413985338398218152396507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158275990225598812101597671 237413985338398218152396507)
    ·
      refine ⟨356120978007597327228594761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237413985338398218152396507 356120978007597327228594761)
      ·
        refine ⟨267090733505697995421446071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356120978007597327228594761 267090733505697995421446071)
        ·
          refine ⟨400636100258546993132169107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267090733505697995421446071 400636100258546993132169107)
          ·
            refine ⟨600954150387820489698253661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400636100258546993132169107 600954150387820489698253661)
            ·
              refine ⟨225357806395432683636845123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600954150387820489698253661 225357806395432683636845123)
              ·
                refine ⟨338036709593149025455267685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225357806395432683636845123 338036709593149025455267685)
                ·
                  refine ⟨63381883048715442272862691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338036709593149025455267685 63381883048715442272862691)
                  ·
                    refine ⟨95072824573073163409294037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63381883048715442272862691 95072824573073163409294037)
                    ·
                      refine ⟨2228269325931402267405329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95072824573073163409294037 2228269325931402267405329)
                      ·
                        rfl

theorem cell23_4339539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_4339539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339539 prefixEnd_4339539 := by exact prefixLift 4339539
  have htrace : WordTrace (prefixWord ++ tailWord_4339539) baseStart_4339539 baseEnd_4339539 := by
    simpa [prefixWord, tailWord_4339539, baseEnd_4339539] using wordTrace_append hprefix tailTrace_4339539
  have hstable : (prefixWord ++ tailWord_4339539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339539).length < 2 ^ (prefixWord ++ tailWord_4339539).sum := by decide
  have hdescent : baseEnd_4339539 < baseStart_4339539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339546 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_4339546 : Nat := 118140960795 + 4339546 * 2 ^ 59
def prefixEnd_4339546 : Nat := 4983230072969 + 3 ^ 40 * 4339546 * 2
def baseEnd_4339546 : Nat := 742757640098661246672599

theorem tailTrace_4339546 : CollatzResearch.WordTrace tailWord_4339546 prefixEnd_4339546 742757640098661246672599 := by
  unfold tailWord_4339546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569061384143363074275623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105517497024382301531401661 39569061384143363074275623)
  ·
    refine ⟨59353592076215044611413435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39569061384143363074275623 59353592076215044611413435)
    ·
      refine ⟨89030388114322566917120153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59353592076215044611413435 89030388114322566917120153)
      ·
        refine ⟨66772791085741925187840115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89030388114322566917120153 66772791085741925187840115)
        ·
          refine ⟨100159186628612887781760173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66772791085741925187840115 100159186628612887781760173)
          ·
            refine ⟨37559694985729832918160065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100159186628612887781760173 37559694985729832918160065)
            ·
              refine ⟨28169771239297374688620049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37559694985729832918160065 28169771239297374688620049)
              ·
                refine ⟨21127328429473031016465037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28169771239297374688620049 21127328429473031016465037)
                ·
                  refine ⟨7922748161052386631174389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21127328429473031016465037 7922748161052386631174389)
                  ·
                    refine ⟨742757640098661246672599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7922748161052386631174389 742757640098661246672599)
                    ·
                      rfl

theorem cell23_4339546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_4339546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339546 prefixEnd_4339546 := by exact prefixLift 4339546
  have htrace : WordTrace (prefixWord ++ tailWord_4339546) baseStart_4339546 baseEnd_4339546 := by
    simpa [prefixWord, tailWord_4339546, baseEnd_4339546] using wordTrace_append hprefix tailTrace_4339546
  have hstable : (prefixWord ++ tailWord_4339546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339546).length < 2 ^ (prefixWord ++ tailWord_4339546).sum := by decide
  have hdescent : baseEnd_4339546 < baseStart_4339546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339553 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_4339553 : Nat := 118140960795 + 4339553 * 2 ^ 59
def prefixEnd_4339553 : Nat := 4983230072969 + 3 ^ 40 * 4339553 * 2
def baseEnd_4339553 : Nat := 2228276514660565212630265

theorem tailTrace_4339553 : CollatzResearch.WordTrace tailWord_4339553 prefixEnd_4339553 2228276514660565212630265 := by
  unfold tailWord_4339553
  simp only [CollatzResearch.WordTrace]
  refine ⟨158276500847548092492607313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105517667231698728328404875 158276500847548092492607313)
  ·
    refine ⟨118707375635661069369455485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158276500847548092492607313 118707375635661069369455485)
    ·
      refine ⟨44515265863372901013545807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118707375635661069369455485 44515265863372901013545807)
      ·
        refine ⟨66772898795059351520318711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44515265863372901013545807 66772898795059351520318711)
        ·
          refine ⟨100159348192589027280478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66772898795059351520318711 100159348192589027280478067)
          ·
            refine ⟨150239022288883540920717101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100159348192589027280478067 150239022288883540920717101)
            ·
              refine ⟨56339633358331327845268913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150239022288883540920717101 56339633358331327845268913)
              ·
                refine ⟨42254725018748495883951685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56339633358331327845268913 42254725018748495883951685)
                ·
                  refine ⟨7922760941015342978240941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42254725018748495883951685 7922760941015342978240941)
                  ·
                    refine ⟨2971035352880753616840353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7922760941015342978240941 2971035352880753616840353)
                    ·
                      refine ⟨2228276514660565212630265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971035352880753616840353 2228276514660565212630265)
                      ·
                        rfl

theorem cell23_4339553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_4339553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339553 prefixEnd_4339553 := by exact prefixLift 4339553
  have htrace : WordTrace (prefixWord ++ tailWord_4339553) baseStart_4339553 baseEnd_4339553 := by
    simpa [prefixWord, tailWord_4339553, baseEnd_4339553] using wordTrace_append hprefix tailTrace_4339553
  have hstable : (prefixWord ++ tailWord_4339553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339553).length < 2 ^ (prefixWord ++ tailWord_4339553).sum := by decide
  have hdescent : baseEnd_4339553 < baseStart_4339553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339594 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4339594 : Nat := 118140960795 + 4339594 * 2 ^ 59
def prefixEnd_4339594 : Nat := 4983230072969 + 3 ^ 40 * 4339594 * 2
def baseEnd_4339594 : Nat := 2228297567367399552217577

theorem tailTrace_4339594 : CollatzResearch.WordTrace tailWord_4339594 prefixEnd_4339594 2228297567367399552217577 := by
  unfold tailWord_4339594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569499060099889123712459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105518664160266370996566557 39569499060099889123712459)
  ·
    refine ⟨59354248590149833685568689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39569499060099889123712459 59354248590149833685568689)
    ·
      refine ⟨44515686442612375264176517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59354248590149833685568689 44515686442612375264176517)
      ·
        refine ⟨8346691207989820362033097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44515686442612375264176517 8346691207989820362033097)
        ·
          refine ⟨6260018405992365271524823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346691207989820362033097 6260018405992365271524823)
          ·
            refine ⟨9390027608988547907287235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260018405992365271524823 9390027608988547907287235)
            ·
              refine ⟨14085041413482821860930853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9390027608988547907287235 14085041413482821860930853)
              ·
                refine ⟨2640945265028029098924535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14085041413482821860930853 2640945265028029098924535)
                ·
                  refine ⟨3961417897542043648386803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640945265028029098924535 3961417897542043648386803)
                  ·
                    refine ⟨5942126846313065472580205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961417897542043648386803 5942126846313065472580205)
                    ·
                      refine ⟨2228297567367399552217577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942126846313065472580205 2228297567367399552217577)
                      ·
                        rfl

theorem cell23_4339594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4339594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339594 prefixEnd_4339594 := by exact prefixLift 4339594
  have htrace : WordTrace (prefixWord ++ tailWord_4339594) baseStart_4339594 baseEnd_4339594 := by
    simpa [prefixWord, tailWord_4339594, baseEnd_4339594] using wordTrace_append hprefix tailTrace_4339594
  have hstable : (prefixWord ++ tailWord_4339594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339594).length < 2 ^ (prefixWord ++ tailWord_4339594).sum := by decide
  have hdescent : baseEnd_4339594 < baseStart_4339594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339596 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4339596 : Nat := 118140960795 + 4339596 * 2 ^ 59
def prefixEnd_4339596 : Nat := 4983230072969 + 3 ^ 40 * 4339596 * 2
def baseEnd_4339596 : Nat := 2228298594328708544392567

theorem tailTrace_4339596 : CollatzResearch.WordTrace tailWord_4339596 prefixEnd_4339596 2228298594328708544392567 := by
  unfold tailWord_4339596
  simp only [CollatzResearch.WordTrace]
  refine ⟨79139034593196155418211321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105518712790928207224281761 79139034593196155418211321)
  ·
    refine ⟨59354275944897116563658491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79139034593196155418211321 59354275944897116563658491)
    ·
      refine ⟨89031413917345674845487737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59354275944897116563658491 89031413917345674845487737)
      ·
        refine ⟨66773560438009256134115803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89031413917345674845487737 66773560438009256134115803)
        ·
          refine ⟨100160340657013884201173705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66773560438009256134115803 100160340657013884201173705)
          ·
            refine ⟨75120255492760413150880279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100160340657013884201173705 75120255492760413150880279)
            ·
              refine ⟨112680383239140619726320419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75120255492760413150880279 112680383239140619726320419)
              ·
                refine ⟨169020574858710929589480629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112680383239140619726320419 169020574858710929589480629)
                ·
                  refine ⟨15845678893004149649013809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169020574858710929589480629 15845678893004149649013809)
                  ·
                    refine ⟨11884259169753112236760357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15845678893004149649013809 11884259169753112236760357)
                    ·
                      refine ⟨2228298594328708544392567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11884259169753112236760357 2228298594328708544392567)
                      ·
                        rfl

theorem cell23_4339596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4339596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339596 prefixEnd_4339596 := by exact prefixLift 4339596
  have htrace : WordTrace (prefixWord ++ tailWord_4339596) baseStart_4339596 baseEnd_4339596 := by
    simpa [prefixWord, tailWord_4339596, baseEnd_4339596] using wordTrace_append hprefix tailTrace_4339596
  have hstable : (prefixWord ++ tailWord_4339596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339596).length < 2 ^ (prefixWord ++ tailWord_4339596).sum := by decide
  have hdescent : baseEnd_4339596 < baseStart_4339596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339610 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_4339610 : Nat := 118140960795 + 4339610 * 2 ^ 59
def prefixEnd_4339610 : Nat := 4983230072969 + 3 ^ 40 * 4339610 * 2
def baseEnd_4339610 : Nat := 742768594352623829872501

theorem tailTrace_4339610 : CollatzResearch.WordTrace tailWord_4339610 prefixEnd_4339610 742768594352623829872501 := by
  unfold tailWord_4339610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569644952085397806858071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105519053205561060818288189 39569644952085397806858071)
  ·
    refine ⟨59354467428128096710287107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39569644952085397806858071 59354467428128096710287107)
    ·
      refine ⟨89031701142192145065430661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59354467428128096710287107 89031701142192145065430661)
      ·
        refine ⟨16693443964161027199768249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89031701142192145065430661 16693443964161027199768249)
        ·
          refine ⟨12520082973120770399826187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16693443964161027199768249 12520082973120770399826187)
          ·
            refine ⟨18780124459681155599739281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12520082973120770399826187 18780124459681155599739281)
            ·
              refine ⟨14085093344760866699804461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18780124459681155599739281 14085093344760866699804461)
              ·
                refine ⟨5281910004285325012426673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14085093344760866699804461 5281910004285325012426673)
                ·
                  refine ⟨3961432503213993759320005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281910004285325012426673 3961432503213993759320005)
                  ·
                    refine ⟨742768594352623829872501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961432503213993759320005 742768594352623829872501)
                    ·
                      rfl

theorem cell23_4339610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_4339610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339610 prefixEnd_4339610 := by exact prefixLift 4339610
  have htrace : WordTrace (prefixWord ++ tailWord_4339610) baseStart_4339610 baseEnd_4339610 := by
    simpa [prefixWord, tailWord_4339610, baseEnd_4339610] using wordTrace_append hprefix tailTrace_4339610
  have hstable : (prefixWord ++ tailWord_4339610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339610).length < 2 ^ (prefixWord ++ tailWord_4339610).sum := by decide
  have hdescent : baseEnd_4339610 < baseStart_4339610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339613 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4339613 : Nat := 118140960795 + 4339613 * 2 ^ 59
def prefixEnd_4339613 : Nat := 4983230072969 + 3 ^ 40 * 4339613 * 2
def baseEnd_4339613 : Nat := 2228307323499834977879989

theorem tailTrace_4339613 : CollatzResearch.WordTrace tailWord_4339613 prefixEnd_4339613 2228307323499834977879989 := by
  unfold tailWord_4339613
  simp only [CollatzResearch.WordTrace]
  refine ⟨158278689227330722739791493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105519126151553815159860995 158278689227330722739791493)
  ·
    refine ⟨29677254230124510513710905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158278689227330722739791493 29677254230124510513710905)
    ·
      refine ⟨22257940672593382885283179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29677254230124510513710905 22257940672593382885283179)
      ·
        refine ⟨33386911008890074327924769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22257940672593382885283179 33386911008890074327924769)
        ·
          refine ⟨25040183256667555745943577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33386911008890074327924769 25040183256667555745943577)
          ·
            refine ⟨18780137442500666809457683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25040183256667555745943577 18780137442500666809457683)
            ·
              refine ⟨28170206163751000214186525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18780137442500666809457683 28170206163751000214186525)
              ·
                refine ⟨10563827311406625080319947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28170206163751000214186525 10563827311406625080319947)
                ·
                  refine ⟨15845740967109937620479921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10563827311406625080319947 15845740967109937620479921)
                  ·
                    refine ⟨11884305725332453215359941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15845740967109937620479921 11884305725332453215359941)
                    ·
                      refine ⟨2228307323499834977879989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11884305725332453215359941 2228307323499834977879989)
                      ·
                        rfl

theorem cell23_4339613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4339613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339613 prefixEnd_4339613 := by exact prefixLift 4339613
  have htrace : WordTrace (prefixWord ++ tailWord_4339613) baseStart_4339613 baseEnd_4339613 := by
    simpa [prefixWord, tailWord_4339613, baseEnd_4339613] using wordTrace_append hprefix tailTrace_4339613
  have hstable : (prefixWord ++ tailWord_4339613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339613).length < 2 ^ (prefixWord ++ tailWord_4339613).sum := by decide
  have hdescent : baseEnd_4339613 < baseStart_4339613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339637 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4339637 : Nat := 118140960795 + 4339637 * 2 ^ 59
def prefixEnd_4339637 : Nat := 4983230072969 + 3 ^ 40 * 4339637 * 2
def baseEnd_4339637 : Nat := 2228319647035542883979879

theorem tailTrace_4339637 : CollatzResearch.WordTrace tailWord_4339637 prefixEnd_4339637 2228319647035542883979879 := by
  unfold tailWord_4339637
  simp only [CollatzResearch.WordTrace]
  refine ⟨158279564579243774838665165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105519709719495849892443443 158279564579243774838665165)
  ·
    refine ⟨59354836717216415564499437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158279564579243774838665165 59354836717216415564499437)
    ·
      refine ⟨22258063768956155836687289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59354836717216415564499437 22258063768956155836687289)
      ·
        refine ⟨16693547826717116877515467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22258063768956155836687289 16693547826717116877515467)
        ·
          refine ⟨25040321740075675316273201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16693547826717116877515467 25040321740075675316273201)
          ·
            refine ⟨18780241305056756487204901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25040321740075675316273201 18780241305056756487204901)
            ·
              refine ⟨3521295244698141841350919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18780241305056756487204901 3521295244698141841350919)
              ·
                refine ⟨5281942867047212762026379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521295244698141841350919 5281942867047212762026379)
                ·
                  refine ⟨7922914300570819143039569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281942867047212762026379 7922914300570819143039569)
                  ·
                    refine ⟨5942185725428114357279677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7922914300570819143039569 5942185725428114357279677)
                    ·
                      refine ⟨2228319647035542883979879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942185725428114357279677 2228319647035542883979879)
                      ·
                        rfl

theorem cell23_4339637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4339637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339637 prefixEnd_4339637 := by exact prefixLift 4339637
  have htrace : WordTrace (prefixWord ++ tailWord_4339637) baseStart_4339637 baseEnd_4339637 := by
    simpa [prefixWord, tailWord_4339637, baseEnd_4339637] using wordTrace_append hprefix tailTrace_4339637
  have hstable : (prefixWord ++ tailWord_4339637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339637).length < 2 ^ (prefixWord ++ tailWord_4339637).sum := by decide
  have hdescent : baseEnd_4339637 < baseStart_4339637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339644 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_4339644 : Nat := 118140960795 + 4339644 * 2 ^ 59
def prefixEnd_4339644 : Nat := 4983230072969 + 3 ^ 40 * 4339644 * 2
def baseEnd_4339644 : Nat := 742774413800041452197449

theorem tailTrace_4339644 : CollatzResearch.WordTrace tailWord_4339644 prefixEnd_4339644 742774413800041452197449 := by
  unfold tailWord_4339644
  simp only [CollatzResearch.WordTrace]
  refine ⟨79139909945109207517084993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105519879926812276689446657 79139909945109207517084993)
  ·
    refine ⟨59354932458831905637813745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79139909945109207517084993 59354932458831905637813745)
    ·
      refine ⟨44516199344123929228360309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59354932458831905637813745 44516199344123929228360309)
      ·
        refine ⟨4173393688511618365158779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44516199344123929228360309 4173393688511618365158779)
        ·
          refine ⟨6260090532767427547738169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173393688511618365158779 6260090532767427547738169)
          ·
            refine ⟨4695067899575570660803627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6260090532767427547738169 4695067899575570660803627)
            ·
              refine ⟨7042601849363355991205441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695067899575570660803627 7042601849363355991205441)
              ·
                refine ⟨5281951387022516993404081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042601849363355991205441 5281951387022516993404081)
                ·
                  refine ⟨3961463540266887745053061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281951387022516993404081 3961463540266887745053061)
                  ·
                    refine ⟨742774413800041452197449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961463540266887745053061 742774413800041452197449)
                    ·
                      rfl

theorem cell23_4339644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_4339644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339644 prefixEnd_4339644 := by exact prefixLift 4339644
  have htrace : WordTrace (prefixWord ++ tailWord_4339644) baseStart_4339644 baseEnd_4339644 := by
    simpa [prefixWord, tailWord_4339644, baseEnd_4339644] using wordTrace_append hprefix tailTrace_4339644
  have hstable : (prefixWord ++ tailWord_4339644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339644).length < 2 ^ (prefixWord ++ tailWord_4339644).sum := by decide
  have hdescent : baseEnd_4339644 < baseStart_4339644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339690 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_4339690 : Nat := 118140960795 + 4339690 * 2 ^ 59
def prefixEnd_4339690 : Nat := 4983230072969 + 3 ^ 40 * 4339690 * 2
def baseEnd_4339690 : Nat := 2228346861510231176617135

theorem tailTrace_4339690 : CollatzResearch.WordTrace tailWord_4339690 prefixEnd_4339690 2228346861510231176617135 := by
  unfold tailWord_4339690
  simp only [CollatzResearch.WordTrace]
  refine ⟨39570374412012941222586131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105520998432034509926896349 39570374412012941222586131)
  ·
    refine ⟨59355561618019411833879197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39570374412012941222586131 59355561618019411833879197)
    ·
      refine ⟨22258335606757279437704699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59355561618019411833879197 22258335606757279437704699)
      ·
        refine ⟨33387503410135919156557049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22258335606757279437704699 33387503410135919156557049)
        ·
          refine ⟨25040627557601939367417787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33387503410135919156557049 25040627557601939367417787)
          ·
            refine ⟨37560941336402909051126681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25040627557601939367417787 37560941336402909051126681)
            ·
              refine ⟨28170706002302181788345011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37560941336402909051126681 28170706002302181788345011)
              ·
                refine ⟨42256059003453272682517517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28170706002302181788345011 42256059003453272682517517)
                ·
                  refine ⟨15846022126294977255944069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42256059003453272682517517 15846022126294977255944069)
                  ·
                    refine ⟨2971129148680308235489513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15846022126294977255944069 2971129148680308235489513)
                    ·
                      refine ⟨2228346861510231176617135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971129148680308235489513 2228346861510231176617135)
                      ·
                        rfl

theorem cell23_4339690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_4339690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339690 prefixEnd_4339690 := by exact prefixLift 4339690
  have htrace : WordTrace (prefixWord ++ tailWord_4339690) baseStart_4339690 baseEnd_4339690 := by
    simpa [prefixWord, tailWord_4339690, baseEnd_4339690] using wordTrace_append hprefix tailTrace_4339690
  have hstable : (prefixWord ++ tailWord_4339690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339690).length < 2 ^ (prefixWord ++ tailWord_4339690).sum := by decide
  have hdescent : baseEnd_4339690 < baseStart_4339690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339696 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 9]
def baseStart_4339696 : Nat := 118140960795 + 4339696 * 2 ^ 59
def prefixEnd_4339696 : Nat := 4983230072969 + 3 ^ 40 * 4339696 * 2
def baseEnd_4339696 : Nat := 247594438043795350349123

theorem tailTrace_4339696 : CollatzResearch.WordTrace tailWord_4339696 prefixEnd_4339696 247594438043795350349123 := by
  unfold tailWord_4339696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79140858243015013957531471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105521144324020018610041961 79140858243015013957531471)
  ·
    refine ⟨118711287364522520936297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79140858243015013957531471 118711287364522520936297207)
    ·
      refine ⟨178066931046783781404445811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118711287364522520936297207 178066931046783781404445811)
      ·
        refine ⟨267100396570175672106668717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178066931046783781404445811 267100396570175672106668717)
        ·
          refine ⟨100162648713815877040000769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267100396570175672106668717 100162648713815877040000769)
          ·
            refine ⟨75121986535361907780000577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100162648713815877040000769 75121986535361907780000577)
            ·
              refine ⟨56341489901521430835000433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75121986535361907780000577 56341489901521430835000433)
              ·
                refine ⟨42256117426141073126250325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56341489901521430835000433 42256117426141073126250325)
                ·
                  refine ⟨247594438043795350349123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42256117426141073126250325 247594438043795350349123)
                  ·
                    rfl

theorem cell23_4339696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_4339696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339696 prefixEnd_4339696 := by exact prefixLift 4339696
  have htrace : WordTrace (prefixWord ++ tailWord_4339696) baseStart_4339696 baseEnd_4339696 := by
    simpa [prefixWord, tailWord_4339696, baseEnd_4339696] using wordTrace_append hprefix tailTrace_4339696
  have hstable : (prefixWord ++ tailWord_4339696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339696).length < 2 ^ (prefixWord ++ tailWord_4339696).sum := by decide
  have hdescent : baseEnd_4339696 < baseStart_4339696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339723 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3]
def baseStart_4339723 : Nat := 118140960795 + 4339723 * 2 ^ 59
def prefixEnd_4339723 : Nat := 4983230072969 + 3 ^ 40 * 4339723 * 2
def baseEnd_4339723 : Nat := 2228363806371829547504483

theorem tailTrace_4339723 : CollatzResearch.WordTrace tailWord_4339723 prefixEnd_4339723 2228363806371829547504483 := by
  unfold tailWord_4339723
  simp only [CollatzResearch.WordTrace]
  refine ⟨158282701256932211526295823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105521800837954807684197215 158282701256932211526295823)
  ·
    refine ⟨237424051885398317289443735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158282701256932211526295823 237424051885398317289443735)
    ·
      refine ⟨356136077828097475934165603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237424051885398317289443735 356136077828097475934165603)
      ·
        refine ⟨534204116742146213901248405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356136077828097475934165603 534204116742146213901248405)
        ·
          refine ⟨25040817972288103776621019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 534204116742146213901248405 25040817972288103776621019)
          ·
            refine ⟨37561226958432155664931529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25040817972288103776621019 37561226958432155664931529)
            ·
              refine ⟨28170920218824116748698647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37561226958432155664931529 28170920218824116748698647)
              ·
                refine ⟨42256380328236175123047971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28170920218824116748698647 42256380328236175123047971)
                ·
                  refine ⟨63384570492354262684571957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42256380328236175123047971 63384570492354262684571957)
                  ·
                    refine ⟨5942303483658212126678621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63384570492354262684571957 5942303483658212126678621)
                    ·
                      refine ⟨2228363806371829547504483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942303483658212126678621 2228363806371829547504483)
                      ·
                        rfl

theorem cell23_4339723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].length) (baseStart_4339723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339723 prefixEnd_4339723 := by exact prefixLift 4339723
  have htrace : WordTrace (prefixWord ++ tailWord_4339723) baseStart_4339723 baseEnd_4339723 := by
    simpa [prefixWord, tailWord_4339723, baseEnd_4339723] using wordTrace_append hprefix tailTrace_4339723
  have hstable : (prefixWord ++ tailWord_4339723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339723).length < 2 ^ (prefixWord ++ tailWord_4339723).sum := by decide
  have hdescent : baseEnd_4339723 < baseStart_4339723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339764 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4339764 : Nat := 118140960795 + 4339764 * 2 ^ 59
def prefixEnd_4339764 : Nat := 4983230072969 + 3 ^ 40 * 4339764 * 2
def baseEnd_4339764 : Nat := 247598317675407098565755

theorem tailTrace_4339764 : CollatzResearch.WordTrace tailWord_4339764 prefixEnd_4339764 247598317675407098565755 := by
  unfold tailWord_4339764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79142098324891837764269173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105522797766522450352358897 79142098324891837764269173)
  ·
    refine ⟨7419571717958609790400235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79142098324891837764269173 7419571717958609790400235)
    ·
      refine ⟨11129357576937914685600353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419571717958609790400235 11129357576937914685600353)
      ·
        refine ⟨8347018182703436014200265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11129357576937914685600353 8347018182703436014200265)
        ·
          refine ⟨6260263637027577010650199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8347018182703436014200265 6260263637027577010650199)
          ·
            refine ⟨9390395455541365515975299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260263637027577010650199 9390395455541365515975299)
            ·
              refine ⟨14085593183312048273962949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9390395455541365515975299 14085593183312048273962949)
              ·
                refine ⟨2641048721871009051368053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14085593183312048273962949 2641048721871009051368053)
                ·
                  refine ⟨247598317675407098565755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641048721871009051368053 247598317675407098565755)
                  ·
                    rfl

theorem cell23_4339764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4339764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339764 prefixEnd_4339764 := by exact prefixLift 4339764
  have htrace : WordTrace (prefixWord ++ tailWord_4339764) baseStart_4339764 baseEnd_4339764 := by
    simpa [prefixWord, tailWord_4339764, baseEnd_4339764] using wordTrace_append hprefix tailTrace_4339764
  have hstable : (prefixWord ++ tailWord_4339764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339764).length < 2 ^ (prefixWord ++ tailWord_4339764).sum := by decide
  have hdescent : baseEnd_4339764 < baseStart_4339764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339790 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_4339790 : Nat := 118140960795 + 4339790 * 2 ^ 59
def prefixEnd_4339790 : Nat := 4983230072969 + 3 ^ 40 * 4339790 * 2
def baseEnd_4339790 : Nat := 742799403191893595122225

theorem tailTrace_4339790 : CollatzResearch.WordTrace tailWord_4339790 prefixEnd_4339790 742799403191893595122225 := by
  unfold tailWord_4339790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19785643118461185246123103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105523429965126321312656549 19785643118461185246123103)
  ·
    refine ⟨29678464677691777869184655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19785643118461185246123103 29678464677691777869184655)
    ·
      refine ⟨44517697016537666803776983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29678464677691777869184655 44517697016537666803776983)
      ·
        refine ⟨66776545524806500205665475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44517697016537666803776983 66776545524806500205665475)
        ·
          refine ⟨100164818287209750308498213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66776545524806500205665475 100164818287209750308498213)
          ·
            refine ⟨18780903428851828182843415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100164818287209750308498213 18780903428851828182843415)
            ·
              refine ⟨28171355143277742274265123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18780903428851828182843415 28171355143277742274265123)
              ·
                refine ⟨42257032714916613411397685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28171355143277742274265123 42257032714916613411397685)
                ·
                  refine ⟨3961596817023432507318533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42257032714916613411397685 3961596817023432507318533)
                  ·
                    refine ⟨742799403191893595122225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961596817023432507318533 742799403191893595122225)
                    ·
                      rfl

theorem cell23_4339790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_4339790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339790 prefixEnd_4339790 := by exact prefixLift 4339790
  have htrace : WordTrace (prefixWord ++ tailWord_4339790) baseStart_4339790 baseEnd_4339790 := by
    simpa [prefixWord, tailWord_4339790, baseEnd_4339790] using wordTrace_append hprefix tailTrace_4339790
  have hstable : (prefixWord ++ tailWord_4339790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339790).length < 2 ^ (prefixWord ++ tailWord_4339790).sum := by decide
  have hdescent : baseEnd_4339790 < baseStart_4339790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339794 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4339794 : Nat := 118140960795 + 4339794 * 2 ^ 59
def prefixEnd_4339794 : Nat := 4983230072969 + 3 ^ 40 * 4339794 * 2
def baseEnd_4339794 : Nat := 742800087832766256572219

theorem tailTrace_4339794 : CollatzResearch.WordTrace tailWord_4339794 prefixEnd_4339794 742800087832766256572219 := by
  unfold tailWord_4339794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39571322709918747663032609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105523527226449993768086957 39571322709918747663032609)
  ·
    refine ⟨29678492032439060747274457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39571322709918747663032609 29678492032439060747274457)
    ·
      refine ⟨22258869024329295560455843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29678492032439060747274457 22258869024329295560455843)
      ·
        refine ⟨33388303536493943340683765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22258869024329295560455843 33388303536493943340683765)
        ·
          refine ⟨3130153456546307188189103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33388303536493943340683765 3130153456546307188189103)
          ·
            refine ⟨4695230184819460782283655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130153456546307188189103 4695230184819460782283655)
            ·
              refine ⟨7042845277229191173425483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695230184819460782283655 7042845277229191173425483)
              ·
                refine ⟨10564267915843786760138225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7042845277229191173425483 10564267915843786760138225)
                ·
                  refine ⟨7923200936882840070103669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10564267915843786760138225 7923200936882840070103669)
                  ·
                    refine ⟨742800087832766256572219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7923200936882840070103669 742800087832766256572219)
                    ·
                      rfl

theorem cell23_4339794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4339794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339794 prefixEnd_4339794 := by exact prefixLift 4339794
  have htrace : WordTrace (prefixWord ++ tailWord_4339794) baseStart_4339794 baseEnd_4339794 := by
    simpa [prefixWord, tailWord_4339794, baseEnd_4339794] using wordTrace_append hprefix tailTrace_4339794
  have hstable : (prefixWord ++ tailWord_4339794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339794).length < 2 ^ (prefixWord ++ tailWord_4339794).sum := by decide
  have hdescent : baseEnd_4339794 < baseStart_4339794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339797 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4339797 : Nat := 118140960795 + 4339797 * 2 ^ 59
def prefixEnd_4339797 : Nat := 4983230072969 + 3 ^ 40 * 4339797 * 2
def baseEnd_4339797 : Nat := 2228401803940262257979143

theorem tailTrace_4339797 : CollatzResearch.WordTrace tailWord_4339797 prefixEnd_4339797 2228401803940262257979143 := by
  unfold tailWord_4339797
  simp only [CollatzResearch.WordTrace]
  refine ⟨158285400258664122164489645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105523600172442748109659763 158285400258664122164489645)
  ·
    refine ⟨59357025096999045811683617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158285400258664122164489645 59357025096999045811683617)
    ·
      refine ⟨44517768822749284358762713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59357025096999045811683617 44517768822749284358762713)
      ·
        refine ⟨33388326617061963269072035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44517768822749284358762713 33388326617061963269072035)
        ·
          refine ⟨50082489925592944903608053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33388326617061963269072035 50082489925592944903608053)
          ·
            refine ⟨4695233430524338584713255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50082489925592944903608053 4695233430524338584713255)
            ·
              refine ⟨7042850145786507877069883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695233430524338584713255 7042850145786507877069883)
              ·
                refine ⟨10564275218679761815604825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7042850145786507877069883 10564275218679761815604825)
                ·
                  refine ⟨7923206414009821361703619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10564275218679761815604825 7923206414009821361703619)
                  ·
                    refine ⟨11884809621014732042555429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7923206414009821361703619 11884809621014732042555429)
                    ·
                      refine ⟨2228401803940262257979143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11884809621014732042555429 2228401803940262257979143)
                      ·
                        rfl

theorem cell23_4339797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4339797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339797 prefixEnd_4339797 := by exact prefixLift 4339797
  have htrace : WordTrace (prefixWord ++ tailWord_4339797) baseStart_4339797 baseEnd_4339797 := by
    simpa [prefixWord, tailWord_4339797, baseEnd_4339797] using wordTrace_append hprefix tailTrace_4339797
  have hstable : (prefixWord ++ tailWord_4339797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339797).length < 2 ^ (prefixWord ++ tailWord_4339797).sum := by decide
  have hdescent : baseEnd_4339797 < baseStart_4339797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339800 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4339800 : Nat := 118140960795 + 4339800 * 2 ^ 59
def prefixEnd_4339800 : Nat := 4983230072969 + 3 ^ 40 * 4339800 * 2
def baseEnd_4339800 : Nat := 2228403344382225746241629

theorem tailTrace_4339800 : CollatzResearch.WordTrace tailWord_4339800 prefixEnd_4339800 2228403344382225746241629 := by
  unfold tailWord_4339800
  simp only [CollatzResearch.WordTrace]
  refine ⟨79142754838826626838424427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105523673118435502451232569 79142754838826626838424427)
  ·
    refine ⟨118714132258239940257636641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79142754838826626838424427 118714132258239940257636641)
    ·
      refine ⟨89035599193679955193227481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118714132258239940257636641 89035599193679955193227481)
      ·
        refine ⟨66776699395259966394920611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89035599193679955193227481 66776699395259966394920611)
        ·
          refine ⟨100165049092889949592380917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66776699395259966394920611 100165049092889949592380917)
          ·
            refine ⟨9390473352458432774285711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100165049092889949592380917 9390473352458432774285711)
            ·
              refine ⟨14085710028687649161428567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9390473352458432774285711 14085710028687649161428567)
              ·
                refine ⟨21128565043031473742142851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14085710028687649161428567 21128565043031473742142851)
                ·
                  refine ⟨31692847564547210613214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21128565043031473742142851 31692847564547210613214277)
                  ·
                    refine ⟨5942408918352601989977677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31692847564547210613214277 5942408918352601989977677)
                    ·
                      refine ⟨2228403344382225746241629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942408918352601989977677 2228403344382225746241629)
                      ·
                        rfl

theorem cell23_4339800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4339800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339800 prefixEnd_4339800 := by exact prefixLift 4339800
  have htrace : WordTrace (prefixWord ++ tailWord_4339800) baseStart_4339800 baseEnd_4339800 := by
    simpa [prefixWord, tailWord_4339800, baseEnd_4339800] using wordTrace_append hprefix tailTrace_4339800
  have hstable : (prefixWord ++ tailWord_4339800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339800).length < 2 ^ (prefixWord ++ tailWord_4339800).sum := by decide
  have hdescent : baseEnd_4339800 < baseStart_4339800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339820 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 6]
def baseStart_4339820 : Nat := 118140960795 + 4339820 * 2 ^ 59
def prefixEnd_4339820 : Nat := 4983230072969 + 3 ^ 40 * 4339820 * 2
def baseEnd_4339820 : Nat := 247601512666146185332393

theorem tailTrace_4339820 : CollatzResearch.WordTrace tailWord_4339820 prefixEnd_4339820 247601512666146185332393 := by
  unfold tailWord_4339820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79143119568790398546288457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105524159425053864728384609 79143119568790398546288457)
  ·
    refine ⟨59357339676592798909716343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79143119568790398546288457 59357339676592798909716343)
    ·
      refine ⟨89036009514889198364574515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59357339676592798909716343 89036009514889198364574515)
      ·
        refine ⟨133554014272333797546861773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89036009514889198364574515 133554014272333797546861773)
        ·
          refine ⟨50082755352125174080073165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133554014272333797546861773 50082755352125174080073165)
          ·
            refine ⟨18781033257046940280027437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50082755352125174080073165 18781033257046940280027437)
            ·
              refine ⟨7042887471392602605010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18781033257046940280027437 7042887471392602605010289)
              ·
                refine ⟨5282165603544451953757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042887471392602605010289 5282165603544451953757717)
                ·
                  refine ⟨247601512666146185332393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5282165603544451953757717 247601512666146185332393)
                  ·
                    rfl

theorem cell23_4339820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_4339820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339820 prefixEnd_4339820 := by exact prefixLift 4339820
  have htrace : WordTrace (prefixWord ++ tailWord_4339820) baseStart_4339820 baseEnd_4339820 := by
    simpa [prefixWord, tailWord_4339820, baseEnd_4339820] using wordTrace_append hprefix tailTrace_4339820
  have hstable : (prefixWord ++ tailWord_4339820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339820).length < 2 ^ (prefixWord ++ tailWord_4339820).sum := by decide
  have hdescent : baseEnd_4339820 < baseStart_4339820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339823 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_4339823 : Nat := 118140960795 + 4339823 * 2 ^ 59
def prefixEnd_4339823 : Nat := 4983230072969 + 3 ^ 40 * 4339823 * 2
def baseEnd_4339823 : Nat := 2228415154437279156254023

theorem tailTrace_4339823 : CollatzResearch.WordTrace tailWord_4339823 prefixEnd_4339823 2228415154437279156254023 := by
  unfold tailWord_4339823
  simp only [CollatzResearch.WordTrace]
  refine ⟨158286348556569928604936123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105524232371046619069957415 158286348556569928604936123)
  ·
    refine ⟨237429522834854892907404185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158286348556569928604936123 237429522834854892907404185)
    ·
      refine ⟨178072142126141169680553139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237429522834854892907404185 178072142126141169680553139)
      ·
        refine ⟨267108213189211754520829709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178072142126141169680553139 267108213189211754520829709)
        ·
          refine ⟨100165579945954407945311141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267108213189211754520829709 100165579945954407945311141)
          ·
            refine ⟨18781046239866451489745839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100165579945954407945311141 18781046239866451489745839)
            ·
              refine ⟨28171569359799677234618759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18781046239866451489745839 28171569359799677234618759)
              ·
                refine ⟨42257354039699515851928139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28171569359799677234618759 42257354039699515851928139)
                ·
                  refine ⟨63386031059549273777892209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42257354039699515851928139 63386031059549273777892209)
                  ·
                    refine ⟨47539523294661955333419157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63386031059549273777892209 47539523294661955333419157)
                    ·
                      refine ⟨2228415154437279156254023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47539523294661955333419157 2228415154437279156254023)
                      ·
                        rfl

theorem cell23_4339823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_4339823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339823 prefixEnd_4339823 := by exact prefixLift 4339823
  have htrace : WordTrace (prefixWord ++ tailWord_4339823) baseStart_4339823 baseEnd_4339823 := by
    simpa [prefixWord, tailWord_4339823, baseEnd_4339823] using wordTrace_append hprefix tailTrace_4339823
  have hstable : (prefixWord ++ tailWord_4339823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339823).length < 2 ^ (prefixWord ++ tailWord_4339823).sum := by decide
  have hdescent : baseEnd_4339823 < baseStart_4339823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339837 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 6]
def baseStart_4339837 : Nat := 118140960795 + 4339837 * 2 ^ 59
def prefixEnd_4339837 : Nat := 4983230072969 + 3 ^ 40 * 4339837 * 2
def baseEnd_4339837 : Nat := 247602482574049122386551

theorem tailTrace_4339837 : CollatzResearch.WordTrace tailWord_4339837 prefixEnd_4339837 247602482574049122386551 := by
  unfold tailWord_4339837
  simp only [CollatzResearch.WordTrace]
  refine ⟨158286859178519208995945765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105524572785679472663963843 158286859178519208995945765)
  ·
    refine ⟨29678786095972351686739831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158286859178519208995945765 29678786095972351686739831)
    ·
      refine ⟨44518179143958527530109747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29678786095972351686739831 44518179143958527530109747)
      ·
        refine ⟨66777268715937791295164621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44518179143958527530109747 66777268715937791295164621)
        ·
          refine ⟨25041475768476671735686733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66777268715937791295164621 25041475768476671735686733)
          ·
            refine ⟨9390553413178751900882525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25041475768476671735686733 9390553413178751900882525)
            ·
              refine ⟨3521457529942031962830947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9390553413178751900882525 3521457529942031962830947)
              ·
                refine ⟨5282186294913047944246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521457529942031962830947 5282186294913047944246421)
                ·
                  refine ⟨247602482574049122386551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5282186294913047944246421 247602482574049122386551)
                  ·
                    rfl

theorem cell23_4339837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_4339837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339837 prefixEnd_4339837 := by exact prefixLift 4339837
  have htrace : WordTrace (prefixWord ++ tailWord_4339837) baseStart_4339837 baseEnd_4339837 := by
    simpa [prefixWord, tailWord_4339837, baseEnd_4339837] using wordTrace_append hprefix tailTrace_4339837
  have hstable : (prefixWord ++ tailWord_4339837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339837).length < 2 ^ (prefixWord ++ tailWord_4339837).sum := by decide
  have hdescent : baseEnd_4339837 < baseStart_4339837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339847 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_4339847 : Nat := 118140960795 + 4339847 * 2 ^ 59
def prefixEnd_4339847 : Nat := 4983230072969 + 3 ^ 40 * 4339847 * 2
def baseEnd_4339847 : Nat := 2228427477972987062353913

theorem tailTrace_4339847 : CollatzResearch.WordTrace tailWord_4339847 prefixEnd_4339847 2228427477972987062353913 := by
  unfold tailWord_4339847
  simp only [CollatzResearch.WordTrace]
  refine ⟨158287223908482980703809795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105524815938988653802539863 158287223908482980703809795)
  ·
    refine ⟨237430835862724471055714693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158287223908482980703809795 237430835862724471055714693)
    ·
      refine ⟨44518281724260838322946505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237430835862724471055714693 44518281724260838322946505)
      ·
        refine ⟨33388711293195628742209879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44518281724260838322946505 33388711293195628742209879)
        ·
          refine ⟨50083066939793443113314819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33388711293195628742209879 50083066939793443113314819)
          ·
            refine ⟨75124600409690164669972229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50083066939793443113314819 75124600409690164669972229)
            ·
              refine ⟨14085862576816905875619793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75124600409690164669972229 14085862576816905875619793)
              ·
                refine ⟨10564396932612679406714845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14085862576816905875619793 10564396932612679406714845)
                ·
                  refine ⟨3961648849729754777518067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10564396932612679406714845 3961648849729754777518067)
                  ·
                    refine ⟨5942473274594632166277101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961648849729754777518067 5942473274594632166277101)
                    ·
                      refine ⟨2228427477972987062353913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942473274594632166277101 2228427477972987062353913)
                      ·
                        rfl

theorem cell23_4339847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_4339847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339847 prefixEnd_4339847 := by exact prefixLift 4339847
  have htrace : WordTrace (prefixWord ++ tailWord_4339847) baseStart_4339847 baseEnd_4339847 := by
    simpa [prefixWord, tailWord_4339847, baseEnd_4339847] using wordTrace_append hprefix tailTrace_4339847
  have hstable : (prefixWord ++ tailWord_4339847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339847).length < 2 ^ (prefixWord ++ tailWord_4339847).sum := by decide
  have hdescent : baseEnd_4339847 < baseStart_4339847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339874 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4339874 : Nat := 118140960795 + 4339874 * 2 ^ 59
def prefixEnd_4339874 : Nat := 4983230072969 + 3 ^ 40 * 4339874 * 2
def baseEnd_4339874 : Nat := 2228441341950658456716289

theorem tailTrace_4339874 : CollatzResearch.WordTrace tailWord_4339874 prefixEnd_4339874 2228441341950658456716289 := by
  unfold tailWord_4339874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39572052169846291078760669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105525472452923442876695117 39572052169846291078760669)
  ·
    refine ⟨14839519563692359154535251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39572052169846291078760669 14839519563692359154535251)
    ·
      refine ⟨22259279345538538731802877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14839519563692359154535251 22259279345538538731802877)
      ·
        refine ⟨8347229754576952024426079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22259279345538538731802877 8347229754576952024426079)
        ·
          refine ⟨12520844631865428036639119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8347229754576952024426079 12520844631865428036639119)
          ·
            refine ⟨18781266947798142054958679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12520844631865428036639119 18781266947798142054958679)
            ·
              refine ⟨28171900421697213082438019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18781266947798142054958679 28171900421697213082438019)
              ·
                refine ⟨42257850632545819623657029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28171900421697213082438019 42257850632545819623657029)
                ·
                  refine ⟨7923346993602341179435693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42257850632545819623657029 7923346993602341179435693)
                  ·
                    refine ⟨2971255122600877942288385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7923346993602341179435693 2971255122600877942288385)
                    ·
                      refine ⟨2228441341950658456716289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971255122600877942288385 2228441341950658456716289)
                      ·
                        rfl

theorem cell23_4339874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4339874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339874 prefixEnd_4339874 := by exact prefixLift 4339874
  have htrace : WordTrace (prefixWord ++ tailWord_4339874) baseStart_4339874 baseEnd_4339874 := by
    simpa [prefixWord, tailWord_4339874, baseEnd_4339874] using wordTrace_append hprefix tailTrace_4339874
  have hstable : (prefixWord ++ tailWord_4339874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339874).length < 2 ^ (prefixWord ++ tailWord_4339874).sum := by decide
  have hdescent : baseEnd_4339874 < baseStart_4339874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339890 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4339890 : Nat := 118140960795 + 4339890 * 2 ^ 59
def prefixEnd_4339890 : Nat := 4983230072969 + 3 ^ 40 * 4339890 * 2
def baseEnd_4339890 : Nat := 2228449557641130394116215

theorem tailTrace_4339890 : CollatzResearch.WordTrace tailWord_4339890 prefixEnd_4339890 2228449557641130394116215 := by
  unfold tailWord_4339890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39572198061831799761906281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105525861498218132698416749 39572198061831799761906281)
  ·
    refine ⟨29679148546373849821429711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39572198061831799761906281 29679148546373849821429711)
    ·
      refine ⟨44518722819560774732144567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29679148546373849821429711 44518722819560774732144567)
      ·
        refine ⟨66778084229341162098216851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44518722819560774732144567 66778084229341162098216851)
        ·
          refine ⟨100167126344011743147325277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66778084229341162098216851 100167126344011743147325277)
          ·
            refine ⟨37562672379004403680246979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100167126344011743147325277 37562672379004403680246979)
            ·
              refine ⟨56344008568506605520370469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37562672379004403680246979 56344008568506605520370469)
              ·
                refine ⟨10564501606594988535069463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56344008568506605520370469 10564501606594988535069463)
                ·
                  refine ⟨15846752409892482802604195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10564501606594988535069463 15846752409892482802604195)
                  ·
                    refine ⟨23770128614838724203906293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15846752409892482802604195 23770128614838724203906293)
                    ·
                      refine ⟨2228449557641130394116215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23770128614838724203906293 2228449557641130394116215)
                      ·
                        rfl

theorem cell23_4339890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4339890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339890 prefixEnd_4339890 := by exact prefixLift 4339890
  have htrace : WordTrace (prefixWord ++ tailWord_4339890) baseStart_4339890 baseEnd_4339890 := by
    simpa [prefixWord, tailWord_4339890, baseEnd_4339890] using wordTrace_append hprefix tailTrace_4339890
  have hstable : (prefixWord ++ tailWord_4339890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339890).length < 2 ^ (prefixWord ++ tailWord_4339890).sum := by decide
  have hdescent : baseEnd_4339890 < baseStart_4339890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339897 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_4339897 : Nat := 118140960795 + 4339897 * 2 ^ 59
def prefixEnd_4339897 : Nat := 4983230072969 + 3 ^ 40 * 4339897 * 2
def baseEnd_4339897 : Nat := 742817717335237288909561

theorem tailTrace_4339897 : CollatzResearch.WordTrace tailWord_4339897 prefixEnd_4339897 742817717335237288909561 := by
  unfold tailWord_4339897
  simp only [CollatzResearch.WordTrace]
  refine ⟨158289047558301839243129945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105526031705534559495419963 158289047558301839243129945)
  ·
    refine ⟨118716785668726379432347459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158289047558301839243129945 118716785668726379432347459)
    ·
      refine ⟨178075178503089569148521189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118716785668726379432347459 178075178503089569148521189)
      ·
        refine ⟨33389095969329294215347723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178075178503089569148521189 33389095969329294215347723)
        ·
          refine ⟨50083643953993941323021585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33389095969329294215347723 50083643953993941323021585)
          ·
            refine ⟨37562732965495455992266189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50083643953993941323021585 37562732965495455992266189)
            ·
              refine ⟨14086024862060795997099821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37562732965495455992266189 14086024862060795997099821)
              ·
                refine ⟨5282259323272798498912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14086024862060795997099821 5282259323272798498912433)
                ·
                  refine ⟨3961694492454598874184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5282259323272798498912433 3961694492454598874184325)
                  ·
                    refine ⟨742817717335237288909561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961694492454598874184325 742817717335237288909561)
                    ·
                      rfl

theorem cell23_4339897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_4339897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339897 prefixEnd_4339897 := by exact prefixLift 4339897
  have htrace : WordTrace (prefixWord ++ tailWord_4339897) baseStart_4339897 baseEnd_4339897 := by
    simpa [prefixWord, tailWord_4339897, baseEnd_4339897] using wordTrace_append hprefix tailTrace_4339897
  have hstable : (prefixWord ++ tailWord_4339897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339897).length < 2 ^ (prefixWord ++ tailWord_4339897).sum := by decide
  have hdescent : baseEnd_4339897 < baseStart_4339897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339904 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_4339904 : Nat := 118140960795 + 4339904 * 2 ^ 59
def prefixEnd_4339904 : Nat := 4983230072969 + 3 ^ 40 * 4339904 * 2
def baseEnd_4339904 : Nat := 2228456746370293339341151

theorem tailTrace_4339904 : CollatzResearch.WordTrace tailWord_4339904 prefixEnd_4339904 2228456746370293339341151 := by
  unfold tailWord_4339904
  simp only [CollatzResearch.WordTrace]
  refine ⟨79144651434638239719317383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105526201912850986292423177 79144651434638239719317383)
  ·
    refine ⟨118716977151957359578976075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79144651434638239719317383 118716977151957359578976075)
    ·
      refine ⟨178075465727936039368464113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118716977151957359578976075 178075465727936039368464113)
      ·
        refine ⟨133556599295952029526348085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178075465727936039368464113 133556599295952029526348085)
        ·
          refine ⟨12520931183995502768095133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133556599295952029526348085 12520931183995502768095133)
          ·
            refine ⟨4695349193998313538035675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12520931183995502768095133 4695349193998313538035675)
            ·
              refine ⟨7043023790997470307053513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695349193998313538035675 7043023790997470307053513)
              ·
                refine ⟨5282267843248102730290135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7043023790997470307053513 5282267843248102730290135)
                ·
                  refine ⟨7923401764872154095435203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282267843248102730290135 7923401764872154095435203)
                  ·
                    refine ⟨11885102647308231143152805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7923401764872154095435203 11885102647308231143152805)
                    ·
                      refine ⟨2228456746370293339341151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11885102647308231143152805 2228456746370293339341151)
                      ·
                        rfl

theorem cell23_4339904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_4339904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339904 prefixEnd_4339904 := by exact prefixLift 4339904
  have htrace : WordTrace (prefixWord ++ tailWord_4339904) baseStart_4339904 baseEnd_4339904 := by
    simpa [prefixWord, tailWord_4339904, baseEnd_4339904] using wordTrace_append hprefix tailTrace_4339904
  have hstable : (prefixWord ++ tailWord_4339904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339904).length < 2 ^ (prefixWord ++ tailWord_4339904).sum := by decide
  have hdescent : baseEnd_4339904 < baseStart_4339904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339923 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 9]
def baseStart_4339923 : Nat := 118140960795 + 4339923 * 2 ^ 59
def prefixEnd_4339923 : Nat := 4983230072969 + 3 ^ 40 * 4339923 * 2
def baseEnd_4339923 : Nat := 742822167500909588334521

theorem tailTrace_4339923 : CollatzResearch.WordTrace tailWord_4339923 prefixEnd_4339923 742822167500909588334521 := by
  unfold tailWord_4339923
  simp only [CollatzResearch.WordTrace]
  refine ⟨158289995856207645683576423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105526663904138430455717615 158289995856207645683576423)
  ·
    refine ⟨237434993784311468525364635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158289995856207645683576423 237434993784311468525364635)
    ·
      refine ⟨356152490676467202788046953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237434993784311468525364635 356152490676467202788046953)
      ·
        refine ⟨267114368007350402091035215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356152490676467202788046953 267114368007350402091035215)
        ·
          refine ⟨400671552011025603136552823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267114368007350402091035215 400671552011025603136552823)
          ·
            refine ⟨601007328016538404704829235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400671552011025603136552823 601007328016538404704829235)
            ·
              refine ⟨901510992024807607057243853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601007328016538404704829235 901510992024807607057243853)
              ·
                refine ⟨338066622009302852646466445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901510992024807607057243853 338066622009302852646466445)
                ·
                  refine ⟨126774983253488569742424917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338066622009302852646466445 126774983253488569742424917)
                  ·
                    refine ⟨742822167500909588334521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126774983253488569742424917 742822167500909588334521)
                    ·
                      rfl

theorem cell23_4339923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_4339923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339923 prefixEnd_4339923 := by exact prefixLift 4339923
  have htrace : WordTrace (prefixWord ++ tailWord_4339923) baseStart_4339923 baseEnd_4339923 := by
    simpa [prefixWord, tailWord_4339923, baseEnd_4339923] using wordTrace_append hprefix tailTrace_4339923
  have hstable : (prefixWord ++ tailWord_4339923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339923).length < 2 ^ (prefixWord ++ tailWord_4339923).sum := by decide
  have hdescent : baseEnd_4339923 < baseStart_4339923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339932 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4339932 : Nat := 118140960795 + 4339932 * 2 ^ 59
def prefixEnd_4339932 : Nat := 4983230072969 + 3 ^ 40 * 4339932 * 2
def baseEnd_4339932 : Nat := 2228471123828619229791023

theorem tailTrace_4339932 : CollatzResearch.WordTrace tailWord_4339932 prefixEnd_4339932 2228471123828619229791023 := by
  unfold tailWord_4339932
  simp only [CollatzResearch.WordTrace]
  refine ⟨79145162056587520110327025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105526882742116693480436033 79145162056587520110327025)
  ·
    refine ⟨59358871542440640082745269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79145162056587520110327025 59358871542440640082745269)
    ·
      refine ⟨5564894207103810007757369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59358871542440640082745269 5564894207103810007757369)
      ·
        refine ⟨4173670655327857505818027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5564894207103810007757369 4173670655327857505818027)
        ·
          refine ⟨6260505982991786258727041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173670655327857505818027 6260505982991786258727041)
          ·
            refine ⟨4695379487243839694045281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6260505982991786258727041 4695379487243839694045281)
            ·
              refine ⟨3521534615432879770533961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695379487243839694045281 3521534615432879770533961)
              ·
                refine ⟨2641150961574659827900471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521534615432879770533961 2641150961574659827900471)
                ·
                  refine ⟨3961726442361989741850707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641150961574659827900471 3961726442361989741850707)
                  ·
                    refine ⟨5942589663542984612776061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961726442361989741850707 5942589663542984612776061)
                    ·
                      refine ⟨2228471123828619229791023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942589663542984612776061 2228471123828619229791023)
                      ·
                        rfl

theorem cell23_4339932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4339932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339932 prefixEnd_4339932 := by exact prefixLift 4339932
  have htrace : WordTrace (prefixWord ++ tailWord_4339932) baseStart_4339932 baseEnd_4339932 := by
    simpa [prefixWord, tailWord_4339932, baseEnd_4339932] using wordTrace_append hprefix tailTrace_4339932
  have hstable : (prefixWord ++ tailWord_4339932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339932).length < 2 ^ (prefixWord ++ tailWord_4339932).sum := by decide
  have hdescent : baseEnd_4339932 < baseStart_4339932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339947 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 5, 3, 2]
def baseStart_4339947 : Nat := 118140960795 + 4339947 * 2 ^ 59
def prefixEnd_4339947 : Nat := 4983230072969 + 3 ^ 40 * 4339947 * 2
def baseEnd_4339947 : Nat := 2228478826038436671103453

theorem tailTrace_4339947 : CollatzResearch.WordTrace tailWord_4339947 prefixEnd_4339947 2228478826038436671103453 := by
  unfold tailWord_4339947
  simp only [CollatzResearch.WordTrace]
  refine ⟨158290871208120697782450095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105527247472080465188300063 158290871208120697782450095)
  ·
    refine ⟨237436306812181046673675143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158290871208120697782450095 237436306812181046673675143)
    ·
      refine ⟨356154460218271570010512715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237436306812181046673675143 356154460218271570010512715)
      ·
        refine ⟨534231690327407355015769073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356154460218271570010512715 534231690327407355015769073)
        ·
          refine ⟨400673767745555516261826805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534231690327407355015769073 400673767745555516261826805)
          ·
            refine ⟨37563165726145829649546263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 400673767745555516261826805 37563165726145829649546263)
            ·
              refine ⟨56344748589218744474319395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37563165726145829649546263 56344748589218744474319395)
              ·
                refine ⟨84517122883828116711479093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56344748589218744474319395 84517122883828116711479093)
                ·
                  refine ⟨7923480270358885941701165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84517122883828116711479093 7923480270358885941701165)
                  ·
                    refine ⟨2971305101384582228137937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7923480270358885941701165 2971305101384582228137937)
                    ·
                      refine ⟨2228478826038436671103453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971305101384582228137937 2228478826038436671103453)
                      ·
                        rfl

theorem cell23_4339947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3, 2].length) (baseStart_4339947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339947 prefixEnd_4339947 := by exact prefixLift 4339947
  have htrace : WordTrace (prefixWord ++ tailWord_4339947) baseStart_4339947 baseEnd_4339947 := by
    simpa [prefixWord, tailWord_4339947, baseEnd_4339947] using wordTrace_append hprefix tailTrace_4339947
  have hstable : (prefixWord ++ tailWord_4339947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339947).length < 2 ^ (prefixWord ++ tailWord_4339947).sum := by decide
  have hdescent : baseEnd_4339947 < baseStart_4339947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339950 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4339950 : Nat := 118140960795 + 4339950 * 2 ^ 59
def prefixEnd_4339950 : Nat := 4983230072969 + 3 ^ 40 * 4339950 * 2
def baseEnd_4339950 : Nat := 2228480366480400159365939

theorem tailTrace_4339950 : CollatzResearch.WordTrace tailWord_4339950 prefixEnd_4339950 2228480366480400159365939 := by
  unfold tailWord_4339950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19786372578388728661851163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105527320418073219529872869 19786372578388728661851163)
  ·
    refine ⟨29679558867583092992776745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19786372578388728661851163 29679558867583092992776745)
    ·
      refine ⟨22259669150687319744582559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29679558867583092992776745 22259669150687319744582559)
      ·
        refine ⟨33389503726030979616873839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22259669150687319744582559 33389503726030979616873839)
        ·
          refine ⟨50084255589046469425310759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33389503726030979616873839 50084255589046469425310759)
          ·
            refine ⟨75126383383569704137966139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50084255589046469425310759 75126383383569704137966139)
            ·
              refine ⟨112689575075354556206949209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75126383383569704137966139 112689575075354556206949209)
              ·
                refine ⟨84517181306515917155211907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112689575075354556206949209 84517181306515917155211907)
                ·
                  refine ⟨126775771959773875732817861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84517181306515917155211907 126775771959773875732817861)
                  ·
                    refine ⟨23770457242457601699903349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126775771959773875732817861 23770457242457601699903349)
                    ·
                      refine ⟨2228480366480400159365939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23770457242457601699903349 2228480366480400159365939)
                      ·
                        rfl

theorem cell23_4339950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4339950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339950 prefixEnd_4339950 := by exact prefixLift 4339950
  have htrace : WordTrace (prefixWord ++ tailWord_4339950) baseStart_4339950 baseEnd_4339950 := by
    simpa [prefixWord, tailWord_4339950, baseEnd_4339950] using wordTrace_append hprefix tailTrace_4339950
  have hstable : (prefixWord ++ tailWord_4339950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339950).length < 2 ^ (prefixWord ++ tailWord_4339950).sum := by decide
  have hdescent : baseEnd_4339950 < baseStart_4339950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339954 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4339954 : Nat := 118140960795 + 4339954 * 2 ^ 59
def prefixEnd_4339954 : Nat := 4983230072969 + 3 ^ 40 * 4339954 * 2
def baseEnd_4339954 : Nat := 2228482420403018143715921

theorem tailTrace_4339954 : CollatzResearch.WordTrace tailWord_4339954 prefixEnd_4339954 2228482420403018143715921 := by
  unfold tailWord_4339954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39572781629773834494488729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105527417679396891985303277 39572781629773834494488729)
  ·
    refine ⟨29679586222330375870866547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39572781629773834494488729 29679586222330375870866547)
    ·
      refine ⟨44519379333495563806299821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29679586222330375870866547 44519379333495563806299821)
      ·
        refine ⟨16694767250060836427362433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44519379333495563806299821 16694767250060836427362433)
        ·
          refine ⟨12521075437545627320521825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16694767250060836427362433 12521075437545627320521825)
          ·
            refine ⟨9390806578159220490391369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12521075437545627320521825 9390806578159220490391369)
            ·
              refine ⟨7043104933619415367793527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9390806578159220490391369 7043104933619415367793527)
              ·
                refine ⟨10564657400429123051690291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043104933619415367793527 10564657400429123051690291)
                ·
                  refine ⟨15846986100643684577535437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10564657400429123051690291 15846986100643684577535437)
                  ·
                    refine ⟨5942619787741381716575789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15846986100643684577535437 5942619787741381716575789)
                    ·
                      refine ⟨2228482420403018143715921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942619787741381716575789 2228482420403018143715921)
                      ·
                        rfl

theorem cell23_4339954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4339954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339954 prefixEnd_4339954 := by exact prefixLift 4339954
  have htrace : WordTrace (prefixWord ++ tailWord_4339954) baseStart_4339954 baseEnd_4339954 := by
    simpa [prefixWord, tailWord_4339954, baseEnd_4339954] using wordTrace_append hprefix tailTrace_4339954
  have hstable : (prefixWord ++ tailWord_4339954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339954).length < 2 ^ (prefixWord ++ tailWord_4339954).sum := by decide
  have hdescent : baseEnd_4339954 < baseStart_4339954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339964 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_4339964 : Nat := 118140960795 + 4339964 * 2 ^ 59
def prefixEnd_4339964 : Nat := 4983230072969 + 3 ^ 40 * 4339964 * 2
def baseEnd_4339964 : Nat := 2228487555209563104590875

theorem tailTrace_4339964 : CollatzResearch.WordTrace tailWord_4339964 prefixEnd_4339964 2228487555209563104590875 := by
  unfold tailWord_4339964
  simp only [CollatzResearch.WordTrace]
  refine ⟨79145745624529554842909473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105527660832706073123879297 79145745624529554842909473)
  ·
    refine ⟨59359309218397166132182105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79145745624529554842909473 59359309218397166132182105)
    ·
      refine ⟨44519481913797874599136579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59359309218397166132182105 44519481913797874599136579)
      ·
        refine ⟨66779222870696811898704869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44519481913797874599136579 66779222870696811898704869)
        ·
          refine ⟨12521104288255652231007163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66779222870696811898704869 12521104288255652231007163)
          ·
            refine ⟨18781656432383478346510745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12521104288255652231007163 18781656432383478346510745)
            ·
              refine ⟨14086242324287608759883059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18781656432383478346510745 14086242324287608759883059)
              ·
                refine ⟨21129363486431413139824589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14086242324287608759883059 21129363486431413139824589)
                ·
                  refine ⟨7923511307411779927434221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21129363486431413139824589 7923511307411779927434221)
                  ·
                    refine ⟨2971316740279417472787833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7923511307411779927434221 2971316740279417472787833)
                    ·
                      refine ⟨2228487555209563104590875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971316740279417472787833 2228487555209563104590875)
                      ·
                        rfl

theorem cell23_4339964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_4339964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339964 prefixEnd_4339964 := by exact prefixLift 4339964
  have htrace : WordTrace (prefixWord ++ tailWord_4339964) baseStart_4339964 baseEnd_4339964 := by
    simpa [prefixWord, tailWord_4339964, baseEnd_4339964] using wordTrace_append hprefix tailTrace_4339964
  have hstable : (prefixWord ++ tailWord_4339964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339964).length < 2 ^ (prefixWord ++ tailWord_4339964).sum := by decide
  have hdescent : baseEnd_4339964 < baseStart_4339964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339975 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4339975 : Nat := 118140960795 + 4339975 * 2 ^ 59
def prefixEnd_4339975 : Nat := 4983230072969 + 3 ^ 40 * 4339975 * 2
def baseEnd_4339975 : Nat := 2228493203496762561553325

theorem tailTrace_4339975 : CollatzResearch.WordTrace tailWord_4339975 prefixEnd_4339975 2228493203496762561553325 := by
  unfold tailWord_4339975
  simp only [CollatzResearch.WordTrace]
  refine ⟨158291892452019258564469379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105527928301346172376312919 158291892452019258564469379)
  ·
    refine ⟨237437838678028887846704069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158291892452019258564469379 237437838678028887846704069)
    ·
      refine ⟨44519594752130416471257013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237437838678028887846704069 44519594752130416471257013)
      ·
        refine ⟨4173712008012226544180345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44519594752130416471257013 4173712008012226544180345)
        ·
          refine ⟨3130284006009169908135259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4173712008012226544180345 3130284006009169908135259)
          ·
            refine ⟨4695426009013754862202889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130284006009169908135259 4695426009013754862202889)
            ·
              refine ⟨3521569506760316146652167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695426009013754862202889 3521569506760316146652167)
              ·
                refine ⟨5282354260140474219978251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521569506760316146652167 5282354260140474219978251)
                ·
                  refine ⟨7923531390210711329967377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282354260140474219978251 7923531390210711329967377)
                  ·
                    refine ⟨5942648542658033497475533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7923531390210711329967377 5942648542658033497475533)
                    ·
                      refine ⟨2228493203496762561553325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942648542658033497475533 2228493203496762561553325)
                      ·
                        rfl

theorem cell23_4339975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4339975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339975 prefixEnd_4339975 := by exact prefixLift 4339975
  have htrace : WordTrace (prefixWord ++ tailWord_4339975) baseStart_4339975 baseEnd_4339975 := by
    simpa [prefixWord, tailWord_4339975, baseEnd_4339975] using wordTrace_append hprefix tailTrace_4339975
  have hstable : (prefixWord ++ tailWord_4339975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339975).length < 2 ^ (prefixWord ++ tailWord_4339975).sum := by decide
  have hdescent : baseEnd_4339975 < baseStart_4339975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4339980 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4339980 : Nat := 118140960795 + 4339980 * 2 ^ 59
def prefixEnd_4339980 : Nat := 4983230072969 + 3 ^ 40 * 4339980 * 2
def baseEnd_4339980 : Nat := 2228495770900035041990801

theorem tailTrace_4339980 : CollatzResearch.WordTrace tailWord_4339980 prefixEnd_4339980 2228495770900035041990801 := by
  unfold tailWord_4339980
  simp only [CollatzResearch.WordTrace]
  refine ⟨79146037408500572209200697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105528049878000762945600929 79146037408500572209200697)
  ·
    refine ⟨59359528056375429156900523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79146037408500572209200697 59359528056375429156900523)
    ·
      refine ⟨89039292084563143735350785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59359528056375429156900523 89039292084563143735350785)
      ·
        refine ⟨66779469063422357801513089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89039292084563143735350785 66779469063422357801513089)
        ·
          refine ⟨50084601797566768351134817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66779469063422357801513089 50084601797566768351134817)
          ·
            refine ⟨37563451348175076263351113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50084601797566768351134817 37563451348175076263351113)
            ·
              refine ⟨28172588511131307197513335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37563451348175076263351113 28172588511131307197513335)
              ·
                refine ⟨42258882766696960796270003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28172588511131307197513335 42258882766696960796270003)
                ·
                  refine ⟨63388324150045441194405005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42258882766696960796270003 63388324150045441194405005)
                  ·
                    refine ⟨23770621556267040447901877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63388324150045441194405005 23770621556267040447901877)
                    ·
                      refine ⟨2228495770900035041990801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23770621556267040447901877 2228495770900035041990801)
                      ·
                        rfl

theorem cell23_4339980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4339980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4339980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4339980 prefixEnd_4339980 := by exact prefixLift 4339980
  have htrace : WordTrace (prefixWord ++ tailWord_4339980) baseStart_4339980 baseEnd_4339980 := by
    simpa [prefixWord, tailWord_4339980, baseEnd_4339980] using wordTrace_append hprefix tailTrace_4339980
  have hstable : (prefixWord ++ tailWord_4339980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4339980).length < 2 ^ (prefixWord ++ tailWord_4339980).sum := by decide
  have hdescent : baseEnd_4339980 < baseStart_4339980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4339980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340037 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_4340037 : Nat := 118140960795 + 4340037 * 2 ^ 59
def prefixEnd_4340037 : Nat := 4983230072969 + 3 ^ 40 * 4340037 * 2
def baseEnd_4340037 : Nat := 2228525039297341318978039

theorem tailTrace_4340037 : CollatzResearch.WordTrace tailWord_4340037 prefixEnd_4340037 2228525039297341318978039 := by
  unfold tailWord_4340037
  simp only [CollatzResearch.WordTrace]
  refine ⟨158294153777794643153226365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105529435851863095435484243 158294153777794643153226365)
  ·
    refine ⟨59360307666672991182459887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158294153777794643153226365 59360307666672991182459887)
    ·
      refine ⟨89040461500009486773689831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59360307666672991182459887 89040461500009486773689831)
      ·
        refine ⟨133560692250014230160534747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89040461500009486773689831 133560692250014230160534747)
        ·
          refine ⟨200341038375021345240802121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133560692250014230160534747 200341038375021345240802121)
          ·
            refine ⟨150255778781266008930601591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200341038375021345240802121 150255778781266008930601591)
            ·
              refine ⟨225383668171899013395902387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150255778781266008930601591 225383668171899013395902387)
              ·
                refine ⟨338075502257848520093853581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225383668171899013395902387 338075502257848520093853581)
                ·
                  refine ⟨126778313346693195035195093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338075502257848520093853581 126778313346693195035195093)
                  ·
                    refine ⟨2971366719063121758637385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 126778313346693195035195093 2971366719063121758637385)
                    ·
                      refine ⟨2228525039297341318978039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971366719063121758637385 2228525039297341318978039)
                      ·
                        rfl

theorem cell23_4340037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_4340037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340037 prefixEnd_4340037 := by exact prefixLift 4340037
  have htrace : WordTrace (prefixWord ++ tailWord_4340037) baseStart_4340037 baseEnd_4340037 := by
    simpa [prefixWord, tailWord_4340037, baseEnd_4340037] using wordTrace_append hprefix tailTrace_4340037
  have hstable : (prefixWord ++ tailWord_4340037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340037).length < 2 ^ (prefixWord ++ tailWord_4340037).sum := by decide
  have hdescent : baseEnd_4340037 < baseStart_4340037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340067 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4340067 : Nat := 118140960795 + 4340067 * 2 ^ 59
def prefixEnd_4340067 : Nat := 4983230072969 + 3 ^ 40 * 4340067 * 2
def baseEnd_4340067 : Nat := 2228540443716976201602901

theorem tailTrace_4340067 : CollatzResearch.WordTrace tailWord_4340067 prefixEnd_4340067 2228540443716976201602901 := by
  unfold tailWord_4340067
  simp only [CollatzResearch.WordTrace]
  refine ⟨158295247967685958276818455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105530165311790638851212303 158295247967685958276818455)
  ·
    refine ⟨237442871951528937415227683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158295247967685958276818455 237442871951528937415227683)
    ·
      refine ⟨356164307927293406122841525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237442871951528937415227683 356164307927293406122841525)
      ·
        refine ⟨33390403868183756824016393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 356164307927293406122841525 33390403868183756824016393)
        ·
          refine ⟨25042802901137817618012295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33390403868183756824016393 25042802901137817618012295)
          ·
            refine ⟨37564204351706726427018443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25042802901137817618012295 37564204351706726427018443)
            ·
              refine ⟨56346306527560089640527665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37564204351706726427018443 56346306527560089640527665)
              ·
                refine ⟨42259729895670067230395749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56346306527560089640527665 42259729895670067230395749)
                ·
                  refine ⟨7923699355438137605699203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42259729895670067230395749 7923699355438137605699203)
                  ·
                    refine ⟨11885549033157206408548805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7923699355438137605699203 11885549033157206408548805)
                    ·
                      refine ⟨2228540443716976201602901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11885549033157206408548805 2228540443716976201602901)
                      ·
                        rfl

theorem cell23_4340067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4340067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340067 prefixEnd_4340067 := by exact prefixLift 4340067
  have htrace : WordTrace (prefixWord ++ tailWord_4340067) baseStart_4340067 baseEnd_4340067 := by
    simpa [prefixWord, tailWord_4340067, baseEnd_4340067] using wordTrace_append hprefix tailTrace_4340067
  have hstable : (prefixWord ++ tailWord_4340067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340067).length < 2 ^ (prefixWord ++ tailWord_4340067).sum := by decide
  have hdescent : baseEnd_4340067 < baseStart_4340067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340104 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4340104 : Nat := 118140960795 + 4340104 * 2 ^ 59
def prefixEnd_4340104 : Nat := 4983230072969 + 3 ^ 40 * 4340104 * 2
def baseEnd_4340104 : Nat := 2228559442501192556840231

theorem tailTrace_4340104 : CollatzResearch.WordTrace tailWord_4340104 prefixEnd_4340104 2228559442501192556840231 := by
  unfold tailWord_4340104
  simp only [CollatzResearch.WordTrace]
  refine ⟨79148298734275956797957683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105531064979034609063943577 79148298734275956797957683)
  ·
    refine ⟨118722448101413935196936525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79148298734275956797957683 118722448101413935196936525)
    ·
      refine ⟨44520918038030225698851197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118722448101413935196936525 44520918038030225698851197)
      ·
        refine ⟨16695344264261334637069199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44520918038030225698851197 16695344264261334637069199)
        ·
          refine ⟨25043016396392001955603799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16695344264261334637069199 25043016396392001955603799)
          ·
            refine ⟨37564524594588002933405699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25043016396392001955603799 37564524594588002933405699)
            ·
              refine ⟨56346786891882004400108549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37564524594588002933405699 56346786891882004400108549)
              ·
                refine ⟨10565022542227875825020353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56346786891882004400108549 10565022542227875825020353)
                ·
                  refine ⟨7923766906670906868765265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10565022542227875825020353 7923766906670906868765265)
                  ·
                    refine ⟨5942825180003180151573949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7923766906670906868765265 5942825180003180151573949)
                    ·
                      refine ⟨2228559442501192556840231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942825180003180151573949 2228559442501192556840231)
                      ·
                        rfl

theorem cell23_4340104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4340104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340104 prefixEnd_4340104 := by exact prefixLift 4340104
  have htrace : WordTrace (prefixWord ++ tailWord_4340104) baseStart_4340104 baseEnd_4340104 := by
    simpa [prefixWord, tailWord_4340104, baseEnd_4340104] using wordTrace_append hprefix tailTrace_4340104
  have hstable : (prefixWord ++ tailWord_4340104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340104).length < 2 ^ (prefixWord ++ tailWord_4340104).sum := by decide
  have hdescent : baseEnd_4340104 < baseStart_4340104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340107 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 6]
def baseStart_4340107 : Nat := 118140960795 + 4340107 * 2 ^ 59
def prefixEnd_4340107 : Nat := 4983230072969 + 3 ^ 40 * 4340107 * 2
def baseEnd_4340107 : Nat := 247617886993684005011413

theorem tailTrace_4340107 : CollatzResearch.WordTrace tailWord_4340107 prefixEnd_4340107 247617886993684005011413 := by
  unfold tailWord_4340107
  simp only [CollatzResearch.WordTrace]
  refine ⟨158296706887541045108274575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105531137925027363405516383 158296706887541045108274575)
  ·
    refine ⟨237445060331311567662411863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158296706887541045108274575 237445060331311567662411863)
    ·
      refine ⟨356167590496967351493617795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237445060331311567662411863 356167590496967351493617795)
      ·
        refine ⟨534251385745451027240426693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356167590496967351493617795 534251385745451027240426693)
        ·
          refine ⟨100172134827272067607580005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534251385745451027240426693 100172134827272067607580005)
          ·
            refine ⟨18782275280113512676421251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100172134827272067607580005 18782275280113512676421251)
            ·
              refine ⟨28173412920170269014631877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18782275280113512676421251 28173412920170269014631877)
              ·
                refine ⟨5282514922531925440243477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28173412920170269014631877 5282514922531925440243477)
                ·
                  refine ⟨247617886993684005011413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5282514922531925440243477 247617886993684005011413)
                  ·
                    rfl

theorem cell23_4340107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 6].length) (baseStart_4340107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340107 prefixEnd_4340107 := by exact prefixLift 4340107
  have htrace : WordTrace (prefixWord ++ tailWord_4340107) baseStart_4340107 baseEnd_4340107 := by
    simpa [prefixWord, tailWord_4340107, baseEnd_4340107] using wordTrace_append hprefix tailTrace_4340107
  have hstable : (prefixWord ++ tailWord_4340107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340107).length < 2 ^ (prefixWord ++ tailWord_4340107).sum := by decide
  have hdescent : baseEnd_4340107 < baseStart_4340107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340117 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_4340117 : Nat := 118140960795 + 4340117 * 2 ^ 59
def prefixEnd_4340117 : Nat := 4983230072969 + 3 ^ 40 * 4340117 * 2
def baseEnd_4340117 : Nat := 2228566117749701005977671

theorem tailTrace_4340117 : CollatzResearch.WordTrace tailWord_4340117 prefixEnd_4340117 2228566117749701005977671 := by
  unfold tailWord_4340117
  simp only [CollatzResearch.WordTrace]
  refine ⟨158297071617504816816138605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105531381078336544544092403 158297071617504816816138605)
  ·
    refine ⟨59361401856564306306051977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158297071617504816816138605 59361401856564306306051977)
    ·
      refine ⟨44521051392423229729538983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59361401856564306306051977 44521051392423229729538983)
      ·
        refine ⟨66781577088634844594308475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44521051392423229729538983 66781577088634844594308475)
        ·
          refine ⟨100172365632952266891462713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66781577088634844594308475 100172365632952266891462713)
          ·
            refine ⟨75129274224714200168597035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100172365632952266891462713 75129274224714200168597035)
            ·
              refine ⟨112693911337071300252895553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75129274224714200168597035 112693911337071300252895553)
              ·
                refine ⟨84520433502803475189671665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112693911337071300252895553 84520433502803475189671665)
                ·
                  refine ⟨63390325127102606392253749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84520433502803475189671665 63390325127102606392253749)
                  ·
                    refine ⟨5942842980665869349273789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63390325127102606392253749 5942842980665869349273789)
                    ·
                      refine ⟨2228566117749701005977671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942842980665869349273789 2228566117749701005977671)
                      ·
                        rfl

theorem cell23_4340117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_4340117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340117 prefixEnd_4340117 := by exact prefixLift 4340117
  have htrace : WordTrace (prefixWord ++ tailWord_4340117) baseStart_4340117 baseEnd_4340117 := by
    simpa [prefixWord, tailWord_4340117, baseEnd_4340117] using wordTrace_append hprefix tailTrace_4340117
  have hstable : (prefixWord ++ tailWord_4340117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340117).length < 2 ^ (prefixWord ++ tailWord_4340117).sum := by decide
  have hdescent : baseEnd_4340117 < baseStart_4340117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340168 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_4340168 : Nat := 118140960795 + 4340168 * 2 ^ 59
def prefixEnd_4340168 : Nat := 4983230072969 + 3 ^ 40 * 4340168 * 2
def baseEnd_4340168 : Nat := 2228592305263080306439937

theorem tailTrace_4340168 : CollatzResearch.WordTrace tailWord_4340168 prefixEnd_4340168 2228592305263080306439937 := by
  unfold tailWord_4340168
  simp only [CollatzResearch.WordTrace]
  refine ⟨79149465870160026263122579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105532621160213368350830105 79149465870160026263122579)
  ·
    refine ⟨118724198805240039394683869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79149465870160026263122579 118724198805240039394683869)
    ·
      refine ⟨44521574551965014773006451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118724198805240039394683869 44521574551965014773006451)
      ·
        refine ⟨66782361827947522159509677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44521574551965014773006451 66782361827947522159509677)
        ·
          refine ⟨25043385685480320809816129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66782361827947522159509677 25043385685480320809816129)
          ·
            refine ⟨18782539264110240607362097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25043385685480320809816129 18782539264110240607362097)
            ·
              refine ⟨14086904448082680455521573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18782539264110240607362097 14086904448082680455521573)
              ·
                refine ⟨2641294584015502585410295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14086904448082680455521573 2641294584015502585410295)
                ·
                  refine ⟨3961941876023253878115443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641294584015502585410295 3961941876023253878115443)
                  ·
                    refine ⟨5942912814034880817173165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961941876023253878115443 5942912814034880817173165)
                    ·
                      refine ⟨2228592305263080306439937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5942912814034880817173165 2228592305263080306439937)
                      ·
                        rfl

theorem cell23_4340168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_4340168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340168 prefixEnd_4340168 := by exact prefixLift 4340168
  have htrace : WordTrace (prefixWord ++ tailWord_4340168) baseStart_4340168 baseEnd_4340168 := by
    simpa [prefixWord, tailWord_4340168, baseEnd_4340168] using wordTrace_append hprefix tailTrace_4340168
  have hstable : (prefixWord ++ tailWord_4340168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340168).length < 2 ^ (prefixWord ++ tailWord_4340168).sum := by decide
  have hdescent : baseEnd_4340168 < baseStart_4340168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340191 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_4340191 : Nat := 118140960795 + 4340191 * 2 ^ 59
def prefixEnd_4340191 : Nat := 4983230072969 + 3 ^ 40 * 4340191 * 2
def baseEnd_4340191 : Nat := 2228604115318133716452331

theorem tailTrace_4340191 : CollatzResearch.WordTrace tailWord_4340191 prefixEnd_4340191 2228604115318133716452331 := by
  unfold tailWord_4340191
  simp only [CollatzResearch.WordTrace]
  refine ⟨158299770619236727454332427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105533180412824484969554951 158299770619236727454332427)
  ·
    refine ⟨237449655928855091181498641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158299770619236727454332427 237449655928855091181498641)
    ·
      refine ⟨178087241946641318386123981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237449655928855091181498641 178087241946641318386123981)
      ·
        refine ⟨66782715729990494394796493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178087241946641318386123981 66782715729990494394796493)
        ·
          refine ⟨25043518398746435398048685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66782715729990494394796493 25043518398746435398048685)
          ·
            refine ⟨9391319399529913274268257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25043518398746435398048685 9391319399529913274268257)
            ·
              refine ⟨7043489549647434955701193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9391319399529913274268257 7043489549647434955701193)
              ·
                refine ⟨5282617162235576216775895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7043489549647434955701193 5282617162235576216775895)
                ·
                  refine ⟨7923925743353364325163843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282617162235576216775895 7923925743353364325163843)
                  ·
                    refine ⟨11885888615030046487745765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7923925743353364325163843 11885888615030046487745765)
                    ·
                      refine ⟨2228604115318133716452331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11885888615030046487745765 2228604115318133716452331)
                      ·
                        rfl

theorem cell23_4340191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_4340191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340191 prefixEnd_4340191 := by exact prefixLift 4340191
  have htrace : WordTrace (prefixWord ++ tailWord_4340191) baseStart_4340191 baseEnd_4340191 := by
    simpa [prefixWord, tailWord_4340191, baseEnd_4340191] using wordTrace_append hprefix tailTrace_4340191
  have hstable : (prefixWord ++ tailWord_4340191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340191).length < 2 ^ (prefixWord ++ tailWord_4340191).sum := by decide
  have hdescent : baseEnd_4340191 < baseStart_4340191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340225 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4340225 : Nat := 118140960795 + 4340225 * 2 ^ 59
def prefixEnd_4340225 : Nat := 4983230072969 + 3 ^ 40 * 4340225 * 2
def baseEnd_4340225 : Nat := 2228621573660386583427175

theorem tailTrace_4340225 : CollatzResearch.WordTrace tailWord_4340225 prefixEnd_4340225 2228621573660386583427175 := by
  unfold tailWord_4340225
  simp only [CollatzResearch.WordTrace]
  refine ⟨158301010701113551261070129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105534007134075700840713419 158301010701113551261070129)
  ·
    refine ⟨118725758025835163445802597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158301010701113551261070129 118725758025835163445802597)
    ·
      refine ⟨22261079629844093146087987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118725758025835163445802597 22261079629844093146087987)
      ·
        refine ⟨33391619444766139719131981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22261079629844093146087987 33391619444766139719131981)
        ·
          refine ⟨12521857291787302394674493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33391619444766139719131981 12521857291787302394674493)
          ·
            refine ⟨4695696484420238398002935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12521857291787302394674493 4695696484420238398002935)
            ·
              refine ⟨7043544726630357597004403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695696484420238398002935 7043544726630357597004403)
              ·
                refine ⟨10565317089945536395506605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043544726630357597004403 10565317089945536395506605)
                ·
                  refine ⟨3961993908729576148314977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10565317089945536395506605 3961993908729576148314977)
                  ·
                    refine ⟨2971495431547182111236233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3961993908729576148314977 2971495431547182111236233)
                    ·
                      refine ⟨2228621573660386583427175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971495431547182111236233 2228621573660386583427175)
                      ·
                        rfl

theorem cell23_4340225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4340225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340225 prefixEnd_4340225 := by exact prefixLift 4340225
  have htrace : WordTrace (prefixWord ++ tailWord_4340225) baseStart_4340225 baseEnd_4340225 := by
    simpa [prefixWord, tailWord_4340225, baseEnd_4340225] using wordTrace_append hprefix tailTrace_4340225
  have hstable : (prefixWord ++ tailWord_4340225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340225).length < 2 ^ (prefixWord ++ tailWord_4340225).sum := by decide
  have hdescent : baseEnd_4340225 < baseStart_4340225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340227 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 7]
def baseStart_4340227 : Nat := 118140960795 + 4340227 * 2 ^ 59
def prefixEnd_4340227 : Nat := 4983230072969 + 3 ^ 40 * 4340227 * 2
def baseEnd_4340227 : Nat := 742874200207231858534055

theorem tailTrace_4340227 : CollatzResearch.WordTrace tailWord_4340227 prefixEnd_4340227 742874200207231858534055 := by
  unfold tailWord_4340227
  simp only [CollatzResearch.WordTrace]
  refine ⟨158301083647106305602642935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105534055764737537068428623 158301083647106305602642935)
  ·
    refine ⟨237451625470659458403964403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158301083647106305602642935 237451625470659458403964403)
    ·
      refine ⟨356177438205989187605946605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237451625470659458403964403 356177438205989187605946605)
      ·
        refine ⟨133566539327245945352229977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356177438205989187605946605 133566539327245945352229977)
        ·
          refine ⟨100174904495434459014172483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133566539327245945352229977 100174904495434459014172483)
          ·
            refine ⟨150262356743151688521258725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100174904495434459014172483 150262356743151688521258725)
            ·
              refine ⟨28174191889340941597736011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150262356743151688521258725 28174191889340941597736011)
              ·
                refine ⟨42261287834011412396604017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28174191889340941597736011 42261287834011412396604017)
                ·
                  refine ⟨31695965875508559297453013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42261287834011412396604017 31695965875508559297453013)
                  ·
                    refine ⟨742874200207231858534055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31695965875508559297453013 742874200207231858534055)
                    ·
                      rfl

theorem cell23_4340227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_4340227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340227 prefixEnd_4340227 := by exact prefixLift 4340227
  have htrace : WordTrace (prefixWord ++ tailWord_4340227) baseStart_4340227 baseEnd_4340227 := by
    simpa [prefixWord, tailWord_4340227, baseEnd_4340227] using wordTrace_append hprefix tailTrace_4340227
  have hstable : (prefixWord ++ tailWord_4340227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340227).length < 2 ^ (prefixWord ++ tailWord_4340227).sum := by decide
  have hdescent : baseEnd_4340227 < baseStart_4340227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340281 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4340281 : Nat := 118140960795 + 4340281 * 2 ^ 59
def prefixEnd_4340281 : Nat := 4983230072969 + 3 ^ 40 * 4340281 * 2
def baseEnd_4340281 : Nat := 2228650328577038364326917

theorem tailTrace_4340281 : CollatzResearch.WordTrace tailWord_4340281 prefixEnd_4340281 2228650328577038364326917 := by
  unfold tailWord_4340281
  simp only [CollatzResearch.WordTrace]
  refine ⟨158303053188910672825108697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105535368792607115216739131 158303053188910672825108697)
  ·
    refine ⟨118727289891683004618831523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158303053188910672825108697 118727289891683004618831523)
    ·
      refine ⟨178090934837524506928247285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118727289891683004618831523 178090934837524506928247285)
      ·
        refine ⟨16696025141017922524523183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178090934837524506928247285 16696025141017922524523183)
        ·
          refine ⟨25044037711526883786784775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16696025141017922524523183 25044037711526883786784775)
          ·
            refine ⟨37566056567290325680177163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25044037711526883786784775 37566056567290325680177163)
            ·
              refine ⟨56349084850935488520265745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37566056567290325680177163 56349084850935488520265745)
              ·
                refine ⟨42261813638201616390199309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56349084850935488520265745 42261813638201616390199309)
                ·
                  refine ⟨15848180114325606146324741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42261813638201616390199309 15848180114325606146324741)
                  ·
                    refine ⟨2971533771436051152435889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15848180114325606146324741 2971533771436051152435889)
                    ·
                      refine ⟨2228650328577038364326917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971533771436051152435889 2228650328577038364326917)
                      ·
                        rfl

theorem cell23_4340281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4340281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340281 prefixEnd_4340281 := by exact prefixLift 4340281
  have htrace : WordTrace (prefixWord ++ tailWord_4340281) baseStart_4340281 baseEnd_4340281 := by
    simpa [prefixWord, tailWord_4340281, baseEnd_4340281] using wordTrace_append hprefix tailTrace_4340281
  have hstable : (prefixWord ++ tailWord_4340281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340281).length < 2 ^ (prefixWord ++ tailWord_4340281).sum := by decide
  have hdescent : baseEnd_4340281 < baseStart_4340281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340292 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4340292 : Nat := 118140960795 + 4340292 * 2 ^ 59
def prefixEnd_4340292 : Nat := 4983230072969 + 3 ^ 40 * 4340292 * 2
def baseEnd_4340292 : Nat := 2228655976864237821289367

theorem tailTrace_4340292 : CollatzResearch.WordTrace tailWord_4340292 prefixEnd_4340292 2228655976864237821289367 := by
  unfold tailWord_4340292
  simp only [CollatzResearch.WordTrace]
  refine ⟨79151727195935410851879565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105535636261247214469172753 79151727195935410851879565)
  ·
    refine ⟨29681897698475779069454837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79151727195935410851879565 29681897698475779069454837)
    ·
      refine ⟨2782677909232104287761391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29681897698475779069454837 2782677909232104287761391)
      ·
        refine ⟨4174016863848156431642087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782677909232104287761391 4174016863848156431642087)
        ·
          refine ⟨6261025295772234647463131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4174016863848156431642087 6261025295772234647463131)
          ·
            refine ⟨9391537943658351971194697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6261025295772234647463131 9391537943658351971194697)
            ·
              refine ⟨7043653457743763978396023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9391537943658351971194697 7043653457743763978396023)
              ·
                refine ⟨10565480186615645967594035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043653457743763978396023 10565480186615645967594035)
                ·
                  refine ⟨15848220279923468951391053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10565480186615645967594035 15848220279923468951391053)
                  ·
                    refine ⟨5943082604971300856771645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15848220279923468951391053 5943082604971300856771645)
                    ·
                      refine ⟨2228655976864237821289367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943082604971300856771645 2228655976864237821289367)
                      ·
                        rfl

theorem cell23_4340292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4340292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340292 prefixEnd_4340292 := by exact prefixLift 4340292
  have htrace : WordTrace (prefixWord ++ tailWord_4340292) baseStart_4340292 baseEnd_4340292 := by
    simpa [prefixWord, tailWord_4340292, baseEnd_4340292] using wordTrace_append hprefix tailTrace_4340292
  have hstable : (prefixWord ++ tailWord_4340292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340292).length < 2 ^ (prefixWord ++ tailWord_4340292).sum := by decide
  have hdescent : baseEnd_4340292 < baseStart_4340292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340298 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_4340298 : Nat := 118140960795 + 4340298 * 2 ^ 59
def prefixEnd_4340298 : Nat := 4983230072969 + 3 ^ 40 * 4340298 * 2
def baseEnd_4340298 : Nat := 2228659057748164797814339

theorem tailTrace_4340298 : CollatzResearch.WordTrace tailWord_4340298 prefixEnd_4340298 2228659057748164797814339 := by
  unfold tailWord_4340298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39575918307462271182119387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105535782153232723152318365 39575918307462271182119387)
  ·
    refine ⟨59363877461193406773179081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39575918307462271182119387 59363877461193406773179081)
    ·
      refine ⟨44522908095895055079884311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59363877461193406773179081 44522908095895055079884311)
      ·
        refine ⟨66784362143842582619826467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44522908095895055079884311 66784362143842582619826467)
        ·
          refine ⟨100176543215763873929739701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66784362143842582619826467 100176543215763873929739701)
          ·
            refine ⟨9391550926477863180913097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100176543215763873929739701 9391550926477863180913097)
            ·
              refine ⟨7043663194858397385684823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9391550926477863180913097 7043663194858397385684823)
              ·
                refine ⟨10565494792287596078527235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043663194858397385684823 10565494792287596078527235)
                ·
                  refine ⟨15848242188431394117790853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10565494792287596078527235 15848242188431394117790853)
                  ·
                    refine ⟨2971545410330886397085785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15848242188431394117790853 2971545410330886397085785)
                    ·
                      refine ⟨2228659057748164797814339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971545410330886397085785 2228659057748164797814339)
                      ·
                        rfl

theorem cell23_4340298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_4340298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340298 prefixEnd_4340298 := by exact prefixLift 4340298
  have htrace : WordTrace (prefixWord ++ tailWord_4340298) baseStart_4340298 baseEnd_4340298 := by
    simpa [prefixWord, tailWord_4340298, baseEnd_4340298] using wordTrace_append hprefix tailTrace_4340298
  have hstable : (prefixWord ++ tailWord_4340298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340298).length < 2 ^ (prefixWord ++ tailWord_4340298).sum := by decide
  have hdescent : baseEnd_4340298 < baseStart_4340298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340321 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 5]
def baseStart_4340321 : Nat := 118140960795 + 4340321 * 2 ^ 59
def prefixEnd_4340321 : Nat := 4983230072969 + 3 ^ 40 * 4340321 * 2
def baseEnd_4340321 : Nat := 247630096422579800869637

theorem tailTrace_4340321 : CollatzResearch.WordTrace tailWord_4340321 prefixEnd_4340321 247630096422579800869637 := by
  unfold tailWord_4340321
  simp only [CollatzResearch.WordTrace]
  refine ⟨158304512108765759656564817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105536341405843839771043211 158304512108765759656564817)
  ·
    refine ⟨118728384081574319742423613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158304512108765759656564817 118728384081574319742423613)
    ·
      refine ⟨44523144030590369903408855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118728384081574319742423613 44523144030590369903408855)
      ·
        refine ⟨66784716045885554855113283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44523144030590369903408855 66784716045885554855113283)
        ·
          refine ⟨100177074068828332282669925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66784716045885554855113283 100177074068828332282669925)
          ·
            refine ⟨18783201387905312303000611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100177074068828332282669925 18783201387905312303000611)
            ·
              refine ⟨28174802081857968454500917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18783201387905312303000611 28174802081857968454500917)
              ·
                refine ⟨2641387695174184542609461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28174802081857968454500917 2641387695174184542609461)
                ·
                  refine ⟨247630096422579800869637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641387695174184542609461 247630096422579800869637)
                  ·
                    rfl

theorem cell23_4340321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 5].length) (baseStart_4340321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340321 prefixEnd_4340321 := by exact prefixLift 4340321
  have htrace : WordTrace (prefixWord ++ tailWord_4340321) baseStart_4340321 baseEnd_4340321 := by
    simpa [prefixWord, tailWord_4340321, baseEnd_4340321] using wordTrace_append hprefix tailTrace_4340321
  have hstable : (prefixWord ++ tailWord_4340321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340321).length < 2 ^ (prefixWord ++ tailWord_4340321).sum := by decide
  have hdescent : baseEnd_4340321 < baseStart_4340321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340381 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_4340381 : Nat := 118140960795 + 4340381 * 2 ^ 59
def prefixEnd_4340381 : Nat := 4983230072969 + 3 ^ 40 * 4340381 * 2
def baseEnd_4340381 : Nat := 742900558880829324358819

theorem tailTrace_4340381 : CollatzResearch.WordTrace tailWord_4340381 prefixEnd_4340381 742900558880829324358819 := by
  unfold tailWord_4340381
  simp only [CollatzResearch.WordTrace]
  refine ⟨158306700488548389903748997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105537800325698926602499331 158306700488548389903748997)
  ·
    refine ⟨29682506341602823106952937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158306700488548389903748997 29682506341602823106952937)
    ·
      refine ⟨22261879756202117330214703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29682506341602823106952937 22261879756202117330214703)
      ·
        refine ⟨33392819634303175995322055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22261879756202117330214703 33392819634303175995322055)
        ·
          refine ⟨50089229451454763992983083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33392819634303175995322055 50089229451454763992983083)
          ·
            refine ⟨75133844177182145989474625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50089229451454763992983083 75133844177182145989474625)
            ·
              refine ⟨56350383132886609492105969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75133844177182145989474625 56350383132886609492105969)
              ·
                refine ⟨42262787349664957119079477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56350383132886609492105969 42262787349664957119079477)
                ·
                  refine ⟨3962136314031089729913701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42262787349664957119079477 3962136314031089729913701)
                  ·
                    refine ⟨742900558880829324358819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962136314031089729913701 742900558880829324358819)
                    ·
                      rfl

theorem cell23_4340381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_4340381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340381 prefixEnd_4340381 := by exact prefixLift 4340381
  have htrace : WordTrace (prefixWord ++ tailWord_4340381) baseStart_4340381 baseEnd_4340381 := by
    simpa [prefixWord, tailWord_4340381, baseEnd_4340381] using wordTrace_append hprefix tailTrace_4340381
  have hstable : (prefixWord ++ tailWord_4340381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340381).length < 2 ^ (prefixWord ++ tailWord_4340381).sum := by decide
  have hdescent : baseEnd_4340381 < baseStart_4340381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340471 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 6, 4]
def baseStart_4340471 : Nat := 118140960795 + 4340471 * 2 ^ 59
def prefixEnd_4340471 : Nat := 4983230072969 + 3 ^ 40 * 4340471 * 2
def baseEnd_4340471 : Nat := 742915963300464206983681

theorem tailTrace_4340471 : CollatzResearch.WordTrace tailWord_4340471 prefixEnd_4340471 742915963300464206983681 := by
  unfold tailWord_4340471
  simp only [CollatzResearch.WordTrace]
  refine ⟨158309983058222335274525267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105539988705481556849683511 158309983058222335274525267)
  ·
    refine ⟨237464974587333502911787901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158309983058222335274525267 237464974587333502911787901)
    ·
      refine ⟨89049365470250063591920463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237464974587333502911787901 89049365470250063591920463)
      ·
        refine ⟨133574048205375095387880695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89049365470250063591920463 133574048205375095387880695)
        ·
          refine ⟨200361072308062643081821043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133574048205375095387880695 200361072308062643081821043)
          ·
            refine ⟨300541608462093964622731565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200361072308062643081821043 300541608462093964622731565)
            ·
              refine ⟨112703103173285236733524337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300541608462093964622731565 112703103173285236733524337)
              ·
                refine ⟨84527327379963927550143253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112703103173285236733524337 84527327379963927550143253)
                ·
                  refine ⟨3962218470935809103912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84527327379963927550143253 3962218470935809103912965)
                  ·
                    refine ⟨742915963300464206983681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962218470935809103912965 742915963300464206983681)
                    ·
                      rfl

theorem cell23_4340471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_4340471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340471 prefixEnd_4340471 := by exact prefixLift 4340471
  have htrace : WordTrace (prefixWord ++ tailWord_4340471) baseStart_4340471 baseEnd_4340471 := by
    simpa [prefixWord, tailWord_4340471, baseEnd_4340471] using wordTrace_append hprefix tailTrace_4340471
  have hstable : (prefixWord ++ tailWord_4340471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340471).length < 2 ^ (prefixWord ++ tailWord_4340471).sum := by decide
  have hdescent : baseEnd_4340471 < baseStart_4340471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340482 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4340482 : Nat := 118140960795 + 4340482 * 2 ^ 59
def prefixEnd_4340482 : Nat := 4983230072969 + 3 ^ 40 * 4340482 * 2
def baseEnd_4340482 : Nat := 2228753538188592077913493

theorem tailTrace_4340482 : CollatzResearch.WordTrace tailWord_4340482 prefixEnd_4340482 2228753538188592077913493 := by
  unfold tailWord_4340482
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577596065295621038293925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105540256174121656102117133 39577596065295621038293925)
  ·
    refine ⟨7420799262242928944680111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39577596065295621038293925 7420799262242928944680111)
    ·
      refine ⟨11131198893364393417020167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7420799262242928944680111 11131198893364393417020167)
      ·
        refine ⟨16696798340046590125530251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11131198893364393417020167 16696798340046590125530251)
        ·
          refine ⟨25045197510069885188295377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16696798340046590125530251 25045197510069885188295377)
          ·
            refine ⟨18783898132552413891221533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25045197510069885188295377 18783898132552413891221533)
            ·
              refine ⟨7043961799707155209208075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18783898132552413891221533 7043961799707155209208075)
              ·
                refine ⟨10565942699560732813812113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043961799707155209208075 10565942699560732813812113)
                ·
                  refine ⟨7924457024670549610359085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10565942699560732813812113 7924457024670549610359085)
                  ·
                    refine ⟨2971671384251456103884657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7924457024670549610359085 2971671384251456103884657)
                    ·
                      refine ⟨2228753538188592077913493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971671384251456103884657 2228753538188592077913493)
                      ·
                        rfl

theorem cell23_4340482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4340482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340482 prefixEnd_4340482 := by exact prefixLift 4340482
  have htrace : WordTrace (prefixWord ++ tailWord_4340482) baseStart_4340482 baseEnd_4340482 := by
    simpa [prefixWord, tailWord_4340482, baseEnd_4340482] using wordTrace_append hprefix tailTrace_4340482
  have hstable : (prefixWord ++ tailWord_4340482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340482).length < 2 ^ (prefixWord ++ tailWord_4340482).sum := by decide
  have hdescent : baseEnd_4340482 < baseStart_4340482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340512 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4340512 : Nat := 118140960795 + 4340512 * 2 ^ 59
def prefixEnd_4340512 : Nat := 4983230072969 + 3 ^ 40 * 4340512 * 2
def baseEnd_4340512 : Nat := 2228768942608226960538355

theorem tailTrace_4340512 : CollatzResearch.WordTrace tailWord_4340512 prefixEnd_4340512 2228768942608226960538355 := by
  unfold tailWord_4340512
  simp only [CollatzResearch.WordTrace]
  refine ⟨79155739225536899638383895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105540985634049199517845193 79155739225536899638383895)
  ·
    refine ⟨118733608838305349457575843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79155739225536899638383895 118733608838305349457575843)
    ·
      refine ⟨178100413257458024186363765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118733608838305349457575843 178100413257458024186363765)
      ·
        refine ⟨16696913742886689767471603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178100413257458024186363765 16696913742886689767471603)
        ·
          refine ⟨25045370614330034651207405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16696913742886689767471603 25045370614330034651207405)
          ·
            refine ⟨9392013980373762994202777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25045370614330034651207405 9392013980373762994202777)
            ·
              refine ⟨7044010485280322245652083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9392013980373762994202777 7044010485280322245652083)
              ·
                refine ⟨10566015727920483368478125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044010485280322245652083 10566015727920483368478125)
                ·
                  refine ⟨3962255897970181263179297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10566015727920483368478125 3962255897970181263179297)
                  ·
                    refine ⟨2971691923477635947384473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3962255897970181263179297 2971691923477635947384473)
                    ·
                      refine ⟨2228768942608226960538355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971691923477635947384473 2228768942608226960538355)
                      ·
                        rfl

theorem cell23_4340512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4340512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340512 prefixEnd_4340512 := by exact prefixLift 4340512
  have htrace : WordTrace (prefixWord ++ tailWord_4340512) baseStart_4340512 baseEnd_4340512 := by
    simpa [prefixWord, tailWord_4340512, baseEnd_4340512] using wordTrace_append hprefix tailTrace_4340512
  have hstable : (prefixWord ++ tailWord_4340512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340512).length < 2 ^ (prefixWord ++ tailWord_4340512).sum := by decide
  have hdescent : baseEnd_4340512 < baseStart_4340512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340522 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4340522 : Nat := 118140960795 + 4340522 * 2 ^ 59
def prefixEnd_4340522 : Nat := 4983230072969 + 3 ^ 40 * 4340522 * 2
def baseEnd_4340522 : Nat := 742924692471590640471103

theorem tailTrace_4340522 : CollatzResearch.WordTrace tailWord_4340522 prefixEnd_4340522 742924692471590640471103 := by
  unfold tailWord_4340522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577960795259392746157955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105541228787358380656421213 39577960795259392746157955)
  ·
    refine ⟨59366941192889089119236933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39577960795259392746157955 59366941192889089119236933)
    ·
      refine ⟨11131301473666704209856925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59366941192889089119236933 11131301473666704209856925)
      ·
        refine ⟨4174238052625014078696347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11131301473666704209856925 4174238052625014078696347)
        ·
          refine ⟨6261357078937521118044521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4174238052625014078696347 6261357078937521118044521)
          ·
            refine ⟨4696017809203140838533391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6261357078937521118044521 4696017809203140838533391)
            ·
              refine ⟨7044026713804711257800087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696017809203140838533391 7044026713804711257800087)
              ·
                refine ⟨10566040070707066886700131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044026713804711257800087 10566040070707066886700131)
                ·
                  refine ⟨15849060106060600330050197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10566040070707066886700131 15849060106060600330050197)
                  ·
                    refine ⟨742924692471590640471103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15849060106060600330050197 742924692471590640471103)
                    ·
                      rfl

theorem cell23_4340522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4340522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340522 prefixEnd_4340522 := by exact prefixLift 4340522
  have htrace : WordTrace (prefixWord ++ tailWord_4340522) baseStart_4340522 baseEnd_4340522 := by
    simpa [prefixWord, tailWord_4340522, baseEnd_4340522] using wordTrace_append hprefix tailTrace_4340522
  have hstable : (prefixWord ++ tailWord_4340522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340522).length < 2 ^ (prefixWord ++ tailWord_4340522).sum := by decide
  have hdescent : baseEnd_4340522 < baseStart_4340522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340551 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_4340551 : Nat := 118140960795 + 4340551 * 2 ^ 59
def prefixEnd_4340551 : Nat := 4983230072969 + 3 ^ 40 * 4340551 * 2
def baseEnd_4340551 : Nat := 2228788968353752307950675

theorem tailTrace_4340551 : CollatzResearch.WordTrace tailWord_4340551 prefixEnd_4340551 2228788968353752307950675 := by
  unfold tailWord_4340551
  simp only [CollatzResearch.WordTrace]
  refine ⟨158312900897932508937437507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105541933931955005958291671 158312900897932508937437507)
  ·
    refine ⟨237469351346898763406156261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158312900897932508937437507 237469351346898763406156261)
    ·
      refine ⟨44525503377543518138654299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237469351346898763406156261 44525503377543518138654299)
      ·
        refine ⟨66788255066315277207981449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44525503377543518138654299 66788255066315277207981449)
        ·
          refine ⟨50091191299736457905986087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66788255066315277207981449 50091191299736457905986087)
          ·
            refine ⟨75136786949604686858979131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50091191299736457905986087 75136786949604686858979131)
            ·
              refine ⟨112705180424407030288468697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75136786949604686858979131 112705180424407030288468697)
              ·
                refine ⟨84528885318305272716351523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112705180424407030288468697 84528885318305272716351523)
                ·
                  refine ⟨126793327977457909074527285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84528885318305272716351523 126793327977457909074527285)
                  ·
                    refine ⟨11886874497886678975736933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126793327977457909074527285 11886874497886678975736933)
                    ·
                      refine ⟨2228788968353752307950675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11886874497886678975736933 2228788968353752307950675)
                      ·
                        rfl

theorem cell23_4340551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_4340551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340551 prefixEnd_4340551 := by exact prefixLift 4340551
  have htrace : WordTrace (prefixWord ++ tailWord_4340551) baseStart_4340551 baseEnd_4340551 := by
    simpa [prefixWord, tailWord_4340551, baseEnd_4340551] using wordTrace_append hprefix tailTrace_4340551
  have hstable : (prefixWord ++ tailWord_4340551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340551).length < 2 ^ (prefixWord ++ tailWord_4340551).sum := by decide
  have hdescent : baseEnd_4340551 < baseStart_4340551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340579 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 2, 1, 3]
def baseStart_4340579 : Nat := 118140960795 + 4340579 * 2 ^ 59
def prefixEnd_4340579 : Nat := 4983230072969 + 3 ^ 40 * 4340579 * 2
def baseEnd_4340579 : Nat := 2228803345812078198400547

theorem tailTrace_4340579 : CollatzResearch.WordTrace tailWord_4340579 prefixEnd_4340579 2228803345812078198400547 := by
  unfold tailWord_4340579
  simp only [CollatzResearch.WordTrace]
  refine ⟨158313922141831069719456791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105542614761220713146304527 158313922141831069719456791)
  ·
    refine ⟨237470883212746604579185187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158313922141831069719456791 237470883212746604579185187)
    ·
      refine ⟨356206324819119906868777781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237470883212746604579185187 356206324819119906868777781)
      ·
        refine ⟨33394342951792491268947917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 356206324819119906868777781 33394342951792491268947917)
        ·
          refine ⟨12522878606922184225855469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33394342951792491268947917 12522878606922184225855469)
          ·
            refine ⟨4696079477595819084695801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12522878606922184225855469 4696079477595819084695801)
            ·
              refine ⟨3522059608196864313521851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696079477595819084695801 3522059608196864313521851)
              ·
                refine ⟨5283089412295296470282777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522059608196864313521851 5283089412295296470282777)
                ·
                  refine ⟨3962317059221472352712083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5283089412295296470282777 3962317059221472352712083)
                  ·
                    refine ⟨5943475588832208529068125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3962317059221472352712083 5943475588832208529068125)
                    ·
                      refine ⟨2228803345812078198400547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943475588832208529068125 2228803345812078198400547)
                      ·
                        rfl

theorem cell23_4340579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_4340579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340579 prefixEnd_4340579 := by exact prefixLift 4340579
  have htrace : WordTrace (prefixWord ++ tailWord_4340579) baseStart_4340579 baseEnd_4340579 := by
    simpa [prefixWord, tailWord_4340579, baseEnd_4340579] using wordTrace_append hprefix tailTrace_4340579
  have hstable : (prefixWord ++ tailWord_4340579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340579).length < 2 ^ (prefixWord ++ tailWord_4340579).sum := by decide
  have hdescent : baseEnd_4340579 < baseStart_4340579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340591 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 7]
def baseStart_4340591 : Nat := 118140960795 + 4340591 * 2 ^ 59
def prefixEnd_4340591 : Nat := 4983230072969 + 3 ^ 40 * 4340591 * 2
def baseEnd_4340591 : Nat := 247645500842214683494499

theorem tailTrace_4340591 : CollatzResearch.WordTrace tailWord_4340591 prefixEnd_4340591 247645500842214683494499 := by
  unfold tailWord_4340591
  simp only [CollatzResearch.WordTrace]
  refine ⟨158314359817787595768893627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105542906545191730512595751 158314359817787595768893627)
  ·
    refine ⟨237471539726681393653340441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158314359817787595768893627 237471539726681393653340441)
    ·
      refine ⟨178103654795011045240005331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237471539726681393653340441 178103654795011045240005331)
      ·
        refine ⟨267155482192516567860007997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178103654795011045240005331 267155482192516567860007997)
        ·
          refine ⟨100183305822193712947502999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267155482192516567860007997 100183305822193712947502999)
          ·
            refine ⟨150274958733290569421254499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100183305822193712947502999 150274958733290569421254499)
            ·
              refine ⟨225412438099935854131881749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150274958733290569421254499 225412438099935854131881749)
              ·
                refine ⟨10566208035934493162431957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225412438099935854131881749 10566208035934493162431957)
                ·
                  refine ⟨247645500842214683494499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10566208035934493162431957 247645500842214683494499)
                  ·
                    rfl

theorem cell23_4340591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 7].length) (baseStart_4340591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340591 prefixEnd_4340591 := by exact prefixLift 4340591
  have htrace : WordTrace (prefixWord ++ tailWord_4340591) baseStart_4340591 baseEnd_4340591 := by
    simpa [prefixWord, tailWord_4340591, baseEnd_4340591] using wordTrace_append hprefix tailTrace_4340591
  have hstable : (prefixWord ++ tailWord_4340591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340591).length < 2 ^ (prefixWord ++ tailWord_4340591).sum := by decide
  have hdescent : baseEnd_4340591 < baseStart_4340591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340651 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 8]
def baseStart_4340651 : Nat := 118140960795 + 4340651 * 2 ^ 59
def prefixEnd_4340651 : Nat := 4983230072969 + 3 ^ 40 * 4340651 * 2
def baseEnd_4340651 : Nat := 742946772139733972233405

theorem tailTrace_4340651 : CollatzResearch.WordTrace tailWord_4340651 prefixEnd_4340651 742946772139733972233405 := by
  unfold tailWord_4340651
  simp only [CollatzResearch.WordTrace]
  refine ⟨158316548197570226016077807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105544365465046817344051871 158316548197570226016077807)
  ·
    refine ⟨237474822296355339024116711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158316548197570226016077807 237474822296355339024116711)
    ·
      refine ⟨356212233444533008536175067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237474822296355339024116711 356212233444533008536175067)
      ·
        refine ⟨534318350166799512804262601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356212233444533008536175067 534318350166799512804262601)
        ·
          refine ⟨400738762625099634603196951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534318350166799512804262601 400738762625099634603196951)
          ·
            refine ⟨601108143937649451904795427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400738762625099634603196951 601108143937649451904795427)
            ·
              refine ⟨901662215906474177857193141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601108143937649451904795427 901662215906474177857193141)
              ·
                refine ⟨84530832741231954174111857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901662215906474177857193141 84530832741231954174111857)
                ·
                  refine ⟨63398124555923965630583893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84530832741231954174111857 63398124555923965630583893)
                  ·
                    refine ⟨742946772139733972233405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63398124555923965630583893 742946772139733972233405)
                    ·
                      rfl

theorem cell23_4340651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_4340651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340651 prefixEnd_4340651 := by exact prefixLift 4340651
  have htrace : WordTrace (prefixWord ++ tailWord_4340651) baseStart_4340651 baseEnd_4340651 := by
    simpa [prefixWord, tailWord_4340651, baseEnd_4340651] using wordTrace_append hprefix tailTrace_4340651
  have hstable : (prefixWord ++ tailWord_4340651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340651).length < 2 ^ (prefixWord ++ tailWord_4340651).sum := by decide
  have hdescent : baseEnd_4340651 < baseStart_4340651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340692 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4340692 : Nat := 118140960795 + 4340692 * 2 ^ 59
def prefixEnd_4340692 : Nat := 4983230072969 + 3 ^ 40 * 4340692 * 2
def baseEnd_4340692 : Nat := 2228861369126036256287527

theorem tailTrace_4340692 : CollatzResearch.WordTrace tailWord_4340692 prefixEnd_4340692 2228861369126036256287527 := by
  unfold tailWord_4340692
  simp only [CollatzResearch.WordTrace]
  refine ⟨79159021795210845009160165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105545362393614460012213553 79159021795210845009160165)
  ·
    refine ⟨14842316586602033439217531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79159021795210845009160165 14842316586602033439217531)
    ·
      refine ⟨22263474879903050158826297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14842316586602033439217531 22263474879903050158826297)
      ·
        refine ⟨16697606159927287619119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22263474879903050158826297 16697606159927287619119723)
        ·
          refine ⟨25046409239890931428679585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16697606159927287619119723 25046409239890931428679585)
          ·
            refine ⟨18784806929918198571509689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25046409239890931428679585 18784806929918198571509689)
            ·
              refine ⟨14088605197438648928632267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18784806929918198571509689 14088605197438648928632267)
              ·
                refine ⟨21132907796157973392948401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14088605197438648928632267 21132907796157973392948401)
                ·
                  refine ⟨15849680847118480044711301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21132907796157973392948401 15849680847118480044711301)
                  ·
                    refine ⟨2971815158834715008383369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15849680847118480044711301 2971815158834715008383369)
                    ·
                      refine ⟨2228861369126036256287527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971815158834715008383369 2228861369126036256287527)
                      ·
                        rfl

theorem cell23_4340692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4340692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340692 prefixEnd_4340692 := by exact prefixLift 4340692
  have htrace : WordTrace (prefixWord ++ tailWord_4340692) baseStart_4340692 baseEnd_4340692 := by
    simpa [prefixWord, tailWord_4340692, baseEnd_4340692] using wordTrace_append hprefix tailTrace_4340692
  have hstable : (prefixWord ++ tailWord_4340692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340692).length < 2 ^ (prefixWord ++ tailWord_4340692).sum := by decide
  have hdescent : baseEnd_4340692 < baseStart_4340692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340719 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 1, 4]
def baseStart_4340719 : Nat := 118140960795 + 4340719 * 2 ^ 59
def prefixEnd_4340719 : Nat := 4983230072969 + 3 ^ 40 * 4340719 * 2
def baseEnd_4340719 : Nat := 742958411034569216883301

theorem tailTrace_4340719 : CollatzResearch.WordTrace tailWord_4340719 prefixEnd_4340719 742958411034569216883301 := by
  unfold tailWord_4340719
  simp only [CollatzResearch.WordTrace]
  refine ⟨158319028361323873629553211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105546018907549249086368807 158319028361323873629553211)
  ·
    refine ⟨237478542541985810444329817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158319028361323873629553211 237478542541985810444329817)
    ·
      refine ⟨178108906906489357833247363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237478542541985810444329817 178108906906489357833247363)
      ·
        refine ⟨267163360359734036749871045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178108906906489357833247363 267163360359734036749871045)
        ·
          refine ⟨50093130067450131890600821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267163360359734036749871045 50093130067450131890600821)
          ·
            refine ⟨4696230943823449864743827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50093130067450131890600821 4696230943823449864743827)
            ·
              refine ⟨7044346415735174797115741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696230943823449864743827 7044346415735174797115741)
              ·
                refine ⟨2641629905900690548918403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7044346415735174797115741 2641629905900690548918403)
                ·
                  refine ⟨3962444858851035823377605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641629905900690548918403 3962444858851035823377605)
                  ·
                    refine ⟨742958411034569216883301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962444858851035823377605 742958411034569216883301)
                    ·
                      rfl

theorem cell23_4340719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_4340719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340719 prefixEnd_4340719 := by exact prefixLift 4340719
  have htrace : WordTrace (prefixWord ++ tailWord_4340719) baseStart_4340719 baseEnd_4340719 := by
    simpa [prefixWord, tailWord_4340719, baseEnd_4340719] using wordTrace_append hprefix tailTrace_4340719
  have hstable : (prefixWord ++ tailWord_4340719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340719).length < 2 ^ (prefixWord ++ tailWord_4340719).sum := by decide
  have hdescent : baseEnd_4340719 < baseStart_4340719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340728 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_4340728 : Nat := 118140960795 + 4340728 * 2 ^ 59
def prefixEnd_4340728 : Nat := 4983230072969 + 3 ^ 40 * 4340728 * 2
def baseEnd_4340728 : Nat := 742959951476532705145787

theorem tailTrace_4340728 : CollatzResearch.WordTrace tailWord_4340728 prefixEnd_4340728 742959951476532705145787 := by
  unfold tailWord_4340728
  simp only [CollatzResearch.WordTrace]
  refine ⟨79159678309145634083315419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105546237745527512111087225 79159678309145634083315419)
  ·
    refine ⟨118739517463718451124973129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79159678309145634083315419 118739517463718451124973129)
    ·
      refine ⟨89054638097788838343729847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118739517463718451124973129 89054638097788838343729847)
      ·
        refine ⟨133581957146683257515594771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89054638097788838343729847 133581957146683257515594771)
        ·
          refine ⟨200372935720024886273392157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133581957146683257515594771 200372935720024886273392157)
          ·
            refine ⟨75139850895009332352522059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200372935720024886273392157 75139850895009332352522059)
            ·
              refine ⟨112709776342513998528783089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75139850895009332352522059 112709776342513998528783089)
              ·
                refine ⟨84532332256885498896587317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112709776342513998528783089 84532332256885498896587317)
                ·
                  refine ⟨7924906149083015521555061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84532332256885498896587317 7924906149083015521555061)
                  ·
                    refine ⟨742959951476532705145787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7924906149083015521555061 742959951476532705145787)
                    ·
                      rfl

theorem cell23_4340728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_4340728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340728 prefixEnd_4340728 := by exact prefixLift 4340728
  have htrace : WordTrace (prefixWord ++ tailWord_4340728) baseStart_4340728 baseEnd_4340728 := by
    simpa [prefixWord, tailWord_4340728, baseEnd_4340728] using wordTrace_append hprefix tailTrace_4340728
  have hstable : (prefixWord ++ tailWord_4340728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340728).length < 2 ^ (prefixWord ++ tailWord_4340728).sum := by decide
  have hdescent : baseEnd_4340728 < baseStart_4340728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340769 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4340769 : Nat := 118140960795 + 4340769 * 2 ^ 59
def prefixEnd_4340769 : Nat := 4983230072969 + 3 ^ 40 * 4340769 * 2
def baseEnd_4340769 : Nat := 2228900907136432455024673

theorem tailTrace_4340769 : CollatzResearch.WordTrace tailWord_4340769 prefixEnd_4340769 2228900907136432455024673 := by
  unfold tailWord_4340769
  simp only [CollatzResearch.WordTrace]
  refine ⟨158320852011142732168873361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105547234674095154779248907 158320852011142732168873361)
  ·
    refine ⟨118740639008357049126655021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158320852011142732168873361 118740639008357049126655021)
    ·
      refine ⟨44527739628133893422495633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118740639008357049126655021 44527739628133893422495633)
      ·
        refine ⟨33395804721100420066871725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44527739628133893422495633 33395804721100420066871725)
        ·
          refine ⟨12523426770412657525076897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33395804721100420066871725 12523426770412657525076897)
          ·
            refine ⟨9392570077809493143807673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12523426770412657525076897 9392570077809493143807673)
            ·
              refine ⟨7044427558357119857855755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9392570077809493143807673 7044427558357119857855755)
              ·
                refine ⟨10566641337535679786783633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044427558357119857855755 10566641337535679786783633)
                ·
                  refine ⟨7924981003151759840087725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10566641337535679786783633 7924981003151759840087725)
                  ·
                    refine ⟨2971867876181909940032897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7924981003151759840087725 2971867876181909940032897)
                    ·
                      refine ⟨2228900907136432455024673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2971867876181909940032897 2228900907136432455024673)
                      ·
                        rfl

theorem cell23_4340769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4340769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340769 prefixEnd_4340769 := by exact prefixLift 4340769
  have htrace : WordTrace (prefixWord ++ tailWord_4340769) baseStart_4340769 baseEnd_4340769 := by
    simpa [prefixWord, tailWord_4340769, baseEnd_4340769] using wordTrace_append hprefix tailTrace_4340769
  have hstable : (prefixWord ++ tailWord_4340769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340769).length < 2 ^ (prefixWord ++ tailWord_4340769).sum := by decide
  have hdescent : baseEnd_4340769 < baseStart_4340769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340792 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_4340792 : Nat := 118140960795 + 4340792 * 2 ^ 59
def prefixEnd_4340792 : Nat := 4983230072969 + 3 ^ 40 * 4340792 * 2
def baseEnd_4340792 : Nat := 742970905730495288345689

theorem tailTrace_4340792 : CollatzResearch.WordTrace tailWord_4340792 prefixEnd_4340792 742970905730495288345689 := by
  unfold tailWord_4340792
  simp only [CollatzResearch.WordTrace]
  refine ⟨79160845445029703548480315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105547793926706271397973753 79160845445029703548480315)
  ·
    refine ⟨118741268167544555322720473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79160845445029703548480315 118741268167544555322720473)
    ·
      refine ⟨89055951125658416492040355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118741268167544555322720473 89055951125658416492040355)
      ·
        refine ⟨133583926688487624738060533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89055951125658416492040355 133583926688487624738060533)
        ·
          refine ⟨12523493127045714819193175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133583926688487624738060533 12523493127045714819193175)
          ·
            refine ⟨18785239690568572228789763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12523493127045714819193175 18785239690568572228789763)
            ·
              refine ⟨28177859535852858343184645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18785239690568572228789763 28177859535852858343184645)
              ·
                refine ⟨5283348662972410939347121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28177859535852858343184645 5283348662972410939347121)
                ·
                  refine ⟨3962511497229308204510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5283348662972410939347121 3962511497229308204510341)
                  ·
                    refine ⟨742970905730495288345689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962511497229308204510341 742970905730495288345689)
                    ·
                      rfl

theorem cell23_4340792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_4340792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340792 prefixEnd_4340792 := by exact prefixLift 4340792
  have htrace : WordTrace (prefixWord ++ tailWord_4340792) baseStart_4340792 baseEnd_4340792 := by
    simpa [prefixWord, tailWord_4340792, baseEnd_4340792] using wordTrace_append hprefix tailTrace_4340792
  have hstable : (prefixWord ++ tailWord_4340792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340792).length < 2 ^ (prefixWord ++ tailWord_4340792).sum := by decide
  have hdescent : baseEnd_4340792 < baseStart_4340792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340793 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4340793 : Nat := 118140960795 + 4340793 * 2 ^ 59
def prefixEnd_4340793 : Nat := 4983230072969 + 3 ^ 40 * 4340793 * 2
def baseEnd_4340793 : Nat := 2228913230672140361124563

theorem tailTrace_4340793 : CollatzResearch.WordTrace tailWord_4340793 prefixEnd_4340793 2228913230672140361124563 := by
  unfold tailWord_4340793
  simp only [CollatzResearch.WordTrace]
  refine ⟨158321727363055784267747033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105547818242037189511831355 158321727363055784267747033)
  ·
    refine ⟨118741295522291838200810275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158321727363055784267747033 118741295522291838200810275)
    ·
      refine ⟨178111943283437757301215413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118741295522291838200810275 178111943283437757301215413)
      ·
        refine ⟨16697994682822289746988945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178111943283437757301215413 16697994682822289746988945)
        ·
          refine ⟨12523496012116717310241709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16697994682822289746988945 12523496012116717310241709)
          ·
            refine ⟨4696311004543768991340641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12523496012116717310241709 4696311004543768991340641)
            ·
              refine ⟨3522233253407826743505481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696311004543768991340641 3522233253407826743505481)
              ·
                refine ⟨2641674940055870057629111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522233253407826743505481 2641674940055870057629111)
                ·
                  refine ⟨3962512410083805086443667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641674940055870057629111 3962512410083805086443667)
                  ·
                    refine ⟨5943768615125707629665501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3962512410083805086443667 5943768615125707629665501)
                    ·
                      refine ⟨2228913230672140361124563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943768615125707629665501 2228913230672140361124563)
                      ·
                        rfl

theorem cell23_4340793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4340793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340793 prefixEnd_4340793 := by exact prefixLift 4340793
  have htrace : WordTrace (prefixWord ++ tailWord_4340793) baseStart_4340793 baseEnd_4340793 := by
    simpa [prefixWord, tailWord_4340793, baseEnd_4340793] using wordTrace_append hprefix tailTrace_4340793
  have hstable : (prefixWord ++ tailWord_4340793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340793).length < 2 ^ (prefixWord ++ tailWord_4340793).sum := by decide
  have hdescent : baseEnd_4340793 < baseStart_4340793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
