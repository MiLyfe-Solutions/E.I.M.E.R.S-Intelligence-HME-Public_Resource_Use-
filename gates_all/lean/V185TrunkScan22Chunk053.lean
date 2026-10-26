import V185TrunkScan22Chunk052

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_476812 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_476812 : Nat := 118140960795 + 476812 * 2 ^ 59
def prefixEnd_476812 : Nat := 4983230072969 + 3 ^ 40 * 476812 * 2
def baseEnd_476812 : Nat := 163222491887795803038125

theorem tailTrace_476812 : CollatzResearch.WordTrace tailWord_476812 prefixEnd_476812 163222491887795803038125 := by
  unfold tailWord_476812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695381174299515925748345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11593841565732687900997793 8695381174299515925748345)
  ·
    refine ⟨6521535880724636944311259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8695381174299515925748345 6521535880724636944311259)
    ·
      refine ⟨9782303821086955416466889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6521535880724636944311259 9782303821086955416466889)
      ·
        refine ⟨7336727865815216562350167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782303821086955416466889 7336727865815216562350167)
        ·
          refine ⟨11005091798722824843525251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336727865815216562350167 11005091798722824843525251)
          ·
            refine ⟨16507637698084237265287877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005091798722824843525251 16507637698084237265287877)
            ·
              refine ⟨3095182068390794487241477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16507637698084237265287877 3095182068390794487241477)
              ·
                refine ⟨580346637823273966357777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3095182068390794487241477 580346637823273966357777)
                ·
                  refine ⟨435259978367455474768333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580346637823273966357777 435259978367455474768333)
                  ·
                    refine ⟨163222491887795803038125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435259978367455474768333 163222491887795803038125)
                    ·
                      rfl

theorem cell22_476812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_476812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476812 prefixEnd_476812 := by exact prefixLift 476812
  have htrace : WordTrace (prefixWord ++ tailWord_476812) baseStart_476812 baseEnd_476812 := by
    simpa [prefixWord, tailWord_476812, baseEnd_476812] using wordTrace_append hprefix tailTrace_476812
  have hstable : (prefixWord ++ tailWord_476812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476812).length < 2 ^ (prefixWord ++ tailWord_476812).sum := by decide
  have hdescent : baseEnd_476812 < baseStart_476812 := by decide
  rcases family_descends (prefixWord ++ tailWord_476812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476932 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_476932 : Nat := 118140960795 + 476932 * 2 ^ 59
def prefixEnd_476932 : Nat := 4983230072969 + 3 ^ 40 * 476932 * 2
def baseEnd_476932 : Nat := 54421190113385163345919

theorem tailTrace_476932 : CollatzResearch.WordTrace tailWord_476932 prefixEnd_476932 54421190113385163345919 := by
  unfold tailWord_476932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697569554082146172932525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11596759405442861563910033 8697569554082146172932525)
  ·
    refine ⟨3261588582780804814849697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8697569554082146172932525 3261588582780804814849697)
    ·
      refine ⟨2446191437085603611137273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3261588582780804814849697 2446191437085603611137273)
      ·
        refine ⟨1834643577814202708352955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2446191437085603611137273 1834643577814202708352955)
        ·
          refine ⟨2751965366721304062529433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834643577814202708352955 2751965366721304062529433)
          ·
            refine ⟨2063974025040978046897075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751965366721304062529433 2063974025040978046897075)
            ·
              refine ⟨3095961037561467070345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063974025040978046897075 3095961037561467070345613)
              ·
                refine ⟨1160985389085550151379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3095961037561467070345613 1160985389085550151379605)
                ·
                  refine ⟨54421190113385163345919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1160985389085550151379605 54421190113385163345919)
                  ·
                    rfl

theorem cell22_476932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_476932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476932 prefixEnd_476932 := by exact prefixLift 476932
  have htrace : WordTrace (prefixWord ++ tailWord_476932) baseStart_476932 baseEnd_476932 := by
    simpa [prefixWord, tailWord_476932, baseEnd_476932] using wordTrace_append hprefix tailTrace_476932
  have hstable : (prefixWord ++ tailWord_476932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476932).length < 2 ^ (prefixWord ++ tailWord_476932).sum := by decide
  have hdescent : baseEnd_476932 < baseStart_476932 := by decide
  rcases family_descends (prefixWord ++ tailWord_476932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476962 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_476962 : Nat := 118140960795 + 476962 * 2 ^ 59
def prefixEnd_476962 : Nat := 4983230072969 + 3 ^ 40 * 476962 * 2
def baseEnd_476962 : Nat := 163273839953245411787665

theorem tailTrace_476962 : CollatzResearch.WordTrace tailWord_476962 prefixEnd_476962 163273839953245411787665 := by
  unfold tailWord_476962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349058324513901867364285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11597488865370404979638093 4349058324513901867364285)
  ·
    refine ⟨1630896871692713200261607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4349058324513901867364285 1630896871692713200261607)
    ·
      refine ⟨2446345307539069800392411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630896871692713200261607 2446345307539069800392411)
      ·
        refine ⟨3669517961308604700588617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446345307539069800392411 3669517961308604700588617)
        ·
          refine ⟨2752138470981453525441463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669517961308604700588617 2752138470981453525441463)
          ·
            refine ⟨4128207706472180288162195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752138470981453525441463 4128207706472180288162195)
            ·
              refine ⟨6192311559708270432243293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128207706472180288162195 6192311559708270432243293)
              ·
                refine ⟨2322116834890601412091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6192311559708270432243293 2322116834890601412091235)
                ·
                  refine ⟨3483175252335902118136853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322116834890601412091235 3483175252335902118136853)
                  ·
                    refine ⟨163273839953245411787665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3483175252335902118136853 163273839953245411787665)
                    ·
                      rfl

theorem cell22_476962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_476962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476962 prefixEnd_476962 := by exact prefixLift 476962
  have htrace : WordTrace (prefixWord ++ tailWord_476962) baseStart_476962 baseEnd_476962 := by
    simpa [prefixWord, tailWord_476962, baseEnd_476962] using wordTrace_append hprefix tailTrace_476962
  have hstable : (prefixWord ++ tailWord_476962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476962).length < 2 ^ (prefixWord ++ tailWord_476962).sum := by decide
  have hdescent : baseEnd_476962 < baseStart_476962 := by decide
  rcases family_descends (prefixWord ++ tailWord_476962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476964 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_476964 : Nat := 118140960795 + 476964 * 2 ^ 59
def prefixEnd_476964 : Nat := 4983230072969 + 3 ^ 40 * 476964 * 2
def baseEnd_476964 : Nat := 163274524594118073237659

theorem tailTrace_476964 : CollatzResearch.WordTrace tailWord_476964 prefixEnd_476964 163274524594118073237659 := by
  unfold tailWord_476964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698153122024180905514973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11597537496032241207353297 8698153122024180905514973)
  ·
    refine ⟨3261807420759067839568115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8698153122024180905514973 3261807420759067839568115)
    ·
      refine ⟨4892711131138601759352173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261807420759067839568115 4892711131138601759352173)
      ·
        refine ⟨1834766674176975659757065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4892711131138601759352173 1834766674176975659757065)
        ·
          refine ⟨1376075005632731744817799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834766674176975659757065 1376075005632731744817799)
          ·
            refine ⟨2064112508449097617226699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376075005632731744817799 2064112508449097617226699)
            ·
              refine ⟨3096168762673646425840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064112508449097617226699 3096168762673646425840049)
              ·
                refine ⟨2322126572005234819380037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096168762673646425840049 2322126572005234819380037)
                ·
                  refine ⟨435398732250981528633757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322126572005234819380037 435398732250981528633757)
                  ·
                    refine ⟨163274524594118073237659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435398732250981528633757 163274524594118073237659)
                    ·
                      rfl

theorem cell22_476964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_476964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476964 prefixEnd_476964 := by exact prefixLift 476964
  have htrace : WordTrace (prefixWord ++ tailWord_476964) baseStart_476964 baseEnd_476964 := by
    simpa [prefixWord, tailWord_476964, baseEnd_476964] using wordTrace_append hprefix tailTrace_476964
  have hstable : (prefixWord ++ tailWord_476964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476964).length < 2 ^ (prefixWord ++ tailWord_476964).sum := by decide
  have hdescent : baseEnd_476964 < baseStart_476964 := by decide
  rcases family_descends (prefixWord ++ tailWord_476964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_476975 : Nat := 118140960795 + 476975 * 2 ^ 59
def prefixEnd_476975 : Nat := 4983230072969 + 3 ^ 40 * 476975 * 2
def baseEnd_476975 : Nat := 163278290118917711212625

theorem tailTrace_476975 : CollatzResearch.WordTrace tailWord_476975 prefixEnd_476975 163278290118917711212625 := by
  unfold tailWord_476975
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396707447008510689680379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597804964672340459786919 17396707447008510689680379)
  ·
    refine ⟨26095061170512766034520569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396707447008510689680379 26095061170512766034520569)
    ·
      refine ⟨19571295877884574525890427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26095061170512766034520569 19571295877884574525890427)
      ·
        refine ⟨29356943816826861788835641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19571295877884574525890427 29356943816826861788835641)
        ·
          refine ⟨22017707862620146341626731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29356943816826861788835641 22017707862620146341626731)
          ·
            refine ⟨33026561793930219512440097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22017707862620146341626731 33026561793930219512440097)
            ·
              refine ⟨24769921345447664634330073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33026561793930219512440097 24769921345447664634330073)
              ·
                refine ⟨18577441009085748475747555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24769921345447664634330073 18577441009085748475747555)
                ·
                  refine ⟨27866161513628622713621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18577441009085748475747555 27866161513628622713621333)
                  ·
                    refine ⟨163278290118917711212625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27866161513628622713621333 163278290118917711212625)
                    ·
                      rfl

theorem cell22_476975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_476975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476975 prefixEnd_476975 := by exact prefixLift 476975
  have htrace : WordTrace (prefixWord ++ tailWord_476975) baseStart_476975 baseEnd_476975 := by
    simpa [prefixWord, tailWord_476975, baseEnd_476975] using wordTrace_append hprefix tailTrace_476975
  have hstable : (prefixWord ++ tailWord_476975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476975).length < 2 ^ (prefixWord ++ tailWord_476975).sum := by decide
  have hdescent : baseEnd_476975 < baseStart_476975 := by decide
  rcases family_descends (prefixWord ++ tailWord_476975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476977 : List Nat := [1, 2, 2, 3, 2, 4, 8]
def baseStart_476977 : Nat := 118140960795 + 476977 * 2 ^ 59
def prefixEnd_476977 : Nat := 4983230072969 + 3 ^ 40 * 476977 * 2
def baseEnd_476977 : Nat := 6047369435547791580097

theorem tailTrace_476977 : CollatzResearch.WordTrace tailWord_476977 prefixEnd_476977 6047369435547791580097 := by
  unfold tailWord_476977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396780393001265031253185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597853595334176687502123 17396780393001265031253185)
  ·
    refine ⟨13047585294750948773439889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17396780393001265031253185 13047585294750948773439889)
    ·
      refine ⟨9785688971063211580079917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13047585294750948773439889 9785688971063211580079917)
      ·
        refine ⟨3669633364148704342529969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9785688971063211580079917 3669633364148704342529969)
        ·
          refine ⟨2752225023111528256897477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669633364148704342529969 2752225023111528256897477)
          ·
            refine ⟨516042191833411548168277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2752225023111528256897477 516042191833411548168277)
            ·
              refine ⟨6047369435547791580097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 516042191833411548168277 6047369435547791580097)
              ·
                rfl

theorem cell22_476977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 8].length) (baseStart_476977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476977 prefixEnd_476977 := by exact prefixLift 476977
  have htrace : WordTrace (prefixWord ++ tailWord_476977) baseStart_476977 baseEnd_476977 := by
    simpa [prefixWord, tailWord_476977, baseEnd_476977] using wordTrace_append hprefix tailTrace_476977
  have hstable : (prefixWord ++ tailWord_476977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476977).length < 2 ^ (prefixWord ++ tailWord_476977).sum := by decide
  have hdescent : baseEnd_476977 < baseStart_476977 := by decide
  rcases family_descends (prefixWord ++ tailWord_476977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476979 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_476979 : Nat := 118140960795 + 476979 * 2 ^ 59
def prefixEnd_476979 : Nat := 4983230072969 + 3 ^ 40 * 476979 * 2
def baseEnd_476979 : Nat := 163279659400663034112613

theorem tailTrace_476979 : CollatzResearch.WordTrace tailWord_476979 prefixEnd_476979 163279659400663034112613 := by
  unfold tailWord_476979
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396853338994019372825991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597902225996012915217327 17396853338994019372825991)
  ·
    refine ⟨26095280008491029059238987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396853338994019372825991 26095280008491029059238987)
    ·
      refine ⟨39142920012736543588858481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26095280008491029059238987 39142920012736543588858481)
      ·
        refine ⟨29357190009552407691643861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39142920012736543588858481 29357190009552407691643861)
        ·
          refine ⟨688059140848884555272903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29357190009552407691643861 688059140848884555272903)
          ·
            refine ⟨1032088711273326832909355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688059140848884555272903 1032088711273326832909355)
            ·
              refine ⟨1548133066909990249364033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032088711273326832909355 1548133066909990249364033)
              ·
                refine ⟨1161099800182492687023025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548133066909990249364033 1161099800182492687023025)
                ·
                  refine ⟨870824850136869515267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161099800182492687023025 870824850136869515267269)
                  ·
                    refine ⟨163279659400663034112613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870824850136869515267269 163279659400663034112613)
                    ·
                      rfl

theorem cell22_476979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_476979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_476979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_476979 prefixEnd_476979 := by exact prefixLift 476979
  have htrace : WordTrace (prefixWord ++ tailWord_476979) baseStart_476979 baseEnd_476979 := by
    simpa [prefixWord, tailWord_476979, baseEnd_476979] using wordTrace_append hprefix tailTrace_476979
  have hstable : (prefixWord ++ tailWord_476979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476979).length < 2 ^ (prefixWord ++ tailWord_476979).sum := by decide
  have hdescent : baseEnd_476979 < baseStart_476979 := by decide
  rcases family_descends (prefixWord ++ tailWord_476979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477112 : List Nat := [2, 1, 2, 1, 2, 3, 2, 9]
def baseStart_477112 : Nat := 118140960795 + 477112 * 2 ^ 59
def prefixEnd_477112 : Nat := 4983230072969 + 3 ^ 40 * 477112 * 2
def baseEnd_477112 : Nat := 18147243113188335615245

theorem tailTrace_477112 : CollatzResearch.WordTrace tailWord_477112 prefixEnd_477112 18147243113188335615245 := by
  unfold tailWord_477112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700852123756091543708795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11601136165008122058278393 8700852123756091543708795)
  ·
    refine ⟨13051278185634137315563193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8700852123756091543708795 13051278185634137315563193)
    ·
      refine ⟨9788458639225602986672395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13051278185634137315563193 9788458639225602986672395)
      ·
        refine ⟨14682687958838404480008593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788458639225602986672395 14682687958838404480008593)
        ·
          refine ⟨11012015969128803360006445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14682687958838404480008593 11012015969128803360006445)
          ·
            refine ⟨4129505988423301260002417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11012015969128803360006445 4129505988423301260002417)
            ·
              refine ⟨3097129491317475945001813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129505988423301260002417 3097129491317475945001813)
              ·
                refine ⟨18147243113188335615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3097129491317475945001813 18147243113188335615245)
                ·
                  rfl

theorem cell22_477112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_477112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477112 prefixEnd_477112 := by exact prefixLift 477112
  have htrace : WordTrace (prefixWord ++ tailWord_477112) baseStart_477112 baseEnd_477112 := by
    simpa [prefixWord, tailWord_477112, baseEnd_477112] using wordTrace_append hprefix tailTrace_477112
  have hstable : (prefixWord ++ tailWord_477112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477112).length < 2 ^ (prefixWord ++ tailWord_477112).sum := by decide
  have hdescent : baseEnd_477112 < baseStart_477112 := by decide
  rcases family_descends (prefixWord ++ tailWord_477112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477127 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_477127 : Nat := 118140960795 + 477127 * 2 ^ 59
def prefixEnd_477127 : Nat := 4983230072969 + 3 ^ 40 * 477127 * 2
def baseEnd_477127 : Nat := 163330322825239981412159

theorem tailTrace_477127 : CollatzResearch.WordTrace tailWord_477127 prefixEnd_477127 163330322825239981412159 := by
  unfold tailWord_477127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402251342457840649213635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11601500894971893766142423 17402251342457840649213635)
  ·
    refine ⟨26103377013686760973820453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17402251342457840649213635 26103377013686760973820453)
    ·
      refine ⟨4894383190066267682591335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26103377013686760973820453 4894383190066267682591335)
      ·
        refine ⟨7341574785099401523887003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894383190066267682591335 7341574785099401523887003)
        ·
          refine ⟨11012362177649102285830505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341574785099401523887003 11012362177649102285830505)
          ·
            refine ⟨8259271633236826714372879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11012362177649102285830505 8259271633236826714372879)
            ·
              refine ⟨12388907449855240071559319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259271633236826714372879 12388907449855240071559319)
              ·
                refine ⟨18583361174782860107338979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12388907449855240071559319 18583361174782860107338979)
                ·
                  refine ⟨27875041762174290161008469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18583361174782860107338979 27875041762174290161008469)
                  ·
                    refine ⟨163330322825239981412159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27875041762174290161008469 163330322825239981412159)
                    ·
                      rfl

theorem cell22_477127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_477127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477127 prefixEnd_477127 := by exact prefixLift 477127
  have htrace : WordTrace (prefixWord ++ tailWord_477127) baseStart_477127 baseEnd_477127 := by
    simpa [prefixWord, tailWord_477127, baseEnd_477127] using wordTrace_append hprefix tailTrace_477127
  have hstable : (prefixWord ++ tailWord_477127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477127).length < 2 ^ (prefixWord ++ tailWord_477127).sum := by decide
  have hdescent : baseEnd_477127 < baseStart_477127 := by decide
  rcases family_descends (prefixWord ++ tailWord_477127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477146 : List Nat := [3, 1, 1, 2, 6, 1, 8]
def baseStart_477146 : Nat := 118140960795 + 477146 * 2 ^ 59
def prefixEnd_477146 : Nat := 4983230072969 + 3 ^ 40 * 477146 * 2
def baseEnd_477146 : Nat := 6049512107908528340263

theorem tailTrace_477146 : CollatzResearch.WordTrace tailWord_477146 prefixEnd_477146 6049512107908528340263 := by
  unfold tailWord_477146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350736082347251723538823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11601962886259337929436861 4350736082347251723538823)
  ·
    refine ⟨6526104123520877585308235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350736082347251723538823 6526104123520877585308235)
    ·
      refine ⟨9789156185281316377962353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526104123520877585308235 9789156185281316377962353)
      ·
        refine ⟨7341867138960987283471765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9789156185281316377962353 7341867138960987283471765)
        ·
          refine ⟨344150022138796278912739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7341867138960987283471765 344150022138796278912739)
          ·
            refine ⟨516225033208194418369109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344150022138796278912739 516225033208194418369109)
            ·
              refine ⟨6049512107908528340263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 516225033208194418369109 6049512107908528340263)
              ·
                rfl

theorem cell22_477146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 8].length) (baseStart_477146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477146 prefixEnd_477146 := by exact prefixLift 477146
  have htrace : WordTrace (prefixWord ++ tailWord_477146) baseStart_477146 baseEnd_477146 := by
    simpa [prefixWord, tailWord_477146, baseEnd_477146] using wordTrace_append hprefix tailTrace_477146
  have hstable : (prefixWord ++ tailWord_477146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477146).length < 2 ^ (prefixWord ++ tailWord_477146).sum := by decide
  have hdescent : baseEnd_477146 < baseStart_477146 := by decide
  rcases family_descends (prefixWord ++ tailWord_477146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477212 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_477212 : Nat := 118140960795 + 477212 * 2 ^ 59
def prefixEnd_477212 : Nat := 4983230072969 + 3 ^ 40 * 477212 * 2
def baseEnd_477212 : Nat := 163359420062328093036899

theorem tailTrace_477212 : CollatzResearch.WordTrace tailWord_477212 prefixEnd_477212 163359420062328093036899 := by
  unfold tailWord_477212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702675773574950083028945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11603567698099933444038593 8702675773574950083028945)
  ·
    refine ⟨6527006830181212562271709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8702675773574950083028945 6527006830181212562271709)
    ·
      refine ⟨2447627561317954710851891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6527006830181212562271709 2447627561317954710851891)
      ·
        refine ⟨3671441341976932066277837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447627561317954710851891 3671441341976932066277837)
        ·
          refine ⟨1376790503241349524854189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3671441341976932066277837 1376790503241349524854189)
          ·
            refine ⟨516296438715506071820321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1376790503241349524854189 516296438715506071820321)
            ·
              refine ⟨387222329036629553865241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516296438715506071820321 387222329036629553865241)
              ·
                refine ⟨290416746777472165398931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387222329036629553865241 290416746777472165398931)
                ·
                  refine ⟨435625120166208248098397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290416746777472165398931 435625120166208248098397)
                  ·
                    refine ⟨163359420062328093036899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435625120166208248098397 163359420062328093036899)
                    ·
                      rfl

theorem cell22_477212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_477212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477212 prefixEnd_477212 := by exact prefixLift 477212
  have htrace : WordTrace (prefixWord ++ tailWord_477212) baseStart_477212 baseEnd_477212 := by
    simpa [prefixWord, tailWord_477212, baseEnd_477212] using wordTrace_append hprefix tailTrace_477212
  have hstable : (prefixWord ++ tailWord_477212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477212).length < 2 ^ (prefixWord ++ tailWord_477212).sum := by decide
  have hdescent : baseEnd_477212 < baseStart_477212 := by decide
  rcases family_descends (prefixWord ++ tailWord_477212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477219 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 6]
def baseStart_477219 : Nat := 118140960795 + 477219 * 2 ^ 59
def prefixEnd_477219 : Nat := 4983230072969 + 3 ^ 40 * 477219 * 2
def baseEnd_477219 : Nat := 54453938768460802703959

theorem tailTrace_477219 : CollatzResearch.WordTrace tailWord_477219 prefixEnd_477219 54453938768460802703959 := by
  unfold tailWord_477219
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405606858124540361562711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11603737905416360241041807 17405606858124540361562711)
  ·
    refine ⟨26108410287186810542344067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17405606858124540361562711 26108410287186810542344067)
    ·
      refine ⟨39162615430780215813516101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26108410287186810542344067 39162615430780215813516101)
      ·
        refine ⟨7342990393271290465034269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39162615430780215813516101 7342990393271290465034269)
        ·
          refine ⟨2753621397476733924387851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7342990393271290465034269 2753621397476733924387851)
          ·
            refine ⟨4130432096215100886581777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753621397476733924387851 4130432096215100886581777)
            ·
              refine ⟨3097824072161325664936333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130432096215100886581777 3097824072161325664936333)
              ·
                refine ⟨1161684027060497124351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097824072161325664936333 1161684027060497124351125)
                ·
                  refine ⟨54453938768460802703959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1161684027060497124351125 54453938768460802703959)
                  ·
                    rfl

theorem cell22_477219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_477219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477219 prefixEnd_477219 := by exact prefixLift 477219
  have htrace : WordTrace (prefixWord ++ tailWord_477219) baseStart_477219 baseEnd_477219 := by
    simpa [prefixWord, tailWord_477219, baseEnd_477219] using wordTrace_append hprefix tailTrace_477219
  have hstable : (prefixWord ++ tailWord_477219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477219).length < 2 ^ (prefixWord ++ tailWord_477219).sum := by decide
  have hdescent : baseEnd_477219 < baseStart_477219 := by decide
  rcases family_descends (prefixWord ++ tailWord_477219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477223 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 5]
def baseStart_477223 : Nat := 118140960795 + 477223 * 2 ^ 59
def prefixEnd_477223 : Nat := 4983230072969 + 3 ^ 40 * 477223 * 2
def baseEnd_477223 : Nat := 163363185587127731011865

theorem tailTrace_477223 : CollatzResearch.WordTrace tailWord_477223 prefixEnd_477223 163363185587127731011865 := by
  unfold tailWord_477223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405752750110049044708323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11603835166740032696472215 17405752750110049044708323)
  ·
    refine ⟨26108629125165073567062485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17405752750110049044708323 26108629125165073567062485)
    ·
      refine ⟨611920995121056411728027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26108629125165073567062485 611920995121056411728027)
      ·
        refine ⟨917881492681584617592041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611920995121056411728027 917881492681584617592041)
        ·
          refine ⟨688411119511188463194031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917881492681584617592041 688411119511188463194031)
          ·
            refine ⟨1032616679266782694791047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688411119511188463194031 1032616679266782694791047)
            ·
              refine ⟨1548925018900174042186571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032616679266782694791047 1548925018900174042186571)
              ·
                refine ⟨2323387528350261063279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548925018900174042186571 2323387528350261063279857)
                ·
                  refine ⟨1742540646262695797459893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2323387528350261063279857 1742540646262695797459893)
                  ·
                    refine ⟨163363185587127731011865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1742540646262695797459893 163363185587127731011865)
                    ·
                      rfl

theorem cell22_477223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_477223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477223 prefixEnd_477223 := by exact prefixLift 477223
  have htrace : WordTrace (prefixWord ++ tailWord_477223) baseStart_477223 baseEnd_477223 := by
    simpa [prefixWord, tailWord_477223, baseEnd_477223] using wordTrace_append hprefix tailTrace_477223
  have hstable : (prefixWord ++ tailWord_477223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477223).length < 2 ^ (prefixWord ++ tailWord_477223).sum := by decide
  have hdescent : baseEnd_477223 < baseStart_477223 := by decide
  rcases family_descends (prefixWord ++ tailWord_477223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477238 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_477238 : Nat := 118140960795 + 477238 * 2 ^ 59
def prefixEnd_477238 : Nat := 4983230072969 + 3 ^ 40 * 477238 * 2
def baseEnd_477238 : Nat := 163368320393672691886819

theorem tailTrace_477238 : CollatzResearch.WordTrace tailWord_477238 prefixEnd_477238 163368320393672691886819 := by
  unfold tailWord_477238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087893740315981662906523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11604199896703804404336245 1087893740315981662906523)
  ·
    refine ⟨1631840610473972494359785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1087893740315981662906523 1631840610473972494359785)
    ·
      refine ⟨1223880457855479370769839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1631840610473972494359785 1223880457855479370769839)
      ·
        refine ⟨1835820686783219056154759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223880457855479370769839 1835820686783219056154759)
        ·
          refine ⟨2753731030174828584232139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835820686783219056154759 2753731030174828584232139)
          ·
            refine ⟨4130596545262242876348209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753731030174828584232139 4130596545262242876348209)
            ·
              refine ⟨3097947408946682157261157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130596545262242876348209 3097947408946682157261157)
              ·
                refine ⟨580865139177502904486467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3097947408946682157261157 580865139177502904486467)
                ·
                  refine ⟨871297708766254356729701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580865139177502904486467 871297708766254356729701)
                  ·
                    refine ⟨163368320393672691886819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 871297708766254356729701 163368320393672691886819)
                    ·
                      rfl

theorem cell22_477238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_477238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477238 prefixEnd_477238 := by exact prefixLift 477238
  have htrace : WordTrace (prefixWord ++ tailWord_477238) baseStart_477238 baseEnd_477238 := by
    simpa [prefixWord, tailWord_477238, baseEnd_477238] using wordTrace_append hprefix tailTrace_477238
  have hstable : (prefixWord ++ tailWord_477238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477238).length < 2 ^ (prefixWord ++ tailWord_477238).sum := by decide
  have hdescent : baseEnd_477238 < baseStart_477238 := by decide
  rcases family_descends (prefixWord ++ tailWord_477238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477270 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_477270 : Nat := 118140960795 + 477270 * 2 ^ 59
def prefixEnd_477270 : Nat := 4983230072969 + 3 ^ 40 * 477270 * 2
def baseEnd_477270 : Nat := 54459758215878425028907

theorem tailTrace_477270 : CollatzResearch.WordTrace tailWord_477270 prefixEnd_477270 54459758215878425028907 := by
  unfold tailWord_477270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087966686308736004479329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11604977987293184047779509 1087966686308736004479329)
  ·
    refine ⟨815975014731552003359497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087966686308736004479329 815975014731552003359497)
    ·
      refine ⟨611981261048664002519623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 815975014731552003359497 611981261048664002519623)
      ·
        refine ⟨917971891572996003779435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611981261048664002519623 917971891572996003779435)
        ·
          refine ⟨1376957837359494005669153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917971891572996003779435 1376957837359494005669153)
          ·
            refine ⟨1032718378019620504251865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376957837359494005669153 1032718378019620504251865)
            ·
              refine ⟨774538783514715378188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032718378019620504251865 774538783514715378188899)
              ·
                refine ⟨1161808175272073067283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774538783514715378188899 1161808175272073067283349)
                ·
                  refine ⟨54459758215878425028907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1161808175272073067283349 54459758215878425028907)
                  ·
                    rfl

theorem cell22_477270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_477270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477270 prefixEnd_477270 := by exact prefixLift 477270
  have htrace : WordTrace (prefixWord ++ tailWord_477270) baseStart_477270 baseEnd_477270 := by
    simpa [prefixWord, tailWord_477270, baseEnd_477270] using wordTrace_append hprefix tailTrace_477270
  have hstable : (prefixWord ++ tailWord_477270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477270).length < 2 ^ (prefixWord ++ tailWord_477270).sum := by decide
  have hdescent : baseEnd_477270 < baseStart_477270 := by decide
  rcases family_descends (prefixWord ++ tailWord_477270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477285 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_477285 : Nat := 118140960795 + 477285 * 2 ^ 59
def prefixEnd_477285 : Nat := 4983230072969 + 3 ^ 40 * 477285 * 2
def baseEnd_477285 : Nat := 163384409454180235961675

theorem tailTrace_477285 : CollatzResearch.WordTrace tailWord_477285 prefixEnd_477285 163384409454180235961675 := by
  unfold tailWord_477285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408014075885433633465309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11605342717256955755643539 17408014075885433633465309)
  ·
    refine ⟨6528005278457037612549491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17408014075885433633465309 6528005278457037612549491)
    ·
      refine ⟨9792007917685556418824237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528005278457037612549491 9792007917685556418824237)
      ·
        refine ⟨3672002969132083657059089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9792007917685556418824237 3672002969132083657059089)
        ·
          refine ⟨2754002226849062742794317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672002969132083657059089 2754002226849062742794317)
          ·
            refine ⟨1032750835068398528547869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2754002226849062742794317 1032750835068398528547869)
            ·
              refine ⟨387281563150649448205451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032750835068398528547869 387281563150649448205451)
              ·
                refine ⟨580922344725974172308177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387281563150649448205451 580922344725974172308177)
                ·
                  refine ⟨435691758544480629231133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580922344725974172308177 435691758544480629231133)
                  ·
                    refine ⟨163384409454180235961675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435691758544480629231133 163384409454180235961675)
                    ·
                      rfl

theorem cell22_477285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_477285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477285 prefixEnd_477285 := by exact prefixLift 477285
  have htrace : WordTrace (prefixWord ++ tailWord_477285) baseStart_477285 baseEnd_477285 := by
    simpa [prefixWord, tailWord_477285, baseEnd_477285] using wordTrace_append hprefix tailTrace_477285
  have hstable : (prefixWord ++ tailWord_477285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477285).length < 2 ^ (prefixWord ++ tailWord_477285).sum := by decide
  have hdescent : baseEnd_477285 < baseStart_477285 := by decide
  rcases family_descends (prefixWord ++ tailWord_477285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477298 : List Nat := [3, 2, 1, 2, 2, 4, 2, 6]
def baseStart_477298 : Nat := 118140960795 + 477298 * 2 ^ 59
def prefixEnd_477298 : Nat := 4983230072969 + 3 ^ 40 * 477298 * 2
def baseEnd_477298 : Nat := 18154317735539170598515

theorem tailTrace_477298 : CollatzResearch.WordTrace tailWord_477298 prefixEnd_477298 18154317735539170598515 := by
  unfold tailWord_477298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352122056209584213422137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11605658816558891235792365 4352122056209584213422137)
  ·
    refine ⟨3264091542157188160066603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4352122056209584213422137 3264091542157188160066603)
    ·
      refine ⟨4896137313235782240099905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264091542157188160066603 4896137313235782240099905)
      ·
        refine ⟨3672102984926836680074929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4896137313235782240099905 3672102984926836680074929)
        ·
          refine ⟨2754077238695127510056197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672102984926836680074929 2754077238695127510056197)
          ·
            refine ⟨516389482255336408135537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2754077238695127510056197 516389482255336408135537)
            ·
              refine ⟨387292111691502306101653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516389482255336408135537 387292111691502306101653)
              ·
                refine ⟨18154317735539170598515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 387292111691502306101653 18154317735539170598515)
                ·
                  rfl

theorem cell22_477298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_477298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477298 prefixEnd_477298 := by exact prefixLift 477298
  have htrace : WordTrace (prefixWord ++ tailWord_477298) baseStart_477298 baseEnd_477298 := by
    simpa [prefixWord, tailWord_477298, baseEnd_477298] using wordTrace_append hprefix tailTrace_477298
  have hstable : (prefixWord ++ tailWord_477298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477298).length < 2 ^ (prefixWord ++ tailWord_477298).sum := by decide
  have hdescent : baseEnd_477298 < baseStart_477298 := by decide
  rcases family_descends (prefixWord ++ tailWord_477298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477343 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 5]
def baseStart_477343 : Nat := 118140960795 + 477343 * 2 ^ 59
def prefixEnd_477343 : Nat := 4983230072969 + 3 ^ 40 * 477343 * 2
def baseEnd_477343 : Nat := 54468088013162472670499

theorem tailTrace_477343 : CollatzResearch.WordTrace tailWord_477343 prefixEnd_477343 54468088013162472670499 := by
  unfold tailWord_477343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410129509675309539076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11606753006450206359384455 17410129509675309539076683)
  ·
    refine ⟨26115194264512964308615025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17410129509675309539076683 26115194264512964308615025)
    ·
      refine ⟨19586395698384723231461269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26115194264512964308615025 19586395698384723231461269)
      ·
        refine ⟨918112298361783901474747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19586395698384723231461269 918112298361783901474747)
        ·
          refine ⟨1377168447542675852212121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918112298361783901474747 1377168447542675852212121)
          ·
            refine ⟨1032876335657006889159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377168447542675852212121 1032876335657006889159091)
            ·
              refine ⟨1549314503485510333738637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032876335657006889159091 1549314503485510333738637)
              ·
                refine ⟨580992938807066375151989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549314503485510333738637 580992938807066375151989)
                ·
                  refine ⟨54468088013162472670499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580992938807066375151989 54468088013162472670499)
                  ·
                    rfl

theorem cell22_477343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].length) (baseStart_477343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477343 prefixEnd_477343 := by exact prefixLift 477343
  have htrace : WordTrace (prefixWord ++ tailWord_477343) baseStart_477343 baseEnd_477343 := by
    simpa [prefixWord, tailWord_477343, baseEnd_477343] using wordTrace_append hprefix tailTrace_477343
  have hstable : (prefixWord ++ tailWord_477343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477343).length < 2 ^ (prefixWord ++ tailWord_477343).sum := by decide
  have hdescent : baseEnd_477343 < baseStart_477343 := by decide
  rcases family_descends (prefixWord ++ tailWord_477343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477386 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_477386 : Nat := 118140960795 + 477386 * 2 ^ 59
def prefixEnd_477386 : Nat := 4983230072969 + 3 ^ 40 * 477386 * 2
def baseEnd_477386 : Nat := 163418983818249639186365

theorem tailTrace_477386 : CollatzResearch.WordTrace tailWord_477386 prefixEnd_477386 163418983818249639186365 := by
  unfold tailWord_477386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352924462129881970723003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11607798565679685255261341 4352924462129881970723003)
  ·
    refine ⟨6529386693194822956084505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352924462129881970723003 6529386693194822956084505)
    ·
      refine ⟨4897040019896117217063379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6529386693194822956084505 4897040019896117217063379)
      ·
        refine ⟨7345560029844175825595069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897040019896117217063379 7345560029844175825595069)
        ·
          refine ⟨2754585011191565934598151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7345560029844175825595069 2754585011191565934598151)
          ·
            refine ⟨4131877516787348901897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754585011191565934598151 4131877516787348901897227)
            ·
              refine ⟨6197816275181023352845841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131877516787348901897227 6197816275181023352845841)
              ·
                refine ⟨4648362206385767514634381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197816275181023352845841 4648362206385767514634381)
                ·
                  refine ⟨1743135827394662817987893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648362206385767514634381 1743135827394662817987893)
                  ·
                    refine ⟨163418983818249639186365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1743135827394662817987893 163418983818249639186365)
                    ·
                      rfl

theorem cell22_477386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_477386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477386 prefixEnd_477386 := by exact prefixLift 477386
  have htrace : WordTrace (prefixWord ++ tailWord_477386) baseStart_477386 baseEnd_477386 := by
    simpa [prefixWord, tailWord_477386, baseEnd_477386] using wordTrace_append hprefix tailTrace_477386
  have hstable : (prefixWord ++ tailWord_477386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477386).length < 2 ^ (prefixWord ++ tailWord_477386).sum := by decide
  have hdescent : baseEnd_477386 < baseStart_477386 := by decide
  rcases family_descends (prefixWord ++ tailWord_477386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477401 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_477401 : Nat := 118140960795 + 477401 * 2 ^ 59
def prefixEnd_477401 : Nat := 4983230072969 + 3 ^ 40 * 477401 * 2
def baseEnd_477401 : Nat := 163424118624794600061319

theorem tailTrace_477401 : CollatzResearch.WordTrace tailWord_477401 prefixEnd_477401 163424118624794600061319 := by
  unfold tailWord_477401
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412244943465185444688057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11608163295643456963125371 17412244943465185444688057)
  ·
    refine ⟨13059183707598889083516043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17412244943465185444688057 13059183707598889083516043)
    ·
      refine ⟨19588775561398333625274065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13059183707598889083516043 19588775561398333625274065)
      ·
        refine ⟨14691581671048750218955549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19588775561398333625274065 14691581671048750218955549)
        ·
          refine ⟨5509343126643281332108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14691581671048750218955549 5509343126643281332108331)
          ·
            refine ⟨8264014689964921998162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509343126643281332108331 8264014689964921998162497)
            ·
              refine ⟨6198011017473691498621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264014689964921998162497 6198011017473691498621873)
              ·
                refine ⟨4648508263105268623966405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198011017473691498621873 4648508263105268623966405)
                ·
                  refine ⟨871595299332237866993701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4648508263105268623966405 871595299332237866993701)
                  ·
                    refine ⟨163424118624794600061319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 871595299332237866993701 163424118624794600061319)
                    ·
                      rfl

theorem cell22_477401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_477401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477401 prefixEnd_477401 := by exact prefixLift 477401
  have htrace : WordTrace (prefixWord ++ tailWord_477401) baseStart_477401 baseEnd_477401 := by
    simpa [prefixWord, tailWord_477401, baseEnd_477401] using wordTrace_append hprefix tailTrace_477401
  have hstable : (prefixWord ++ tailWord_477401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477401).length < 2 ^ (prefixWord ++ tailWord_477401).sum := by decide
  have hdescent : baseEnd_477401 < baseStart_477401 := by decide
  rcases family_descends (prefixWord ++ tailWord_477401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477525 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_477525 : Nat := 118140960795 + 477525 * 2 ^ 59
def prefixEnd_477525 : Nat := 4983230072969 + 3 ^ 40 * 477525 * 2
def baseEnd_477525 : Nat := 163466566358899609960939

theorem tailTrace_477525 : CollatzResearch.WordTrace tailWord_477525 prefixEnd_477525 163466566358899609960939 := by
  unfold tailWord_477525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416767595015954622202029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11611178396677303081468019 17416767595015954622202029)
  ·
    refine ⟨6531287848130982983325761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17416767595015954622202029 6531287848130982983325761)
    ·
      refine ⟨4898465886098237237494321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6531287848130982983325761 4898465886098237237494321)
      ·
        refine ⟨3673849414573677928120741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898465886098237237494321 3673849414573677928120741)
        ·
          refine ⟨688846765232564611522639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3673849414573677928120741 688846765232564611522639)
          ·
            refine ⟨1033270147848846917283959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688846765232564611522639 1033270147848846917283959)
            ·
              refine ⟨1549905221773270375925939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033270147848846917283959 1549905221773270375925939)
              ·
                refine ⟨2324857832659905563888909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549905221773270375925939 2324857832659905563888909)
                ·
                  refine ⟨871821687247464586458341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2324857832659905563888909 871821687247464586458341)
                  ·
                    refine ⟨163466566358899609960939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 871821687247464586458341 163466566358899609960939)
                    ·
                      rfl

theorem cell22_477525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_477525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477525 prefixEnd_477525 := by exact prefixLift 477525
  have htrace : WordTrace (prefixWord ++ tailWord_477525) baseStart_477525 baseEnd_477525 := by
    simpa [prefixWord, tailWord_477525, baseEnd_477525] using wordTrace_append hprefix tailTrace_477525
  have hstable : (prefixWord ++ tailWord_477525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477525).length < 2 ^ (prefixWord ++ tailWord_477525).sum := by decide
  have hdescent : baseEnd_477525 < baseStart_477525 := by decide
  rcases family_descends (prefixWord ++ tailWord_477525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477540 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_477540 : Nat := 118140960795 + 477540 * 2 ^ 59
def prefixEnd_477540 : Nat := 4983230072969 + 3 ^ 40 * 477540 * 2
def baseEnd_477540 : Nat := 54490567055148190278631

theorem tailTrace_477540 : CollatzResearch.WordTrace tailWord_477540 prefixEnd_477540 54490567055148190278631 := by
  unfold tailWord_477540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708657344980806091999037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11611543126641074789332049 8708657344980806091999037)
  ·
    refine ⟨3265746504367802284499639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8708657344980806091999037 3265746504367802284499639)
    ·
      refine ⟨4898619756551703426749459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265746504367802284499639 4898619756551703426749459)
      ·
        refine ⟨7347929634827555140124189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898619756551703426749459 7347929634827555140124189)
        ·
          refine ⟨2755473613060333177546571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7347929634827555140124189 2755473613060333177546571)
          ·
            refine ⟨4133210419590499766319857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755473613060333177546571 4133210419590499766319857)
            ·
              refine ⟨3099907814692874824739893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133210419590499766319857 3099907814692874824739893)
              ·
                refine ⟨290616357627457014819365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3099907814692874824739893 290616357627457014819365)
                ·
                  refine ⟨54490567055148190278631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290616357627457014819365 54490567055148190278631)
                  ·
                    rfl

theorem cell22_477540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_477540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477540 prefixEnd_477540 := by exact prefixLift 477540
  have htrace : WordTrace (prefixWord ++ tailWord_477540) baseStart_477540 baseEnd_477540 := by
    simpa [prefixWord, tailWord_477540, baseEnd_477540] using wordTrace_append hprefix tailTrace_477540
  have hstable : (prefixWord ++ tailWord_477540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477540).length < 2 ^ (prefixWord ++ tailWord_477540).sum := by decide
  have hdescent : baseEnd_477540 < baseStart_477540 := by decide
  rcases family_descends (prefixWord ++ tailWord_477540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477557 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 4]
def baseStart_477557 : Nat := 118140960795 + 477557 * 2 ^ 59
def prefixEnd_477557 : Nat := 4983230072969 + 3 ^ 40 * 477557 * 2
def baseEnd_477557 : Nat := 54492506870954064386947

theorem tailTrace_477557 : CollatzResearch.WordTrace tailWord_477557 prefixEnd_477557 54492506870954064386947 := by
  unfold tailWord_477557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417934730900024087366925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11611956487266682724911283 17417934730900024087366925)
  ·
    refine ⟨6531725524087509032762597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17417934730900024087366925 6531725524087509032762597)
    ·
      refine ⟨1224698535766407943642987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6531725524087509032762597 1224698535766407943642987)
      ·
        refine ⟨1837047803649611915464481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224698535766407943642987 1837047803649611915464481)
        ·
          refine ⟨1377785852737208936598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837047803649611915464481 1377785852737208936598361)
          ·
            refine ⟨1033339389552906702448771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377785852737208936598361 1033339389552906702448771)
            ·
              refine ⟨1550009084329360053673157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033339389552906702448771 1550009084329360053673157)
              ·
                refine ⟨290626703311755010063717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1550009084329360053673157 290626703311755010063717)
                ·
                  refine ⟨54492506870954064386947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290626703311755010063717 54492506870954064386947)
                  ·
                    rfl

theorem cell22_477557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_477557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477557 prefixEnd_477557 := by exact prefixLift 477557
  have htrace : WordTrace (prefixWord ++ tailWord_477557) baseStart_477557 baseEnd_477557 := by
    simpa [prefixWord, tailWord_477557, baseEnd_477557] using wordTrace_append hprefix tailTrace_477557
  have hstable : (prefixWord ++ tailWord_477557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477557).length < 2 ^ (prefixWord ++ tailWord_477557).sum := by decide
  have hdescent : baseEnd_477557 < baseStart_477557 := by decide
  rcases family_descends (prefixWord ++ tailWord_477557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477617 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_477617 : Nat := 118140960795 + 477617 * 2 ^ 59
def prefixEnd_477617 : Nat := 4983230072969 + 3 ^ 40 * 477617 * 2
def baseEnd_477617 : Nat := 163498059839042036660657

theorem tailTrace_477617 : CollatzResearch.WordTrace tailWord_477617 prefixEnd_477617 163498059839042036660657 := by
  unfold tailWord_477617
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420123110682654334551105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11613415407121769556367403 17420123110682654334551105)
  ·
    refine ⟨13065092333011990750913329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17420123110682654334551105 13065092333011990750913329)
    ·
      refine ⟨9798819249758993063184997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13065092333011990750913329 9798819249758993063184997)
      ·
        refine ⟨1837278609329811199347187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9798819249758993063184997 1837278609329811199347187)
        ·
          refine ⟨2755917913994716799020781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837278609329811199347187 2755917913994716799020781)
          ·
            refine ⟨1033469217748018799632793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2755917913994716799020781 1033469217748018799632793)
            ·
              refine ⟨775101913311014099724595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033469217748018799632793 775101913311014099724595)
              ·
                refine ⟨1162652869966521149586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775101913311014099724595 1162652869966521149586893)
                ·
                  refine ⟨435994826237445431095085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162652869966521149586893 435994826237445431095085)
                  ·
                    refine ⟨163498059839042036660657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435994826237445431095085 163498059839042036660657)
                    ·
                      rfl

theorem cell22_477617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_477617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477617 prefixEnd_477617 := by exact prefixLift 477617
  have htrace : WordTrace (prefixWord ++ tailWord_477617) baseStart_477617 baseEnd_477617 := by
    simpa [prefixWord, tailWord_477617, baseEnd_477617] using wordTrace_append hprefix tailTrace_477617
  have hstable : (prefixWord ++ tailWord_477617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477617).length < 2 ^ (prefixWord ++ tailWord_477617).sum := by decide
  have hdescent : baseEnd_477617 < baseStart_477617 := by decide
  rcases family_descends (prefixWord ++ tailWord_477617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477630 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_477630 : Nat := 118140960795 + 477630 * 2 ^ 59
def prefixEnd_477630 : Nat := 4983230072969 + 3 ^ 40 * 477630 * 2
def baseEnd_477630 : Nat := 54500836668238112028539

theorem tailTrace_477630 : CollatzResearch.WordTrace tailWord_477630 prefixEnd_477630 54500836668238112028539 := by
  unfold tailWord_477630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177574657454444694346793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11613731506423705036516229 2177574657454444694346793)
  ·
    refine ⟨1633180993090833520760095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2177574657454444694346793 1633180993090833520760095)
    ·
      refine ⟨2449771489636250281140143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633180993090833520760095 2449771489636250281140143)
      ·
        refine ⟨3674657234454375421710215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449771489636250281140143 3674657234454375421710215)
        ·
          refine ⟨5511985851681563132565323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674657234454375421710215 5511985851681563132565323)
          ·
            refine ⟨8267978777522344698847985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511985851681563132565323 8267978777522344698847985)
            ·
              refine ⟨6200984083141758524135989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267978777522344698847985 6200984083141758524135989)
              ·
                refine ⟨581342257794539861637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6200984083141758524135989 581342257794539861637749)
                ·
                  refine ⟨54500836668238112028539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581342257794539861637749 54500836668238112028539)
                  ·
                    rfl

theorem cell22_477630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_477630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477630 prefixEnd_477630 := by exact prefixLift 477630
  have htrace : WordTrace (prefixWord ++ tailWord_477630) baseStart_477630 baseEnd_477630 := by
    simpa [prefixWord, tailWord_477630, baseEnd_477630] using wordTrace_append hprefix tailTrace_477630
  have hstable : (prefixWord ++ tailWord_477630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477630).length < 2 ^ (prefixWord ++ tailWord_477630).sum := by decide
  have hdescent : baseEnd_477630 < baseStart_477630 := by decide
  rcases family_descends (prefixWord ++ tailWord_477630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477673 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_477673 : Nat := 118140960795 + 477673 * 2 ^ 59
def prefixEnd_477673 : Nat := 4983230072969 + 3 ^ 40 * 477673 * 2
def baseEnd_477673 : Nat := 163517229783476557260485

theorem tailTrace_477673 : CollatzResearch.WordTrace tailWord_477673 prefixEnd_477673 163517229783476557260485 := by
  unfold tailWord_477673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422165598479775898589673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11614777065653183932393115 17422165598479775898589673)
  ·
    refine ⟨13066624198859831923942255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17422165598479775898589673 13066624198859831923942255)
    ·
      refine ⟨19599936298289747885913383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13066624198859831923942255 19599936298289747885913383)
      ·
        refine ⟨29399904447434621828870075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19599936298289747885913383 29399904447434621828870075)
        ·
          refine ⟨44099856671151932743305113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399904447434621828870075 44099856671151932743305113)
          ·
            refine ⟨33074892503363949557478835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44099856671151932743305113 33074892503363949557478835)
            ·
              refine ⟨49612338755045924336218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33074892503363949557478835 49612338755045924336218253)
              ·
                refine ⟨18604627033142221626081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49612338755045924336218253 18604627033142221626081845)
                ·
                  refine ⟨1744183784357083277445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18604627033142221626081845 1744183784357083277445173)
                  ·
                    refine ⟨163517229783476557260485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1744183784357083277445173 163517229783476557260485)
                    ·
                      rfl

theorem cell22_477673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_477673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477673 prefixEnd_477673 := by exact prefixLift 477673
  have htrace : WordTrace (prefixWord ++ tailWord_477673) baseStart_477673 baseEnd_477673 := by
    simpa [prefixWord, tailWord_477673, baseEnd_477673] using wordTrace_append hprefix tailTrace_477673
  have hstable : (prefixWord ++ tailWord_477673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477673).length < 2 ^ (prefixWord ++ tailWord_477673).sum := by decide
  have hdescent : baseEnd_477673 < baseStart_477673 := by decide
  rcases family_descends (prefixWord ++ tailWord_477673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477690 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_477690 : Nat := 118140960795 + 477690 * 2 ^ 59
def prefixEnd_477690 : Nat := 4983230072969 + 3 ^ 40 * 477690 * 2
def baseEnd_477690 : Nat := 163523049230894179585433

theorem tailTrace_477690 : CollatzResearch.WordTrace tailWord_477690 prefixEnd_477690 163523049230894179585433 := by
  unfold tailWord_477690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355696409854546950489631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11615190426278791867972349 4355696409854546950489631)
  ·
    refine ⟨6533544614781820425734447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355696409854546950489631 6533544614781820425734447)
    ·
      refine ⟨9800316922172730638601671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533544614781820425734447 9800316922172730638601671)
      ·
        refine ⟨14700475383259095957902507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9800316922172730638601671 14700475383259095957902507)
        ·
          refine ⟨22050713074888643936853761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14700475383259095957902507 22050713074888643936853761)
          ·
            refine ⟨16538034806166482952640321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22050713074888643936853761 16538034806166482952640321)
            ·
              refine ⟨12403526104624862214480241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16538034806166482952640321 12403526104624862214480241)
              ·
                refine ⟨9302644578468646660860181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403526104624862214480241 9302644578468646660860181)
                ·
                  refine ⟨436061464615717812227821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9302644578468646660860181 436061464615717812227821)
                  ·
                    refine ⟨163523049230894179585433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436061464615717812227821 163523049230894179585433)
                    ·
                      rfl

theorem cell22_477690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_477690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477690 prefixEnd_477690 := by exact prefixLift 477690
  have htrace : WordTrace (prefixWord ++ tailWord_477690) baseStart_477690 baseEnd_477690 := by
    simpa [prefixWord, tailWord_477690, baseEnd_477690] using wordTrace_append hprefix tailTrace_477690
  have hstable : (prefixWord ++ tailWord_477690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477690).length < 2 ^ (prefixWord ++ tailWord_477690).sum := by decide
  have hdescent : baseEnd_477690 < baseStart_477690 := by decide
  rcases family_descends (prefixWord ++ tailWord_477690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477724 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_477724 : Nat := 118140960795 + 477724 * 2 ^ 59
def prefixEnd_477724 : Nat := 4983230072969 + 3 ^ 40 * 477724 * 2
def baseEnd_477724 : Nat := 163534688125729424235329

theorem tailTrace_477724 : CollatzResearch.WordTrace tailWord_477724 prefixEnd_477724 163534688125729424235329 := by
  unfold tailWord_477724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712012860647505804348113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616017147530007739130817 8712012860647505804348113)
  ·
    refine ⟨6534009645485629353261085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8712012860647505804348113 6534009645485629353261085)
    ·
      refine ⟨2450253617057111007472907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6534009645485629353261085 2450253617057111007472907)
      ·
        refine ⟨3675380425585666511209361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450253617057111007472907 3675380425585666511209361)
        ·
          refine ⟨2756535319189249883407021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675380425585666511209361 2756535319189249883407021)
          ·
            refine ⟨1033700744695968706277633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2756535319189249883407021 1033700744695968706277633)
            ·
              refine ⟨775275558521976529708225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033700744695968706277633 775275558521976529708225)
              ·
                refine ⟨581456668891482397281169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775275558521976529708225 581456668891482397281169)
                ·
                  refine ⟨436092501668611797960877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581456668891482397281169 436092501668611797960877)
                  ·
                    refine ⟨163534688125729424235329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436092501668611797960877 163534688125729424235329)
                    ·
                      rfl

theorem cell22_477724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_477724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477724 prefixEnd_477724 := by exact prefixLift 477724
  have htrace : WordTrace (prefixWord ++ tailWord_477724) baseStart_477724 baseEnd_477724 := by
    simpa [prefixWord, tailWord_477724, baseEnd_477724] using wordTrace_append hprefix tailTrace_477724
  have hstable : (prefixWord ++ tailWord_477724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477724).length < 2 ^ (prefixWord ++ tailWord_477724).sum := by decide
  have hdescent : baseEnd_477724 < baseStart_477724 := by decide
  rcases family_descends (prefixWord ++ tailWord_477724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477752 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_477752 : Nat := 118140960795 + 477752 * 2 ^ 59
def prefixEnd_477752 : Nat := 4983230072969 + 3 ^ 40 * 477752 * 2
def baseEnd_477752 : Nat := 163544273097946684535243

theorem tailTrace_477752 : CollatzResearch.WordTrace tailWord_477752 prefixEnd_477752 163544273097946684535243 := by
  unfold tailWord_477752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712523482596786195357755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616697976795714927143673 8712523482596786195357755)
  ·
    refine ⟨13068785223895179293036633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712523482596786195357755 13068785223895179293036633)
    ·
      refine ⟨9801588917921384469777475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13068785223895179293036633 9801588917921384469777475)
      ·
        refine ⟨14702383376882076704666213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801588917921384469777475 14702383376882076704666213)
        ·
          refine ⟨2756696883165389382124915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14702383376882076704666213 2756696883165389382124915)
          ·
            refine ⟨4135045324748084073187373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756696883165389382124915 4135045324748084073187373)
            ·
              refine ⟨1550641996780531527445265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135045324748084073187373 1550641996780531527445265)
              ·
                refine ⟨1162981497585398645583949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550641996780531527445265 1162981497585398645583949)
                ·
                  refine ⟨436118061594524492093981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162981497585398645583949 436118061594524492093981)
                  ·
                    refine ⟨163544273097946684535243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436118061594524492093981 163544273097946684535243)
                    ·
                      rfl

theorem cell22_477752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_477752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477752 prefixEnd_477752 := by exact prefixLift 477752
  have htrace : WordTrace (prefixWord ++ tailWord_477752) baseStart_477752 baseEnd_477752 := by
    simpa [prefixWord, tailWord_477752, baseEnd_477752] using wordTrace_append hprefix tailTrace_477752
  have hstable : (prefixWord ++ tailWord_477752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477752).length < 2 ^ (prefixWord ++ tailWord_477752).sum := by decide
  have hdescent : baseEnd_477752 < baseStart_477752 := by decide
  rcases family_descends (prefixWord ++ tailWord_477752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477844 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_477844 : Nat := 118140960795 + 477844 * 2 ^ 59
def prefixEnd_477844 : Nat := 4983230072969 + 3 ^ 40 * 477844 * 2
def baseEnd_477844 : Nat := 54525255526029703744987

theorem tailTrace_477844 : CollatzResearch.WordTrace tailWord_477844 prefixEnd_477844 54525255526029703744987 := by
  unfold tailWord_477844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714201240430136051532293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11618934987240181402043057 8714201240430136051532293)
  ·
    refine ⟨1633912732580650509662305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8714201240430136051532293 1633912732580650509662305)
    ·
      refine ⟨1225434549435487882246729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1633912732580650509662305 1225434549435487882246729)
      ·
        refine ⟨919075912076615911685047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225434549435487882246729 919075912076615911685047)
        ·
          refine ⟨1378613868114923867527571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919075912076615911685047 1378613868114923867527571)
          ·
            refine ⟨2067920802172385801291357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378613868114923867527571 2067920802172385801291357)
            ·
              refine ⟨775470300814644675484259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067920802172385801291357 775470300814644675484259)
              ·
                refine ⟨1163205451221967013226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775470300814644675484259 1163205451221967013226389)
                ·
                  refine ⟨54525255526029703744987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1163205451221967013226389 54525255526029703744987)
                  ·
                    rfl

theorem cell22_477844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_477844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477844 prefixEnd_477844 := by exact prefixLift 477844
  have htrace : WordTrace (prefixWord ++ tailWord_477844) baseStart_477844 baseEnd_477844 := by
    simpa [prefixWord, tailWord_477844, baseEnd_477844] using wordTrace_append hprefix tailTrace_477844
  have hstable : (prefixWord ++ tailWord_477844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477844).length < 2 ^ (prefixWord ++ tailWord_477844).sum := by decide
  have hdescent : baseEnd_477844 < baseStart_477844 := by decide
  rcases family_descends (prefixWord ++ tailWord_477844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477863 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 1, 4]
def baseStart_477863 : Nat := 118140960795 + 477863 * 2 ^ 59
def prefixEnd_477863 : Nat := 4983230072969 + 3 ^ 40 * 477863 * 2
def baseEnd_477863 : Nat := 163582270666379395009903

theorem tailTrace_477863 : CollatzResearch.WordTrace tailWord_477863 prefixEnd_477863 163582270666379395009903 := by
  unfold tailWord_477863
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429095467791438348006243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11619396978527625565337495 17429095467791438348006243)
  ·
    refine ⟨26143643201687157522009365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429095467791438348006243 26143643201687157522009365)
    ·
      refine ⟨1225483275079085508844189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26143643201687157522009365 1225483275079085508844189)
      ·
        refine ⟨459556228154657065816571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1225483275079085508844189 459556228154657065816571)
        ·
          refine ⟨689334342231985598724857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459556228154657065816571 689334342231985598724857)
          ·
            refine ⟨517000756673989199043643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689334342231985598724857 517000756673989199043643)
            ·
              refine ⟨775501135010983798565465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517000756673989199043643 775501135010983798565465)
              ·
                refine ⟨581625851258237848924099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775501135010983798565465 581625851258237848924099)
                ·
                  refine ⟨872438776887356773386149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581625851258237848924099 872438776887356773386149)
                  ·
                    refine ⟨163582270666379395009903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872438776887356773386149 163582270666379395009903)
                    ·
                      rfl

theorem cell22_477863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_477863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477863 prefixEnd_477863 := by exact prefixLift 477863
  have htrace : WordTrace (prefixWord ++ tailWord_477863) baseStart_477863 baseEnd_477863 := by
    simpa [prefixWord, tailWord_477863, baseEnd_477863] using wordTrace_append hprefix tailTrace_477863
  have hstable : (prefixWord ++ tailWord_477863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477863).length < 2 ^ (prefixWord ++ tailWord_477863).sum := by decide
  have hdescent : baseEnd_477863 < baseStart_477863 := by decide
  rcases family_descends (prefixWord ++ tailWord_477863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477889 : List Nat := [1, 2, 6, 2, 1, 10]
def baseStart_477889 : Nat := 118140960795 + 477889 * 2 ^ 59
def prefixEnd_477889 : Nat := 4983230072969 + 3 ^ 40 * 477889 * 2
def baseEnd_477889 : Nat := 2019644086391654245183

theorem tailTrace_477889 : CollatzResearch.WordTrace tailWord_477889 prefixEnd_477889 2019644086391654245183 := by
  unfold tailWord_477889
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430043765697244788452721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11620029177131496525635147 17430043765697244788452721)
  ·
    refine ⟨13072532824272933591339541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17430043765697244788452721 13072532824272933591339541)
    ·
      refine ⟨612774976137793762094041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13072532824272933591339541 612774976137793762094041)
      ·
        refine ⟨459581232103345321570531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612774976137793762094041 459581232103345321570531)
        ·
          refine ⟨689371848155017982355797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459581232103345321570531 689371848155017982355797)
          ·
            refine ⟨2019644086391654245183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 689371848155017982355797 2019644086391654245183)
            ·
              rfl

theorem cell22_477889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 10].length) (baseStart_477889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477889 prefixEnd_477889 := by exact prefixLift 477889
  have htrace : WordTrace (prefixWord ++ tailWord_477889) baseStart_477889 baseEnd_477889 := by
    simpa [prefixWord, tailWord_477889, baseEnd_477889] using wordTrace_append hprefix tailTrace_477889
  have hstable : (prefixWord ++ tailWord_477889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477889).length < 2 ^ (prefixWord ++ tailWord_477889).sum := by decide
  have hdescent : baseEnd_477889 < baseStart_477889 := by decide
  rcases family_descends (prefixWord ++ tailWord_477889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477902 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_477902 : Nat := 118140960795 + 477902 * 2 ^ 59
def prefixEnd_477902 : Nat := 4983230072969 + 3 ^ 40 * 477902 * 2
def baseEnd_477902 : Nat := 163595621163396293284783

theorem tailTrace_477902 : CollatzResearch.WordTrace tailWord_477902 prefixEnd_477902 163595621163396293284783 := by
  unfold tailWord_477902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178814739331268501084495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11620345276433432005783973 2178814739331268501084495)
  ·
    refine ⟨3268222108996902751626743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178814739331268501084495 3268222108996902751626743)
    ·
      refine ⟨4902333163495354127440115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268222108996902751626743 4902333163495354127440115)
      ·
        refine ⟨7353499745243031191160173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902333163495354127440115 7353499745243031191160173)
        ·
          refine ⟨2757562404466136696685065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7353499745243031191160173 2757562404466136696685065)
          ·
            refine ⟨2068171803349602522513799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2757562404466136696685065 2068171803349602522513799)
            ·
              refine ⟨3102257705024403783770699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068171803349602522513799 3102257705024403783770699)
              ·
                refine ⟨4653386557536605675656049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102257705024403783770699 4653386557536605675656049)
                ·
                  refine ⟨3490039918152454256742037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653386557536605675656049 3490039918152454256742037)
                  ·
                    refine ⟨163595621163396293284783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3490039918152454256742037 163595621163396293284783)
                    ·
                      rfl

theorem cell22_477902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_477902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477902 prefixEnd_477902 := by exact prefixLift 477902
  have htrace : WordTrace (prefixWord ++ tailWord_477902) baseStart_477902 baseEnd_477902 := by
    simpa [prefixWord, tailWord_477902, baseEnd_477902] using wordTrace_append hprefix tailTrace_477902
  have hstable : (prefixWord ++ tailWord_477902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477902).length < 2 ^ (prefixWord ++ tailWord_477902).sum := by decide
  have hdescent : baseEnd_477902 < baseStart_477902 := by decide
  rcases family_descends (prefixWord ++ tailWord_477902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477906 : List Nat := [3, 2, 2, 2, 4, 1, 1, 7]
def baseStart_477906 : Nat := 118140960795 + 477906 * 2 ^ 59
def prefixEnd_477906 : Nat := 4983230072969 + 3 ^ 40 * 477906 * 2
def baseEnd_477906 : Nat := 18177443382793512909419

theorem tailTrace_477906 : CollatzResearch.WordTrace tailWord_477906 prefixEnd_477906 18177443382793512909419 := by
  unfold tailWord_477906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357665951658914172955393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11620442537757104461214381 4357665951658914172955393)
  ·
    refine ⟨3268249463744185629716545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4357665951658914172955393 3268249463744185629716545)
    ·
      refine ⟨2451187097808139222287409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268249463744185629716545 2451187097808139222287409)
      ·
        refine ⟨1838390323356104416715557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2451187097808139222287409 1838390323356104416715557)
        ·
          refine ⟨344698185629269578134167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1838390323356104416715557 344698185629269578134167)
          ·
            refine ⟨517047278443904367201251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344698185629269578134167 517047278443904367201251)
            ·
              refine ⟨775570917665856550801877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517047278443904367201251 775570917665856550801877)
              ·
                refine ⟨18177443382793512909419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 775570917665856550801877 18177443382793512909419)
                ·
                  rfl

theorem cell22_477906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_477906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477906 prefixEnd_477906 := by exact prefixLift 477906
  have htrace : WordTrace (prefixWord ++ tailWord_477906) baseStart_477906 baseEnd_477906 := by
    simpa [prefixWord, tailWord_477906, baseEnd_477906] using wordTrace_append hprefix tailTrace_477906
  have hstable : (prefixWord ++ tailWord_477906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477906).length < 2 ^ (prefixWord ++ tailWord_477906).sum := by decide
  have hdescent : baseEnd_477906 < baseStart_477906 := by decide
  rcases family_descends (prefixWord ++ tailWord_477906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477938 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_477938 : Nat := 118140960795 + 477938 * 2 ^ 59
def prefixEnd_477938 : Nat := 4983230072969 + 3 ^ 40 * 477938 * 2
def baseEnd_477938 : Nat := 163607944699104199384673

theorem tailTrace_477938 : CollatzResearch.WordTrace tailWord_477938 prefixEnd_477938 163607944699104199384673 := by
  unfold tailWord_477938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357957735629931539246617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11621220628346484104657645 4357957735629931539246617)
  ·
    refine ⟨3268468301722448654434963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4357957735629931539246617 3268468301722448654434963)
    ·
      refine ⟨4902702452583672981652445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268468301722448654434963 4902702452583672981652445)
      ·
        refine ⟨1838513419718877368119667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4902702452583672981652445 1838513419718877368119667)
        ·
          refine ⟨2757770129578316052179501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838513419718877368119667 2757770129578316052179501)
          ·
            refine ⟨1034163798591868519567313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2757770129578316052179501 1034163798591868519567313)
            ·
              refine ⟨775622848943901389675485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034163798591868519567313 775622848943901389675485)
              ·
                refine ⟨290858568353963021128307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775622848943901389675485 290858568353963021128307)
                ·
                  refine ⟨436287852530944531692461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290858568353963021128307 436287852530944531692461)
                  ·
                    refine ⟨163607944699104199384673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436287852530944531692461 163607944699104199384673)
                    ·
                      rfl

theorem cell22_477938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_477938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477938 prefixEnd_477938 := by exact prefixLift 477938
  have htrace : WordTrace (prefixWord ++ tailWord_477938) baseStart_477938 baseEnd_477938 := by
    simpa [prefixWord, tailWord_477938, baseEnd_477938] using wordTrace_append hprefix tailTrace_477938
  have hstable : (prefixWord ++ tailWord_477938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477938).length < 2 ^ (prefixWord ++ tailWord_477938).sum := by decide
  have hdescent : baseEnd_477938 < baseStart_477938 := by decide
  rcases family_descends (prefixWord ++ tailWord_477938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477977 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_477977 : Nat := 118140960795 + 477977 * 2 ^ 59
def prefixEnd_477977 : Nat := 4983230072969 + 3 ^ 40 * 477977 * 2
def baseEnd_477977 : Nat := 163621295196121097659553

theorem tailTrace_477977 : CollatzResearch.WordTrace tailWord_477977 prefixEnd_477977 163621295196121097659553 := by
  unfold tailWord_477977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433253389378435817656185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11622168926252290545104123 17433253389378435817656185)
  ·
    refine ⟨13074940042033826863242139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17433253389378435817656185 13074940042033826863242139)
    ·
      refine ⟨19612410063050740294863209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074940042033826863242139 19612410063050740294863209)
      ·
        refine ⟨14709307547288055221147407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19612410063050740294863209 14709307547288055221147407)
        ·
          refine ⟨22063961320932082831721111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14709307547288055221147407 22063961320932082831721111)
          ·
            refine ⟨33095941981398124247581667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063961320932082831721111 33095941981398124247581667)
            ·
              refine ⟨49643912972097186371372501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33095941981398124247581667 49643912972097186371372501)
              ·
                refine ⟨1163529210283527805579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49643912972097186371372501 1163529210283527805579043)
                ·
                  refine ⟨1745293815425291708368565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163529210283527805579043 1745293815425291708368565)
                  ·
                    refine ⟨163621295196121097659553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1745293815425291708368565 163621295196121097659553)
                    ·
                      rfl

theorem cell22_477977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_477977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_477977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_477977 prefixEnd_477977 := by exact prefixLift 477977
  have htrace : WordTrace (prefixWord ++ tailWord_477977) baseStart_477977 baseEnd_477977 := by
    simpa [prefixWord, tailWord_477977, baseEnd_477977] using wordTrace_append hprefix tailTrace_477977
  have hstable : (prefixWord ++ tailWord_477977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477977).length < 2 ^ (prefixWord ++ tailWord_477977).sum := by decide
  have hdescent : baseEnd_477977 < baseStart_477977 := by decide
  rcases family_descends (prefixWord ++ tailWord_477977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478013 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 6]
def baseStart_478013 : Nat := 118140960795 + 478013 * 2 ^ 59
def prefixEnd_478013 : Nat := 4983230072969 + 3 ^ 40 * 478013 * 2
def baseEnd_478013 : Nat := 54544539577276334586481

theorem tailTrace_478013 : CollatzResearch.WordTrace tailWord_478013 prefixEnd_478013 54544539577276334586481 := by
  unfold tailWord_478013
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434566417248013965966693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11623044278165342643977795 17434566417248013965966693)
  ·
    refine ⟨3268981203234002618618755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17434566417248013965966693 3268981203234002618618755)
    ·
      refine ⟨4903471804851003927928133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268981203234002618618755 4903471804851003927928133)
      ·
        refine ⟨919400963409563236486525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4903471804851003927928133 919400963409563236486525)
        ·
          refine ⟨344775361278586213682447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 919400963409563236486525 344775361278586213682447)
          ·
            refine ⟨517163041917879320523671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344775361278586213682447 517163041917879320523671)
            ·
              refine ⟨775744562876818980785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517163041917879320523671 775744562876818980785507)
              ·
                refine ⟨1163616844315228471178261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775744562876818980785507 1163616844315228471178261)
                ·
                  refine ⟨54544539577276334586481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1163616844315228471178261 54544539577276334586481)
                  ·
                    rfl

theorem cell22_478013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_478013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478013 prefixEnd_478013 := by exact prefixLift 478013
  have htrace : WordTrace (prefixWord ++ tailWord_478013) baseStart_478013 baseEnd_478013 := by
    simpa [prefixWord, tailWord_478013, baseEnd_478013] using wordTrace_append hprefix tailTrace_478013
  have hstable : (prefixWord ++ tailWord_478013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478013).length < 2 ^ (prefixWord ++ tailWord_478013).sum := by decide
  have hdescent : baseEnd_478013 < baseStart_478013 := by decide
  rcases family_descends (prefixWord ++ tailWord_478013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478028 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_478028 : Nat := 118140960795 + 478028 * 2 ^ 59
def prefixEnd_478028 : Nat := 4983230072969 + 3 ^ 40 * 478028 * 2
def baseEnd_478028 : Nat := 163638753538373964634397

theorem tailTrace_478028 : CollatzResearch.WordTrace tailWord_478028 prefixEnd_478028 163638753538373964634397 := by
  unfold tailWord_478028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717556756096835763881369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11623409008129114351841825 8717556756096835763881369)
  ·
    refine ⟨6538167567072626822911027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8717556756096835763881369 6538167567072626822911027)
    ·
      refine ⟨9807251350608940234366541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538167567072626822911027 9807251350608940234366541)
      ·
        refine ⟨3677719256478352587887453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9807251350608940234366541 3677719256478352587887453)
        ·
          refine ⟨1379144721179382220457795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3677719256478352587887453 1379144721179382220457795)
          ·
            refine ⟨2068717081769073330686693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379144721179382220457795 2068717081769073330686693)
            ·
              refine ⟨387884452831701249503755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2068717081769073330686693 387884452831701249503755)
              ·
                refine ⟨581826679247551874255633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387884452831701249503755 581826679247551874255633)
                ·
                  refine ⟨436370009435663905691725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581826679247551874255633 436370009435663905691725)
                  ·
                    refine ⟨163638753538373964634397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436370009435663905691725 163638753538373964634397)
                    ·
                      rfl

theorem cell22_478028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_478028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478028 prefixEnd_478028 := by exact prefixLift 478028
  have htrace : WordTrace (prefixWord ++ tailWord_478028) baseStart_478028 baseEnd_478028 := by
    simpa [prefixWord, tailWord_478028, baseEnd_478028] using wordTrace_append hprefix tailTrace_478028
  have hstable : (prefixWord ++ tailWord_478028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478028).length < 2 ^ (prefixWord ++ tailWord_478028).sum := by decide
  have hdescent : baseEnd_478028 < baseStart_478028 := by decide
  rcases family_descends (prefixWord ++ tailWord_478028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478073 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_478073 : Nat := 118140960795 + 478073 * 2 ^ 59
def prefixEnd_478073 : Nat := 4983230072969 + 3 ^ 40 * 478073 * 2
def baseEnd_478073 : Nat := 163654157958008847259259

theorem tailTrace_478073 : CollatzResearch.WordTrace tailWord_478073 prefixEnd_478073 163654157958008847259259 := by
  unfold tailWord_478073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436754797030644213150873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11624503198020429475433915 17436754797030644213150873)
  ·
    refine ⟨13077566097772983159863155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17436754797030644213150873 13077566097772983159863155)
    ·
      refine ⟨19616349146659474739794733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077566097772983159863155 19616349146659474739794733)
      ·
        refine ⟨7356130929997303027423025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19616349146659474739794733 7356130929997303027423025)
        ·
          refine ⟨5517098197497977270567269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356130929997303027423025 5517098197497977270567269)
          ·
            refine ⟨1034455912030870738231363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5517098197497977270567269 1034455912030870738231363)
            ·
              refine ⟨1551683868046306107347045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034455912030870738231363 1551683868046306107347045)
              ·
                refine ⟨290940725258682395127571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1551683868046306107347045 290940725258682395127571)
                ·
                  refine ⟨436411087888023592691357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290940725258682395127571 436411087888023592691357)
                  ·
                    refine ⟨163654157958008847259259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436411087888023592691357 163654157958008847259259)
                    ·
                      rfl

theorem cell22_478073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_478073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478073 prefixEnd_478073 := by exact prefixLift 478073
  have htrace : WordTrace (prefixWord ++ tailWord_478073) baseStart_478073 baseEnd_478073 := by
    simpa [prefixWord, tailWord_478073, baseEnd_478073] using wordTrace_append hprefix tailTrace_478073
  have hstable : (prefixWord ++ tailWord_478073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478073).length < 2 ^ (prefixWord ++ tailWord_478073).sum := by decide
  have hdescent : baseEnd_478073 < baseStart_478073 := by decide
  rcases family_descends (prefixWord ++ tailWord_478073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478116 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_478116 : Nat := 118140960795 + 478116 * 2 ^ 59
def prefixEnd_478116 : Nat := 4983230072969 + 3 ^ 40 * 478116 * 2
def baseEnd_478116 : Nat := 163668877736771068434127

theorem tailTrace_478116 : CollatzResearch.WordTrace tailWord_478116 prefixEnd_478116 163668877736771068434127 := by
  unfold tailWord_478116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719161567937431278483101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11625548757249908371310801 8719161567937431278483101)
  ·
    refine ⟨3269685587976536729431163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8719161567937431278483101 3269685587976536729431163)
    ·
      refine ⟨4904528381964805094146745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269685587976536729431163 4904528381964805094146745)
      ·
        refine ⟨3678396286473603820610059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904528381964805094146745 3678396286473603820610059)
        ·
          refine ⟨5517594429710405730915089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678396286473603820610059 5517594429710405730915089)
          ·
            refine ⟨4138195822282804298186317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517594429710405730915089 4138195822282804298186317)
            ·
              refine ⟨1551823433356051611819869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4138195822282804298186317 1551823433356051611819869)
              ·
                refine ⟨581933787508519354432451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1551823433356051611819869 581933787508519354432451)
                ·
                  refine ⟨872900681262779031648677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581933787508519354432451 872900681262779031648677)
                  ·
                    refine ⟨163668877736771068434127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872900681262779031648677 163668877736771068434127)
                    ·
                      rfl

theorem cell22_478116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_478116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478116 prefixEnd_478116 := by exact prefixLift 478116
  have htrace : WordTrace (prefixWord ++ tailWord_478116) baseStart_478116 baseEnd_478116 := by
    simpa [prefixWord, tailWord_478116, baseEnd_478116] using wordTrace_append hprefix tailTrace_478116
  have hstable : (prefixWord ++ tailWord_478116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478116).length < 2 ^ (prefixWord ++ tailWord_478116).sum := by decide
  have hdescent : baseEnd_478116 < baseStart_478116 := by decide
  rcases family_descends (prefixWord ++ tailWord_478116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478144 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_478144 : Nat := 118140960795 + 478144 * 2 ^ 59
def prefixEnd_478144 : Nat := 4983230072969 + 3 ^ 40 * 478144 * 2
def baseEnd_478144 : Nat := 163678462708988328734041

theorem tailTrace_478144 : CollatzResearch.WordTrace tailWord_478144 prefixEnd_478144 163678462708988328734041 := by
  unfold tailWord_478144
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719672189886711669492743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11626229586515615559323657 8719672189886711669492743)
  ·
    refine ⟨13079508284830067504239115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8719672189886711669492743 13079508284830067504239115)
    ·
      refine ⟨19619262427245101256358673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13079508284830067504239115 19619262427245101256358673)
      ·
        refine ⟨14714446820433825942269005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619262427245101256358673 14714446820433825942269005)
        ·
          refine ⟨5517917557662684728350877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14714446820433825942269005 5517917557662684728350877)
          ·
            refine ⟨2069219084123506773131579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5517917557662684728350877 2069219084123506773131579)
            ·
              refine ⟨3103828626185260159697369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069219084123506773131579 3103828626185260159697369)
              ·
                refine ⟨2327871469638945119773027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103828626185260159697369 2327871469638945119773027)
                ·
                  refine ⟨3491807204458417679659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327871469638945119773027 3491807204458417679659541)
                  ·
                    refine ⟨163678462708988328734041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3491807204458417679659541 163678462708988328734041)
                    ·
                      rfl

theorem cell22_478144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_478144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478144 prefixEnd_478144 := by exact prefixLift 478144
  have htrace : WordTrace (prefixWord ++ tailWord_478144) baseStart_478144 baseEnd_478144 := by
    simpa [prefixWord, tailWord_478144, baseEnd_478144] using wordTrace_append hprefix tailTrace_478144
  have hstable : (prefixWord ++ tailWord_478144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478144).length < 2 ^ (prefixWord ++ tailWord_478144).sum := by decide
  have hdescent : baseEnd_478144 < baseStart_478144 := by decide
  rcases family_descends (prefixWord ++ tailWord_478144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478159 : List Nat := [1, 1, 2, 1, 1, 7, 1, 8]
def baseStart_478159 : Nat := 118140960795 + 478159 * 2 ^ 59
def prefixEnd_478159 : Nat := 4983230072969 + 3 ^ 40 * 478159 * 2
def baseEnd_478159 : Nat := 18187066390614809956555

theorem tailTrace_478159 : CollatzResearch.WordTrace tailWord_478159 prefixEnd_478159 18187066390614809956555 := by
  unfold tailWord_478159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439891474719080900781531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11626594316479387267187687 17439891474719080900781531)
  ·
    refine ⟨26159837212078621351172297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17439891474719080900781531 26159837212078621351172297)
    ·
      refine ⟨19619877909058966013379223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26159837212078621351172297 19619877909058966013379223)
      ·
        refine ⟨29429816863588449020068835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19619877909058966013379223 29429816863588449020068835)
        ·
          refine ⟨44144725295382673530103253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429816863588449020068835 44144725295382673530103253)
          ·
            refine ⟨1034641999110531410861795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44144725295382673530103253 1034641999110531410861795)
            ·
              refine ⟨1551962998665797116292693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034641999110531410861795 1551962998665797116292693)
              ·
                refine ⟨18187066390614809956555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1551962998665797116292693 18187066390614809956555)
                ·
                  rfl

theorem cell22_478159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 8].length) (baseStart_478159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478159 prefixEnd_478159 := by exact prefixLift 478159
  have htrace : WordTrace (prefixWord ++ tailWord_478159) baseStart_478159 baseEnd_478159 := by
    simpa [prefixWord, tailWord_478159, baseEnd_478159] using wordTrace_append hprefix tailTrace_478159
  have hstable : (prefixWord ++ tailWord_478159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478159).length < 2 ^ (prefixWord ++ tailWord_478159).sum := by decide
  have hdescent : baseEnd_478159 < baseStart_478159 := by decide
  rcases family_descends (prefixWord ++ tailWord_478159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478165 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 4]
def baseStart_478165 : Nat := 118140960795 + 478165 * 2 ^ 59
def prefixEnd_478165 : Nat := 4983230072969 + 3 ^ 40 * 478165 * 2
def baseEnd_478165 : Nat := 54561883812717091319659

theorem tailTrace_478165 : CollatzResearch.WordTrace tailWord_478165 prefixEnd_478165 54561883812717091319659 := by
  unfold tailWord_478165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440110312697343925499949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11626740208464895950333299 17440110312697343925499949)
  ·
    refine ⟨6540041367261503972062481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17440110312697343925499949 6540041367261503972062481)
    ·
      refine ⟨4905031025446127979046861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6540041367261503972062481 4905031025446127979046861)
      ·
        refine ⟨1839386634542297992142573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4905031025446127979046861 1839386634542297992142573)
        ·
          refine ⟨689769987953361747053465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1839386634542297992142573 689769987953361747053465)
          ·
            refine ⟨517327490965021310290099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689769987953361747053465 517327490965021310290099)
            ·
              refine ⟨775991236447531965435149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517327490965021310290099 775991236447531965435149)
              ·
                refine ⟨290996713667824487038181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775991236447531965435149 290996713667824487038181)
                ·
                  refine ⟨54561883812717091319659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290996713667824487038181 54561883812717091319659)
                  ·
                    rfl

theorem cell22_478165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_478165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478165 prefixEnd_478165 := by exact prefixLift 478165
  have htrace : WordTrace (prefixWord ++ tailWord_478165) baseStart_478165 baseEnd_478165 := by
    simpa [prefixWord, tailWord_478165, baseEnd_478165] using wordTrace_append hprefix tailTrace_478165
  have hstable : (prefixWord ++ tailWord_478165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478165).length < 2 ^ (prefixWord ++ tailWord_478165).sum := by decide
  have hdescent : baseEnd_478165 < baseStart_478165 := by decide
  rcases family_descends (prefixWord ++ tailWord_478165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478178 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_478178 : Nat := 118140960795 + 478178 * 2 ^ 59
def prefixEnd_478178 : Nat := 4983230072969 + 3 ^ 40 * 478178 * 2
def baseEnd_478178 : Nat := 163690101603823573383937

theorem tailTrace_478178 : CollatzResearch.WordTrace tailWord_478178 prefixEnd_478178 163690101603823573383937 := by
  unfold tailWord_478178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360146115412561786430797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11627056307766831430482125 4360146115412561786430797)
  ·
    refine ⟨1635054793279710669911549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4360146115412561786430797 1635054793279710669911549)
    ·
      refine ⟨613145547479891501216831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1635054793279710669911549 613145547479891501216831)
      ·
        refine ⟨919718321219837251825247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613145547479891501216831 919718321219837251825247)
        ·
          refine ⟨1379577481829755877737871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919718321219837251825247 1379577481829755877737871)
          ·
            refine ⟨2069366222744633816606807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379577481829755877737871 2069366222744633816606807)
            ·
              refine ⟨3104049334116950724910211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069366222744633816606807 3104049334116950724910211)
              ·
                refine ⟨4656074001175426087365317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104049334116950724910211 4656074001175426087365317)
                ·
                  refine ⟨873013875220392391380997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4656074001175426087365317 873013875220392391380997)
                  ·
                    refine ⟨163690101603823573383937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873013875220392391380997 163690101603823573383937)
                    ·
                      rfl

theorem cell22_478178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_478178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478178 prefixEnd_478178 := by exact prefixLift 478178
  have htrace : WordTrace (prefixWord ++ tailWord_478178) baseStart_478178 baseEnd_478178 := by
    simpa [prefixWord, tailWord_478178, baseEnd_478178] using wordTrace_append hprefix tailTrace_478178
  have hstable : (prefixWord ++ tailWord_478178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478178).length < 2 ^ (prefixWord ++ tailWord_478178).sum := by decide
  have hdescent : baseEnd_478178 < baseStart_478178 := by decide
  rcases family_descends (prefixWord ++ tailWord_478178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478197 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_478197 : Nat := 118140960795 + 478197 * 2 ^ 59
def prefixEnd_478197 : Nat := 4983230072969 + 3 ^ 40 * 478197 * 2
def baseEnd_478197 : Nat := 163696605692113857158879

theorem tailTrace_478197 : CollatzResearch.WordTrace tailWord_478197 prefixEnd_478197 163696605692113857158879 := by
  unfold tailWord_478197
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441277448581413390664845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11627518299054275593776563 17441277448581413390664845)
  ·
    refine ⟨6540479043218030021499317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17441277448581413390664845 6540479043218030021499317)
    ·
      refine ⟨613169910301690314515561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6540479043218030021499317 613169910301690314515561)
      ·
        refine ⟨459877432726267735886671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613169910301690314515561 459877432726267735886671)
        ·
          refine ⟨689816149089401603830007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459877432726267735886671 689816149089401603830007)
          ·
            refine ⟨1034724223634102405745011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689816149089401603830007 1034724223634102405745011)
            ·
              refine ⟨1552086335451153608617517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034724223634102405745011 1552086335451153608617517)
              ·
                refine ⟨582032375794182603231569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552086335451153608617517 582032375794182603231569)
                ·
                  refine ⟨436524281845636952423677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582032375794182603231569 436524281845636952423677)
                  ·
                    refine ⟨163696605692113857158879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436524281845636952423677 163696605692113857158879)
                    ·
                      rfl

theorem cell22_478197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_478197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478197 prefixEnd_478197 := by exact prefixLift 478197
  have htrace : WordTrace (prefixWord ++ tailWord_478197) baseStart_478197 baseEnd_478197 := by
    simpa [prefixWord, tailWord_478197, baseEnd_478197] using wordTrace_append hprefix tailTrace_478197
  have hstable : (prefixWord ++ tailWord_478197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478197).length < 2 ^ (prefixWord ++ tailWord_478197).sum := by decide
  have hdescent : baseEnd_478197 < baseStart_478197 := by decide
  rcases family_descends (prefixWord ++ tailWord_478197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478242 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_478242 : Nat := 118140960795 + 478242 * 2 ^ 59
def prefixEnd_478242 : Nat := 4983230072969 + 3 ^ 40 * 478242 * 2
def baseEnd_478242 : Nat := 163712010111748739783741

theorem tailTrace_478242 : CollatzResearch.WordTrace tailWord_478242 prefixEnd_478242 163712010111748739783741 := by
  unfold tailWord_478242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360729683354596519013245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11628612488945590717368653 4360729683354596519013245)
  ·
    refine ⟨1635273631257973694629967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4360729683354596519013245 1635273631257973694629967)
    ·
      refine ⟨2452910446886960541944951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635273631257973694629967 2452910446886960541944951)
      ·
        refine ⟨3679365670330440812917427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452910446886960541944951 3679365670330440812917427)
        ·
          refine ⟨5519048505495661219376141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679365670330440812917427 5519048505495661219376141)
          ·
            refine ⟨2069643189560872957266053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5519048505495661219376141 2069643189560872957266053)
            ·
              refine ⟨388058098042663679487385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2069643189560872957266053 388058098042663679487385)
              ·
                refine ⟨291043573531997759615539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388058098042663679487385 291043573531997759615539)
                ·
                  refine ⟨436565360297996639423309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291043573531997759615539 436565360297996639423309)
                  ·
                    refine ⟨163712010111748739783741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436565360297996639423309 163712010111748739783741)
                    ·
                      rfl

theorem cell22_478242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_478242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478242 prefixEnd_478242 := by exact prefixLift 478242
  have htrace : WordTrace (prefixWord ++ tailWord_478242) baseStart_478242 baseEnd_478242 := by
    simpa [prefixWord, tailWord_478242, baseEnd_478242] using wordTrace_append hprefix tailTrace_478242
  have hstable : (prefixWord ++ tailWord_478242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478242).length < 2 ^ (prefixWord ++ tailWord_478242).sum := by decide
  have hdescent : baseEnd_478242 < baseStart_478242 := by decide
  rcases family_descends (prefixWord ++ tailWord_478242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478285 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_478285 : Nat := 118140960795 + 478285 * 2 ^ 59
def prefixEnd_478285 : Nat := 4983230072969 + 3 ^ 40 * 478285 * 2
def baseEnd_478285 : Nat := 163726729890510960958609

theorem tailTrace_478285 : CollatzResearch.WordTrace tailWord_478285 prefixEnd_478285 163726729890510960958609 := by
  unfold tailWord_478285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444487072262604419868309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11629658048175069613245539 17444487072262604419868309)
  ·
    refine ⟨817710331512309582181327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17444487072262604419868309 817710331512309582181327)
    ·
      refine ⟨1226565497268464373271991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817710331512309582181327 1226565497268464373271991)
      ·
        refine ⟨1839848245902696559907987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226565497268464373271991 1839848245902696559907987)
        ·
          refine ⟨2759772368854044839861981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839848245902696559907987 2759772368854044839861981)
          ·
            refine ⟨1034914638320266814948243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2759772368854044839861981 1034914638320266814948243)
            ·
              refine ⟨1552371957480400222422365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034914638320266814948243 1552371957480400222422365)
              ·
                refine ⟨582139484055150083408387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552371957480400222422365 582139484055150083408387)
                ·
                  refine ⟨873209226082725125112581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582139484055150083408387 873209226082725125112581)
                  ·
                    refine ⟨163726729890510960958609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873209226082725125112581 163726729890510960958609)
                    ·
                      rfl

theorem cell22_478285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_478285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478285 prefixEnd_478285 := by exact prefixLift 478285
  have htrace : WordTrace (prefixWord ++ tailWord_478285) baseStart_478285 baseEnd_478285 := by
    simpa [prefixWord, tailWord_478285, baseEnd_478285] using wordTrace_append hprefix tailTrace_478285
  have hstable : (prefixWord ++ tailWord_478285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478285).length < 2 ^ (prefixWord ++ tailWord_478285).sum := by decide
  have hdescent : baseEnd_478285 < baseStart_478285 := by decide
  rcases family_descends (prefixWord ++ tailWord_478285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478296 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_478296 : Nat := 118140960795 + 478296 * 2 ^ 59
def prefixEnd_478296 : Nat := 4983230072969 + 3 ^ 40 * 478296 * 2
def baseEnd_478296 : Nat := 163730495415310598933575

theorem tailTrace_478296 : CollatzResearch.WordTrace tailWord_478296 prefixEnd_478296 163730495415310598933575 := by
  unfold tailWord_478296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722444137611376649259371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11629925516815168865679161 8722444137611376649259371)
  ·
    refine ⟨13083666206417064973889057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8722444137611376649259371 13083666206417064973889057)
    ·
      refine ⟨9812749654812798730416793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13083666206417064973889057 9812749654812798730416793)
      ·
        refine ⟨7359562241109599047812595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812749654812798730416793 7359562241109599047812595)
        ·
          refine ⟨11039343361664398571718893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359562241109599047812595 11039343361664398571718893)
          ·
            refine ⟨4139753760624149464394585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039343361664398571718893 4139753760624149464394585)
            ·
              refine ⟨3104815320468112098295939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139753760624149464394585 3104815320468112098295939)
              ·
                refine ⟨4657222980702168147443909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104815320468112098295939 4657222980702168147443909)
                ·
                  refine ⟨873229308881656527645733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4657222980702168147443909 873229308881656527645733)
                  ·
                    refine ⟨163730495415310598933575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873229308881656527645733 163730495415310598933575)
                    ·
                      rfl

theorem cell22_478296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_478296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478296 prefixEnd_478296 := by exact prefixLift 478296
  have htrace : WordTrace (prefixWord ++ tailWord_478296) baseStart_478296 baseEnd_478296 := by
    simpa [prefixWord, tailWord_478296, baseEnd_478296] using wordTrace_append hprefix tailTrace_478296
  have hstable : (prefixWord ++ tailWord_478296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478296).length < 2 ^ (prefixWord ++ tailWord_478296).sum := by decide
  have hdescent : baseEnd_478296 < baseStart_478296 := by decide
  rcases family_descends (prefixWord ++ tailWord_478296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478298 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_478298 : Nat := 118140960795 + 478298 * 2 ^ 59
def prefixEnd_478298 : Nat := 4983230072969 + 3 ^ 40 * 478298 * 2
def baseEnd_478298 : Nat := 163731180056183260383569

theorem tailTrace_478298 : CollatzResearch.WordTrace tailWord_478298 prefixEnd_478298 163731180056183260383569 := by
  unfold tailWord_478298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361240305303876910022887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11629974147477005093394365 4361240305303876910022887)
  ·
    refine ⟨6541860457955815365034331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361240305303876910022887 6541860457955815365034331)
    ·
      refine ⟨9812790686933723047551497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6541860457955815365034331 9812790686933723047551497)
      ·
        refine ⟨7359593015200292285663623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812790686933723047551497 7359593015200292285663623)
        ·
          refine ⟨11039389522800438428495435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359593015200292285663623 11039389522800438428495435)
          ·
            refine ⟨16559084284200657642743153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039389522800438428495435 16559084284200657642743153)
            ·
              refine ⟨12419313213150493232057365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16559084284200657642743153 12419313213150493232057365)
              ·
                refine ⟨582155306866429370252689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12419313213150493232057365 582155306866429370252689)
                ·
                  refine ⟨436616480149822027689517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582155306866429370252689 436616480149822027689517)
                  ·
                    refine ⟨163731180056183260383569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436616480149822027689517 163731180056183260383569)
                    ·
                      rfl

theorem cell22_478298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_478298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478298 prefixEnd_478298 := by exact prefixLift 478298
  have htrace : WordTrace (prefixWord ++ tailWord_478298) baseStart_478298 baseEnd_478298 := by
    simpa [prefixWord, tailWord_478298, baseEnd_478298] using wordTrace_append hprefix tailTrace_478298
  have hstable : (prefixWord ++ tailWord_478298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478298).length < 2 ^ (prefixWord ++ tailWord_478298).sum := by decide
  have hdescent : baseEnd_478298 < baseStart_478298 := by decide
  rcases family_descends (prefixWord ++ tailWord_478298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478360 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_478360 : Nat := 118140960795 + 478360 * 2 ^ 59
def prefixEnd_478360 : Nat := 4983230072969 + 3 ^ 40 * 478360 * 2
def baseEnd_478360 : Nat := 163752403923235765333379

theorem tailTrace_478360 : CollatzResearch.WordTrace tailWord_478360 prefixEnd_478360 163752403923235765333379 := by
  unfold tailWord_478360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723611273495446114424267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11631481697993928152565689 8723611273495446114424267)
  ·
    refine ⟨13085416910243169171636401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8723611273495446114424267 13085416910243169171636401)
    ·
      refine ⟨9814062682682376878727301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13085416910243169171636401 9814062682682376878727301)
      ·
        refine ⟨1840136753002945664761369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9814062682682376878727301 1840136753002945664761369)
        ·
          refine ⟨1380102564752209248571027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840136753002945664761369 1380102564752209248571027)
          ·
            refine ⟨2070153847128313872856541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380102564752209248571027 2070153847128313872856541)
            ·
              refine ⟨776307692673117702321203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070153847128313872856541 776307692673117702321203)
              ·
                refine ⟨1164461539009676553481805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776307692673117702321203 1164461539009676553481805)
                ·
                  refine ⟨436673077128628707555677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164461539009676553481805 436673077128628707555677)
                  ·
                    refine ⟨163752403923235765333379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436673077128628707555677 163752403923235765333379)
                    ·
                      rfl

theorem cell22_478360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_478360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478360 prefixEnd_478360 := by exact prefixLift 478360
  have htrace : WordTrace (prefixWord ++ tailWord_478360) baseStart_478360 baseEnd_478360 := by
    simpa [prefixWord, tailWord_478360, baseEnd_478360] using wordTrace_append hprefix tailTrace_478360
  have hstable : (prefixWord ++ tailWord_478360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478360).length < 2 ^ (prefixWord ++ tailWord_478360).sum := by decide
  have hdescent : baseEnd_478360 < baseStart_478360 := by decide
  rcases family_descends (prefixWord ++ tailWord_478360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_478371 : Nat := 118140960795 + 478371 * 2 ^ 59
def prefixEnd_478371 : Nat := 4983230072969 + 3 ^ 40 * 478371 * 2
def baseEnd_478371 : Nat := 163756169448035403308345

theorem tailTrace_478371 : CollatzResearch.WordTrace tailWord_478371 prefixEnd_478371 163756169448035403308345 := by
  unfold tailWord_478371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447623749951041107498967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11631749166634027404999311 17447623749951041107498967)
  ·
    refine ⟨26171435624926561661248451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17447623749951041107498967 26171435624926561661248451)
    ·
      refine ⟨39257153437389842491872677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26171435624926561661248451 39257153437389842491872677)
      ·
        refine ⟨7360716269510595467226127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39257153437389842491872677 7360716269510595467226127)
        ·
          refine ⟨11041074404265893200839191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360716269510595467226127 11041074404265893200839191)
          ·
            refine ⟨16561611606398839801258787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041074404265893200839191 16561611606398839801258787)
            ·
              refine ⟨24842417409598259701888181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16561611606398839801258787 24842417409598259701888181)
              ·
                refine ⟨2328976632149836847052017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24842417409598259701888181 2328976632149836847052017)
                ·
                  refine ⟨1746732474112377635289013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328976632149836847052017 1746732474112377635289013)
                  ·
                    refine ⟨163756169448035403308345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1746732474112377635289013 163756169448035403308345)
                    ·
                      rfl

theorem cell22_478371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_478371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478371 prefixEnd_478371 := by exact prefixLift 478371
  have htrace : WordTrace (prefixWord ++ tailWord_478371) baseStart_478371 baseEnd_478371 := by
    simpa [prefixWord, tailWord_478371, baseEnd_478371] using wordTrace_append hprefix tailTrace_478371
  have hstable : (prefixWord ++ tailWord_478371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478371).length < 2 ^ (prefixWord ++ tailWord_478371).sum := by decide
  have hdescent : baseEnd_478371 < baseStart_478371 := by decide
  rcases family_descends (prefixWord ++ tailWord_478371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478373 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 5]
def baseStart_478373 : Nat := 118140960795 + 478373 * 2 ^ 59
def prefixEnd_478373 : Nat := 4983230072969 + 3 ^ 40 * 478373 * 2
def baseEnd_478373 : Nat := 54585618029636021586113

theorem tailTrace_478373 : CollatzResearch.WordTrace tailWord_478373 prefixEnd_478373 54585618029636021586113 := by
  unfold tailWord_478373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447696695943795449071773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11631797797295863632714515 17447696695943795449071773)
  ·
    refine ⟨6542886260978923293401915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17447696695943795449071773 6542886260978923293401915)
    ·
      refine ⟨9814329391468384940102873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542886260978923293401915 9814329391468384940102873)
      ·
        refine ⟨7360747043601288705077155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9814329391468384940102873 7360747043601288705077155)
        ·
          refine ⟨11041120565401933057615733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360747043601288705077155 11041120565401933057615733)
          ·
            refine ⟨1035105053006431224151475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11041120565401933057615733 1035105053006431224151475)
            ·
              refine ⟨1552657579509646836227213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035105053006431224151475 1552657579509646836227213)
              ·
                refine ⟨582246592316117563585205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552657579509646836227213 582246592316117563585205)
                ·
                  refine ⟨54585618029636021586113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 582246592316117563585205 54585618029636021586113)
                  ·
                    rfl

theorem cell22_478373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_478373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478373 prefixEnd_478373 := by exact prefixLift 478373
  have htrace : WordTrace (prefixWord ++ tailWord_478373) baseStart_478373 baseEnd_478373 := by
    simpa [prefixWord, tailWord_478373, baseEnd_478373] using wordTrace_append hprefix tailTrace_478373
  have hstable : (prefixWord ++ tailWord_478373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478373).length < 2 ^ (prefixWord ++ tailWord_478373).sum := by decide
  have hdescent : baseEnd_478373 < baseStart_478373 := by decide
  rcases family_descends (prefixWord ++ tailWord_478373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478418 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_478418 : Nat := 118140960795 + 478418 * 2 ^ 59
def prefixEnd_478418 : Nat := 4983230072969 + 3 ^ 40 * 478418 * 2
def baseEnd_478418 : Nat := 54590752836180982461067

theorem tailTrace_478418 : CollatzResearch.WordTrace tailWord_478418 prefixEnd_478418 54590752836180982461067 := by
  unfold tailWord_478418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362334495195192033614977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11632891987187178756306605 4362334495195192033614977)
  ·
    refine ⟨3271750871396394025211233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4362334495195192033614977 3271750871396394025211233)
    ·
      refine ⟨2453813153547295518908425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271750871396394025211233 2453813153547295518908425)
      ·
        refine ⟨1840359865160471639181319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453813153547295518908425 1840359865160471639181319)
        ·
          refine ⟨2760539797740707458771979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840359865160471639181319 2760539797740707458771979)
          ·
            refine ⟨4140809696611061188157969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760539797740707458771979 4140809696611061188157969)
            ·
              refine ⟨3105607272458295891118477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140809696611061188157969 3105607272458295891118477)
              ·
                refine ⟨1164602727171860959169429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105607272458295891118477 1164602727171860959169429)
                ·
                  refine ⟨54590752836180982461067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1164602727171860959169429 54590752836180982461067)
                  ·
                    rfl

theorem cell22_478418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_478418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478418 prefixEnd_478418 := by exact prefixLift 478418
  have htrace : WordTrace (prefixWord ++ tailWord_478418) baseStart_478418 baseEnd_478418 := by
    simpa [prefixWord, tailWord_478418, baseEnd_478418] using wordTrace_append hprefix tailTrace_478418
  have hstable : (prefixWord ++ tailWord_478418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478418).length < 2 ^ (prefixWord ++ tailWord_478418).sum := by decide
  have hdescent : baseEnd_478418 < baseStart_478418 := by decide
  rcases family_descends (prefixWord ++ tailWord_478418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478422 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_478422 : Nat := 118140960795 + 478422 * 2 ^ 59
def prefixEnd_478422 : Nat := 4983230072969 + 3 ^ 40 * 478422 * 2
def baseEnd_478422 : Nat := 163773627790288270283189

theorem tailTrace_478422 : CollatzResearch.WordTrace tailWord_478422 prefixEnd_478422 163773627790288270283189 := by
  unfold tailWord_478422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090592742047892301100345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11632989248510851211737013 1090592742047892301100345)
  ·
    refine ⟨817944556535919225825259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1090592742047892301100345 817944556535919225825259)
    ·
      refine ⟨1226916834803878838737889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817944556535919225825259 1226916834803878838737889)
      ·
        refine ⟨920187626102909129053417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226916834803878838737889 920187626102909129053417)
        ·
          refine ⟨690140719577181846790063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920187626102909129053417 690140719577181846790063)
          ·
            refine ⟨1035211079365772770185095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690140719577181846790063 1035211079365772770185095)
            ·
              refine ⟨1552816619048659155277643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035211079365772770185095 1552816619048659155277643)
              ·
                refine ⟨2329224928572988732916465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552816619048659155277643 2329224928572988732916465)
                ·
                  refine ⟨1746918696429741549687349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329224928572988732916465 1746918696429741549687349)
                  ·
                    refine ⟨163773627790288270283189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1746918696429741549687349 163773627790288270283189)
                    ·
                      rfl

theorem cell22_478422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_478422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478422 prefixEnd_478422 := by exact prefixLift 478422
  have htrace : WordTrace (prefixWord ++ tailWord_478422) baseStart_478422 baseEnd_478422 := by
    simpa [prefixWord, tailWord_478422, baseEnd_478422] using wordTrace_append hprefix tailTrace_478422
  have hstable : (prefixWord ++ tailWord_478422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478422).length < 2 ^ (prefixWord ++ tailWord_478422).sum := by decide
  have hdescent : baseEnd_478422 < baseStart_478422 := by decide
  rcases family_descends (prefixWord ++ tailWord_478422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478433 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_478433 : Nat := 118140960795 + 478433 * 2 ^ 59
def prefixEnd_478433 : Nat := 4983230072969 + 3 ^ 40 * 478433 * 2
def baseEnd_478433 : Nat := 163777393315087908258155

theorem tailTrace_478433 : CollatzResearch.WordTrace tailWord_478433 prefixEnd_478433 163777393315087908258155 := by
  unfold tailWord_478433
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449885075726425696255953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11633256717150950464170635 17449885075726425696255953)
  ·
    refine ⟨13087413806794819272191965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17449885075726425696255953 13087413806794819272191965)
    ·
      refine ⟨4907780177548057227071987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13087413806794819272191965 4907780177548057227071987)
      ·
        refine ⟨7361670266322085840607981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907780177548057227071987 7361670266322085840607981)
        ·
          refine ⟨2760626349870782190227993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7361670266322085840607981 2760626349870782190227993)
          ·
            refine ⟨2070469762403086642670995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760626349870782190227993 2070469762403086642670995)
            ·
              refine ⟨3105704643604629964006493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070469762403086642670995 3105704643604629964006493)
              ·
                refine ⟨1164639241351736236502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105704643604629964006493 1164639241351736236502435)
                ·
                  refine ⟨1746958862027604354753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164639241351736236502435 1746958862027604354753653)
                  ·
                    refine ⟨163777393315087908258155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1746958862027604354753653 163777393315087908258155)
                    ·
                      rfl

theorem cell22_478433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_478433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478433 prefixEnd_478433 := by exact prefixLift 478433
  have htrace : WordTrace (prefixWord ++ tailWord_478433) baseStart_478433 baseEnd_478433 := by
    simpa [prefixWord, tailWord_478433, baseEnd_478433] using wordTrace_append hprefix tailTrace_478433
  have hstable : (prefixWord ++ tailWord_478433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478433).length < 2 ^ (prefixWord ++ tailWord_478433).sum := by decide
  have hdescent : baseEnd_478433 < baseStart_478433 := by decide
  rcases family_descends (prefixWord ++ tailWord_478433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478467 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 2, 3]
def baseStart_478467 : Nat := 118140960795 + 478467 * 2 ^ 59
def prefixEnd_478467 : Nat := 4983230072969 + 3 ^ 40 * 478467 * 2
def baseEnd_478467 : Nat := 163789032209923152908051

theorem tailTrace_478467 : CollatzResearch.WordTrace tailWord_478467 prefixEnd_478467 163789032209923152908051 := by
  unfold tailWord_478467
  simp only [CollatzResearch.WordTrace]
  refine ⟨17451125157603249502993655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11634083438402166335329103 17451125157603249502993655)
  ·
    refine ⟨26176687736404874254490483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17451125157603249502993655 26176687736404874254490483)
    ·
      refine ⟨39265031604607311381735725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26176687736404874254490483 39265031604607311381735725)
      ·
        refine ⟨14724386851727741768150897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39265031604607311381735725 14724386851727741768150897)
        ·
          refine ⟨11043290138795806326113173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14724386851727741768150897 11043290138795806326113173)
          ·
            refine ⟨517654225256053421536555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11043290138795806326113173 517654225256053421536555)
            ·
              refine ⟨776481337884080132304833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517654225256053421536555 776481337884080132304833)
              ·
                refine ⟨582361003413060099228625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776481337884080132304833 582361003413060099228625)
                ·
                  refine ⟨436770752559795074421469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582361003413060099228625 436770752559795074421469)
                  ·
                    refine ⟨163789032209923152908051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436770752559795074421469 163789032209923152908051)
                    ·
                      rfl

theorem cell22_478467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].length) (baseStart_478467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478467 prefixEnd_478467 := by exact prefixLift 478467
  have htrace : WordTrace (prefixWord ++ tailWord_478467) baseStart_478467 baseEnd_478467 := by
    simpa [prefixWord, tailWord_478467, baseEnd_478467] using wordTrace_append hprefix tailTrace_478467
  have hstable : (prefixWord ++ tailWord_478467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478467).length < 2 ^ (prefixWord ++ tailWord_478467).sum := by decide
  have hdescent : baseEnd_478467 < baseStart_478467 := by decide
  rcases family_descends (prefixWord ++ tailWord_478467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478529 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_478529 : Nat := 118140960795 + 478529 * 2 ^ 59
def prefixEnd_478529 : Nat := 4983230072969 + 3 ^ 40 * 478529 * 2
def baseEnd_478529 : Nat := 163810256076975657857861

theorem tailTrace_478529 : CollatzResearch.WordTrace tailWord_478529 prefixEnd_478529 163810256076975657857861 := by
  unfold tailWord_478529
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453386483378634091750641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11635590988919089394500427 17453386483378634091750641)
  ·
    refine ⟨13090039862533975568812981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17453386483378634091750641 13090039862533975568812981)
    ·
      refine ⟨1227191237112560209576217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13090039862533975568812981 1227191237112560209576217)
      ·
        refine ⟨920393427834420157182163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227191237112560209576217 920393427834420157182163)
        ·
          refine ⟨1380590141751630235773245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920393427834420157182163 1380590141751630235773245)
          ·
            refine ⟨517721303156861338414967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380590141751630235773245 517721303156861338414967)
            ·
              refine ⟨776581954735292007622451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517721303156861338414967 776581954735292007622451)
              ·
                refine ⟨1164872932102938011433677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776581954735292007622451 1164872932102938011433677)
                ·
                  refine ⟨436827349538601754287629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164872932102938011433677 436827349538601754287629)
                  ·
                    refine ⟨163810256076975657857861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436827349538601754287629 163810256076975657857861)
                    ·
                      rfl

theorem cell22_478529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_478529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478529 prefixEnd_478529 := by exact prefixLift 478529
  have htrace : WordTrace (prefixWord ++ tailWord_478529) baseStart_478529 baseEnd_478529 := by
    simpa [prefixWord, tailWord_478529, baseEnd_478529] using wordTrace_append hprefix tailTrace_478529
  have hstable : (prefixWord ++ tailWord_478529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478529).length < 2 ^ (prefixWord ++ tailWord_478529).sum := by decide
  have hdescent : baseEnd_478529 < baseStart_478529 := by decide
  rcases family_descends (prefixWord ++ tailWord_478529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478553 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 6]
def baseStart_478553 : Nat := 118140960795 + 478553 * 2 ^ 59
def prefixEnd_478553 : Nat := 4983230072969 + 3 ^ 40 * 478553 * 2
def baseEnd_478553 : Nat := 54606157255815865085929

theorem tailTrace_478553 : CollatzResearch.WordTrace tailWord_478553 prefixEnd_478553 54606157255815865085929 := by
  unfold tailWord_478553
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454261835291686190624313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11636174556861124127082875 17454261835291686190624313)
  ·
    refine ⟨13090696376468764642968235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17454261835291686190624313 13090696376468764642968235)
    ·
      refine ⟨19636044564703146964452353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090696376468764642968235 19636044564703146964452353)
      ·
        refine ⟨14727033423527360223339265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19636044564703146964452353 14727033423527360223339265)
        ·
          refine ⟨11045275067645520167504449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14727033423527360223339265 11045275067645520167504449)
          ·
            refine ⟨8283956300734140125628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045275067645520167504449 8283956300734140125628337)
            ·
              refine ⟨6212967225550605094221253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283956300734140125628337 6212967225550605094221253)
              ·
                refine ⟨1164931354790738455166485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6212967225550605094221253 1164931354790738455166485)
                ·
                  refine ⟨54606157255815865085929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1164931354790738455166485 54606157255815865085929)
                  ·
                    rfl

theorem cell22_478553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_478553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478553 prefixEnd_478553 := by exact prefixLift 478553
  have htrace : WordTrace (prefixWord ++ tailWord_478553) baseStart_478553 baseEnd_478553 := by
    simpa [prefixWord, tailWord_478553, baseEnd_478553] using wordTrace_append hprefix tailTrace_478553
  have hstable : (prefixWord ++ tailWord_478553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478553).length < 2 ^ (prefixWord ++ tailWord_478553).sum := by decide
  have hdescent : baseEnd_478553 < baseStart_478553 := by decide
  rcases family_descends (prefixWord ++ tailWord_478553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478585 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_478585 : Nat := 118140960795 + 478585 * 2 ^ 59
def prefixEnd_478585 : Nat := 4983230072969 + 3 ^ 40 * 478585 * 2
def baseEnd_478585 : Nat := 163829426021410178457689

theorem tailTrace_478585 : CollatzResearch.WordTrace tailWord_478585 prefixEnd_478585 163829426021410178457689 := by
  unfold tailWord_478585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455428971175755655789209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11636952647450503770526139 17455428971175755655789209)
  ·
    refine ⟨13091571728381816741841907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17455428971175755655789209 13091571728381816741841907)
    ·
      refine ⟨19637357592572725112762861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13091571728381816741841907 19637357592572725112762861)
      ·
        refine ⟨7364009097214771917286073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19637357592572725112762861 7364009097214771917286073)
        ·
          refine ⟨5523006822911078937964555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364009097214771917286073 5523006822911078937964555)
          ·
            refine ⟨8284510234366618406946833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523006822911078937964555 8284510234366618406946833)
            ·
              refine ⟨6213382675774963805210125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284510234366618406946833 6213382675774963805210125)
              ·
                refine ⟨2330018503415611426953797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6213382675774963805210125 2330018503415611426953797)
                ·
                  refine ⟨436878469390427142553837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330018503415611426953797 436878469390427142553837)
                  ·
                    refine ⟨163829426021410178457689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436878469390427142553837 163829426021410178457689)
                    ·
                      rfl

theorem cell22_478585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_478585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478585 prefixEnd_478585 := by exact prefixLift 478585
  have htrace : WordTrace (prefixWord ++ tailWord_478585) baseStart_478585 baseEnd_478585 := by
    simpa [prefixWord, tailWord_478585, baseEnd_478585] using wordTrace_append hprefix tailTrace_478585
  have hstable : (prefixWord ++ tailWord_478585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478585).length < 2 ^ (prefixWord ++ tailWord_478585).sum := by decide
  have hdescent : baseEnd_478585 < baseStart_478585 := by decide
  rcases family_descends (prefixWord ++ tailWord_478585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478617 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_478617 : Nat := 118140960795 + 478617 * 2 ^ 59
def prefixEnd_478617 : Nat := 4983230072969 + 3 ^ 40 * 478617 * 2
def baseEnd_478617 : Nat := 163840380275372761657591

theorem tailTrace_478617 : CollatzResearch.WordTrace tailWord_478617 prefixEnd_478617 163840380275372761657591 := by
  unfold tailWord_478617
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456596107059825120954105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637730738039883413969403 17456596107059825120954105)
  ·
    refine ⟨13092447080294868840715579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17456596107059825120954105 13092447080294868840715579)
    ·
      refine ⟨19638670620442303261073369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13092447080294868840715579 19638670620442303261073369)
      ·
        refine ⟨14729002965331727445805027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19638670620442303261073369 14729002965331727445805027)
        ·
          refine ⟨22093504447997591168707541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14729002965331727445805027 22093504447997591168707541)
          ·
            refine ⟨517816510499943543016583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22093504447997591168707541 517816510499943543016583)
            ·
              refine ⟨776724765749915314524875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517816510499943543016583 776724765749915314524875)
              ·
                refine ⟨1165087148624872971787313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776724765749915314524875 1165087148624872971787313)
                ·
                  refine ⟨873815361468654728840485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165087148624872971787313 873815361468654728840485)
                  ·
                    refine ⟨163840380275372761657591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873815361468654728840485 163840380275372761657591)
                    ·
                      rfl

theorem cell22_478617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_478617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478617 prefixEnd_478617 := by exact prefixLift 478617
  have htrace : WordTrace (prefixWord ++ tailWord_478617) baseStart_478617 baseEnd_478617 := by
    simpa [prefixWord, tailWord_478617, baseEnd_478617] using wordTrace_append hprefix tailTrace_478617
  have hstable : (prefixWord ++ tailWord_478617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478617).length < 2 ^ (prefixWord ++ tailWord_478617).sum := by decide
  have hdescent : baseEnd_478617 < baseStart_478617 := by decide
  rcases family_descends (prefixWord ++ tailWord_478617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478632 : List Nat := [2, 1, 6, 1, 2, 1, 9]
def baseStart_478632 : Nat := 118140960795 + 478632 * 2 ^ 59
def prefixEnd_478632 : Nat := 4983230072969 + 3 ^ 40 * 478632 * 2
def baseEnd_478632 : Nat := 6068352410441397130835

theorem tailTrace_478632 : CollatzResearch.WordTrace tailWord_478632 prefixEnd_478632 6068352410441397130835 := by
  unfold tailWord_478632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728571601002741341375075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11638095468003655121833433 8728571601002741341375075)
  ·
    refine ⟨13092857401504112012062613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8728571601002741341375075 13092857401504112012062613)
    ·
      refine ⟨613727690695505250565435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13092857401504112012062613 613727690695505250565435)
      ·
        refine ⟨920591536043257875848153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613727690695505250565435 920591536043257875848153)
        ·
          refine ⟨690443652032443406886115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920591536043257875848153 690443652032443406886115)
          ·
            refine ⟨1035665478048665110329173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690443652032443406886115 1035665478048665110329173)
            ·
              refine ⟨6068352410441397130835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1035665478048665110329173 6068352410441397130835)
              ·
                rfl

theorem cell22_478632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 9].length) (baseStart_478632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478632 prefixEnd_478632 := by exact prefixLift 478632
  have htrace : WordTrace (prefixWord ++ tailWord_478632) baseStart_478632 baseEnd_478632 := by
    simpa [prefixWord, tailWord_478632, baseEnd_478632] using wordTrace_append hprefix tailTrace_478632
  have hstable : (prefixWord ++ tailWord_478632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478632).length < 2 ^ (prefixWord ++ tailWord_478632).sum := by decide
  have hdescent : baseEnd_478632 < baseStart_478632 := by decide
  rcases family_descends (prefixWord ++ tailWord_478632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478647 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 3, 3]
def baseStart_478647 : Nat := 118140960795 + 478647 * 2 ^ 59
def prefixEnd_478647 : Nat := 4983230072969 + 3 ^ 40 * 478647 * 2
def baseEnd_478647 : Nat := 163850649888462683407499

theorem tailTrace_478647 : CollatzResearch.WordTrace tailWord_478647 prefixEnd_478647 163850649888462683407499 := by
  unfold tailWord_478647
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457690296951140244546195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11638460197967426829697463 17457690296951140244546195)
  ·
    refine ⟨26186535445426710366819293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17457690296951140244546195 26186535445426710366819293)
    ·
      refine ⟨9819950792035016387557235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26186535445426710366819293 9819950792035016387557235)
      ·
        refine ⟨14729926188052524581335853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9819950792035016387557235 14729926188052524581335853)
        ·
          refine ⟨5523722320519696718000945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14729926188052524581335853 5523722320519696718000945)
          ·
            refine ⟨4142791740389772538500709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523722320519696718000945 4142791740389772538500709)
            ·
              refine ⟨776773451323082350968883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4142791740389772538500709 776773451323082350968883)
              ·
                refine ⟨1165160176984623526453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776773451323082350968883 1165160176984623526453325)
                ·
                  refine ⟨436935066369233822419997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165160176984623526453325 436935066369233822419997)
                  ·
                    refine ⟨163850649888462683407499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436935066369233822419997 163850649888462683407499)
                    ·
                      rfl

theorem cell22_478647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_478647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478647 prefixEnd_478647 := by exact prefixLift 478647
  have htrace : WordTrace (prefixWord ++ tailWord_478647) baseStart_478647 baseEnd_478647 := by
    simpa [prefixWord, tailWord_478647, baseEnd_478647] using wordTrace_append hprefix tailTrace_478647
  have hstable : (prefixWord ++ tailWord_478647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478647).length < 2 ^ (prefixWord ++ tailWord_478647).sum := by decide
  have hdescent : baseEnd_478647 < baseStart_478647 := by decide
  rcases family_descends (prefixWord ++ tailWord_478647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478681 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_478681 : Nat := 118140960795 + 478681 * 2 ^ 59
def prefixEnd_478681 : Nat := 4983230072969 + 3 ^ 40 * 478681 * 2
def baseEnd_478681 : Nat := 163862288783297928057395

theorem tailTrace_478681 : CollatzResearch.WordTrace tailWord_478681 prefixEnd_478681 163862288783297928057395 := by
  unfold tailWord_478681
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458930378827964051283897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11639286919218642700855931 17458930378827964051283897)
  ·
    refine ⟨13094197784120973038462923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17458930378827964051283897 13094197784120973038462923)
    ·
      refine ⟨19641296676181459557694385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13094197784120973038462923 19641296676181459557694385)
      ·
        refine ⟨14730972507136094668270789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19641296676181459557694385 14730972507136094668270789)
        ·
          refine ⟨2762057345088017750300773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14730972507136094668270789 2762057345088017750300773)
          ·
            refine ⟨517885752204003328181395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2762057345088017750300773 517885752204003328181395)
            ·
              refine ⟨776828628306004992272093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517885752204003328181395 776828628306004992272093)
              ·
                refine ⟨291310735614751872102035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776828628306004992272093 291310735614751872102035)
                ·
                  refine ⟨436966103422127808153053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291310735614751872102035 436966103422127808153053)
                  ·
                    refine ⟨163862288783297928057395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436966103422127808153053 163862288783297928057395)
                    ·
                      rfl

theorem cell22_478681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_478681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478681 prefixEnd_478681 := by exact prefixLift 478681
  have htrace : WordTrace (prefixWord ++ tailWord_478681) baseStart_478681 baseEnd_478681 := by
    simpa [prefixWord, tailWord_478681, baseEnd_478681] using wordTrace_append hprefix tailTrace_478681
  have hstable : (prefixWord ++ tailWord_478681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478681).length < 2 ^ (prefixWord ++ tailWord_478681).sum := by decide
  have hdescent : baseEnd_478681 < baseStart_478681 := by decide
  rcases family_descends (prefixWord ++ tailWord_478681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478698 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_478698 : Nat := 118140960795 + 478698 * 2 ^ 59
def prefixEnd_478698 : Nat := 4983230072969 + 3 ^ 40 * 478698 * 2
def baseEnd_478698 : Nat := 163868108230715550382343

theorem tailTrace_478698 : CollatzResearch.WordTrace tailWord_478698 prefixEnd_478698 163868108230715550382343 := by
  unfold tailWord_478698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364887604941593988663187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11639700279844250636435165 4364887604941593988663187)
  ·
    refine ⟨6547331407412390982994781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364887604941593988663187 6547331407412390982994781)
    ·
      refine ⟨2455249277779646618623043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6547331407412390982994781 2455249277779646618623043)
      ·
        refine ⟨3682873916669469927934565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455249277779646618623043 3682873916669469927934565)
        ·
          refine ⟨690538859375525611487731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3682873916669469927934565 690538859375525611487731)
          ·
            refine ⟨1035808289063288417231597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690538859375525611487731 1035808289063288417231597)
            ·
              refine ⟨388428108398733156461849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035808289063288417231597 388428108398733156461849)
              ·
                refine ⟨291321081299049867346387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388428108398733156461849 291321081299049867346387)
                ·
                  refine ⟨436981621948574801019581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291321081299049867346387 436981621948574801019581)
                  ·
                    refine ⟨163868108230715550382343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436981621948574801019581 163868108230715550382343)
                    ·
                      rfl

theorem cell22_478698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_478698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478698 prefixEnd_478698 := by exact prefixLift 478698
  have htrace : WordTrace (prefixWord ++ tailWord_478698) baseStart_478698 baseEnd_478698 := by
    simpa [prefixWord, tailWord_478698, baseEnd_478698] using wordTrace_append hprefix tailTrace_478698
  have hstable : (prefixWord ++ tailWord_478698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478698).length < 2 ^ (prefixWord ++ tailWord_478698).sum := by decide
  have hdescent : baseEnd_478698 < baseStart_478698 := by decide
  rcases family_descends (prefixWord ++ tailWord_478698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478724 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_478724 : Nat := 118140960795 + 478724 * 2 ^ 59
def prefixEnd_478724 : Nat := 4983230072969 + 3 ^ 40 * 478724 * 2
def baseEnd_478724 : Nat := 163877008562060149232263

theorem tailTrace_478724 : CollatzResearch.WordTrace tailWord_478724 prefixEnd_478724 163877008562060149232263 := by
  unfold tailWord_478724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730249358836091197549613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11640332478448121596732817 8730249358836091197549613)
  ·
    refine ⟨3273843509563534199081105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8730249358836091197549613 3273843509563534199081105)
    ·
      refine ⟨2455382632172650649310829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273843509563534199081105 2455382632172650649310829)
      ·
        refine ⟨920768487064743993491561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2455382632172650649310829 920768487064743993491561)
        ·
          refine ⟨690576365298557995118671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920768487064743993491561 690576365298557995118671)
          ·
            refine ⟨1035864547947836992678007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690576365298557995118671 1035864547947836992678007)
            ·
              refine ⟨1553796821921755489017011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035864547947836992678007 1553796821921755489017011)
              ·
                refine ⟨2330695232882633233525517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553796821921755489017011 2330695232882633233525517)
                ·
                  refine ⟨874010712330987462572069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2330695232882633233525517 874010712330987462572069)
                  ·
                    refine ⟨163877008562060149232263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874010712330987462572069 163877008562060149232263)
                    ·
                      rfl

theorem cell22_478724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_478724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478724 prefixEnd_478724 := by exact prefixLift 478724
  have htrace : WordTrace (prefixWord ++ tailWord_478724) baseStart_478724 baseEnd_478724 := by
    simpa [prefixWord, tailWord_478724, baseEnd_478724] using wordTrace_append hprefix tailTrace_478724
  have hstable : (prefixWord ++ tailWord_478724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478724).length < 2 ^ (prefixWord ++ tailWord_478724).sum := by decide
  have hdescent : baseEnd_478724 < baseStart_478724 := by decide
  rcases family_descends (prefixWord ++ tailWord_478724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478754 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_478754 : Nat := 118140960795 + 478754 * 2 ^ 59
def prefixEnd_478754 : Nat := 4983230072969 + 3 ^ 40 * 478754 * 2
def baseEnd_478754 : Nat := 163887278175150070982171

theorem tailTrace_478754 : CollatzResearch.WordTrace tailWord_478754 prefixEnd_478754 163887278175150070982171 := by
  unfold tailWord_478754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365398226890874379672829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11641061938375665012460877 4365398226890874379672829)
  ·
    refine ⟨1637024335084077892377311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4365398226890874379672829 1637024335084077892377311)
    ·
      refine ⟨2455536502626116838565967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637024335084077892377311 2455536502626116838565967)
      ·
        refine ⟨3683304753939175257848951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455536502626116838565967 3683304753939175257848951)
        ·
          refine ⟨5524957130908762886773427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683304753939175257848951 5524957130908762886773427)
          ·
            refine ⟨8287435696363144330160141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524957130908762886773427 8287435696363144330160141)
            ·
              refine ⟨3107788386136179123810053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8287435696363144330160141 3107788386136179123810053)
              ·
                refine ⟨582710322400533585714385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3107788386136179123810053 582710322400533585714385)
                ·
                  refine ⟨437032741800400189285789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582710322400533585714385 437032741800400189285789)
                  ·
                    refine ⟨163887278175150070982171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437032741800400189285789 163887278175150070982171)
                    ·
                      rfl

theorem cell22_478754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_478754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478754 prefixEnd_478754 := by exact prefixLift 478754
  have htrace : WordTrace (prefixWord ++ tailWord_478754) baseStart_478754 baseEnd_478754 := by
    simpa [prefixWord, tailWord_478754, baseEnd_478754] using wordTrace_append hprefix tailTrace_478754
  have hstable : (prefixWord ++ tailWord_478754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478754).length < 2 ^ (prefixWord ++ tailWord_478754).sum := by decide
  have hdescent : baseEnd_478754 < baseStart_478754 := by decide
  rcases family_descends (prefixWord ++ tailWord_478754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478795 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 7]
def baseStart_478795 : Nat := 118140960795 + 478795 * 2 ^ 59
def prefixEnd_478795 : Nat := 4983230072969 + 3 ^ 40 * 478795 * 2
def baseEnd_478795 : Nat := 54633771104346543569015

theorem tailTrace_478795 : CollatzResearch.WordTrace tailWord_478795 prefixEnd_478795 54633771104346543569015 := by
  unfold tailWord_478795
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463088300414961520933839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642058866943307680622559 17463088300414961520933839)
  ·
    refine ⟨26194632450622442281400759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463088300414961520933839 26194632450622442281400759)
    ·
      refine ⟨39291948675933663422101139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26194632450622442281400759 39291948675933663422101139)
      ·
        refine ⟨58937923013900495133151709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39291948675933663422101139 58937923013900495133151709)
        ·
          refine ⟨22101721130212685674931891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58937923013900495133151709 22101721130212685674931891)
          ·
            refine ⟨33152581695319028512397837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22101721130212685674931891 33152581695319028512397837)
            ·
              refine ⟨12432218135744635692149189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33152581695319028512397837 12432218135744635692149189)
              ·
                refine ⟨2331040900452119192277973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12432218135744635692149189 2331040900452119192277973)
                ·
                  refine ⟨54633771104346543569015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2331040900452119192277973 54633771104346543569015)
                  ·
                    rfl

theorem cell22_478795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_478795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478795 prefixEnd_478795 := by exact prefixLift 478795
  have htrace : WordTrace (prefixWord ++ tailWord_478795) baseStart_478795 baseEnd_478795 := by
    simpa [prefixWord, tailWord_478795, baseEnd_478795] using wordTrace_append hprefix tailTrace_478795
  have hstable : (prefixWord ++ tailWord_478795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478795).length < 2 ^ (prefixWord ++ tailWord_478795).sum := by decide
  have hdescent : baseEnd_478795 < baseStart_478795 := by decide
  rcases family_descends (prefixWord ++ tailWord_478795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478925 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 4]
def baseStart_478925 : Nat := 118140960795 + 478925 * 2 ^ 59
def prefixEnd_478925 : Nat := 4983230072969 + 3 ^ 40 * 478925 * 2
def baseEnd_478925 : Nat := 54648604989920874985549

theorem tailTrace_478925 : CollatzResearch.WordTrace tailWord_478925 prefixEnd_478925 54648604989920874985549 := by
  unfold tailWord_478925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17467829789943993723166229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11645219859962662482110819 17467829789943993723166229)
  ·
    refine ⟨818804521403624705773417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17467829789943993723166229 818804521403624705773417)
    ·
      refine ⟨614103391052718529330063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818804521403624705773417 614103391052718529330063)
      ·
        refine ⟨921155086579077793995095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614103391052718529330063 921155086579077793995095)
        ·
          refine ⟨1381732629868616690992643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921155086579077793995095 1381732629868616690992643)
          ·
            refine ⟨2072598944802925036488965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381732629868616690992643 2072598944802925036488965)
            ·
              refine ⟨388612302150548444341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2072598944802925036488965 388612302150548444341681)
              ·
                refine ⟨291459226612911333256261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388612302150548444341681 291459226612911333256261)
                ·
                  refine ⟨54648604989920874985549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291459226612911333256261 54648604989920874985549)
                  ·
                    rfl

theorem cell22_478925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_478925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_478925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_478925 prefixEnd_478925 := by exact prefixLift 478925
  have htrace : WordTrace (prefixWord ++ tailWord_478925) baseStart_478925 baseEnd_478925 := by
    simpa [prefixWord, tailWord_478925, baseEnd_478925] using wordTrace_append hprefix tailTrace_478925
  have hstable : (prefixWord ++ tailWord_478925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478925).length < 2 ^ (prefixWord ++ tailWord_478925).sum := by decide
  have hdescent : baseEnd_478925 < baseStart_478925 := by decide
  rcases family_descends (prefixWord ++ tailWord_478925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479009 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 6]
def baseStart_479009 : Nat := 118140960795 + 479009 * 2 ^ 59
def prefixEnd_479009 : Nat := 4983230072969 + 3 ^ 40 * 479009 * 2
def baseEnd_479009 : Nat := 54658189962138135285463

theorem tailTrace_479009 : CollatzResearch.WordTrace tailWord_479009 prefixEnd_479009 54658189962138135285463 := by
  unfold tailWord_479009
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470893521639676069224081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11647262347759784046149387 17470893521639676069224081)
  ·
    refine ⟨13103170141229757051918061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17470893521639676069224081 13103170141229757051918061)
    ·
      refine ⟨4913688802961158894469273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13103170141229757051918061 4913688802961158894469273)
      ·
        refine ⟨3685266602220869170851955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913688802961158894469273 3685266602220869170851955)
        ·
          refine ⟨5527899903331303756277933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685266602220869170851955 5527899903331303756277933)
          ·
            refine ⟨2072962463749238908604225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5527899903331303756277933 2072962463749238908604225)
            ·
              refine ⟨1554721847811929181453169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072962463749238908604225 1554721847811929181453169)
              ·
                refine ⟨1166041385858946886089877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554721847811929181453169 1166041385858946886089877)
                ·
                  refine ⟨54658189962138135285463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166041385858946886089877 54658189962138135285463)
                  ·
                    rfl

theorem cell22_479009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_479009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479009 prefixEnd_479009 := by exact prefixLift 479009
  have htrace : WordTrace (prefixWord ++ tailWord_479009) baseStart_479009 baseEnd_479009 := by
    simpa [prefixWord, tailWord_479009, baseEnd_479009] using wordTrace_append hprefix tailTrace_479009
  have hstable : (prefixWord ++ tailWord_479009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479009).length < 2 ^ (prefixWord ++ tailWord_479009).sum := by decide
  have hdescent : baseEnd_479009 < baseStart_479009 := by decide
  rcases family_descends (prefixWord ++ tailWord_479009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479028 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_479028 : Nat := 118140960795 + 479028 * 2 ^ 59
def prefixEnd_479028 : Nat := 4983230072969 + 3 ^ 40 * 479028 * 2
def baseEnd_479028 : Nat := 163981073974704689631331

theorem tailTrace_479028 : CollatzResearch.WordTrace tailWord_479028 prefixEnd_479028 163981073974704689631331 := by
  unfold tailWord_479028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735793254285421157082869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11647724339047228209443825 8735793254285421157082869)
  ·
    refine ⟨818980617589258233476519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8735793254285421157082869 818980617589258233476519)
    ·
      refine ⟨1228470926383887350214779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818980617589258233476519 1228470926383887350214779)
      ·
        refine ⟨1842706389575831025322169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228470926383887350214779 1842706389575831025322169)
        ·
          refine ⟨1382029792181873268991627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842706389575831025322169 1382029792181873268991627)
          ·
            refine ⟨2073044688272809903487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382029792181873268991627 2073044688272809903487441)
            ·
              refine ⟨1554783516204607427615581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073044688272809903487441 1554783516204607427615581)
              ·
                refine ⟨583043818576727785355843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554783516204607427615581 583043818576727785355843)
                ·
                  refine ⟨874565727865091678033765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583043818576727785355843 874565727865091678033765)
                  ·
                    refine ⟨163981073974704689631331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874565727865091678033765 163981073974704689631331)
                    ·
                      rfl

theorem cell22_479028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_479028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479028 prefixEnd_479028 := by exact prefixLift 479028
  have htrace : WordTrace (prefixWord ++ tailWord_479028) baseStart_479028 baseEnd_479028 := by
    simpa [prefixWord, tailWord_479028, baseEnd_479028] using wordTrace_append hprefix tailTrace_479028
  have hstable : (prefixWord ++ tailWord_479028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479028).length < 2 ^ (prefixWord ++ tailWord_479028).sum := by decide
  have hdescent : baseEnd_479028 < baseStart_479028 := by decide
  rcases family_descends (prefixWord ++ tailWord_479028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479043 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 4]
def baseStart_479043 : Nat := 118140960795 + 479043 * 2 ^ 59
def prefixEnd_479043 : Nat := 4983230072969 + 3 ^ 40 * 479043 * 2
def baseEnd_479043 : Nat := 54662069593749883502095

theorem tailTrace_479043 : CollatzResearch.WordTrace tailWord_479043 prefixEnd_479043 54662069593749883502095 := by
  unfold tailWord_479043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17472133603516499875961783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11648089069010999917307855 17472133603516499875961783)
  ·
    refine ⟨26208200405274749813942675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17472133603516499875961783 26208200405274749813942675)
    ·
      refine ⟨39312300607912124720914013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26208200405274749813942675 39312300607912124720914013)
      ·
        refine ⟨14742112727967046770342755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39312300607912124720914013 14742112727967046770342755)
        ·
          refine ⟨22113169091950570155514133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14742112727967046770342755 22113169091950570155514133)
          ·
            refine ⟨1036554801185182976039725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22113169091950570155514133 1036554801185182976039725)
            ·
              refine ⟨388708050444443616014897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1036554801185182976039725 388708050444443616014897)
              ·
                refine ⟨291531037833332712011173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388708050444443616014897 291531037833332712011173)
                ·
                  refine ⟨54662069593749883502095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291531037833332712011173 54662069593749883502095)
                  ·
                    rfl

theorem cell22_479043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 4].length) (baseStart_479043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479043 prefixEnd_479043 := by exact prefixLift 479043
  have htrace : WordTrace (prefixWord ++ tailWord_479043) baseStart_479043 baseEnd_479043 := by
    simpa [prefixWord, tailWord_479043, baseEnd_479043] using wordTrace_append hprefix tailTrace_479043
  have hstable : (prefixWord ++ tailWord_479043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479043).length < 2 ^ (prefixWord ++ tailWord_479043).sum := by decide
  have hdescent : baseEnd_479043 < baseStart_479043 := by decide
  rcases family_descends (prefixWord ++ tailWord_479043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479058 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_479058 : Nat := 118140960795 + 479058 * 2 ^ 59
def prefixEnd_479058 : Nat := 4983230072969 + 3 ^ 40 * 479058 * 2
def baseEnd_479058 : Nat := 163991343587794611381239

theorem tailTrace_479058 : CollatzResearch.WordTrace tailWord_479058 prefixEnd_479058 163991343587794611381239 := by
  unfold tailWord_479058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368170174615539359439457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11648453798974771625171885 4368170174615539359439457)
  ·
    refine ⟨3276127630961654519579593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4368170174615539359439457 3276127630961654519579593)
    ·
      refine ⟨2457095723221240889684695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276127630961654519579593 2457095723221240889684695)
      ·
        refine ⟨3685643584831861334527043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457095723221240889684695 3685643584831861334527043)
        ·
          refine ⟨5528465377247792001790565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685643584831861334527043 5528465377247792001790565)
          ·
            refine ⟨1036587258233961000335731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5528465377247792001790565 1036587258233961000335731)
            ·
              refine ⟨1554880887350941500503597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036587258233961000335731 1554880887350941500503597)
              ·
                refine ⟨583080332756603062688849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1554880887350941500503597 583080332756603062688849)
                ·
                  refine ⟨437310249567452297016637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583080332756603062688849 437310249567452297016637)
                  ·
                    refine ⟨163991343587794611381239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437310249567452297016637 163991343587794611381239)
                    ·
                      rfl

theorem cell22_479058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_479058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479058 prefixEnd_479058 := by exact prefixLift 479058
  have htrace : WordTrace (prefixWord ++ tailWord_479058) baseStart_479058 baseEnd_479058 := by
    simpa [prefixWord, tailWord_479058, baseEnd_479058] using wordTrace_append hprefix tailTrace_479058
  have hstable : (prefixWord ++ tailWord_479058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479058).length < 2 ^ (prefixWord ++ tailWord_479058).sum := by decide
  have hdescent : baseEnd_479058 < baseStart_479058 := by decide
  rcases family_descends (prefixWord ++ tailWord_479058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479094 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_479094 : Nat := 118140960795 + 479094 * 2 ^ 59
def prefixEnd_479094 : Nat := 4983230072969 + 3 ^ 40 * 479094 * 2
def baseEnd_479094 : Nat := 54667889041167505827043

theorem tailTrace_479094 : CollatzResearch.WordTrace tailWord_479094 prefixEnd_479094 54667889041167505827043 := by
  unfold tailWord_479094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092124607895733474129271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11649329150887823724045557 1092124607895733474129271)
  ·
    refine ⟨1638186911843600211193907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092124607895733474129271 1638186911843600211193907)
    ·
      refine ⟨2457280367765400316790861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638186911843600211193907 2457280367765400316790861)
      ·
        refine ⟨921480137912025118796573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2457280367765400316790861 921480137912025118796573)
        ·
          refine ⟨345555051717009419548715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921480137912025118796573 345555051717009419548715)
          ·
            refine ⟨518332577575514129323073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345555051717009419548715 518332577575514129323073)
            ·
              refine ⟨388749433181635596992305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518332577575514129323073 388749433181635596992305)
              ·
                refine ⟨291562074886226697744229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388749433181635596992305 291562074886226697744229)
                ·
                  refine ⟨54667889041167505827043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291562074886226697744229 54667889041167505827043)
                  ·
                    rfl

theorem cell22_479094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_479094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479094 prefixEnd_479094 := by exact prefixLift 479094
  have htrace : WordTrace (prefixWord ++ tailWord_479094) baseStart_479094 baseEnd_479094 := by
    simpa [prefixWord, tailWord_479094, baseEnd_479094] using wordTrace_append hprefix tailTrace_479094
  have hstable : (prefixWord ++ tailWord_479094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479094).length < 2 ^ (prefixWord ++ tailWord_479094).sum := by decide
  have hdescent : baseEnd_479094 < baseStart_479094 := by decide
  rcases family_descends (prefixWord ++ tailWord_479094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479105 : List Nat := [1, 2, 4, 4, 2, 1, 1, 7]
def baseStart_479105 : Nat := 118140960795 + 479105 * 2 ^ 59
def prefixEnd_479105 : Nat := 4983230072969 + 3 ^ 40 * 479105 * 2
def baseEnd_479105 : Nat := 18223048072033572828455

theorem tailTrace_479105 : CollatzResearch.WordTrace tailWord_479105 prefixEnd_479105 18223048072033572828455 := by
  unfold tailWord_479105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474394929291884464718769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11649596619527922976479179 17474394929291884464718769)
  ·
    refine ⟨13105796196968913348539077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474394929291884464718769 13105796196968913348539077)
    ·
      refine ⟨2457336786931671252851077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13105796196968913348539077 2457336786931671252851077)
      ·
        refine ⟨460750647549688359909577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2457336786931671252851077 460750647549688359909577)
        ·
          refine ⟨345562985662266269932183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460750647549688359909577 345562985662266269932183)
          ·
            refine ⟨518344478493399404898275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345562985662266269932183 518344478493399404898275)
            ·
              refine ⟨777516717740099107347413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518344478493399404898275 777516717740099107347413)
              ·
                refine ⟨18223048072033572828455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 777516717740099107347413 18223048072033572828455)
                ·
                  rfl

theorem cell22_479105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 7].length) (baseStart_479105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479105 prefixEnd_479105 := by exact prefixLift 479105
  have htrace : WordTrace (prefixWord ++ tailWord_479105) baseStart_479105 baseEnd_479105 := by
    simpa [prefixWord, tailWord_479105, baseEnd_479105] using wordTrace_append hprefix tailTrace_479105
  have hstable : (prefixWord ++ tailWord_479105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479105).length < 2 ^ (prefixWord ++ tailWord_479105).sum := by decide
  have hdescent : baseEnd_479105 < baseStart_479105 := by decide
  rcases family_descends (prefixWord ++ tailWord_479105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479137 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_479137 : Nat := 118140960795 + 479137 * 2 ^ 59
def prefixEnd_479137 : Nat := 4983230072969 + 3 ^ 40 * 479137 * 2
def baseEnd_479137 : Nat := 164018386902264738655997

theorem tailTrace_479137 : CollatzResearch.WordTrace tailWord_479137 prefixEnd_479137 164018386902264738655997 := by
  unfold tailWord_479137
  simp only [CollatzResearch.WordTrace]
  refine ⟨17475562065175953929883665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11650374710117302619922443 17475562065175953929883665)
  ·
    refine ⟨13106671548881965447412749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17475562065175953929883665 13106671548881965447412749)
    ·
      refine ⟨4915001830830737042779781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13106671548881965447412749 4915001830830737042779781)
      ·
        refine ⟨921562843280763195521209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4915001830830737042779781 921562843280763195521209)
        ·
          refine ⟨691172132460572396640907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921562843280763195521209 691172132460572396640907)
          ·
            refine ⟨1036758198690858594961361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691172132460572396640907 1036758198690858594961361)
            ·
              refine ⟨777568649018143946221021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036758198690858594961361 777568649018143946221021)
              ·
                refine ⟨291588243381803979832883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777568649018143946221021 291588243381803979832883)
                ·
                  refine ⟨437382365072705969749325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291588243381803979832883 437382365072705969749325)
                  ·
                    refine ⟨164018386902264738655997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437382365072705969749325 164018386902264738655997)
                    ·
                      rfl

theorem cell22_479137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_479137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479137 prefixEnd_479137 := by exact prefixLift 479137
  have htrace : WordTrace (prefixWord ++ tailWord_479137) baseStart_479137 baseEnd_479137 := by
    simpa [prefixWord, tailWord_479137, baseEnd_479137] using wordTrace_append hprefix tailTrace_479137
  have hstable : (prefixWord ++ tailWord_479137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479137).length < 2 ^ (prefixWord ++ tailWord_479137).sum := by decide
  have hdescent : baseEnd_479137 < baseStart_479137 := by decide
  rcases family_descends (prefixWord ++ tailWord_479137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479161 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 6]
def baseStart_479161 : Nat := 118140960795 + 479161 * 2 ^ 59
def prefixEnd_479161 : Nat := 4983230072969 + 3 ^ 40 * 479161 * 2
def baseEnd_479161 : Nat := 54675534197578892018641

theorem tailTrace_479161 : CollatzResearch.WordTrace tailWord_479161 prefixEnd_479161 54675534197578892018641 := by
  unfold tailWord_479161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476437417089006028757337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11650958278059337352504891 17476437417089006028757337)
  ·
    refine ⟨13107328062816754521568003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17476437417089006028757337 13107328062816754521568003)
    ·
      refine ⟨19660992094225131782352005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107328062816754521568003 19660992094225131782352005)
      ·
        refine ⟨3686436017667212209191001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19660992094225131782352005 3686436017667212209191001)
        ·
          refine ⟨2764827013250409156893251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3686436017667212209191001 2764827013250409156893251)
          ·
            refine ⟨4147240519875613735339877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764827013250409156893251 4147240519875613735339877)
            ·
              refine ⟨777607597476677575376227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4147240519875613735339877 777607597476677575376227)
              ·
                refine ⟨1166411396215016363064341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777607597476677575376227 1166411396215016363064341)
                ·
                  refine ⟨54675534197578892018641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166411396215016363064341 54675534197578892018641)
                  ·
                    rfl

theorem cell22_479161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_479161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479161 prefixEnd_479161 := by exact prefixLift 479161
  have htrace : WordTrace (prefixWord ++ tailWord_479161) baseStart_479161 baseEnd_479161 := by
    simpa [prefixWord, tailWord_479161, baseEnd_479161] using wordTrace_append hprefix tailTrace_479161
  have hstable : (prefixWord ++ tailWord_479161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479161).length < 2 ^ (prefixWord ++ tailWord_479161).sum := by decide
  have hdescent : baseEnd_479161 < baseStart_479161 := by decide
  rcases family_descends (prefixWord ++ tailWord_479161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479191 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_479191 : Nat := 118140960795 + 479191 * 2 ^ 59
def prefixEnd_479191 : Nat := 4983230072969 + 3 ^ 40 * 479191 * 2
def baseEnd_479191 : Nat := 164036872205826597805831

theorem tailTrace_479191 : CollatzResearch.WordTrace tailWord_479191 prefixEnd_479191 164036872205826597805831 := by
  unfold tailWord_479191
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477531606980321152349427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11651687737986880768232951 17477531606980321152349427)
  ·
    refine ⟨26216297410470481728524141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17477531606980321152349427 26216297410470481728524141)
    ·
      refine ⟨9831111528926430648196553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26216297410470481728524141 9831111528926430648196553)
      ·
        refine ⟨7373333646694822986147415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9831111528926430648196553 7373333646694822986147415)
        ·
          refine ⟨11060000470042234479221123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373333646694822986147415 11060000470042234479221123)
          ·
            refine ⟨16590000705063351718831685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060000470042234479221123 16590000705063351718831685)
            ·
              refine ⟨3110625132199378447280941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16590000705063351718831685 3110625132199378447280941)
              ·
                refine ⟨1166484424574766917730353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3110625132199378447280941 1166484424574766917730353)
                ·
                  refine ⟨874863318431075188297765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166484424574766917730353 874863318431075188297765)
                  ·
                    refine ⟨164036872205826597805831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874863318431075188297765 164036872205826597805831)
                    ·
                      rfl

theorem cell22_479191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_479191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479191 prefixEnd_479191 := by exact prefixLift 479191
  have htrace : WordTrace (prefixWord ++ tailWord_479191) baseStart_479191 baseEnd_479191 := by
    simpa [prefixWord, tailWord_479191, baseEnd_479191] using wordTrace_append hprefix tailTrace_479191
  have hstable : (prefixWord ++ tailWord_479191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479191).length < 2 ^ (prefixWord ++ tailWord_479191).sum := by decide
  have hdescent : baseEnd_479191 < baseStart_479191 := by decide
  rcases family_descends (prefixWord ++ tailWord_479191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479296 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_479296 : Nat := 118140960795 + 479296 * 2 ^ 59
def prefixEnd_479296 : Nat := 4983230072969 + 3 ^ 40 * 479296 * 2
def baseEnd_479296 : Nat := 54690938617213774643503

theorem tailTrace_479296 : CollatzResearch.WordTrace tailWord_479296 prefixEnd_479296 54690938617213774643503 := by
  unfold tailWord_479296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740680635799962042460871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11654240847733282723281161 8740680635799962042460871)
  ·
    refine ⟨13111020953699943063691307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8740680635799962042460871 13111020953699943063691307)
    ·
      refine ⟨19666531430549914595536961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13111020953699943063691307 19666531430549914595536961)
      ·
        refine ⟨14749898572912435946652721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19666531430549914595536961 14749898572912435946652721)
        ·
          refine ⟨11062423929684326959989541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14749898572912435946652721 11062423929684326959989541)
          ·
            refine ⟨2074204486815811304998039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11062423929684326959989541 2074204486815811304998039)
            ·
              refine ⟨3111306730223716957497059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074204486815811304998039 3111306730223716957497059)
              ·
                refine ⟨4666960095335575436245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111306730223716957497059 4666960095335575436245589)
                ·
                  refine ⟨54690938617213774643503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4666960095335575436245589 54690938617213774643503)
                  ·
                    rfl

theorem cell22_479296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_479296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479296 prefixEnd_479296 := by exact prefixLift 479296
  have htrace : WordTrace (prefixWord ++ tailWord_479296) baseStart_479296 baseEnd_479296 := by
    simpa [prefixWord, tailWord_479296, baseEnd_479296] using wordTrace_append hprefix tailTrace_479296
  have hstable : (prefixWord ++ tailWord_479296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479296).length < 2 ^ (prefixWord ++ tailWord_479296).sum := by decide
  have hdescent : baseEnd_479296 < baseStart_479296 := by decide
  rcases family_descends (prefixWord ++ tailWord_479296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479371 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_479371 : Nat := 118140960795 + 479371 * 2 ^ 59
def prefixEnd_479371 : Nat := 4983230072969 + 3 ^ 40 * 479371 * 2
def baseEnd_479371 : Nat := 164098489884366128305279

theorem tailTrace_479371 : CollatzResearch.WordTrace tailWord_479371 prefixEnd_479371 164098489884366128305279 := by
  unfold tailWord_479371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484096746328211893901967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11656064497552141262601311 17484096746328211893901967)
  ·
    refine ⟨26226145119492317840852951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17484096746328211893901967 26226145119492317840852951)
    ·
      refine ⟨39339217679238476761279427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26226145119492317840852951 39339217679238476761279427)
      ·
        refine ⟨59008826518857715141919141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39339217679238476761279427 59008826518857715141919141)
        ·
          refine ⟨11064154972285821589109839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59008826518857715141919141 11064154972285821589109839)
          ·
            refine ⟨16596232458428732383664759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064154972285821589109839 16596232458428732383664759)
            ·
              refine ⟨24894348687643098575497139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596232458428732383664759 24894348687643098575497139)
              ·
                refine ⟨37341523031464647863245709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894348687643098575497139 37341523031464647863245709)
                ·
                  refine ⟨14003071136799242948717141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37341523031464647863245709 14003071136799242948717141)
                  ·
                    refine ⟨164098489884366128305279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14003071136799242948717141 164098489884366128305279)
                    ·
                      rfl

theorem cell22_479371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_479371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479371 prefixEnd_479371 := by exact prefixLift 479371
  have htrace : WordTrace (prefixWord ++ tailWord_479371) baseStart_479371 baseEnd_479371 := by
    simpa [prefixWord, tailWord_479371, baseEnd_479371] using wordTrace_append hprefix tailTrace_479371
  have hstable : (prefixWord ++ tailWord_479371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479371).length < 2 ^ (prefixWord ++ tailWord_479371).sum := by decide
  have hdescent : baseEnd_479371 < baseStart_479371 := by decide
  rcases family_descends (prefixWord ++ tailWord_479371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479388 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_479388 : Nat := 118140960795 + 479388 * 2 ^ 59
def prefixEnd_479388 : Nat := 4983230072969 + 3 ^ 40 * 479388 * 2
def baseEnd_479388 : Nat := 164104309331783750630227

theorem tailTrace_479388 : CollatzResearch.WordTrace tailWord_479388 prefixEnd_479388 164104309331783750630227 := by
  unfold tailWord_479388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742358393633311898635409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11656477858177749198180545 8742358393633311898635409)
  ·
    refine ⟨6556768795224983923976557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8742358393633311898635409 6556768795224983923976557)
    ·
      refine ⟨2458788298209368971491209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6556768795224983923976557 2458788298209368971491209)
      ·
        refine ⟨1844091223657026728618407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458788298209368971491209 1844091223657026728618407)
        ·
          refine ⟨2766136835485540092927611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844091223657026728618407 2766136835485540092927611)
          ·
            refine ⟨4149205253228310139391417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766136835485540092927611 4149205253228310139391417)
            ·
              refine ⟨3111903939921232604543563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149205253228310139391417 3111903939921232604543563)
              ·
                refine ⟨4667855909881848906815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111903939921232604543563 4667855909881848906815345)
                ·
                  refine ⟨3500891932411386680111509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667855909881848906815345 3500891932411386680111509)
                  ·
                    refine ⟨164104309331783750630227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3500891932411386680111509 164104309331783750630227)
                    ·
                      rfl

theorem cell22_479388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_479388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479388 prefixEnd_479388 := by exact prefixLift 479388
  have htrace : WordTrace (prefixWord ++ tailWord_479388) baseStart_479388 baseEnd_479388 := by
    simpa [prefixWord, tailWord_479388, baseEnd_479388] using wordTrace_append hprefix tailTrace_479388
  have hstable : (prefixWord ++ tailWord_479388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479388).length < 2 ^ (prefixWord ++ tailWord_479388).sum := by decide
  have hdescent : baseEnd_479388 < baseStart_479388 := by decide
  rcases family_descends (prefixWord ++ tailWord_479388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479396 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_479396 : Nat := 118140960795 + 479396 * 2 ^ 59
def prefixEnd_479396 : Nat := 4983230072969 + 3 ^ 40 * 479396 * 2
def baseEnd_479396 : Nat := 164107047895274396430203

theorem tailTrace_479396 : CollatzResearch.WordTrace tailWord_479396 prefixEnd_479396 164107047895274396430203 := by
  unfold tailWord_479396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742504285618820581781021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11656672380825094109041361 8742504285618820581781021)
  ·
    refine ⟨3278439107107057718167883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8742504285618820581781021 3278439107107057718167883)
    ·
      refine ⟨4917658660660586577251825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278439107107057718167883 4917658660660586577251825)
      ·
        refine ⟨3688243995495439932938869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4917658660660586577251825 3688243995495439932938869)
        ·
          refine ⟨345772874577697493713019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3688243995495439932938869 345772874577697493713019)
          ·
            refine ⟨518659311866546240569529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345772874577697493713019 518659311866546240569529)
            ·
              refine ⟨388994483899909680427147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518659311866546240569529 388994483899909680427147)
              ·
                refine ⟨583491725849864520640721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388994483899909680427147 583491725849864520640721)
                ·
                  refine ⟨437618794387398390480541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583491725849864520640721 437618794387398390480541)
                  ·
                    refine ⟨164107047895274396430203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437618794387398390480541 164107047895274396430203)
                    ·
                      rfl

theorem cell22_479396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_479396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479396 prefixEnd_479396 := by exact prefixLift 479396
  have htrace : WordTrace (prefixWord ++ tailWord_479396) baseStart_479396 baseEnd_479396 := by
    simpa [prefixWord, tailWord_479396, baseEnd_479396] using wordTrace_append hprefix tailTrace_479396
  have hstable : (prefixWord ++ tailWord_479396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479396).length < 2 ^ (prefixWord ++ tailWord_479396).sum := by decide
  have hdescent : baseEnd_479396 < baseStart_479396 := by decide
  rcases family_descends (prefixWord ++ tailWord_479396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479482 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_479482 : Nat := 118140960795 + 479482 * 2 ^ 59
def prefixEnd_479482 : Nat := 4983230072969 + 3 ^ 40 * 479482 * 2
def baseEnd_479482 : Nat := 54712162484266279593313

theorem tailTrace_479482 : CollatzResearch.WordTrace tailWord_479482 prefixEnd_479482 54712162484266279593313 := by
  unfold tailWord_479482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372036312231519462798175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11658763499284051900795133 4372036312231519462798175)
  ·
    refine ⟨6558054468347279194197263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4372036312231519462798175 6558054468347279194197263)
    ·
      refine ⟨9837081702520918791295895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558054468347279194197263 9837081702520918791295895)
      ·
        refine ⟨14755622553781378186943843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837081702520918791295895 14755622553781378186943843)
        ·
          refine ⟨22133433830672067280415765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755622553781378186943843 22133433830672067280415765)
          ·
            refine ⟨1037504710812753153769489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22133433830672067280415765 1037504710812753153769489)
            ·
              refine ⟨778128533109564865327117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037504710812753153769489 778128533109564865327117)
              ·
                refine ⟨291798199916086824497669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778128533109564865327117 291798199916086824497669)
                ·
                  refine ⟨54712162484266279593313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291798199916086824497669 54712162484266279593313)
                  ·
                    rfl

theorem cell22_479482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_479482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479482 prefixEnd_479482 := by exact prefixLift 479482
  have htrace : WordTrace (prefixWord ++ tailWord_479482) baseStart_479482 baseEnd_479482 := by
    simpa [prefixWord, tailWord_479482, baseEnd_479482] using wordTrace_append hprefix tailTrace_479482
  have hstable : (prefixWord ++ tailWord_479482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479482).length < 2 ^ (prefixWord ++ tailWord_479482).sum := by decide
  have hdescent : baseEnd_479482 < baseStart_479482 := by decide
  rcases family_descends (prefixWord ++ tailWord_479482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479484 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_479484 : Nat := 118140960795 + 479484 * 2 ^ 59
def prefixEnd_479484 : Nat := 4983230072969 + 3 ^ 40 * 479484 * 2
def baseEnd_479484 : Nat := 164137172093671500229933

theorem tailTrace_479484 : CollatzResearch.WordTrace tailWord_479484 prefixEnd_479484 164137172093671500229933 := by
  unfold tailWord_479484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744109097459416096382753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11658812129945888128510337 8744109097459416096382753)
  ·
    refine ⟨6558081823094562072287065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8744109097459416096382753 6558081823094562072287065)
    ·
      refine ⟨4918561367320921554215299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6558081823094562072287065 4918561367320921554215299)
      ·
        refine ⟨7377842050981382331322949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918561367320921554215299 7377842050981382331322949)
        ·
          refine ⟨1383345384559009187123053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7377842050981382331322949 1383345384559009187123053)
          ·
            refine ⟨518754519209628445171145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1383345384559009187123053 518754519209628445171145)
            ·
              refine ⟨389065889407221333878359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518754519209628445171145 389065889407221333878359)
              ·
                refine ⟨583598834110832000817539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389065889407221333878359 583598834110832000817539)
                ·
                  refine ⟨875398251166248001226309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583598834110832000817539 875398251166248001226309)
                  ·
                    refine ⟨164137172093671500229933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875398251166248001226309 164137172093671500229933)
                    ·
                      rfl

theorem cell22_479484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_479484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479484 prefixEnd_479484 := by exact prefixLift 479484
  have htrace : WordTrace (prefixWord ++ tailWord_479484) baseStart_479484 baseEnd_479484 := by
    simpa [prefixWord, tailWord_479484, baseEnd_479484] using wordTrace_append hprefix tailTrace_479484
  have hstable : (prefixWord ++ tailWord_479484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479484).length < 2 ^ (prefixWord ++ tailWord_479484).sum := by decide
  have hdescent : baseEnd_479484 < baseStart_479484 := by decide
  rcases family_descends (prefixWord ++ tailWord_479484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479497 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_479497 : Nat := 118140960795 + 479497 * 2 ^ 59
def prefixEnd_479497 : Nat := 4983230072969 + 3 ^ 40 * 479497 * 2
def baseEnd_479497 : Nat := 164141622259343799654893

theorem tailTrace_479497 : CollatzResearch.WordTrace tailWord_479497 prefixEnd_479497 164141622259343799654893 := by
  unfold tailWord_479497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17488692343871735412988745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11659128229247823608659163 17488692343871735412988745)
  ·
    refine ⟨13116519257903801559741559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17488692343871735412988745 13116519257903801559741559)
    ·
      refine ⟨19674778886855702339612339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116519257903801559741559 19674778886855702339612339)
      ·
        refine ⟨29512168330283553509418509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19674778886855702339612339 29512168330283553509418509)
        ·
          refine ⟨11067063123856332566031941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29512168330283553509418509 11067063123856332566031941)
          ·
            refine ⟨2075074335723062356130989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11067063123856332566031941 2075074335723062356130989)
            ·
              refine ⟨778152875896148383549121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2075074335723062356130989 778152875896148383549121)
              ·
                refine ⟨583614656922111287661841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778152875896148383549121 583614656922111287661841)
                ·
                  refine ⟨437710992691583465746381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583614656922111287661841 437710992691583465746381)
                  ·
                    refine ⟨164141622259343799654893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437710992691583465746381 164141622259343799654893)
                    ·
                      rfl

theorem cell22_479497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_479497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479497 prefixEnd_479497 := by exact prefixLift 479497
  have htrace : WordTrace (prefixWord ++ tailWord_479497) baseStart_479497 baseEnd_479497 := by
    simpa [prefixWord, tailWord_479497, baseEnd_479497] using wordTrace_append hprefix tailTrace_479497
  have hstable : (prefixWord ++ tailWord_479497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479497).length < 2 ^ (prefixWord ++ tailWord_479497).sum := by decide
  have hdescent : baseEnd_479497 < baseStart_479497 := by decide
  rcases family_descends (prefixWord ++ tailWord_479497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479514 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_479514 : Nat := 118140960795 + 479514 * 2 ^ 59
def prefixEnd_479514 : Nat := 4983230072969 + 3 ^ 40 * 479514 * 2
def baseEnd_479514 : Nat := 164147441706761421979841

theorem tailTrace_479514 : CollatzResearch.WordTrace tailWord_479514 prefixEnd_479514 164147441706761421979841 := by
  unfold tailWord_479514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372328096202536829089399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11659541589873431544238397 4372328096202536829089399)
  ·
    refine ⟨6558492144303805243634099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4372328096202536829089399 6558492144303805243634099)
    ·
      refine ⟨9837738216455707865451149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558492144303805243634099 9837738216455707865451149)
      ·
        refine ⟨3689151831170890449544181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9837738216455707865451149 3689151831170890449544181)
        ·
          refine ⟨345857984172270979644767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3689151831170890449544181 345857984172270979644767)
          ·
            refine ⟨518786976258406469467151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345857984172270979644767 518786976258406469467151)
            ·
              refine ⟨778180464387609704200727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518786976258406469467151 778180464387609704200727)
              ·
                refine ⟨1167270696581414556301091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778180464387609704200727 1167270696581414556301091)
                ·
                  refine ⟨1750906044872121834451637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167270696581414556301091 1750906044872121834451637)
                  ·
                    refine ⟨164147441706761421979841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1750906044872121834451637 164147441706761421979841)
                    ·
                      rfl

theorem cell22_479514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_479514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479514 prefixEnd_479514 := by exact prefixLift 479514
  have htrace : WordTrace (prefixWord ++ tailWord_479514) baseStart_479514 baseEnd_479514 := by
    simpa [prefixWord, tailWord_479514, baseEnd_479514] using wordTrace_append hprefix tailTrace_479514
  have hstable : (prefixWord ++ tailWord_479514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479514).length < 2 ^ (prefixWord ++ tailWord_479514).sum := by decide
  have hdescent : baseEnd_479514 < baseStart_479514 := by decide
  rcases family_descends (prefixWord ++ tailWord_479514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479533 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 4]
def baseStart_479533 : Nat := 118140960795 + 479533 * 2 ^ 59
def prefixEnd_479533 : Nat := 4983230072969 + 3 ^ 40 * 479533 * 2
def baseEnd_479533 : Nat := 54717981931683901918261

theorem tailTrace_479533 : CollatzResearch.WordTrace tailWord_479533 prefixEnd_479533 54717981931683901918261 := by
  unfold tailWord_479533
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490005371741313561299253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11660003581160875707532835 17490005371741313561299253)
  ·
    refine ⟨1639688003600748146371805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17490005371741313561299253 1639688003600748146371805)
    ·
      refine ⟨614883001350280554889427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1639688003600748146371805 614883001350280554889427)
      ·
        refine ⟨922324502025420832334141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614883001350280554889427 922324502025420832334141)
        ·
          refine ⟨345871688259532812125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922324502025420832334141 345871688259532812125303)
          ·
            refine ⟨518807532389299218187955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345871688259532812125303 518807532389299218187955)
            ·
              refine ⟨778211298583948827281933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518807532389299218187955 778211298583948827281933)
              ·
                refine ⟨291829236968980810230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778211298583948827281933 291829236968980810230725)
                ·
                  refine ⟨54717981931683901918261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291829236968980810230725 54717981931683901918261)
                  ·
                    rfl

theorem cell22_479533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_479533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479533 prefixEnd_479533 := by exact prefixLift 479533
  have htrace : WordTrace (prefixWord ++ tailWord_479533) baseStart_479533 baseEnd_479533 := by
    simpa [prefixWord, tailWord_479533, baseEnd_479533] using wordTrace_append hprefix tailTrace_479533
  have hstable : (prefixWord ++ tailWord_479533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479533).length < 2 ^ (prefixWord ++ tailWord_479533).sum := by decide
  have hdescent : baseEnd_479533 < baseStart_479533 := by decide
  rcases family_descends (prefixWord ++ tailWord_479533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479570 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_479570 : Nat := 118140960795 + 479570 * 2 ^ 59
def prefixEnd_479570 : Nat := 4983230072969 + 3 ^ 40 * 479570 * 2
def baseEnd_479570 : Nat := 164166611651195942579669

theorem tailTrace_479570 : CollatzResearch.WordTrace tailWord_479570 prefixEnd_479570 164166611651195942579669 := by
  unfold tailWord_479570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372838718151817220099041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11660903248404845920264109 4372838718151817220099041)
  ·
    refine ⟨3279629038613862915074281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4372838718151817220099041 3279629038613862915074281)
    ·
      refine ⟨2459721778960397186305711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3279629038613862915074281 2459721778960397186305711)
      ·
        refine ⟨3689582668440595779458567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459721778960397186305711 3689582668440595779458567)
        ·
          refine ⟨5534374002660893669187851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689582668440595779458567 5534374002660893669187851)
          ·
            refine ⟨8301561003991340503781777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534374002660893669187851 8301561003991340503781777)
            ·
              refine ⟨6226170752993505377836333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301561003991340503781777 6226170752993505377836333)
              ·
                refine ⟨2334814032372564516688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6226170752993505377836333 2334814032372564516688625)
                ·
                  refine ⟨1751110524279423387516469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334814032372564516688625 1751110524279423387516469)
                  ·
                    refine ⟨164166611651195942579669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1751110524279423387516469 164166611651195942579669)
                    ·
                      rfl

theorem cell22_479570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_479570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479570 prefixEnd_479570 := by exact prefixLift 479570
  have htrace : WordTrace (prefixWord ++ tailWord_479570) baseStart_479570 baseEnd_479570 := by
    simpa [prefixWord, tailWord_479570, baseEnd_479570] using wordTrace_append hprefix tailTrace_479570
  have hstable : (prefixWord ++ tailWord_479570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479570).length < 2 ^ (prefixWord ++ tailWord_479570).sum := by decide
  have hdescent : baseEnd_479570 < baseStart_479570 := by decide
  rcases family_descends (prefixWord ++ tailWord_479570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479572 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_479572 : Nat := 118140960795 + 479572 * 2 ^ 59
def prefixEnd_479572 : Nat := 4983230072969 + 3 ^ 40 * 479572 * 2
def baseEnd_479572 : Nat := 54722432097356201343221

theorem tailTrace_479572 : CollatzResearch.WordTrace tailWord_479572 prefixEnd_479572 54722432097356201343221 := by
  unfold tailWord_479572
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745713909300011610984485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11660951879066682147979313 8745713909300011610984485)
  ·
    refine ⟨1639821357993752177059591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8745713909300011610984485 1639821357993752177059591)
    ·
      refine ⟨2459732036990628265589387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639821357993752177059591 2459732036990628265589387)
      ·
        refine ⟨3689598055485942398384081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459732036990628265589387 3689598055485942398384081)
        ·
          refine ⟨2767198541614456798788061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689598055485942398384081 2767198541614456798788061)
          ·
            refine ⟨1037699453105421299545523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2767198541614456798788061 1037699453105421299545523)
            ·
              refine ⟨1556549179658131949318285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037699453105421299545523 1556549179658131949318285)
              ·
                refine ⟨583705942371799480994357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556549179658131949318285 583705942371799480994357)
                ·
                  refine ⟨54722432097356201343221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 583705942371799480994357 54722432097356201343221)
                  ·
                    rfl

theorem cell22_479572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_479572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479572 prefixEnd_479572 := by exact prefixLift 479572
  have htrace : WordTrace (prefixWord ++ tailWord_479572) baseStart_479572 baseEnd_479572 := by
    simpa [prefixWord, tailWord_479572, baseEnd_479572] using wordTrace_append hprefix tailTrace_479572
  have hstable : (prefixWord ++ tailWord_479572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479572).length < 2 ^ (prefixWord ++ tailWord_479572).sum := by decide
  have hdescent : baseEnd_479572 < baseStart_479572 := by decide
  rcases family_descends (prefixWord ++ tailWord_479572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479606 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_479606 : Nat := 118140960795 + 479606 * 2 ^ 59
def prefixEnd_479606 : Nat := 4983230072969 + 3 ^ 40 * 479606 * 2
def baseEnd_479606 : Nat := 54726311728967949559853

theorem tailTrace_479606 : CollatzResearch.WordTrace tailWord_479606 prefixEnd_479606 54726311728967949559853 := by
  unfold tailWord_479606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093291743779802939294167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11661778600317898019137781 1093291743779802939294167)
  ·
    refine ⟨1639937615669704408941251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093291743779802939294167 1639937615669704408941251)
    ·
      refine ⟨2459906423504556613411877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639937615669704408941251 2459906423504556613411877)
      ·
        refine ⟨461232454407104365014727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2459906423504556613411877 461232454407104365014727)
        ·
          refine ⟨691848681610656547522091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461232454407104365014727 691848681610656547522091)
          ·
            refine ⟨1037773022415984821283137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691848681610656547522091 1037773022415984821283137)
            ·
              refine ⟨778329766811988615962353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037773022415984821283137 778329766811988615962353)
              ·
                refine ⟨583747325108991461971765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778329766811988615962353 583747325108991461971765)
                ·
                  refine ⟨54726311728967949559853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 583747325108991461971765 54726311728967949559853)
                  ·
                    rfl

theorem cell22_479606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_479606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479606 prefixEnd_479606 := by exact prefixLift 479606
  have htrace : WordTrace (prefixWord ++ tailWord_479606) baseStart_479606 baseEnd_479606 := by
    simpa [prefixWord, tailWord_479606, baseEnd_479606] using wordTrace_append hprefix tailTrace_479606
  have hstable : (prefixWord ++ tailWord_479606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479606).length < 2 ^ (prefixWord ++ tailWord_479606).sum := by decide
  have hdescent : baseEnd_479606 < baseStart_479606 := by decide
  rcases family_descends (prefixWord ++ tailWord_479606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479711 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 1, 3]
def baseStart_479711 : Nat := 118140960795 + 479711 * 2 ^ 59
def prefixEnd_479711 : Nat := 4983230072969 + 3 ^ 40 * 479711 * 2
def baseEnd_479711 : Nat := 164214878832718574804237

theorem tailTrace_479711 : CollatzResearch.WordTrace tailWord_479711 prefixEnd_479711 164214878832718574804237 := by
  unfold tailWord_479711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496497565096449961278987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11664331710064299974185991 17496497565096449961278987)
  ·
    refine ⟨26244746347644674941918481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17496497565096449961278987 26244746347644674941918481)
    ·
      refine ⟨19683559760733506206438861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26244746347644674941918481 19683559760733506206438861)
      ·
        refine ⟨7381334910275064827414573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19683559760733506206438861 7381334910275064827414573)
        ·
          refine ⟨2768000591353149310280465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7381334910275064827414573 2768000591353149310280465)
          ·
            refine ⟨2076000443514861982710349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768000591353149310280465 2076000443514861982710349)
            ·
              refine ⟨778500166318073243516381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2076000443514861982710349 778500166318073243516381)
              ·
                refine ⟨291937562369277466318643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778500166318073243516381 291937562369277466318643)
                ·
                  refine ⟨437906343553916199477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291937562369277466318643 437906343553916199477965)
                  ·
                    refine ⟨164214878832718574804237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437906343553916199477965 164214878832718574804237)
                    ·
                      rfl

theorem cell22_479711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_479711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479711 prefixEnd_479711 := by exact prefixLift 479711
  have htrace : WordTrace (prefixWord ++ tailWord_479711) baseStart_479711 baseEnd_479711 := by
    simpa [prefixWord, tailWord_479711, baseEnd_479711] using wordTrace_append hprefix tailTrace_479711
  have hstable : (prefixWord ++ tailWord_479711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479711).length < 2 ^ (prefixWord ++ tailWord_479711).sum := by decide
  have hdescent : baseEnd_479711 < baseStart_479711 := by decide
  rcases family_descends (prefixWord ++ tailWord_479711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479786 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_479786 : Nat := 118140960795 + 479786 * 2 ^ 59
def prefixEnd_479786 : Nat := 4983230072969 + 3 ^ 40 * 479786 * 2
def baseEnd_479786 : Nat := 54746850955147793059669

theorem tailTrace_479786 : CollatzResearch.WordTrace tailWord_479786 prefixEnd_479786 54746850955147793059669 := by
  unfold tailWord_479786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374808259956184442564803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11666155359883158513506141 4374808259956184442564803)
  ·
    refine ⟨6562212389934276663847205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4374808259956184442564803 6562212389934276663847205)
    ·
      refine ⟨1230414823112676874471351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6562212389934276663847205 1230414823112676874471351)
      ·
        refine ⟨1845622234669015311707027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230414823112676874471351 1845622234669015311707027)
        ·
          refine ⟨2768433352003522967560541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845622234669015311707027 2768433352003522967560541)
          ·
            refine ⟨1038162507001321112835203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2768433352003522967560541 1038162507001321112835203)
            ·
              refine ⟨1557243760501981669252805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038162507001321112835203 1557243760501981669252805)
              ·
                refine ⟨291983205094121562984901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557243760501981669252805 291983205094121562984901)
                ·
                  refine ⟨54746850955147793059669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291983205094121562984901 54746850955147793059669)
                  ·
                    rfl

theorem cell22_479786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_479786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_479786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_479786 prefixEnd_479786 := by exact prefixLift 479786
  have htrace : WordTrace (prefixWord ++ tailWord_479786) baseStart_479786 baseEnd_479786 := by
    simpa [prefixWord, tailWord_479786, baseEnd_479786] using wordTrace_append hprefix tailTrace_479786
  have hstable : (prefixWord ++ tailWord_479786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479786).length < 2 ^ (prefixWord ++ tailWord_479786).sum := by decide
  have hdescent : baseEnd_479786 < baseStart_479786 := by decide
  rcases family_descends (prefixWord ++ tailWord_479786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480009 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_480009 : Nat := 118140960795 + 480009 * 2 ^ 59
def prefixEnd_480009 : Nat := 4983230072969 + 3 ^ 40 * 480009 * 2
def baseEnd_480009 : Nat := 164316890322745130853323

theorem tailTrace_480009 : CollatzResearch.WordTrace tailWord_480009 prefixEnd_480009 164316890322745130853323 := by
  unfold tailWord_480009
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507366518016846855627081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11671577678677897903751387 17507366518016846855627081)
  ·
    refine ⟨13130524888512635141720311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17507366518016846855627081 13130524888512635141720311)
    ·
      refine ⟨19695787332768952712580467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13130524888512635141720311 19695787332768952712580467)
      ·
        refine ⟨29543680999153429068870701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19695787332768952712580467 29543680999153429068870701)
        ·
          refine ⟨11078880374682535900826513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29543680999153429068870701 11078880374682535900826513)
          ·
            refine ⟨8309160281011901925619885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11078880374682535900826513 8309160281011901925619885)
            ·
              refine ⟨3115935105379463222107457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8309160281011901925619885 3115935105379463222107457)
              ·
                refine ⟨2336951329034597416580593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115935105379463222107457 2336951329034597416580593)
                ·
                  refine ⟨1752713496775948062435445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336951329034597416580593 1752713496775948062435445)
                  ·
                    refine ⟨164316890322745130853323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1752713496775948062435445 164316890322745130853323)
                    ·
                      rfl

theorem cell22_480009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_480009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480009 prefixEnd_480009 := by exact prefixLift 480009
  have htrace : WordTrace (prefixWord ++ tailWord_480009) baseStart_480009 baseEnd_480009 := by
    simpa [prefixWord, tailWord_480009, baseEnd_480009] using wordTrace_append hprefix tailTrace_480009
  have hstable : (prefixWord ++ tailWord_480009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480009).length < 2 ^ (prefixWord ++ tailWord_480009).sum := by decide
  have hdescent : baseEnd_480009 < baseStart_480009 := by decide
  rcases family_descends (prefixWord ++ tailWord_480009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480028 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_480028 : Nat := 118140960795 + 480028 * 2 ^ 59
def prefixEnd_480028 : Nat := 4983230072969 + 3 ^ 40 * 480028 * 2
def baseEnd_480028 : Nat := 54774464803678471542755

theorem tailTrace_480028 : CollatzResearch.WordTrace tailWord_480028 prefixEnd_480028 54774464803678471542755 := by
  unfold tailWord_480028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754029752474006550284369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11672039669965342067045825 8754029752474006550284369)
  ·
    refine ⟨6565522314355504912713277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8754029752474006550284369 6565522314355504912713277)
    ·
      refine ⟨2462070867883314342267479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6565522314355504912713277 2462070867883314342267479)
      ·
        refine ⟨3693106301824971513401219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462070867883314342267479 3693106301824971513401219)
        ·
          refine ⟨5539659452737457270101829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693106301824971513401219 5539659452737457270101829)
          ·
            refine ⟨1038686147388273238144093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5539659452737457270101829 1038686147388273238144093)
            ·
              refine ⟨389507305270602464304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038686147388273238144093 389507305270602464304035)
              ·
                refine ⟨584260957905903696456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389507305270602464304035 584260957905903696456053)
                ·
                  refine ⟨54774464803678471542755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584260957905903696456053 54774464803678471542755)
                  ·
                    rfl

theorem cell22_480028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_480028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480028 prefixEnd_480028 := by exact prefixLift 480028
  have htrace : WordTrace (prefixWord ++ tailWord_480028) baseStart_480028 baseEnd_480028 := by
    simpa [prefixWord, tailWord_480028, baseEnd_480028] using wordTrace_append hprefix tailTrace_480028
  have hstable : (prefixWord ++ tailWord_480028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480028).length < 2 ^ (prefixWord ++ tailWord_480028).sum := by decide
  have hdescent : baseEnd_480028 < baseStart_480028 := by decide
  rcases family_descends (prefixWord ++ tailWord_480028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480069 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_480069 : Nat := 118140960795 + 480069 * 2 ^ 59
def prefixEnd_480069 : Nat := 4983230072969 + 3 ^ 40 * 480069 * 2
def baseEnd_480069 : Nat := 164337429548924974353139

theorem tailTrace_480069 : CollatzResearch.WordTrace tailWord_480069 prefixEnd_480069 164337429548924974353139 := by
  unfold tailWord_480069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509554897799477102811261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673036598532984735207507 17509554897799477102811261)
  ·
    refine ⟨6566083086674803913554223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17509554897799477102811261 6566083086674803913554223)
    ·
      refine ⟨9849124630012205870331335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566083086674803913554223 9849124630012205870331335)
      ·
        refine ⟨14773686945018308805497003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849124630012205870331335 14773686945018308805497003)
        ·
          refine ⟨22160530417527463208245505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773686945018308805497003 22160530417527463208245505)
          ·
            refine ⟨16620397813145597406184129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22160530417527463208245505 16620397813145597406184129)
            ·
              refine ⟨12465298359859198054638097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16620397813145597406184129 12465298359859198054638097)
              ·
                refine ⟨9348973769894398540978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12465298359859198054638097 9348973769894398540978573)
                ·
                  refine ⟨3505865163710399452866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9348973769894398540978573 3505865163710399452866965)
                  ·
                    refine ⟨164337429548924974353139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3505865163710399452866965 164337429548924974353139)
                    ·
                      rfl

theorem cell22_480069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_480069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480069 prefixEnd_480069 := by exact prefixLift 480069
  have htrace : WordTrace (prefixWord ++ tailWord_480069) baseStart_480069 baseEnd_480069 := by
    simpa [prefixWord, tailWord_480069, baseEnd_480069] using wordTrace_append hprefix tailTrace_480069
  have hstable : (prefixWord ++ tailWord_480069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480069).length < 2 ^ (prefixWord ++ tailWord_480069).sum := by decide
  have hdescent : baseEnd_480069 < baseStart_480069 := by decide
  rcases family_descends (prefixWord ++ tailWord_480069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480103 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_480103 : Nat := 118140960795 + 480103 * 2 ^ 59
def prefixEnd_480103 : Nat := 4983230072969 + 3 ^ 40 * 480103 * 2
def baseEnd_480103 : Nat := 164349068443760219003035

theorem tailTrace_480103 : CollatzResearch.WordTrace tailWord_480103 prefixEnd_480103 164349068443760219003035 := by
  unfold tailWord_480103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510794979676300909548963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673863319784200606365975 17510794979676300909548963)
  ·
    refine ⟨26266192469514451364323445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17510794979676300909548963 26266192469514451364323445)
    ·
      refine ⟨2462455544016979815405323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26266192469514451364323445 2462455544016979815405323)
      ·
        refine ⟨3693683316025469723107985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462455544016979815405323 3693683316025469723107985)
        ·
          refine ⟨2770262487019102292330989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693683316025469723107985 2770262487019102292330989)
          ·
            refine ⟨1038848432632163359624121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2770262487019102292330989 1038848432632163359624121)
            ·
              refine ⟨779136324474122519718091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038848432632163359624121 779136324474122519718091)
              ·
                refine ⟨1168704486711183779577137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779136324474122519718091 1168704486711183779577137)
                ·
                  refine ⟨876528365033387834682853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168704486711183779577137 876528365033387834682853)
                  ·
                    refine ⟨164349068443760219003035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876528365033387834682853 164349068443760219003035)
                    ·
                      rfl

theorem cell22_480103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_480103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480103 prefixEnd_480103 := by exact prefixLift 480103
  have htrace : WordTrace (prefixWord ++ tailWord_480103) baseStart_480103 baseEnd_480103 := by
    simpa [prefixWord, tailWord_480103, baseEnd_480103] using wordTrace_append hprefix tailTrace_480103
  have hstable : (prefixWord ++ tailWord_480103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480103).length < 2 ^ (prefixWord ++ tailWord_480103).sum := by decide
  have hdescent : baseEnd_480103 < baseStart_480103 := by decide
  rcases family_descends (prefixWord ++ tailWord_480103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480180 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_480180 : Nat := 118140960795 + 480180 * 2 ^ 59
def prefixEnd_480180 : Nat := 4983230072969 + 3 ^ 40 * 480180 * 2
def baseEnd_480180 : Nat := 54791809039119228275933

theorem tailTrace_480180 : CollatzResearch.WordTrace tailWord_480180 prefixEnd_480180 54791809039119228275933 := by
  unfold tailWord_480180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756801700198671530050997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11675735600264895373401329 8756801700198671530050997)
  ·
    refine ⟨820950159393625455942281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8756801700198671530050997 820950159393625455942281)
    ·
      refine ⟨615712619545219091956711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 820950159393625455942281 615712619545219091956711)
      ·
        refine ⟨923568929317828637935067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615712619545219091956711 923568929317828637935067)
        ·
          refine ⟨1385353393976742956902601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923568929317828637935067 1385353393976742956902601)
          ·
            refine ⟨1039015045482557217676951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385353393976742956902601 1039015045482557217676951)
            ·
              refine ⟨1558522568223835826515427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039015045482557217676951 1558522568223835826515427)
              ·
                refine ⟨2337783852335753739773141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558522568223835826515427 2337783852335753739773141)
                ·
                  refine ⟨54791809039119228275933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2337783852335753739773141 54791809039119228275933)
                  ·
                    rfl

theorem cell22_480180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_480180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480180 prefixEnd_480180 := by exact prefixLift 480180
  have htrace : WordTrace (prefixWord ++ tailWord_480180) baseStart_480180 baseEnd_480180 := by
    simpa [prefixWord, tailWord_480180, baseEnd_480180] using wordTrace_append hprefix tailTrace_480180
  have hstable : (prefixWord ++ tailWord_480180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480180).length < 2 ^ (prefixWord ++ tailWord_480180).sum := by decide
  have hdescent : baseEnd_480180 < baseStart_480180 := by decide
  rcases family_descends (prefixWord ++ tailWord_480180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480210 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_480210 : Nat := 118140960795 + 480210 * 2 ^ 59
def prefixEnd_480210 : Nat := 4983230072969 + 3 ^ 40 * 480210 * 2
def baseEnd_480210 : Nat := 164385696730447606577707

theorem tailTrace_480210 : CollatzResearch.WordTrace tailWord_480210 prefixEnd_480210 164385696730447606577707 := by
  unfold tailWord_480210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378674397572164545923521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11676465060192438789129389 4378674397572164545923521)
  ·
    refine ⟨3284005798179123409442641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4378674397572164545923521 3284005798179123409442641)
    ·
      refine ⟨2463004348634342557081981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3284005798179123409442641 2463004348634342557081981)
      ·
        refine ⟨923626630737878458905743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2463004348634342557081981 923626630737878458905743)
        ·
          refine ⟨1385439946106817688358615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923626630737878458905743 1385439946106817688358615)
          ·
            refine ⟨2078159919160226532537923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385439946106817688358615 2078159919160226532537923)
            ·
              refine ⟨3117239878740339798806885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078159919160226532537923 3117239878740339798806885)
              ·
                refine ⟨584482477263813712276291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3117239878740339798806885 584482477263813712276291)
                ·
                  refine ⟨876723715895720568414437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584482477263813712276291 876723715895720568414437)
                  ·
                    refine ⟨164385696730447606577707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876723715895720568414437 164385696730447606577707)
                    ·
                      rfl

theorem cell22_480210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_480210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480210 prefixEnd_480210 := by exact prefixLift 480210
  have htrace : WordTrace (prefixWord ++ tailWord_480210) baseStart_480210 baseEnd_480210 := by
    simpa [prefixWord, tailWord_480210, baseEnd_480210] using wordTrace_append hprefix tailTrace_480210
  have hstable : (prefixWord ++ tailWord_480210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480210).length < 2 ^ (prefixWord ++ tailWord_480210).sum := by decide
  have hdescent : baseEnd_480210 < baseStart_480210 := by decide
  rcases family_descends (prefixWord ++ tailWord_480210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480242 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_480242 : Nat := 118140960795 + 480242 * 2 ^ 59
def prefixEnd_480242 : Nat := 4983230072969 + 3 ^ 40 * 480242 * 2
def baseEnd_480242 : Nat := 54798883661470063259203

theorem tailTrace_480242 : CollatzResearch.WordTrace tailWord_480242 prefixEnd_480242 54798883661470063259203 := by
  unfold tailWord_480242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378966181543181912214745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11677243150781818432572653 4378966181543181912214745)
  ·
    refine ⟨3284224636157386434161059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4378966181543181912214745 3284224636157386434161059)
    ·
      refine ⟨4926336954236079651241589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284224636157386434161059 4926336954236079651241589)
      ·
        refine ⟨461844089459632467303899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4926336954236079651241589 461844089459632467303899)
        ·
          refine ⟨692766134189448700955849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461844089459632467303899 692766134189448700955849)
          ·
            refine ⟨519574600642086525716887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692766134189448700955849 519574600642086525716887)
            ·
              refine ⟨779361900963129788575331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519574600642086525716887 779361900963129788575331)
              ·
                refine ⟨1169042851444694682862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779361900963129788575331 1169042851444694682862997)
                ·
                  refine ⟨54798883661470063259203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1169042851444694682862997 54798883661470063259203)
                  ·
                    rfl

theorem cell22_480242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_480242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480242 prefixEnd_480242 := by exact prefixLift 480242
  have htrace : WordTrace (prefixWord ++ tailWord_480242) baseStart_480242 baseEnd_480242 := by
    simpa [prefixWord, tailWord_480242, baseEnd_480242] using wordTrace_append hprefix tailTrace_480242
  have hstable : (prefixWord ++ tailWord_480242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480242).length < 2 ^ (prefixWord ++ tailWord_480242).sum := by decide
  have hdescent : baseEnd_480242 < baseStart_480242 := by decide
  rcases family_descends (prefixWord ++ tailWord_480242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480257 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_480257 : Nat := 118140960795 + 480257 * 2 ^ 59
def prefixEnd_480257 : Nat := 4983230072969 + 3 ^ 40 * 480257 * 2
def baseEnd_480257 : Nat := 164401785790955150652563

theorem tailTrace_480257 : CollatzResearch.WordTrace tailWord_480257 prefixEnd_480257 164401785790955150652563 := by
  unfold tailWord_480257
  simp only [CollatzResearch.WordTrace]
  refine ⟨17516411821118385210655025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11677607880745590140436683 17516411821118385210655025)
  ·
    refine ⟨13137308865838788907991269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17516411821118385210655025 13137308865838788907991269)
    ·
      refine ⟨2463245412344772920248363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13137308865838788907991269 2463245412344772920248363)
      ·
        refine ⟨3694868118517159380372545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463245412344772920248363 3694868118517159380372545)
        ·
          refine ⟨2771151088887869535279409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694868118517159380372545 2771151088887869535279409)
          ·
            refine ⟨2078363316665902151459557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771151088887869535279409 2078363316665902151459557)
            ·
              refine ⟨389693121874856653398667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2078363316665902151459557 389693121874856653398667)
              ·
                refine ⟨584539682812284980098001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389693121874856653398667 584539682812284980098001)
                ·
                  refine ⟨438404762109213735073501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584539682812284980098001 438404762109213735073501)
                  ·
                    refine ⟨164401785790955150652563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438404762109213735073501 164401785790955150652563)
                    ·
                      rfl

theorem cell22_480257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_480257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480257 prefixEnd_480257 := by exact prefixLift 480257
  have htrace : WordTrace (prefixWord ++ tailWord_480257) baseStart_480257 baseEnd_480257 := by
    simpa [prefixWord, tailWord_480257, baseEnd_480257] using wordTrace_append hprefix tailTrace_480257
  have hstable : (prefixWord ++ tailWord_480257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480257).length < 2 ^ (prefixWord ++ tailWord_480257).sum := by decide
  have hdescent : baseEnd_480257 < baseStart_480257 := by decide
  rcases family_descends (prefixWord ++ tailWord_480257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480274 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_480274 : Nat := 118140960795 + 480274 * 2 ^ 59
def prefixEnd_480274 : Nat := 4983230072969 + 3 ^ 40 * 480274 * 2
def baseEnd_480274 : Nat := 164407605238372772977511

theorem tailTrace_480274 : CollatzResearch.WordTrace tailWord_480274 prefixEnd_480274 164407605238372772977511 := by
  unfold tailWord_480274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379257965514199278505969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11678021241371198076015917 4379257965514199278505969)
  ·
    refine ⟨3284443474135649458879477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379257965514199278505969 3284443474135649458879477)
    ·
      refine ⟨307916575700217136769951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3284443474135649458879477 307916575700217136769951)
      ·
        refine ⟨461874863550325705154927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307916575700217136769951 461874863550325705154927)
        ·
          refine ⟨692812295325488557732391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461874863550325705154927 692812295325488557732391)
          ·
            refine ⟨1039218442988232836598587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692812295325488557732391 1039218442988232836598587)
            ·
              refine ⟨1558827664482349254897881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039218442988232836598587 1558827664482349254897881)
              ·
                refine ⟨1169120748361761941173411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558827664482349254897881 1169120748361761941173411)
                ·
                  refine ⟨1753681122542642911760117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169120748361761941173411 1753681122542642911760117)
                  ·
                    refine ⟨164407605238372772977511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1753681122542642911760117 164407605238372772977511)
                    ·
                      rfl

theorem cell22_480274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_480274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480274 prefixEnd_480274 := by exact prefixLift 480274
  have htrace : WordTrace (prefixWord ++ tailWord_480274) baseStart_480274 baseEnd_480274 := by
    simpa [prefixWord, tailWord_480274, baseEnd_480274] using wordTrace_append hprefix tailTrace_480274
  have hstable : (prefixWord ++ tailWord_480274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480274).length < 2 ^ (prefixWord ++ tailWord_480274).sum := by decide
  have hdescent : baseEnd_480274 < baseStart_480274 := by decide
  rcases family_descends (prefixWord ++ tailWord_480274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480281 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 9]
def baseStart_480281 : Nat := 118140960795 + 480281 * 2 ^ 59
def prefixEnd_480281 : Nat := 4983230072969 + 3 ^ 40 * 480281 * 2
def baseEnd_480281 : Nat := 54803333827142362684163

theorem tailTrace_480281 : CollatzResearch.WordTrace tailWord_480281 prefixEnd_480281 54803333827142362684163 := by
  unfold tailWord_480281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17517287173031437309528697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11678191448687624873019131 17517287173031437309528697)
  ·
    refine ⟨13137965379773577982146523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17517287173031437309528697 13137965379773577982146523)
    ·
      refine ⟨19706948069660366973219785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13137965379773577982146523 19706948069660366973219785)
      ·
        refine ⟨14780211052245275229914839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19706948069660366973219785 14780211052245275229914839)
        ·
          refine ⟨22170316578367912844872259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14780211052245275229914839 22170316578367912844872259)
          ·
            refine ⟨33255474867551869267308389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22170316578367912844872259 33255474867551869267308389)
            ·
              refine ⟨6235401537665975487620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33255474867551869267308389 6235401537665975487620323)
              ·
                refine ⟨9353102306498963231430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6235401537665975487620323 9353102306498963231430485)
                ·
                  refine ⟨54803333827142362684163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9353102306498963231430485 54803333827142362684163)
                  ·
                    rfl

theorem cell22_480281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_480281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480281 prefixEnd_480281 := by exact prefixLift 480281
  have htrace : WordTrace (prefixWord ++ tailWord_480281) baseStart_480281 baseEnd_480281 := by
    simpa [prefixWord, tailWord_480281, baseEnd_480281] using wordTrace_append hprefix tailTrace_480281
  have hstable : (prefixWord ++ tailWord_480281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480281).length < 2 ^ (prefixWord ++ tailWord_480281).sum := by decide
  have hdescent : baseEnd_480281 < baseStart_480281 := by decide
  rcases family_descends (prefixWord ++ tailWord_480281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480313 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_480313 : Nat := 118140960795 + 480313 * 2 ^ 59
def prefixEnd_480313 : Nat := 4983230072969 + 3 ^ 40 * 480313 * 2
def baseEnd_480313 : Nat := 164420955735389671252391

theorem tailTrace_480313 : CollatzResearch.WordTrace tailWord_480313 prefixEnd_480313 164420955735389671252391 := by
  unfold tailWord_480313
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518454308915506774693593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11678969539277004516462395 17518454308915506774693593)
  ·
    refine ⟨13138840731686630081020195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17518454308915506774693593 13138840731686630081020195)
    ·
      refine ⟨19708261097529945121530293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138840731686630081020195 19708261097529945121530293)
      ·
        refine ⟨1847649477893432355143465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19708261097529945121530293 1847649477893432355143465)
        ·
          refine ⟨1385737108420074266357599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847649477893432355143465 1385737108420074266357599)
          ·
            refine ⟨2078605662630111399536399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385737108420074266357599 2078605662630111399536399)
            ·
              refine ⟨3117908493945167099304599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078605662630111399536399 3117908493945167099304599)
              ·
                refine ⟨4676862740917750648956899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117908493945167099304599 4676862740917750648956899)
                ·
                  refine ⟨7015294111376625973435349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676862740917750648956899 7015294111376625973435349)
                  ·
                    refine ⟨164420955735389671252391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7015294111376625973435349 164420955735389671252391)
                    ·
                      rfl

theorem cell22_480313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_480313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480313 prefixEnd_480313 := by exact prefixLift 480313
  have htrace : WordTrace (prefixWord ++ tailWord_480313) baseStart_480313 baseEnd_480313 := by
    simpa [prefixWord, tailWord_480313, baseEnd_480313] using wordTrace_append hprefix tailTrace_480313
  have hstable : (prefixWord ++ tailWord_480313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480313).length < 2 ^ (prefixWord ++ tailWord_480313).sum := by decide
  have hdescent : baseEnd_480313 < baseStart_480313 := by decide
  rcases family_descends (prefixWord ++ tailWord_480313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480328 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_480328 : Nat := 118140960795 + 480328 * 2 ^ 59
def prefixEnd_480328 : Nat := 4983230072969 + 3 ^ 40 * 480328 * 2
def baseEnd_480328 : Nat := 164426090541934632127345

theorem tailTrace_480328 : CollatzResearch.WordTrace tailWord_480328 prefixEnd_480328 164426090541934632127345 := by
  unfold tailWord_480328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759500701930582168244819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11679334269240776224326425 8759500701930582168244819)
  ·
    refine ⟨13139251052895873252367229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8759500701930582168244819 13139251052895873252367229)
    ·
      refine ⟨4927219144835952469637711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13139251052895873252367229 4927219144835952469637711)
      ·
        refine ⟨7390828717253928704456567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927219144835952469637711 7390828717253928704456567)
        ·
          refine ⟨11086243075880893056684851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390828717253928704456567 11086243075880893056684851)
          ·
            refine ⟨16629364613821339585027277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086243075880893056684851 16629364613821339585027277)
            ·
              refine ⟨6236011730183002344385229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16629364613821339585027277 6236011730183002344385229)
              ·
                refine ⟨2338504398818625879144461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6236011730183002344385229 2338504398818625879144461)
                ·
                  refine ⟨876939149556984704679173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2338504398818625879144461 876939149556984704679173)
                  ·
                    refine ⟨164426090541934632127345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 876939149556984704679173 164426090541934632127345)
                    ·
                      rfl

theorem cell22_480328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_480328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480328 prefixEnd_480328 := by exact prefixLift 480328
  have htrace : WordTrace (prefixWord ++ tailWord_480328) baseStart_480328 baseEnd_480328 := by
    simpa [prefixWord, tailWord_480328, baseEnd_480328] using wordTrace_append hprefix tailTrace_480328
  have hstable : (prefixWord ++ tailWord_480328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480328).length < 2 ^ (prefixWord ++ tailWord_480328).sum := by decide
  have hdescent : baseEnd_480328 < baseStart_480328 := by decide
  rcases family_descends (prefixWord ++ tailWord_480328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480349 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 5]
def baseStart_480349 : Nat := 118140960795 + 480349 * 2 ^ 59
def prefixEnd_480349 : Nat := 4983230072969 + 3 ^ 40 * 480349 * 2
def baseEnd_480349 : Nat := 54811093090365859117427

theorem tailTrace_480349 : CollatzResearch.WordTrace tailWord_480349 prefixEnd_480349 54811093090365859117427 := by
  unfold tailWord_480349
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519767336785084923004101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11679844891190056615336067 17519767336785084923004101)
  ·
    refine ⟨3284956375647203423063269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17519767336785084923004101 3284956375647203423063269)
    ·
      refine ⟨615929320433850641824363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3284956375647203423063269 615929320433850641824363)
      ·
        refine ⟨923893980650775962736545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615929320433850641824363 923893980650775962736545)
        ·
          refine ⟨692920485488081972052409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923893980650775962736545 692920485488081972052409)
          ·
            refine ⟨519690364116061479039307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692920485488081972052409 519690364116061479039307)
            ·
              refine ⟨779535546174092218558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519690364116061479039307 779535546174092218558961)
              ·
                refine ⟨584651659630569163919221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779535546174092218558961 584651659630569163919221)
                ·
                  refine ⟨54811093090365859117427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584651659630569163919221 54811093090365859117427)
                  ·
                    rfl

theorem cell22_480349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_480349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480349 prefixEnd_480349 := by exact prefixLift 480349
  have htrace : WordTrace (prefixWord ++ tailWord_480349) baseStart_480349 baseEnd_480349 := by
    simpa [prefixWord, tailWord_480349, baseEnd_480349] using wordTrace_append hprefix tailTrace_480349
  have hstable : (prefixWord ++ tailWord_480349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480349).length < 2 ^ (prefixWord ++ tailWord_480349).sum := by decide
  have hdescent : baseEnd_480349 < baseStart_480349 := by decide
  rcases family_descends (prefixWord ++ tailWord_480349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480426 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_480426 : Nat := 118140960795 + 480426 * 2 ^ 59
def prefixEnd_480426 : Nat := 4983230072969 + 3 ^ 40 * 480426 * 2
def baseEnd_480426 : Nat := 164459637944695043177045

theorem tailTrace_480426 : CollatzResearch.WordTrace tailWord_480426 prefixEnd_480426 164459637944695043177045 := by
  unfold tailWord_480426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380643939376531768389283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11681717171670751382371421 4380643939376531768389283)
  ·
    refine ⟨6570965909064797652583925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380643939376531768389283 6570965909064797652583925)
    ·
      refine ⟨616028053974824779929743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6570965909064797652583925 616028053974824779929743)
      ·
        refine ⟨924042080962237169894615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616028053974824779929743 924042080962237169894615)
        ·
          refine ⟨1386063121443355754841923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924042080962237169894615 1386063121443355754841923)
          ·
            refine ⟨2079094682165033632262885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386063121443355754841923 2079094682165033632262885)
            ·
              refine ⟨389830252905943806049291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2079094682165033632262885 389830252905943806049291)
              ·
                refine ⟨584745379358915709073937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389830252905943806049291 584745379358915709073937)
                ·
                  refine ⟨438559034519186781805453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584745379358915709073937 438559034519186781805453)
                  ·
                    refine ⟨164459637944695043177045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438559034519186781805453 164459637944695043177045)
                    ·
                      rfl

theorem cell22_480426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_480426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480426 prefixEnd_480426 := by exact prefixLift 480426
  have htrace : WordTrace (prefixWord ++ tailWord_480426) baseStart_480426 baseEnd_480426 := by
    simpa [prefixWord, tailWord_480426, baseEnd_480426] using wordTrace_append hprefix tailTrace_480426
  have hstable : (prefixWord ++ tailWord_480426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480426).length < 2 ^ (prefixWord ++ tailWord_480426).sum := by decide
  have hdescent : baseEnd_480426 < baseStart_480426 := by decide
  rcases family_descends (prefixWord ++ tailWord_480426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480480 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_480480 : Nat := 118140960795 + 480480 * 2 ^ 59
def prefixEnd_480480 : Nat := 4983230072969 + 3 ^ 40 * 480480 * 2
def baseEnd_480480 : Nat := 164478123248256902326879

theorem tailTrace_480480 : CollatzResearch.WordTrace tailWord_480480 prefixEnd_480480 164478123248256902326879 := by
  unfold tailWord_480480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762272649655247148011447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11683030199540329530681929 8762272649655247148011447)
  ·
    refine ⟨13143408974482870722017171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762272649655247148011447 13143408974482870722017171)
    ·
      refine ⟨19715113461724306083025757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13143408974482870722017171 19715113461724306083025757)
      ·
        refine ⟨7393167548146614781134659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19715113461724306083025757 7393167548146614781134659)
        ·
          refine ⟨11089751322219922171701989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393167548146614781134659 11089751322219922171701989)
          ·
            refine ⟨2079328372916235407194123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11089751322219922171701989 2079328372916235407194123)
            ·
              refine ⟨3118992559374353110791185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079328372916235407194123 3118992559374353110791185)
              ·
                refine ⟨2339244419530764833093389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118992559374353110791185 2339244419530764833093389)
                ·
                  refine ⟨877216657324036812410021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2339244419530764833093389 877216657324036812410021)
                  ·
                    refine ⟨164478123248256902326879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877216657324036812410021 164478123248256902326879)
                    ·
                      rfl

theorem cell22_480480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_480480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480480 prefixEnd_480480 := by exact prefixLift 480480
  have htrace : WordTrace (prefixWord ++ tailWord_480480) baseStart_480480 baseEnd_480480 := by
    simpa [prefixWord, tailWord_480480, baseEnd_480480] using wordTrace_append hprefix tailTrace_480480
  have hstable : (prefixWord ++ tailWord_480480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480480).length < 2 ^ (prefixWord ++ tailWord_480480).sum := by decide
  have hdescent : baseEnd_480480 < baseStart_480480 := by decide
  rcases family_descends (prefixWord ++ tailWord_480480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480544 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_480544 : Nat := 118140960795 + 480544 * 2 ^ 59
def prefixEnd_480544 : Nat := 4983230072969 + 3 ^ 40 * 480544 * 2
def baseEnd_480544 : Nat := 164500031756182068726683

theorem tailTrace_480544 : CollatzResearch.WordTrace tailWord_480544 prefixEnd_480544 164500031756182068726683 := by
  unfold tailWord_480544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763439785539316613176343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11684586380719088817568457 8763439785539316613176343)
  ·
    refine ⟨13145159678308974919764515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763439785539316613176343 13145159678308974919764515)
    ·
      refine ⟨19717739517463462379646773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145159678308974919764515 19717739517463462379646773)
      ·
        refine ⟨1848538079762199598091885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19717739517463462379646773 1848538079762199598091885)
        ·
          refine ⟨693201779910824849284457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1848538079762199598091885 693201779910824849284457)
          ·
            refine ⟨519901334933118636963343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693201779910824849284457 519901334933118636963343)
            ·
              refine ⟨779852002399677955445015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519901334933118636963343 779852002399677955445015)
              ·
                refine ⟨1169778003599516933167523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779852002399677955445015 1169778003599516933167523)
                ·
                  refine ⟨1754667005399275399751285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169778003599516933167523 1754667005399275399751285)
                  ·
                    refine ⟨164500031756182068726683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1754667005399275399751285 164500031756182068726683)
                    ·
                      rfl

theorem cell22_480544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_480544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480544 prefixEnd_480544 := by exact prefixLift 480544
  have htrace : WordTrace (prefixWord ++ tailWord_480544) baseStart_480544 baseEnd_480544 := by
    simpa [prefixWord, tailWord_480544, baseEnd_480544] using wordTrace_append hprefix tailTrace_480544
  have hstable : (prefixWord ++ tailWord_480544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480544).length < 2 ^ (prefixWord ++ tailWord_480544).sum := by decide
  have hdescent : baseEnd_480544 < baseStart_480544 := by decide
  rcases family_descends (prefixWord ++ tailWord_480544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480585 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 7]
def baseStart_480585 : Nat := 118140960795 + 480585 * 2 ^ 59
def prefixEnd_480585 : Nat := 4983230072969 + 3 ^ 40 * 480585 * 2
def baseEnd_480585 : Nat := 54838022298023876150519

theorem tailTrace_480585 : CollatzResearch.WordTrace tailWord_480585 prefixEnd_480585 54838022298023876150519 := by
  unfold tailWord_480585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17528374963930097228595209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11685583309286731485730139 17528374963930097228595209)
  ·
    refine ⟨13146281222947572921446407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17528374963930097228595209 13146281222947572921446407)
    ·
      refine ⟨19719421834421359382169611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146281222947572921446407 19719421834421359382169611)
      ·
        refine ⟨29579132751632039073254417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719421834421359382169611 29579132751632039073254417)
        ·
          refine ⟨22184349563724029304940813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29579132751632039073254417 22184349563724029304940813)
          ·
            refine ⟨8319131086396510989352805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22184349563724029304940813 8319131086396510989352805)
            ·
              refine ⟨1559837078699345810503651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8319131086396510989352805 1559837078699345810503651)
              ·
                refine ⟨2339755618049018715755477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559837078699345810503651 2339755618049018715755477)
                ·
                  refine ⟨54838022298023876150519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2339755618049018715755477 54838022298023876150519)
                  ·
                    rfl

theorem cell22_480585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_480585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480585 prefixEnd_480585 := by exact prefixLift 480585
  have htrace : WordTrace (prefixWord ++ tailWord_480585) baseStart_480585 baseEnd_480585 := by
    simpa [prefixWord, tailWord_480585, baseEnd_480585] using wordTrace_append hprefix tailTrace_480585
  have hstable : (prefixWord ++ tailWord_480585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480585).length < 2 ^ (prefixWord ++ tailWord_480585).sum := by decide
  have hdescent : baseEnd_480585 < baseStart_480585 := by decide
  rcases family_descends (prefixWord ++ tailWord_480585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480600 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_480600 : Nat := 118140960795 + 480600 * 2 ^ 59
def prefixEnd_480600 : Nat := 4983230072969 + 3 ^ 40 * 480600 * 2
def baseEnd_480600 : Nat := 164519201700616589326511

theorem tailTrace_480600 : CollatzResearch.WordTrace tailWord_480600 prefixEnd_480600 164519201700616589326511 := by
  unfold tailWord_480600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764461029437877395195627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11685948039250503193594169 8764461029437877395195627)
  ·
    refine ⟨13146691544156816092793441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764461029437877395195627 13146691544156816092793441)
    ·
      refine ⟨9860018658117612069595081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13146691544156816092793441 9860018658117612069595081)
      ·
        refine ⟨7395013993588209052196311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9860018658117612069595081 7395013993588209052196311)
        ·
          refine ⟨11092520990382313578294467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395013993588209052196311 11092520990382313578294467)
          ·
            refine ⟨16638781485573470367441701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092520990382313578294467 16638781485573470367441701)
            ·
              refine ⟨3119771528545025693895319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16638781485573470367441701 3119771528545025693895319)
              ·
                refine ⟨4679657292817538540842979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119771528545025693895319 4679657292817538540842979)
                ·
                  refine ⟨7019485939226307811264469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679657292817538540842979 7019485939226307811264469)
                  ·
                    refine ⟨164519201700616589326511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7019485939226307811264469 164519201700616589326511)
                    ·
                      rfl

theorem cell22_480600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_480600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480600 prefixEnd_480600 := by exact prefixLift 480600
  have htrace : WordTrace (prefixWord ++ tailWord_480600) baseStart_480600 baseEnd_480600 := by
    simpa [prefixWord, tailWord_480600, baseEnd_480600] using wordTrace_append hprefix tailTrace_480600
  have hstable : (prefixWord ++ tailWord_480600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480600).length < 2 ^ (prefixWord ++ tailWord_480600).sum := by decide
  have hdescent : baseEnd_480600 < baseStart_480600 := by decide
  rcases family_descends (prefixWord ++ tailWord_480600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480664 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_480664 : Nat := 118140960795 + 480664 * 2 ^ 59
def prefixEnd_480664 : Nat := 4983230072969 + 3 ^ 40 * 480664 * 2
def baseEnd_480664 : Nat := 54847036736180585242105

theorem tailTrace_480664 : CollatzResearch.WordTrace tailWord_480664 prefixEnd_480664 54847036736180585242105 := by
  unfold tailWord_480664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765628165321946860360523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687504220429262480480697 8765628165321946860360523)
  ·
    refine ⟨13148442247982920290540785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8765628165321946860360523 13148442247982920290540785)
    ·
      refine ⟨9861331685987190217905589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13148442247982920290540785 9861331685987190217905589)
      ·
        refine ⟨924499845561299082928649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9861331685987190217905589 924499845561299082928649)
        ·
          refine ⟨693374884170974312196487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924499845561299082928649 693374884170974312196487)
          ·
            refine ⟨1040062326256461468294731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693374884170974312196487 1040062326256461468294731)
            ·
              refine ⟨1560093489384692202442097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040062326256461468294731 1560093489384692202442097)
              ·
                refine ⟨1170070117038519151831573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560093489384692202442097 1170070117038519151831573)
                ·
                  refine ⟨54847036736180585242105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1170070117038519151831573 54847036736180585242105)
                  ·
                    rfl

theorem cell22_480664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_480664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480664 prefixEnd_480664 := by exact prefixLift 480664
  have htrace : WordTrace (prefixWord ++ tailWord_480664) baseStart_480664 baseEnd_480664 := by
    simpa [prefixWord, tailWord_480664, baseEnd_480664] using wordTrace_append hprefix tailTrace_480664
  have hstable : (prefixWord ++ tailWord_480664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480664).length < 2 ^ (prefixWord ++ tailWord_480664).sum := by decide
  have hdescent : baseEnd_480664 < baseStart_480664 := by decide
  rcases family_descends (prefixWord ++ tailWord_480664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480677 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_480677 : Nat := 118140960795 + 480677 * 2 ^ 59
def prefixEnd_480677 : Nat := 4983230072969 + 3 ^ 40 * 480677 * 2
def baseEnd_480677 : Nat := 164545560374214055151275

theorem tailTrace_480677 : CollatzResearch.WordTrace tailWord_480677 prefixEnd_480677 164545560374214055151275 := by
  unfold tailWord_480677
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531730479596796940944285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11687820319731197960629523 17531730479596796940944285)
  ·
    refine ⟨6574398929848798852854107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17531730479596796940944285 6574398929848798852854107)
    ·
      refine ⟨9861598394773198279281161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574398929848798852854107 9861598394773198279281161)
      ·
        refine ⟨7396198796079898709460871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9861598394773198279281161 7396198796079898709460871)
        ·
          refine ⟨11094298194119848064191307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396198796079898709460871 11094298194119848064191307)
          ·
            refine ⟨16641447291179772096286961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094298194119848064191307 16641447291179772096286961)
            ·
              refine ⟨12481085468384829072215221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16641447291179772096286961 12481085468384829072215221)
              ·
                refine ⟨1170101762661077725520177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12481085468384829072215221 1170101762661077725520177)
                ·
                  refine ⟨877576321995808294140133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170101762661077725520177 877576321995808294140133)
                  ·
                    refine ⟨164545560374214055151275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877576321995808294140133 164545560374214055151275)
                    ·
                      rfl

theorem cell22_480677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_480677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480677 prefixEnd_480677 := by exact prefixLift 480677
  have htrace : WordTrace (prefixWord ++ tailWord_480677) baseStart_480677 baseEnd_480677 := by
    simpa [prefixWord, tailWord_480677, baseEnd_480677] using wordTrace_append hprefix tailTrace_480677
  have hstable : (prefixWord ++ tailWord_480677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480677).length < 2 ^ (prefixWord ++ tailWord_480677).sum := by decide
  have hdescent : baseEnd_480677 < baseStart_480677 := by decide
  rcases family_descends (prefixWord ++ tailWord_480677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480679 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 4, 3]
def baseStart_480679 : Nat := 118140960795 + 480679 * 2 ^ 59
def prefixEnd_480679 : Nat := 4983230072969 + 3 ^ 40 * 480679 * 2
def baseEnd_480679 : Nat := 164546245015086716601269

theorem tailTrace_480679 : CollatzResearch.WordTrace tailWord_480679 prefixEnd_480679 164546245015086716601269 := by
  unfold tailWord_480679
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531803425589551282517091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11687868950393034188344727 17531803425589551282517091)
  ·
    refine ⟨26297705138384326923775637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17531803425589551282517091 26297705138384326923775637)
    ·
      refine ⟨1232704928361765324551983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26297705138384326923775637 1232704928361765324551983)
      ·
        refine ⟨1849057392542647986827975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232704928361765324551983 1849057392542647986827975)
        ·
          refine ⟨2773586088813971980241963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849057392542647986827975 2773586088813971980241963)
          ·
            refine ⟨4160379133220957970362945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773586088813971980241963 4160379133220957970362945)
            ·
              refine ⟨3120284349915718477772209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160379133220957970362945 3120284349915718477772209)
              ·
                refine ⟨2340213262436788858329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120284349915718477772209 2340213262436788858329157)
                ·
                  refine ⟨438789986706897910936717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340213262436788858329157 438789986706897910936717)
                  ·
                    refine ⟨164546245015086716601269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438789986706897910936717 164546245015086716601269)
                    ·
                      rfl

theorem cell22_480679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_480679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480679 prefixEnd_480679 := by exact prefixLift 480679
  have htrace : WordTrace (prefixWord ++ tailWord_480679) baseStart_480679 baseEnd_480679 := by
    simpa [prefixWord, tailWord_480679, baseEnd_480679] using wordTrace_append hprefix tailTrace_480679
  have hstable : (prefixWord ++ tailWord_480679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480679).length < 2 ^ (prefixWord ++ tailWord_480679).sum := by decide
  have hdescent : baseEnd_480679 < baseStart_480679 := by decide
  rcases family_descends (prefixWord ++ tailWord_480679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480726 : List Nat := [5, 2, 1, 1, 1, 2, 4, 6]
def baseStart_480726 : Nat := 118140960795 + 480726 * 2 ^ 59
def prefixEnd_480726 : Nat := 4983230072969 + 3 ^ 40 * 480726 * 2
def baseEnd_480726 : Nat := 18284703786177140075125

theorem tailTrace_480726 : CollatzResearch.WordTrace tailWord_480726 prefixEnd_480726 18284703786177140075125 := by
  unfold tailWord_480726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095844853526204894342377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11689011770946185539652021 1095844853526204894342377)
  ·
    refine ⟨821883640144653670756783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1095844853526204894342377 821883640144653670756783)
    ·
      refine ⟨1232825460216980506135175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821883640144653670756783 1232825460216980506135175)
      ·
        refine ⟨1849238190325470759202763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232825460216980506135175 1849238190325470759202763)
        ·
          refine ⟨2773857285488206138804145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849238190325470759202763 2773857285488206138804145)
          ·
            refine ⟨2080392964116154604103109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2773857285488206138804145 2080392964116154604103109)
            ·
              refine ⟨390073680771778988269333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2080392964116154604103109 390073680771778988269333)
              ·
                refine ⟨18284703786177140075125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390073680771778988269333 18284703786177140075125)
                ·
                  rfl

theorem cell22_480726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_480726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480726 prefixEnd_480726 := by exact prefixLift 480726
  have htrace : WordTrace (prefixWord ++ tailWord_480726) baseStart_480726 baseEnd_480726 := by
    simpa [prefixWord, tailWord_480726, baseEnd_480726] using wordTrace_append hprefix tailTrace_480726
  have hstable : (prefixWord ++ tailWord_480726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480726).length < 2 ^ (prefixWord ++ tailWord_480726).sum := by decide
  have hdescent : baseEnd_480726 < baseStart_480726 := by decide
  rcases family_descends (prefixWord ++ tailWord_480726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480737 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 7]
def baseStart_480737 : Nat := 118140960795 + 480737 * 2 ^ 59
def prefixEnd_480737 : Nat := 4983230072969 + 3 ^ 40 * 480737 * 2
def baseEnd_480737 : Nat := 54855366533464632883697

theorem tailTrace_480737 : CollatzResearch.WordTrace tailWord_480737 prefixEnd_480737 54855366533464632883697 := by
  unfold tailWord_480737
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533918859379427188128465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11689279239586284792085643 17533918859379427188128465)
  ·
    refine ⟨13150439144534570391096349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17533918859379427188128465 13150439144534570391096349)
    ·
      refine ⟨4931414679200463896661131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13150439144534570391096349 4931414679200463896661131)
      ·
        refine ⟨7397122018800695844991697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931414679200463896661131 7397122018800695844991697)
        ·
          refine ⟨5547841514100521883743773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7397122018800695844991697 5547841514100521883743773)
          ·
            refine ⟨2080440567787695706403915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5547841514100521883743773 2080440567787695706403915)
            ·
              refine ⟨3120660851681543559605873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080440567787695706403915 3120660851681543559605873)
              ·
                refine ⟨2340495638761157669704405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120660851681543559605873 2340495638761157669704405)
                ·
                  refine ⟨54855366533464632883697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2340495638761157669704405 54855366533464632883697)
                  ·
                    rfl

theorem cell22_480737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_480737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480737 prefixEnd_480737 := by exact prefixLift 480737
  have htrace : WordTrace (prefixWord ++ tailWord_480737) baseStart_480737 baseEnd_480737 := by
    simpa [prefixWord, tailWord_480737, baseEnd_480737] using wordTrace_append hprefix tailTrace_480737
  have hstable : (prefixWord ++ tailWord_480737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480737).length < 2 ^ (prefixWord ++ tailWord_480737).sum := by decide
  have hdescent : baseEnd_480737 < baseStart_480737 := by decide
  rcases family_descends (prefixWord ++ tailWord_480737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480754 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_480754 : Nat := 118140960795 + 480754 * 2 ^ 59
def prefixEnd_480754 : Nat := 4983230072969 + 3 ^ 40 * 480754 * 2
def baseEnd_480754 : Nat := 54857306349270506992013

theorem tailTrace_480754 : CollatzResearch.WordTrace tailWord_480754 prefixEnd_480754 54857306349270506992013 := by
  unfold tailWord_480754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383634725079459772874329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11689692600211892727664877 4383634725079459772874329)
  ·
    refine ⟨3287726043809594829655747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4383634725079459772874329 3287726043809594829655747)
    ·
      refine ⟨4931589065714392244483621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287726043809594829655747 4931589065714392244483621)
      ·
        refine ⟨924672949821448545840679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4931589065714392244483621 924672949821448545840679)
        ·
          refine ⟨1387009424732172818761019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924672949821448545840679 1387009424732172818761019)
          ·
            refine ⟨2080514137098259228141529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387009424732172818761019 2080514137098259228141529)
            ·
              refine ⟨1560385602823694421106147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080514137098259228141529 1560385602823694421106147)
              ·
                refine ⟨2340578404235541631659221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560385602823694421106147 2340578404235541631659221)
                ·
                  refine ⟨54857306349270506992013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2340578404235541631659221 54857306349270506992013)
                  ·
                    rfl

theorem cell22_480754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_480754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480754 prefixEnd_480754 := by exact prefixLift 480754
  have htrace : WordTrace (prefixWord ++ tailWord_480754) baseStart_480754 baseEnd_480754 := by
    simpa [prefixWord, tailWord_480754, baseEnd_480754] using wordTrace_append hprefix tailTrace_480754
  have hstable : (prefixWord ++ tailWord_480754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480754).length < 2 ^ (prefixWord ++ tailWord_480754).sum := by decide
  have hdescent : baseEnd_480754 < baseStart_480754 := by decide
  rcases family_descends (prefixWord ++ tailWord_480754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480758 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_480758 : Nat := 118140960795 + 480758 * 2 ^ 59
def prefixEnd_480758 : Nat := 4983230072969 + 3 ^ 40 * 480758 * 2
def baseEnd_480758 : Nat := 164573288329556843876027

theorem tailTrace_480758 : CollatzResearch.WordTrace tailWord_480758 prefixEnd_480758 164573288329556843876027 := by
  unfold tailWord_480758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095917799518959235915183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11689789861535565183095285 1095917799518959235915183)
  ·
    refine ⟨1643876699278438853872775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095917799518959235915183 1643876699278438853872775)
    ·
      refine ⟨2465815048917658280809163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643876699278438853872775 2465815048917658280809163)
      ·
        refine ⟨3698722573376487421213745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465815048917658280809163 3698722573376487421213745)
        ·
          refine ⟨2774041930032365565910309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698722573376487421213745 2774041930032365565910309)
          ·
            refine ⟨520132861881068543608183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2774041930032365565910309 520132861881068543608183)
            ·
              refine ⟨780199292821602815412275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520132861881068543608183 780199292821602815412275)
              ·
                refine ⟨1170298939232404223118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780199292821602815412275 1170298939232404223118413)
                ·
                  refine ⟨438862102212151583669405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170298939232404223118413 438862102212151583669405)
                  ·
                    refine ⟨164573288329556843876027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438862102212151583669405 164573288329556843876027)
                    ·
                      rfl

theorem cell22_480758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_480758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480758 prefixEnd_480758 := by exact prefixLift 480758
  have htrace : WordTrace (prefixWord ++ tailWord_480758) baseStart_480758 baseEnd_480758 := by
    simpa [prefixWord, tailWord_480758, baseEnd_480758] using wordTrace_append hprefix tailTrace_480758
  have hstable : (prefixWord ++ tailWord_480758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480758).length < 2 ^ (prefixWord ++ tailWord_480758).sum := by decide
  have hdescent : baseEnd_480758 < baseStart_480758 := by decide
  rcases family_descends (prefixWord ++ tailWord_480758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480812 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_480812 : Nat := 118140960795 + 480812 * 2 ^ 59
def prefixEnd_480812 : Nat := 4983230072969 + 3 ^ 40 * 480812 * 2
def baseEnd_480812 : Nat := 164591773633118703025861

theorem tailTrace_480812 : CollatzResearch.WordTrace tailWord_480812 prefixEnd_480812 164591773633118703025861 := by
  unfold tailWord_480812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768327167053857498554345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11691102889405143331405793 8768327167053857498554345)
  ·
    refine ⟨6576245375290393123915759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8768327167053857498554345 6576245375290393123915759)
    ·
      refine ⟨9864368062935589685873639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576245375290393123915759 9864368062935589685873639)
      ·
        refine ⟨14796552094403384528810459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864368062935589685873639 14796552094403384528810459)
        ·
          refine ⟨22194828141605076793215689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796552094403384528810459 22194828141605076793215689)
          ·
            refine ⟨16646121106203807594911767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22194828141605076793215689 16646121106203807594911767)
            ·
              refine ⟨24969181659305711392367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16646121106203807594911767 24969181659305711392367651)
              ·
                refine ⟨37453772488958567088551477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24969181659305711392367651 37453772488958567088551477)
                ·
                  refine ⟨3511291170839865664551701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37453772488958567088551477 3511291170839865664551701)
                  ·
                    refine ⟨164591773633118703025861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3511291170839865664551701 164591773633118703025861)
                    ·
                      rfl

theorem cell22_480812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_480812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480812 prefixEnd_480812 := by exact prefixLift 480812
  have htrace : WordTrace (prefixWord ++ tailWord_480812) baseStart_480812 baseEnd_480812 := by
    simpa [prefixWord, tailWord_480812, baseEnd_480812] using wordTrace_append hprefix tailTrace_480812
  have hstable : (prefixWord ++ tailWord_480812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480812).length < 2 ^ (prefixWord ++ tailWord_480812).sum := by decide
  have hdescent : baseEnd_480812 < baseStart_480812 := by decide
  rcases family_descends (prefixWord ++ tailWord_480812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480831 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 2, 3]
def baseStart_480831 : Nat := 118140960795 + 480831 * 2 ^ 59
def prefixEnd_480831 : Nat := 4983230072969 + 3 ^ 40 * 480831 * 2
def baseEnd_480831 : Nat := 164598277721408986800803

theorem tailTrace_480831 : CollatzResearch.WordTrace tailWord_480831 prefixEnd_480831 164598277721408986800803 := by
  unfold tailWord_480831
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537347321038881242050347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11691564880692587494700231 17537347321038881242050347)
  ·
    refine ⟨26306020981558321863075521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17537347321038881242050347 26306020981558321863075521)
    ·
      refine ⟨19729515736168741397306641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26306020981558321863075521 19729515736168741397306641)
      ·
        refine ⟨14797136802126556047979981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19729515736168741397306641 14797136802126556047979981)
        ·
          refine ⟨5548926300797458517992493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14797136802126556047979981 5548926300797458517992493)
          ·
            refine ⟨2080847362799046944247185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5548926300797458517992493 2080847362799046944247185)
            ·
              refine ⟨1560635522099285208185389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2080847362799046944247185 1560635522099285208185389)
              ·
                refine ⟨585238320787231953069521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1560635522099285208185389 585238320787231953069521)
                ·
                  refine ⟨438928740590423964802141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585238320787231953069521 438928740590423964802141)
                  ·
                    refine ⟨164598277721408986800803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438928740590423964802141 164598277721408986800803)
                    ·
                      rfl

theorem cell22_480831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_480831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480831 prefixEnd_480831 := by exact prefixLift 480831
  have htrace : WordTrace (prefixWord ++ tailWord_480831) baseStart_480831 baseEnd_480831 := by
    simpa [prefixWord, tailWord_480831, baseEnd_480831] using wordTrace_append hprefix tailTrace_480831
  have hstable : (prefixWord ++ tailWord_480831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480831).length < 2 ^ (prefixWord ++ tailWord_480831).sum := by decide
  have hdescent : baseEnd_480831 < baseStart_480831 := by decide
  rcases family_descends (prefixWord ++ tailWord_480831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480910 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_480910 : Nat := 118140960795 + 480910 * 2 ^ 59
def prefixEnd_480910 : Nat := 4983230072969 + 3 ^ 40 * 480910 * 2
def baseEnd_480910 : Nat := 164625321035879114075561

theorem tailTrace_480910 : CollatzResearch.WordTrace tailWord_480910 prefixEnd_480910 164625321035879114075561 := by
  unfold tailWord_480910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192528585969084716772023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11693485791835118489450789 2192528585969084716772023)
  ·
    refine ⟨3288792878953627075158035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192528585969084716772023 3288792878953627075158035)
    ·
      refine ⟨4933189318430440612737053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288792878953627075158035 4933189318430440612737053)
      ·
        refine ⟨1849945994411415229776395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4933189318430440612737053 1849945994411415229776395)
        ·
          refine ⟨2774918991617122844664593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849945994411415229776395 2774918991617122844664593)
          ·
            refine ⟨2081189243712842133498445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774918991617122844664593 2081189243712842133498445)
            ·
              refine ⟨780445966392315800061917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081189243712842133498445 780445966392315800061917)
              ·
                refine ⟨292667237397118425023219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780445966392315800061917 292667237397118425023219)
                ·
                  refine ⟨439000856095677637534829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292667237397118425023219 439000856095677637534829)
                  ·
                    refine ⟨164625321035879114075561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439000856095677637534829 164625321035879114075561)
                    ·
                      rfl

theorem cell22_480910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_480910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480910 prefixEnd_480910 := by exact prefixLift 480910
  have htrace : WordTrace (prefixWord ++ tailWord_480910) baseStart_480910 baseEnd_480910 := by
    simpa [prefixWord, tailWord_480910, baseEnd_480910] using wordTrace_append hprefix tailTrace_480910
  have hstable : (prefixWord ++ tailWord_480910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480910).length < 2 ^ (prefixWord ++ tailWord_480910).sum := by decide
  have hdescent : baseEnd_480910 < baseStart_480910 := by decide
  rcases family_descends (prefixWord ++ tailWord_480910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480927 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 3, 3]
def baseStart_480927 : Nat := 118140960795 + 480927 * 2 ^ 59
def prefixEnd_480927 : Nat := 4983230072969 + 3 ^ 40 * 480927 * 2
def baseEnd_480927 : Nat := 164631140483296736400509

theorem tailTrace_480927 : CollatzResearch.WordTrace tailWord_480927 prefixEnd_480927 164631140483296736400509 := by
  unfold tailWord_480927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540848728691089637545035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11693899152460726425030023 17540848728691089637545035)
  ·
    refine ⟨26311273093036634456317553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17540848728691089637545035 26311273093036634456317553)
    ·
      refine ⟨19733454819777475842238165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26311273093036634456317553 19733454819777475842238165)
      ·
        refine ⟨462502847338534590052457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19733454819777475842238165 462502847338534590052457)
        ·
          refine ⟨346877135503900942539343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462502847338534590052457 346877135503900942539343)
          ·
            refine ⟨520315703255851413809015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346877135503900942539343 520315703255851413809015)
            ·
              refine ⟨780473554883777120713523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520315703255851413809015 780473554883777120713523)
              ·
                refine ⟨1170710332325665681070285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780473554883777120713523 1170710332325665681070285)
                ·
                  refine ⟨439016374622124630401357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170710332325665681070285 439016374622124630401357)
                  ·
                    refine ⟨164631140483296736400509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439016374622124630401357 164631140483296736400509)
                    ·
                      rfl

theorem cell22_480927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_480927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480927 prefixEnd_480927 := by exact prefixLift 480927
  have htrace : WordTrace (prefixWord ++ tailWord_480927) baseStart_480927 baseEnd_480927 := by
    simpa [prefixWord, tailWord_480927, baseEnd_480927] using wordTrace_append hprefix tailTrace_480927
  have hstable : (prefixWord ++ tailWord_480927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480927).length < 2 ^ (prefixWord ++ tailWord_480927).sum := by decide
  have hdescent : baseEnd_480927 < baseStart_480927 := by decide
  rcases family_descends (prefixWord ++ tailWord_480927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480970 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_480970 : Nat := 118140960795 + 480970 * 2 ^ 59
def prefixEnd_480970 : Nat := 4983230072969 + 3 ^ 40 * 480970 * 2
def baseEnd_480970 : Nat := 164645860262058957575377

theorem tailTrace_480970 : CollatzResearch.WordTrace tailWord_480970 prefixEnd_480970 164645860262058957575377 := by
  unfold tailWord_480970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385604266883826995340091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11694944711690205320906909 4385604266883826995340091)
  ·
    refine ⟨6578406400325740493010137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4385604266883826995340091 6578406400325740493010137)
    ·
      refine ⟨4933804800244305369757603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6578406400325740493010137 4933804800244305369757603)
      ·
        refine ⟨7400707200366458054636405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933804800244305369757603 7400707200366458054636405)
        ·
          refine ⟨693816300034355442622163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7400707200366458054636405 693816300034355442622163)
          ·
            refine ⟨1040724450051533163933245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693816300034355442622163 1040724450051533163933245)
            ·
              refine ⟨390271668769324936474967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040724450051533163933245 390271668769324936474967)
              ·
                refine ⟨585407503153987404712451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390271668769324936474967 585407503153987404712451)
                ·
                  refine ⟨878111254730981107068677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585407503153987404712451 878111254730981107068677)
                  ·
                    refine ⟨164645860262058957575377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878111254730981107068677 164645860262058957575377)
                    ·
                      rfl

theorem cell22_480970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_480970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480970 prefixEnd_480970 := by exact prefixLift 480970
  have htrace : WordTrace (prefixWord ++ tailWord_480970) baseStart_480970 baseEnd_480970 := by
    simpa [prefixWord, tailWord_480970, baseEnd_480970] using wordTrace_append hprefix tailTrace_480970
  have hstable : (prefixWord ++ tailWord_480970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480970).length < 2 ^ (prefixWord ++ tailWord_480970).sum := by decide
  have hdescent : baseEnd_480970 < baseStart_480970 := by decide
  rcases family_descends (prefixWord ++ tailWord_480970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480983 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 2, 3]
def baseStart_480983 : Nat := 118140960795 + 480983 * 2 ^ 59
def prefixEnd_480983 : Nat := 4983230072969 + 3 ^ 40 * 480983 * 2
def baseEnd_480983 : Nat := 164650310427731257000337

theorem tailTrace_480983 : CollatzResearch.WordTrace tailWord_480983 prefixEnd_480983 164650310427731257000337 := by
  unfold tailWord_480983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17542891216488211201583603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695260810992140801055735 17542891216488211201583603)
  ·
    refine ⟨26314336824732316802375405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17542891216488211201583603 26314336824732316802375405)
    ·
      refine ⟨9867876309274618800890777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26314336824732316802375405 9867876309274618800890777)
      ·
        refine ⟨7400907231955964100668083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9867876309274618800890777 7400907231955964100668083)
        ·
          refine ⟨11101360847933946151002125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400907231955964100668083 11101360847933946151002125)
          ·
            refine ⟨4163010317975229806625797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11101360847933946151002125 4163010317975229806625797)
            ·
              refine ⟨780564434620355588742337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4163010317975229806625797 780564434620355588742337)
              ·
                refine ⟨585423325965266691556753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780564434620355588742337 585423325965266691556753)
                ·
                  refine ⟨439067494473950018667565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585423325965266691556753 439067494473950018667565)
                  ·
                    refine ⟨164650310427731257000337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439067494473950018667565 164650310427731257000337)
                    ·
                      rfl

theorem cell22_480983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_480983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480983 prefixEnd_480983 := by exact prefixLift 480983
  have htrace : WordTrace (prefixWord ++ tailWord_480983) baseStart_480983 baseEnd_480983 := by
    simpa [prefixWord, tailWord_480983, baseEnd_480983] using wordTrace_append hprefix tailTrace_480983
  have hstable : (prefixWord ++ tailWord_480983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480983).length < 2 ^ (prefixWord ++ tailWord_480983).sum := by decide
  have hdescent : baseEnd_480983 < baseStart_480983 := by decide
  rcases family_descends (prefixWord ++ tailWord_480983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480985 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 4]
def baseStart_480985 : Nat := 118140960795 + 480985 * 2 ^ 59
def prefixEnd_480985 : Nat := 4983230072969 + 3 ^ 40 * 480985 * 2
def baseEnd_480985 : Nat := 54883665022867972816777

theorem tailTrace_480985 : CollatzResearch.WordTrace tailWord_480985 prefixEnd_480985 54883665022867972816777 := by
  unfold tailWord_480985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17542964162480965543156409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695309441653977028770939 17542964162480965543156409)
  ·
    refine ⟨13157223121860724157367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17542964162480965543156409 13157223121860724157367307)
    ·
      refine ⟨19735834682791086236050961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13157223121860724157367307 19735834682791086236050961)
      ·
        refine ⟨14801876012093314677038221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19735834682791086236050961 14801876012093314677038221)
        ·
          refine ⟨5550703504534993003889333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14801876012093314677038221 5550703504534993003889333)
          ·
            refine ⟨520378453550155594114625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5550703504534993003889333 520378453550155594114625)
            ·
              refine ⟨390283840162616695585969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520378453550155594114625 390283840162616695585969)
              ·
                refine ⟨292712880121962521689477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390283840162616695585969 292712880121962521689477)
                ·
                  refine ⟨54883665022867972816777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292712880121962521689477 54883665022867972816777)
                  ·
                    rfl

theorem cell22_480985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_480985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_480985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_480985 prefixEnd_480985 := by exact prefixLift 480985
  have htrace : WordTrace (prefixWord ++ tailWord_480985) baseStart_480985 baseEnd_480985 := by
    simpa [prefixWord, tailWord_480985, baseEnd_480985] using wordTrace_append hprefix tailTrace_480985
  have hstable : (prefixWord ++ tailWord_480985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480985).length < 2 ^ (prefixWord ++ tailWord_480985).sum := by decide
  have hdescent : baseEnd_480985 < baseStart_480985 := by decide
  rcases family_descends (prefixWord ++ tailWord_480985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481011 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 5, 3]
def baseStart_481011 : Nat := 118140960795 + 481011 * 2 ^ 59
def prefixEnd_481011 : Nat := 4983230072969 + 3 ^ 40 * 481011 * 2
def baseEnd_481011 : Nat := 164659895399948517300251

theorem tailTrace_481011 : CollatzResearch.WordTrace tailWord_481011 prefixEnd_481011 164659895399948517300251 := by
  unfold tailWord_481011
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543912460386771983602887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695941640257847989068591 17543912460386771983602887)
  ·
    refine ⟨26315868690580157975404331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543912460386771983602887 26315868690580157975404331)
    ·
      refine ⟨39473803035870236963106497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26315868690580157975404331 39473803035870236963106497)
      ·
        refine ⟨29605352276902677722329873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39473803035870236963106497 29605352276902677722329873)
        ·
          refine ⟨22204014207677008291747405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29605352276902677722329873 22204014207677008291747405)
          ·
            refine ⟨8326505327878878109405277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22204014207677008291747405 8326505327878878109405277)
            ·
              refine ⟨3122439497954579291026979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8326505327878878109405277 3122439497954579291026979)
              ·
                refine ⟨4683659246931868936540469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122439497954579291026979 4683659246931868936540469)
                ·
                  refine ⟨439093054399862712800669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4683659246931868936540469 439093054399862712800669)
                  ·
                    refine ⟨164659895399948517300251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439093054399862712800669 164659895399948517300251)
                    ·
                      rfl

theorem cell22_481011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].length) (baseStart_481011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481011 prefixEnd_481011 := by exact prefixLift 481011
  have htrace : WordTrace (prefixWord ++ tailWord_481011) baseStart_481011 baseEnd_481011 := by
    simpa [prefixWord, tailWord_481011, baseEnd_481011] using wordTrace_append hprefix tailTrace_481011
  have hstable : (prefixWord ++ tailWord_481011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481011).length < 2 ^ (prefixWord ++ tailWord_481011).sum := by decide
  have hdescent : baseEnd_481011 < baseStart_481011 := by decide
  rcases family_descends (prefixWord ++ tailWord_481011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481024 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_481024 : Nat := 118140960795 + 481024 * 2 ^ 59
def prefixEnd_481024 : Nat := 4983230072969 + 3 ^ 40 * 481024 * 2
def baseEnd_481024 : Nat := 54888115188540272241737

theorem tailTrace_481024 : CollatzResearch.WordTrace tailWord_481024 prefixEnd_481024 54888115188540272241737 := by
  unfold tailWord_481024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772193304669837601913063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11696257739559783469217417 8772193304669837601913063)
  ·
    refine ⟨13158289957004756402869595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8772193304669837601913063 13158289957004756402869595)
    ·
      refine ⟨19737434935507134604304393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158289957004756402869595 19737434935507134604304393)
      ·
        refine ⟨14803076201630350953228295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19737434935507134604304393 14803076201630350953228295)
        ·
          refine ⟨22204614302445526429842443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803076201630350953228295 22204614302445526429842443)
          ·
            refine ⟨33306921453668289644763665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22204614302445526429842443 33306921453668289644763665)
            ·
              refine ⟨24980191090251217233572749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33306921453668289644763665 24980191090251217233572749)
              ·
                refine ⟨9367571658844206462589781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24980191090251217233572749 9367571658844206462589781)
                ·
                  refine ⟨54888115188540272241737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9367571658844206462589781 54888115188540272241737)
                  ·
                    rfl

theorem cell22_481024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_481024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481024 prefixEnd_481024 := by exact prefixLift 481024
  have htrace : WordTrace (prefixWord ++ tailWord_481024) baseStart_481024 baseEnd_481024 := by
    simpa [prefixWord, tailWord_481024, baseEnd_481024] using wordTrace_append hprefix tailTrace_481024
  have hstable : (prefixWord ++ tailWord_481024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481024).length < 2 ^ (prefixWord ++ tailWord_481024).sum := by decide
  have hdescent : baseEnd_481024 < baseStart_481024 := by decide
  rcases family_descends (prefixWord ++ tailWord_481024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481045 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_481045 : Nat := 118140960795 + 481045 * 2 ^ 59
def prefixEnd_481045 : Nat := 4983230072969 + 3 ^ 40 * 481045 * 2
def baseEnd_481045 : Nat := 164671534294783761950147

theorem tailTrace_481045 : CollatzResearch.WordTrace tailWord_481045 prefixEnd_481045 164671534294783761950147 := by
  unfold tailWord_481045
  simp only [CollatzResearch.WordTrace]
  refine ⟨17545152542263595790340589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11696768361509063860227059 17545152542263595790340589)
  ·
    refine ⟨6579432203348848421377721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17545152542263595790340589 6579432203348848421377721)
    ·
      refine ⟨4934574152511636316033291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579432203348848421377721 4934574152511636316033291)
      ·
        refine ⟨7401861228767454474049937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934574152511636316033291 7401861228767454474049937)
        ·
          refine ⟨5551395921575590855537453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7401861228767454474049937 5551395921575590855537453)
          ·
            refine ⟨2081773470590846570826545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5551395921575590855537453 2081773470590846570826545)
            ·
              refine ⟨1561330102943134928119909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081773470590846570826545 1561330102943134928119909)
              ·
                refine ⟨292749394301837799022483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1561330102943134928119909 292749394301837799022483)
                ·
                  refine ⟨439124091452756698533725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292749394301837799022483 439124091452756698533725)
                  ·
                    refine ⟨164671534294783761950147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439124091452756698533725 164671534294783761950147)
                    ·
                      rfl

theorem cell22_481045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_481045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481045 prefixEnd_481045 := by exact prefixLift 481045
  have htrace : WordTrace (prefixWord ++ tailWord_481045) baseStart_481045 baseEnd_481045 := by
    simpa [prefixWord, tailWord_481045, baseEnd_481045] using wordTrace_append hprefix tailTrace_481045
  have hstable : (prefixWord ++ tailWord_481045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481045).length < 2 ^ (prefixWord ++ tailWord_481045).sum := by decide
  have hdescent : baseEnd_481045 < baseStart_481045 := by decide
  rcases family_descends (prefixWord ++ tailWord_481045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481056 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_481056 : Nat := 118140960795 + 481056 * 2 ^ 59
def prefixEnd_481056 : Nat := 4983230072969 + 3 ^ 40 * 481056 * 2
def baseEnd_481056 : Nat := 164675299819583399925113

theorem tailTrace_481056 : CollatzResearch.WordTrace tailWord_481056 prefixEnd_481056 164675299819583399925113 := by
  unfold tailWord_481056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772776872611872334495511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11697035830149163112660681 8772776872611872334495511)
  ·
    refine ⟨13159165308917808501743267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8772776872611872334495511 13159165308917808501743267)
    ·
      refine ⟨19738747963376712752614901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159165308917808501743267 19738747963376712752614901)
      ·
        refine ⟨1850507621566566820557647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19738747963376712752614901 1850507621566566820557647)
        ·
          refine ⟨2775761432349850230836471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850507621566566820557647 2775761432349850230836471)
          ·
            refine ⟨4163642148524775346254707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775761432349850230836471 4163642148524775346254707)
            ·
              refine ⟨6245463222787163019382061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163642148524775346254707 6245463222787163019382061)
              ·
                refine ⟨2342048708545186132268273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6245463222787163019382061 2342048708545186132268273)
                ·
                  refine ⟨1756536531408889599201205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342048708545186132268273 1756536531408889599201205)
                  ·
                    refine ⟨164675299819583399925113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1756536531408889599201205 164675299819583399925113)
                    ·
                      rfl

theorem cell22_481056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_481056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481056 prefixEnd_481056 := by exact prefixLift 481056
  have htrace : WordTrace (prefixWord ++ tailWord_481056) baseStart_481056 baseEnd_481056 := by
    simpa [prefixWord, tailWord_481056, baseEnd_481056] using wordTrace_append hprefix tailTrace_481056
  have hstable : (prefixWord ++ tailWord_481056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481056).length < 2 ^ (prefixWord ++ tailWord_481056).sum := by decide
  have hdescent : baseEnd_481056 < baseStart_481056 := by decide
  rcases family_descends (prefixWord ++ tailWord_481056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481122 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_481122 : Nat := 118140960795 + 481122 * 2 ^ 59
def prefixEnd_481122 : Nat := 4983230072969 + 3 ^ 40 * 481122 * 2
def baseEnd_481122 : Nat := 164697892968381227774911

theorem tailTrace_481122 : CollatzResearch.WordTrace tailWord_481122 prefixEnd_481122 164697892968381227774911 := by
  unfold tailWord_481122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386990240746159485223405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11698640641989758627262413 4386990240746159485223405)
  ·
    refine ⟨1645121340279809806958777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4386990240746159485223405 1645121340279809806958777)
    ·
      refine ⟨1233841005209857355219083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645121340279809806958777 1233841005209857355219083)
      ·
        refine ⟨1850761507814786032828625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233841005209857355219083 1850761507814786032828625)
        ·
          refine ⟨1388071130861089524621469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850761507814786032828625 1388071130861089524621469)
          ·
            refine ⟨520526674072908571733051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1388071130861089524621469 520526674072908571733051)
            ·
              refine ⟨780790011109362857599577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520526674072908571733051 780790011109362857599577)
              ·
                refine ⟨585592508332022143199683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780790011109362857599577 585592508332022143199683)
                ·
                  refine ⟨878388762498033214799525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585592508332022143199683 878388762498033214799525)
                  ·
                    refine ⟨164697892968381227774911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878388762498033214799525 164697892968381227774911)
                    ·
                      rfl

theorem cell22_481122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_481122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481122 prefixEnd_481122 := by exact prefixLift 481122
  have htrace : WordTrace (prefixWord ++ tailWord_481122) baseStart_481122 baseEnd_481122 := by
    simpa [prefixWord, tailWord_481122, baseEnd_481122] using wordTrace_append hprefix tailTrace_481122
  have hstable : (prefixWord ++ tailWord_481122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481122).length < 2 ^ (prefixWord ++ tailWord_481122).sum := by decide
  have hdescent : baseEnd_481122 < baseStart_481122 := by decide
  rcases family_descends (prefixWord ++ tailWord_481122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481133 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_481133 : Nat := 118140960795 + 481133 * 2 ^ 59
def prefixEnd_481133 : Nat := 4983230072969 + 3 ^ 40 * 481133 * 2
def baseEnd_481133 : Nat := 164701658493180865749877

theorem tailTrace_481133 : CollatzResearch.WordTrace tailWord_481133 prefixEnd_481133 164701658493180865749877 := by
  unfold tailWord_481133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548362165944786819544053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11698908110629857879696035 17548362165944786819544053)
  ·
    refine ⟨1645158953057323764332255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17548362165944786819544053 1645158953057323764332255)
    ·
      refine ⟨2467738429585985646498383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645158953057323764332255 2467738429585985646498383)
      ·
        refine ⟨3701607644378978469747575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467738429585985646498383 3701607644378978469747575)
        ·
          refine ⟨5552411466568467704621363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701607644378978469747575 5552411466568467704621363)
          ·
            refine ⟨8328617199852701556932045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552411466568467704621363 8328617199852701556932045)
            ·
              refine ⟨3123231449944763083849517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8328617199852701556932045 3123231449944763083849517)
              ·
                refine ⟨1171211793729286156443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123231449944763083849517 1171211793729286156443569)
                ·
                  refine ⟨878408845296964617332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171211793729286156443569 878408845296964617332677)
                  ·
                    refine ⟨164701658493180865749877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878408845296964617332677 164701658493180865749877)
                    ·
                      rfl

theorem cell22_481133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_481133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481133 prefixEnd_481133 := by exact prefixLift 481133
  have htrace : WordTrace (prefixWord ++ tailWord_481133) baseStart_481133 baseEnd_481133 := by
    simpa [prefixWord, tailWord_481133, baseEnd_481133] using wordTrace_append hprefix tailTrace_481133
  have hstable : (prefixWord ++ tailWord_481133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481133).length < 2 ^ (prefixWord ++ tailWord_481133).sum := by decide
  have hdescent : baseEnd_481133 < baseStart_481133 := by decide
  rcases family_descends (prefixWord ++ tailWord_481133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481161 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_481161 : Nat := 118140960795 + 481161 * 2 ^ 59
def prefixEnd_481161 : Nat := 4983230072969 + 3 ^ 40 * 481161 * 2
def baseEnd_481161 : Nat := 164711243465398126049791

theorem tailTrace_481161 : CollatzResearch.WordTrace tailWord_481161 prefixEnd_481161 164711243465398126049791 := by
  unfold tailWord_481161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549383409843347601563337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11699588939895565067708891 17549383409843347601563337)
  ·
    refine ⟨13162037557382510701172503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17549383409843347601563337 13162037557382510701172503)
    ·
      refine ⟨19743056336073766051758755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162037557382510701172503 19743056336073766051758755)
      ·
        refine ⟨29614584504110649077638133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19743056336073766051758755 29614584504110649077638133)
        ·
          refine ⟨2776367297260373351028575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29614584504110649077638133 2776367297260373351028575)
          ·
            refine ⟨4164550945890560026542863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776367297260373351028575 4164550945890560026542863)
            ·
              refine ⟨6246826418835840039814295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164550945890560026542863 6246826418835840039814295)
              ·
                refine ⟨9370239628253760059721443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246826418835840039814295 9370239628253760059721443)
                ·
                  refine ⟨14055359442380640089582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370239628253760059721443 14055359442380640089582165)
                  ·
                    refine ⟨164711243465398126049791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14055359442380640089582165 164711243465398126049791)
                    ·
                      rfl

theorem cell22_481161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_481161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481161 prefixEnd_481161 := by exact prefixLift 481161
  have htrace : WordTrace (prefixWord ++ tailWord_481161) baseStart_481161 baseEnd_481161 := by
    simpa [prefixWord, tailWord_481161, baseEnd_481161] using wordTrace_append hprefix tailTrace_481161
  have hstable : (prefixWord ++ tailWord_481161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481161).length < 2 ^ (prefixWord ++ tailWord_481161).sum := by decide
  have hdescent : baseEnd_481161 < baseStart_481161 := by decide
  rcases family_descends (prefixWord ++ tailWord_481161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481163 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 3, 3]
def baseStart_481163 : Nat := 118140960795 + 481163 * 2 ^ 59
def prefixEnd_481163 : Nat := 4983230072969 + 3 ^ 40 * 481163 * 2
def baseEnd_481163 : Nat := 164711928106270787499785

theorem tailTrace_481163 : CollatzResearch.WordTrace tailWord_481163 prefixEnd_481163 164711928106270787499785 := by
  unfold tailWord_481163
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549456355836101943136143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11699637570557401295424095 17549456355836101943136143)
  ·
    refine ⟨26324184533754152914704215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17549456355836101943136143 26324184533754152914704215)
    ·
      refine ⟨39486276800631229372056323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26324184533754152914704215 39486276800631229372056323)
      ·
        refine ⟨59229415200946844058084485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39486276800631229372056323 59229415200946844058084485)
        ·
          refine ⟨11105515350177533260890841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59229415200946844058084485 11105515350177533260890841)
          ·
            refine ⟨8329136512633149945668131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11105515350177533260890841 8329136512633149945668131)
            ·
              refine ⟨12493704768949724918502197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329136512633149945668131 12493704768949724918502197)
              ·
                refine ⟨1171284822089036711109581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12493704768949724918502197 1171284822089036711109581)
                ·
                  refine ⟨439231808283388766666093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171284822089036711109581 439231808283388766666093)
                  ·
                    refine ⟨164711928106270787499785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439231808283388766666093 164711928106270787499785)
                    ·
                      rfl

theorem cell22_481163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].length) (baseStart_481163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481163 prefixEnd_481163 := by exact prefixLift 481163
  have htrace : WordTrace (prefixWord ++ tailWord_481163) baseStart_481163 baseEnd_481163 := by
    simpa [prefixWord, tailWord_481163, baseEnd_481163] using wordTrace_append hprefix tailTrace_481163
  have hstable : (prefixWord ++ tailWord_481163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481163).length < 2 ^ (prefixWord ++ tailWord_481163).sum := by decide
  have hdescent : baseEnd_481163 < baseStart_481163 := by decide
  rcases family_descends (prefixWord ++ tailWord_481163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481180 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_481180 : Nat := 118140960795 + 481180 * 2 ^ 59
def prefixEnd_481180 : Nat := 4983230072969 + 3 ^ 40 * 481180 * 2
def baseEnd_481180 : Nat := 164717747553688409824733

theorem tailTrace_481180 : CollatzResearch.WordTrace tailWord_481180 prefixEnd_481180 164717747553688409824733 := by
  unfold tailWord_481180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775038198387256923252497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700050931183009231003329 8775038198387256923252497)
  ·
    refine ⟨6581278648790442692439373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8775038198387256923252497 6581278648790442692439373)
    ·
      refine ⟨2467979493296416009664765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6581278648790442692439373 2467979493296416009664765)
      ·
        refine ⟨925492309986156003624287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2467979493296416009664765 925492309986156003624287)
        ·
          refine ⟨1388238464979234005436431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925492309986156003624287 1388238464979234005436431)
          ·
            refine ⟨2082357697468851008154647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388238464979234005436431 2082357697468851008154647)
            ·
              refine ⟨3123536546203276512231971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082357697468851008154647 3123536546203276512231971)
              ·
                refine ⟨4685304819304914768347957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123536546203276512231971 4685304819304914768347957)
                ·
                  refine ⟨439247326809835759532621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685304819304914768347957 439247326809835759532621)
                  ·
                    refine ⟨164717747553688409824733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439247326809835759532621 164717747553688409824733)
                    ·
                      rfl

theorem cell22_481180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_481180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481180 prefixEnd_481180 := by exact prefixLift 481180
  have htrace : WordTrace (prefixWord ++ tailWord_481180) baseStart_481180 baseEnd_481180 := by
    simpa [prefixWord, tailWord_481180, baseEnd_481180] using wordTrace_append hprefix tailTrace_481180
  have hstable : (prefixWord ++ tailWord_481180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481180).length < 2 ^ (prefixWord ++ tailWord_481180).sum := by decide
  have hdescent : baseEnd_481180 < baseStart_481180 := by decide
  rcases family_descends (prefixWord ++ tailWord_481180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481240 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_481240 : Nat := 118140960795 + 481240 * 2 ^ 59
def prefixEnd_481240 : Nat := 4983230072969 + 3 ^ 40 * 481240 * 2
def baseEnd_481240 : Nat := 164738286779868253324549

theorem tailTrace_481240 : CollatzResearch.WordTrace tailWord_481240 prefixEnd_481240 164738286779868253324549 := by
  unfold tailWord_481240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776132388278572046844587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11701509851038096062459449 8776132388278572046844587)
  ·
    refine ⟨13164198582417858070266881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8776132388278572046844587 13164198582417858070266881)
    ·
      refine ⟨9873148936813393552700161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13164198582417858070266881 9873148936813393552700161)
      ·
        refine ⟨7404861702610045164525121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9873148936813393552700161 7404861702610045164525121)
        ·
          refine ⟨5553646276957533873393841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7404861702610045164525121 5553646276957533873393841)
          ·
            refine ⟨4165234707718150405045381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5553646276957533873393841 4165234707718150405045381)
            ·
              refine ⟨780981507697153200946009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4165234707718150405045381 780981507697153200946009)
              ·
                refine ⟨585736130772864900709507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780981507697153200946009 585736130772864900709507)
                ·
                  refine ⟨878604196159297351064261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585736130772864900709507 878604196159297351064261)
                  ·
                    refine ⟨164738286779868253324549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878604196159297351064261 164738286779868253324549)
                    ·
                      rfl

theorem cell22_481240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_481240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481240 prefixEnd_481240 := by exact prefixLift 481240
  have htrace : WordTrace (prefixWord ++ tailWord_481240) baseStart_481240 baseEnd_481240 := by
    simpa [prefixWord, tailWord_481240, baseEnd_481240] using wordTrace_append hprefix tailTrace_481240
  have hstable : (prefixWord ++ tailWord_481240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481240).length < 2 ^ (prefixWord ++ tailWord_481240).sum := by decide
  have hdescent : baseEnd_481240 < baseStart_481240 := by decide
  rcases family_descends (prefixWord ++ tailWord_481240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481287 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 2, 3]
def baseStart_481287 : Nat := 118140960795 + 481287 * 2 ^ 59
def prefixEnd_481287 : Nat := 4983230072969 + 3 ^ 40 * 481287 * 2
def baseEnd_481287 : Nat := 164754375840375797399405

theorem tailTrace_481287 : CollatzResearch.WordTrace tailWord_481287 prefixEnd_481287 164754375840375797399405 := by
  unfold tailWord_481287
  simp only [CollatzResearch.WordTrace]
  refine ⟨17553979007386871120650115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11702652671591247413766743 17553979007386871120650115)
  ·
    refine ⟨26330968511080306680975173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17553979007386871120650115 26330968511080306680975173)
    ·
      refine ⟨4937056595827557502682845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26330968511080306680975173 4937056595827557502682845)
      ·
        refine ⟨1851396223435334063506067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4937056595827557502682845 1851396223435334063506067)
        ·
          refine ⟨2777094335153001095259101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851396223435334063506067 2777094335153001095259101)
          ·
            refine ⟨1041410375682375410722163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2777094335153001095259101 1041410375682375410722163)
            ·
              refine ⟨1562115563523563116083245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041410375682375410722163 1562115563523563116083245)
              ·
                refine ⟨585793336321336168531217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562115563523563116083245 585793336321336168531217)
                ·
                  refine ⟨439345002241002126398413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585793336321336168531217 439345002241002126398413)
                  ·
                    refine ⟨164754375840375797399405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439345002241002126398413 164754375840375797399405)
                    ·
                      rfl

theorem cell22_481287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_481287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481287 prefixEnd_481287 := by exact prefixLift 481287
  have htrace : WordTrace (prefixWord ++ tailWord_481287) baseStart_481287 baseEnd_481287 := by
    simpa [prefixWord, tailWord_481287, baseEnd_481287] using wordTrace_append hprefix tailTrace_481287
  have hstable : (prefixWord ++ tailWord_481287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481287).length < 2 ^ (prefixWord ++ tailWord_481287).sum := by decide
  have hdescent : baseEnd_481287 < baseStart_481287 := by decide
  rcases family_descends (prefixWord ++ tailWord_481287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481343 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_481343 : Nat := 118140960795 + 481343 * 2 ^ 59
def prefixEnd_481343 : Nat := 4983230072969 + 3 ^ 40 * 481343 * 2
def baseEnd_481343 : Nat := 164773545784810317999233

theorem tailTrace_481343 : CollatzResearch.WordTrace tailWord_481343 prefixEnd_481343 164773545784810317999233 := by
  unfold tailWord_481343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17556021495183992684688683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11704014330122661789792455 17556021495183992684688683)
  ·
    refine ⟨26334032242775989027033025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17556021495183992684688683 26334032242775989027033025)
    ·
      refine ⟨19750524182081991770274769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26334032242775989027033025 19750524182081991770274769)
      ·
        refine ⟨14812893136561493827706077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19750524182081991770274769 14812893136561493827706077)
        ·
          refine ⟨5554834926210560185389779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14812893136561493827706077 5554834926210560185389779)
          ·
            refine ⟨8332252389315840278084669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554834926210560185389779 8332252389315840278084669)
            ·
              refine ⟨3124594645993440104281751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8332252389315840278084669 3124594645993440104281751)
              ·
                refine ⟨4686891968990160156422627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124594645993440104281751 4686891968990160156422627)
                ·
                  refine ⟨7030337953485240234633941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686891968990160156422627 7030337953485240234633941)
                  ·
                    refine ⟨164773545784810317999233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7030337953485240234633941 164773545784810317999233)
                    ·
                      rfl

theorem cell22_481343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_481343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481343 prefixEnd_481343 := by exact prefixLift 481343
  have htrace : WordTrace (prefixWord ++ tailWord_481343) baseStart_481343 baseEnd_481343 := by
    simpa [prefixWord, tailWord_481343, baseEnd_481343] using wordTrace_append hprefix tailTrace_481343
  have hstable : (prefixWord ++ tailWord_481343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481343).length < 2 ^ (prefixWord ++ tailWord_481343).sum := by decide
  have hdescent : baseEnd_481343 < baseStart_481343 := by decide
  rcases family_descends (prefixWord ++ tailWord_481343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481409 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_481409 : Nat := 118140960795 + 481409 * 2 ^ 59
def prefixEnd_481409 : Nat := 4983230072969 + 3 ^ 40 * 481409 * 2
def baseEnd_481409 : Nat := 164796138933608145849031

theorem tailTrace_481409 : CollatzResearch.WordTrace tailWord_481409 prefixEnd_481409 164796138933608145849031 := by
  unfold tailWord_481409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558428712944885956591281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705619141963257304394187 17558428712944885956591281)
  ·
    refine ⟨13168821534708664467443461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17558428712944885956591281 13168821534708664467443461)
    ·
      refine ⟨2469154037757874587645649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13168821534708664467443461 2469154037757874587645649)
      ·
        refine ⟨1851865528318405940734237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469154037757874587645649 1851865528318405940734237)
        ·
          refine ⟨694449573119402227775339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1851865528318405940734237 694449573119402227775339)
          ·
            refine ⟨1041674359679103341663009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694449573119402227775339 1041674359679103341663009)
            ·
              refine ⟨781255769759327506247257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041674359679103341663009 781255769759327506247257)
              ·
                refine ⟨585941827319495629685443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781255769759327506247257 585941827319495629685443)
                ·
                  refine ⟨878912740979243444528165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585941827319495629685443 878912740979243444528165)
                  ·
                    refine ⟨164796138933608145849031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878912740979243444528165 164796138933608145849031)
                    ·
                      rfl

theorem cell22_481409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_481409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481409 prefixEnd_481409 := by exact prefixLift 481409
  have htrace : WordTrace (prefixWord ++ tailWord_481409) baseStart_481409 baseEnd_481409 := by
    simpa [prefixWord, tailWord_481409, baseEnd_481409] using wordTrace_append hprefix tailTrace_481409
  have hstable : (prefixWord ++ tailWord_481409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481409).length < 2 ^ (prefixWord ++ tailWord_481409).sum := by decide
  have hdescent : baseEnd_481409 < baseStart_481409 := by decide
  rcases family_descends (prefixWord ++ tailWord_481409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481437 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_481437 : Nat := 118140960795 + 481437 * 2 ^ 59
def prefixEnd_481437 : Nat := 4983230072969 + 3 ^ 40 * 481437 * 2
def baseEnd_481437 : Nat := 164805723905825406148945

theorem tailTrace_481437 : CollatzResearch.WordTrace tailWord_481437 prefixEnd_481437 164805723905825406148945 := by
  unfold tailWord_481437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17559449956843446738610565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11706299971228964492407043 17559449956843446738610565)
  ·
    refine ⟨3292396866908146263489481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17559449956843446738610565 3292396866908146263489481)
    ·
      refine ⟨2469297650181109697617111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292396866908146263489481 2469297650181109697617111)
      ·
        refine ⟨3703946475271664546425667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469297650181109697617111 3703946475271664546425667)
        ·
          refine ⟨5555919712907496819638501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703946475271664546425667 5555919712907496819638501)
          ·
            refine ⟨1041734946170155653682219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5555919712907496819638501 1041734946170155653682219)
            ·
              refine ⟨1562602419255233480523329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041734946170155653682219 1562602419255233480523329)
              ·
                refine ⟨1171951814441425110392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562602419255233480523329 1171951814441425110392497)
                ·
                  refine ⟨878963860831068832794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171951814441425110392497 878963860831068832794373)
                  ·
                    refine ⟨164805723905825406148945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878963860831068832794373 164805723905825406148945)
                    ·
                      rfl

theorem cell22_481437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_481437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481437 prefixEnd_481437 := by exact prefixLift 481437
  have htrace : WordTrace (prefixWord ++ tailWord_481437) baseStart_481437 baseEnd_481437 := by
    simpa [prefixWord, tailWord_481437, baseEnd_481437] using wordTrace_append hprefix tailTrace_481437
  have hstable : (prefixWord ++ tailWord_481437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481437).length < 2 ^ (prefixWord ++ tailWord_481437).sum := by decide
  have hdescent : baseEnd_481437 < baseStart_481437 := by decide
  rcases family_descends (prefixWord ++ tailWord_481437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481460 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_481460 : Nat := 118140960795 + 481460 * 2 ^ 59
def prefixEnd_481460 : Nat := 4983230072969 + 3 ^ 40 * 481460 * 2
def baseEnd_481460 : Nat := 164813597275861012823875

theorem tailTrace_481460 : CollatzResearch.WordTrace tailWord_481460 prefixEnd_481460 164813597275861012823875 := by
  unfold tailWord_481460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780144417880060833348917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11706859223840081111131889 8780144417880060833348917)
  ·
    refine ⟨823138539176255703126461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8780144417880060833348917 823138539176255703126461)
    ·
      refine ⟨308676952191095888672423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 823138539176255703126461 308676952191095888672423)
      ·
        refine ⟨463015428286643833008635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308676952191095888672423 463015428286643833008635)
        ·
          refine ⟨694523142429965749512953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463015428286643833008635 694523142429965749512953)
          ·
            refine ⟨520892356822474312134715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694523142429965749512953 520892356822474312134715)
            ·
              refine ⟨781338535233711468202073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520892356822474312134715 781338535233711468202073)
              ·
                refine ⟨586003901425283601151555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781338535233711468202073 586003901425283601151555)
                ·
                  refine ⟨879005852137925401727333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586003901425283601151555 879005852137925401727333)
                  ·
                    refine ⟨164813597275861012823875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879005852137925401727333 164813597275861012823875)
                    ·
                      rfl

theorem cell22_481460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_481460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481460 prefixEnd_481460 := by exact prefixLift 481460
  have htrace : WordTrace (prefixWord ++ tailWord_481460) baseStart_481460 baseEnd_481460 := by
    simpa [prefixWord, tailWord_481460, baseEnd_481460] using wordTrace_append hprefix tailTrace_481460
  have hstable : (prefixWord ++ tailWord_481460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481460).length < 2 ^ (prefixWord ++ tailWord_481460).sum := by decide
  have hdescent : baseEnd_481460 < baseStart_481460 := by decide
  rcases family_descends (prefixWord ++ tailWord_481460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481495 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_481495 : Nat := 118140960795 + 481495 * 2 ^ 59
def prefixEnd_481495 : Nat := 4983230072969 + 3 ^ 40 * 481495 * 2
def baseEnd_481495 : Nat := 164825578491132588198767

theorem tailTrace_481495 : CollatzResearch.WordTrace tailWord_481495 prefixEnd_481495 164825578491132588198767 := by
  unfold tailWord_481495
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561565390633322644221939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707710260422215096147959 17561565390633322644221939)
  ·
    refine ⟨26342348085949983966332909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17561565390633322644221939 26342348085949983966332909)
    ·
      refine ⟨9878380532231243987374841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26342348085949983966332909 9878380532231243987374841)
      ·
        refine ⟨7408785399173432990531131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878380532231243987374841 7408785399173432990531131)
        ·
          refine ⟨11113178098760149485796697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408785399173432990531131 11113178098760149485796697)
          ·
            refine ⟨8334883574070112114347523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11113178098760149485796697 8334883574070112114347523)
            ·
              refine ⟨12502325361105168171521285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334883574070112114347523 12502325361105168171521285)
              ·
                refine ⟨2344186005207219032160241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12502325361105168171521285 2344186005207219032160241)
                ·
                  refine ⟨1758139503905414274120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344186005207219032160241 1758139503905414274120181)
                  ·
                    refine ⟨164825578491132588198767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1758139503905414274120181 164825578491132588198767)
                    ·
                      rfl

theorem cell22_481495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_481495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481495 prefixEnd_481495 := by exact prefixLift 481495
  have htrace : WordTrace (prefixWord ++ tailWord_481495) baseStart_481495 baseEnd_481495 := by
    simpa [prefixWord, tailWord_481495, baseEnd_481495] using wordTrace_append hprefix tailTrace_481495
  have hstable : (prefixWord ++ tailWord_481495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481495).length < 2 ^ (prefixWord ++ tailWord_481495).sum := by decide
  have hdescent : baseEnd_481495 < baseStart_481495 := by decide
  rcases family_descends (prefixWord ++ tailWord_481495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481512 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_481512 : Nat := 118140960795 + 481512 * 2 ^ 59
def prefixEnd_481512 : Nat := 4983230072969 + 3 ^ 40 * 481512 * 2
def baseEnd_481512 : Nat := 164831397938550210523715

theorem tailTrace_481512 : CollatzResearch.WordTrace tailWord_481512 prefixEnd_481512 164831397938550210523715 := by
  unfold tailWord_481512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781092715785867273795395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11708123621047823031727193 8781092715785867273795395)
  ·
    refine ⟨13171639073678800910693093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8781092715785867273795395 13171639073678800910693093)
    ·
      refine ⟨2469682326314775170754955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13171639073678800910693093 2469682326314775170754955)
      ·
        refine ⟨3704523489472162756132433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469682326314775170754955 3704523489472162756132433)
        ·
          refine ⟨2778392617104122067099325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704523489472162756132433 2778392617104122067099325)
          ·
            refine ⟨1041897231414045775162247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2778392617104122067099325 1041897231414045775162247)
            ·
              refine ⟨1562845847121068662743371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041897231414045775162247 1562845847121068662743371)
              ·
                refine ⟨2344268770681602994115057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562845847121068662743371 2344268770681602994115057)
                ·
                  refine ⟨1758201578011202245586293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344268770681602994115057 1758201578011202245586293)
                  ·
                    refine ⟨164831397938550210523715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1758201578011202245586293 164831397938550210523715)
                    ·
                      rfl

theorem cell22_481512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_481512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481512 prefixEnd_481512 := by exact prefixLift 481512
  have htrace : WordTrace (prefixWord ++ tailWord_481512) baseStart_481512 baseEnd_481512 := by
    simpa [prefixWord, tailWord_481512, baseEnd_481512] using wordTrace_append hprefix tailTrace_481512
  have hstable : (prefixWord ++ tailWord_481512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481512).length < 2 ^ (prefixWord ++ tailWord_481512).sum := by decide
  have hdescent : baseEnd_481512 < baseStart_481512 := by decide
  rcases family_descends (prefixWord ++ tailWord_481512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481544 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_481544 : Nat := 118140960795 + 481544 * 2 ^ 59
def prefixEnd_481544 : Nat := 4983230072969 + 3 ^ 40 * 481544 * 2
def baseEnd_481544 : Nat := 164842352192512793723617

theorem tailTrace_481544 : CollatzResearch.WordTrace tailWord_481544 prefixEnd_481544 164842352192512793723617 := by
  unfold tailWord_481544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781676283727902006377843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11708901711637202675170457 8781676283727902006377843)
  ·
    refine ⟨13172514425591853009566765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8781676283727902006377843 13172514425591853009566765)
    ·
      refine ⟨4939692909596944878587537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13172514425591853009566765 4939692909596944878587537)
      ·
        refine ⟨3704769682197708658940653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939692909596944878587537 3704769682197708658940653)
        ·
          refine ⟨1389288630824140747102745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3704769682197708658940653 1389288630824140747102745)
          ·
            refine ⟨1041966473118105560327059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389288630824140747102745 1041966473118105560327059)
            ·
              refine ⟨1562949709677158340490589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041966473118105560327059 1562949709677158340490589)
              ·
                refine ⟨586106141128934377683971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562949709677158340490589 586106141128934377683971)
                ·
                  refine ⟨879159211693401566525957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586106141128934377683971 879159211693401566525957)
                  ·
                    refine ⟨164842352192512793723617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879159211693401566525957 164842352192512793723617)
                    ·
                      rfl

theorem cell22_481544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_481544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481544 prefixEnd_481544 := by exact prefixLift 481544
  have htrace : WordTrace (prefixWord ++ tailWord_481544) baseStart_481544 baseEnd_481544 := by
    simpa [prefixWord, tailWord_481544, baseEnd_481544] using wordTrace_append hprefix tailTrace_481544
  have hstable : (prefixWord ++ tailWord_481544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481544).length < 2 ^ (prefixWord ++ tailWord_481544).sum := by decide
  have hdescent : baseEnd_481544 < baseStart_481544 := by decide
  rcases family_descends (prefixWord ++ tailWord_481544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481559 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 4]
def baseStart_481559 : Nat := 118140960795 + 481559 * 2 ^ 59
def prefixEnd_481559 : Nat := 4983230072969 + 3 ^ 40 * 481559 * 2
def baseEnd_481559 : Nat := 54949162333019251532857

theorem tailTrace_481559 : CollatzResearch.WordTrace tailWord_481559 prefixEnd_481559 54949162333019251532857 := by
  unfold tailWord_481559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563899662401461574551731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11709266441600974383034487 17563899662401461574551731)
  ·
    refine ⟨26345849493602192361827597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563899662401461574551731 26345849493602192361827597)
    ·
      refine ⟨9879693560100822135685349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26345849493602192361827597 9879693560100822135685349)
      ·
        refine ⟨1852442542518904150441003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9879693560100822135685349 1852442542518904150441003)
        ·
          refine ⟨2778663813778356225661505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852442542518904150441003 2778663813778356225661505)
          ·
            refine ⟨2083997860333767169246129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778663813778356225661505 2083997860333767169246129)
            ·
              refine ⟨1562998395250325376934597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083997860333767169246129 1562998395250325376934597)
              ·
                refine ⟨293062199109436008175237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1562998395250325376934597 293062199109436008175237)
                ·
                  refine ⟨54949162333019251532857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293062199109436008175237 54949162333019251532857)
                  ·
                    rfl

theorem cell22_481559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 4].length) (baseStart_481559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481559 prefixEnd_481559 := by exact prefixLift 481559
  have htrace : WordTrace (prefixWord ++ tailWord_481559) baseStart_481559 baseEnd_481559 := by
    simpa [prefixWord, tailWord_481559, baseEnd_481559] using wordTrace_append hprefix tailTrace_481559
  have hstable : (prefixWord ++ tailWord_481559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481559).length < 2 ^ (prefixWord ++ tailWord_481559).sum := by decide
  have hdescent : baseEnd_481559 < baseStart_481559 := by decide
  rcases family_descends (prefixWord ++ tailWord_481559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481572 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_481572 : Nat := 118140960795 + 481572 * 2 ^ 59
def prefixEnd_481572 : Nat := 4983230072969 + 3 ^ 40 * 481572 * 2
def baseEnd_481572 : Nat := 164851937164730054023531

theorem tailTrace_481572 : CollatzResearch.WordTrace tailWord_481572 prefixEnd_481572 164851937164730054023531 := by
  unfold tailWord_481572
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782186905677182397387485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11709582540902909863183313 8782186905677182397387485)
  ·
    refine ⟨3293320089628943399020307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8782186905677182397387485 3293320089628943399020307)
    ·
      refine ⟨4939980134443415098530461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293320089628943399020307 4939980134443415098530461)
      ·
        refine ⟨1852492550416280661948923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4939980134443415098530461 1852492550416280661948923)
        ·
          refine ⟨2778738825624420992923385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852492550416280661948923 2778738825624420992923385)
          ·
            refine ⟨2084054119218315744692539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778738825624420992923385 2084054119218315744692539)
            ·
              refine ⟨3126081178827473617038809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084054119218315744692539 3126081178827473617038809)
              ·
                refine ⟨2344560884120605212779107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126081178827473617038809 2344560884120605212779107)
                ·
                  refine ⟨3516841326180907819168661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344560884120605212779107 3516841326180907819168661)
                  ·
                    refine ⟨164851937164730054023531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3516841326180907819168661 164851937164730054023531)
                    ·
                      rfl

theorem cell22_481572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_481572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481572 prefixEnd_481572 := by exact prefixLift 481572
  have htrace : WordTrace (prefixWord ++ tailWord_481572) baseStart_481572 baseEnd_481572 := by
    simpa [prefixWord, tailWord_481572, baseEnd_481572] using wordTrace_append hprefix tailTrace_481572
  have hstable : (prefixWord ++ tailWord_481572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481572).length < 2 ^ (prefixWord ++ tailWord_481572).sum := by decide
  have hdescent : baseEnd_481572 < baseStart_481572 := by decide
  rcases family_descends (prefixWord ++ tailWord_481572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481713 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_481713 : Nat := 118140960795 + 481713 * 2 ^ 59
def prefixEnd_481713 : Nat := 4983230072969 + 3 ^ 40 * 481713 * 2
def baseEnd_481713 : Nat := 164900204346252686248099

theorem tailTrace_481713 : CollatzResearch.WordTrace tailWord_481713 prefixEnd_481713 164900204346252686248099 := by
  unfold tailWord_481713
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569516503843545875657793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11713011002562363917105195 17569516503843545875657793)
  ·
    refine ⟨13177137377882659406743345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17569516503843545875657793 13177137377882659406743345)
    ·
      refine ⟨9882853033411994555057509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177137377882659406743345 9882853033411994555057509)
      ·
        refine ⟨1853034943764748979073283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9882853033411994555057509 1853034943764748979073283)
        ·
          refine ⟨2779552415647123468609925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853034943764748979073283 2779552415647123468609925)
          ·
            refine ⟨521166077933835650364361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2779552415647123468609925 521166077933835650364361)
            ·
              refine ⟨390874558450376737773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521166077933835650364361 390874558450376737773271)
              ·
                refine ⟨586311837675565106659907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390874558450376737773271 586311837675565106659907)
                ·
                  refine ⟨879467756513347659989861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586311837675565106659907 879467756513347659989861)
                  ·
                    refine ⟨164900204346252686248099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879467756513347659989861 164900204346252686248099)
                    ·
                      rfl

theorem cell22_481713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_481713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481713 prefixEnd_481713 := by exact prefixLift 481713
  have htrace : WordTrace (prefixWord ++ tailWord_481713) baseStart_481713 baseEnd_481713 := by
    simpa [prefixWord, tailWord_481713, baseEnd_481713] using wordTrace_append hprefix tailTrace_481713
  have hstable : (prefixWord ++ tailWord_481713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481713).length < 2 ^ (prefixWord ++ tailWord_481713).sum := by decide
  have hdescent : baseEnd_481713 < baseStart_481713 := by decide
  rcases family_descends (prefixWord ++ tailWord_481713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481762 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_481762 : Nat := 118140960795 + 481762 * 2 ^ 59
def prefixEnd_481762 : Nat := 4983230072969 + 3 ^ 40 * 481762 * 2
def baseEnd_481762 : Nat := 54972326015877630590983

theorem tailTrace_481762 : CollatzResearch.WordTrace tailWord_481762 prefixEnd_481762 54972326015877630590983 := by
  unfold tailWord_481762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392825920166506811047885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11714202453777351496127693 4392825920166506811047885)
  ·
    refine ⟨1647309720062440054142957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4392825920166506811047885 1647309720062440054142957)
    ·
      refine ⟨617741145023415020303609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1647309720062440054142957 617741145023415020303609)
      ·
        refine ⟨463305858767561265227707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617741145023415020303609 463305858767561265227707)
        ·
          refine ⟨694958788151341897841561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463305858767561265227707 694958788151341897841561)
          ·
            refine ⟨521219091113506423381171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694958788151341897841561 521219091113506423381171)
            ·
              refine ⟨781828636670259635071757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521219091113506423381171 781828636670259635071757)
              ·
                refine ⟨293185738751347363151909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781828636670259635071757 293185738751347363151909)
                ·
                  refine ⟨54972326015877630590983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293185738751347363151909 54972326015877630590983)
                  ·
                    rfl

theorem cell22_481762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_481762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481762 prefixEnd_481762 := by exact prefixLift 481762
  have htrace : WordTrace (prefixWord ++ tailWord_481762) baseStart_481762 baseEnd_481762 := by
    simpa [prefixWord, tailWord_481762, baseEnd_481762] using wordTrace_append hprefix tailTrace_481762
  have hstable : (prefixWord ++ tailWord_481762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481762).length < 2 ^ (prefixWord ++ tailWord_481762).sum := by decide
  have hdescent : baseEnd_481762 < baseStart_481762 := by decide
  rcases family_descends (prefixWord ++ tailWord_481762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481784 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_481784 : Nat := 118140960795 + 481784 * 2 ^ 59
def prefixEnd_481784 : Nat := 4983230072969 + 3 ^ 40 * 481784 * 2
def baseEnd_481784 : Nat := 54974836365744055907627

theorem tailTrace_481784 : CollatzResearch.WordTrace tailWord_481784 prefixEnd_481784 54974836365744055907627 := by
  unfold tailWord_481784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786053043293162500746203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11714737391057550000994937 8786053043293162500746203)
  ·
    refine ⟨13179079564939743751119305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8786053043293162500746203 13179079564939743751119305)
    ·
      refine ⟨9884309673704807813339479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13179079564939743751119305 9884309673704807813339479)
      ·
        refine ⟨14826464510557211720009219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884309673704807813339479 14826464510557211720009219)
        ·
          refine ⟨22239696765835817580013829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14826464510557211720009219 22239696765835817580013829)
          ·
            refine ⟨4169943143594215796252593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22239696765835817580013829 4169943143594215796252593)
            ·
              refine ⟨3127457357695661847189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169943143594215796252593 3127457357695661847189445)
              ·
                refine ⟨586398254567936596348021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3127457357695661847189445 586398254567936596348021)
                ·
                  refine ⟨54974836365744055907627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 586398254567936596348021 54974836365744055907627)
                  ·
                    rfl

theorem cell22_481784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_481784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481784 prefixEnd_481784 := by exact prefixLift 481784
  have htrace : WordTrace (prefixWord ++ tailWord_481784) baseStart_481784 baseEnd_481784 := by
    simpa [prefixWord, tailWord_481784, baseEnd_481784] using wordTrace_append hprefix tailTrace_481784
  have hstable : (prefixWord ++ tailWord_481784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481784).length < 2 ^ (prefixWord ++ tailWord_481784).sum := by decide
  have hdescent : baseEnd_481784 < baseStart_481784 := by decide
  rcases family_descends (prefixWord ++ tailWord_481784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481794 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_481794 : Nat := 118140960795 + 481794 * 2 ^ 59
def prefixEnd_481794 : Nat := 4983230072969 + 3 ^ 40 * 481794 * 2
def baseEnd_481794 : Nat := 164927932301595474972851

theorem tailTrace_481794 : CollatzResearch.WordTrace tailWord_481794 prefixEnd_481794 164927932301595474972851 := by
  unfold tailWord_481794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393117704137524177339109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11714980544366731139570957 4393117704137524177339109)
  ·
    refine ⟨823709569525785783251083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4393117704137524177339109 823709569525785783251083)
    ·
      refine ⟨1235564354288678674876625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823709569525785783251083 1235564354288678674876625)
      ·
        refine ⟨926673265716509006157469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235564354288678674876625 926673265716509006157469)
        ·
          refine ⟨347502474643690877309051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 926673265716509006157469 347502474643690877309051)
          ·
            refine ⟨521253711965536315963577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347502474643690877309051 521253711965536315963577)
            ·
              refine ⟨390940283974152236972683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521253711965536315963577 390940283974152236972683)
              ·
                refine ⟨586410425961228355459025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390940283974152236972683 586410425961228355459025)
                ·
                  refine ⟨439807819470921266594269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586410425961228355459025 439807819470921266594269)
                  ·
                    refine ⟨164927932301595474972851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439807819470921266594269 164927932301595474972851)
                    ·
                      rfl

theorem cell22_481794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_481794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481794 prefixEnd_481794 := by exact prefixLift 481794
  have htrace : WordTrace (prefixWord ++ tailWord_481794) baseStart_481794 baseEnd_481794 := by
    simpa [prefixWord, tailWord_481794, baseEnd_481794] using wordTrace_append hprefix tailTrace_481794
  have hstable : (prefixWord ++ tailWord_481794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481794).length < 2 ^ (prefixWord ++ tailWord_481794).sum := by decide
  have hdescent : baseEnd_481794 < baseStart_481794 := by decide
  rcases family_descends (prefixWord ++ tailWord_481794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_481859 : Nat := 118140960795 + 481859 * 2 ^ 59
def prefixEnd_481859 : Nat := 4983230072969 + 3 ^ 40 * 481859 * 2
def baseEnd_481859 : Nat := 164950183129956972097651

theorem tailTrace_481859 : CollatzResearch.WordTrace tailWord_481859 prefixEnd_481859 164950183129956972097651 := by
  unfold tailWord_481859
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574841561314612810472631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11716561040876408540315087 17574841561314612810472631)
  ·
    refine ⟨26362262341971919215708947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17574841561314612810472631 26362262341971919215708947)
    ·
      refine ⟨39543393512957878823563421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26362262341971919215708947 39543393512957878823563421)
      ·
        refine ⟨14828772567359204558836283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39543393512957878823563421 14828772567359204558836283)
        ·
          refine ⟨22243158851038806838254425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14828772567359204558836283 22243158851038806838254425)
          ·
            refine ⟨16682369138279105128690819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243158851038806838254425 16682369138279105128690819)
            ·
              refine ⟨25023553707418657693036229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682369138279105128690819 25023553707418657693036229)
              ·
                refine ⟨4691916320140998317444293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25023553707418657693036229 4691916320140998317444293)
                ·
                  refine ⟨879734310026437184520805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4691916320140998317444293 879734310026437184520805)
                  ·
                    refine ⟨164950183129956972097651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879734310026437184520805 164950183129956972097651)
                    ·
                      rfl

theorem cell22_481859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_481859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481859 prefixEnd_481859 := by exact prefixLift 481859
  have htrace : WordTrace (prefixWord ++ tailWord_481859) baseStart_481859 baseEnd_481859 := by
    simpa [prefixWord, tailWord_481859, baseEnd_481859] using wordTrace_append hprefix tailTrace_481859
  have hstable : (prefixWord ++ tailWord_481859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481859).length < 2 ^ (prefixWord ++ tailWord_481859).sum := by decide
  have hdescent : baseEnd_481859 < baseStart_481859 := by decide
  rcases family_descends (prefixWord ++ tailWord_481859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481861 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_481861 : Nat := 118140960795 + 481861 * 2 ^ 59
def prefixEnd_481861 : Nat := 4983230072969 + 3 ^ 40 * 481861 * 2
def baseEnd_481861 : Nat := 164950867770829633547645

theorem tailTrace_481861 : CollatzResearch.WordTrace tailWord_481861 prefixEnd_481861 164950867770829633547645 := by
  unfold tailWord_481861
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574914507307367152045437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11716609671538244768030291 17574914507307367152045437)
  ·
    refine ⟨6590592940240262682017039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17574914507307367152045437 6590592940240262682017039)
    ·
      refine ⟨9885889410360394023025559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590592940240262682017039 9885889410360394023025559)
      ·
        refine ⟨14828834115540591034538339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885889410360394023025559 14828834115540591034538339)
        ·
          refine ⟨22243251173310886551807509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14828834115540591034538339 22243251173310886551807509)
          ·
            refine ⟨1042652398748947807115977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22243251173310886551807509 1042652398748947807115977)
            ·
              refine ⟨781989299061710855336983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042652398748947807115977 781989299061710855336983)
              ·
                refine ⟨1172983948592566283005475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781989299061710855336983 1172983948592566283005475)
                ·
                  refine ⟨1759475922888849424508213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172983948592566283005475 1759475922888849424508213)
                  ·
                    refine ⟨164950867770829633547645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1759475922888849424508213 164950867770829633547645)
                    ·
                      rfl

theorem cell22_481861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_481861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481861 prefixEnd_481861 := by exact prefixLift 481861
  have htrace : WordTrace (prefixWord ++ tailWord_481861) baseStart_481861 baseEnd_481861 := by
    simpa [prefixWord, tailWord_481861, baseEnd_481861] using wordTrace_append hprefix tailTrace_481861
  have hstable : (prefixWord ++ tailWord_481861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481861).length < 2 ^ (prefixWord ++ tailWord_481861).sum := by decide
  have hdescent : baseEnd_481861 < baseStart_481861 := by decide
  rcases family_descends (prefixWord ++ tailWord_481861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481876 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_481876 : Nat := 118140960795 + 481876 * 2 ^ 59
def prefixEnd_481876 : Nat := 4983230072969 + 3 ^ 40 * 481876 * 2
def baseEnd_481876 : Nat := 164956002577374594422599

theorem tailTrace_481876 : CollatzResearch.WordTrace tailWord_481876 prefixEnd_481876 164956002577374594422599 := by
  unfold tailWord_481876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787730801126512356920741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11716974401502016475894321 8787730801126512356920741)
  ·
    refine ⟨1647699525211221066922639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8787730801126512356920741 1647699525211221066922639)
    ·
      refine ⟨2471549287816831600383959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647699525211221066922639 2471549287816831600383959)
      ·
        refine ⟨3707323931725247400575939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471549287816831600383959 3707323931725247400575939)
        ·
          refine ⟨5560985897587871100863909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707323931725247400575939 5560985897587871100863909)
          ·
            refine ⟨1042684855797725831411983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5560985897587871100863909 1042684855797725831411983)
            ·
              refine ⟨1564027283696588747117975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042684855797725831411983 1564027283696588747117975)
              ·
                refine ⟨2346040925544883120676963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564027283696588747117975 2346040925544883120676963)
                ·
                  refine ⟨3519061388317324681015445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346040925544883120676963 3519061388317324681015445)
                  ·
                    refine ⟨164956002577374594422599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3519061388317324681015445 164956002577374594422599)
                    ·
                      rfl

theorem cell22_481876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_481876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481876 prefixEnd_481876 := by exact prefixLift 481876
  have htrace : WordTrace (prefixWord ++ tailWord_481876) baseStart_481876 baseEnd_481876 := by
    simpa [prefixWord, tailWord_481876, baseEnd_481876] using wordTrace_append hprefix tailTrace_481876
  have hstable : (prefixWord ++ tailWord_481876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481876).length < 2 ^ (prefixWord ++ tailWord_481876).sum := by decide
  have hdescent : baseEnd_481876 < baseStart_481876 := by decide
  rcases family_descends (prefixWord ++ tailWord_481876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481983 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 1, 4]
def baseStart_481983 : Nat := 118140960795 + 481983 * 2 ^ 59
def prefixEnd_481983 : Nat := 4983230072969 + 3 ^ 40 * 481983 * 2
def baseEnd_481983 : Nat := 164992630864061981997271

theorem tailTrace_481983 : CollatzResearch.WordTrace tailWord_481983 prefixEnd_481983 164992630864061981997271 := by
  unfold tailWord_481983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579364212865381987986603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11719576141910254658657735 17579364212865381987986603)
  ·
    refine ⟨26369046319298072981979905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579364212865381987986603 26369046319298072981979905)
    ·
      refine ⟨19776784739473554736484929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26369046319298072981979905 19776784739473554736484929)
      ·
        refine ⟨14832588554605166052363697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19776784739473554736484929 14832588554605166052363697)
        ·
          refine ⟨11124441415953874539272773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14832588554605166052363697 11124441415953874539272773)
          ·
            refine ⟨2085832765491351476113645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11124441415953874539272773 2085832765491351476113645)
            ·
              refine ⟨782187287059256803542617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085832765491351476113645 782187287059256803542617)
              ·
                refine ⟨586640465294442602656963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782187287059256803542617 586640465294442602656963)
                ·
                  refine ⟨879960697941663903985445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586640465294442602656963 879960697941663903985445)
                  ·
                    refine ⟨164992630864061981997271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879960697941663903985445 164992630864061981997271)
                    ·
                      rfl

theorem cell22_481983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_481983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_481983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_481983 prefixEnd_481983 := by exact prefixLift 481983
  have htrace : WordTrace (prefixWord ++ tailWord_481983) baseStart_481983 baseEnd_481983 := by
    simpa [prefixWord, tailWord_481983, baseEnd_481983] using wordTrace_append hprefix tailTrace_481983
  have hstable : (prefixWord ++ tailWord_481983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481983).length < 2 ^ (prefixWord ++ tailWord_481983).sum := by decide
  have hdescent : baseEnd_481983 < baseStart_481983 := by decide
  rcases family_descends (prefixWord ++ tailWord_481983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482015 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 4]
def baseStart_482015 : Nat := 118140960795 + 482015 * 2 ^ 59
def prefixEnd_482015 : Nat := 4983230072969 + 3 ^ 40 * 482015 * 2
def baseEnd_482015 : Nat := 55001195039341521732391

theorem tailTrace_482015 : CollatzResearch.WordTrace tailWord_482015 prefixEnd_482015 55001195039341521732391 := by
  unfold tailWord_482015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580531348749451453151499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11720354232499634302100999 17580531348749451453151499)
  ·
    refine ⟨26370797023124177179727249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17580531348749451453151499 26370797023124177179727249)
    ·
      refine ⟨19778097767343132884795437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26370797023124177179727249 19778097767343132884795437)
      ·
        refine ⟨7416786662753674831798289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19778097767343132884795437 7416786662753674831798289)
        ·
          refine ⟨5562589997065256123848717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7416786662753674831798289 5562589997065256123848717)
          ·
            refine ⟨2085971248899471046443269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5562589997065256123848717 2085971248899471046443269)
            ·
              refine ⟨391119609168650821208113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2085971248899471046443269 391119609168650821208113)
              ·
                refine ⟨293339706876488115906085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391119609168650821208113 293339706876488115906085)
                ·
                  refine ⟨55001195039341521732391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293339706876488115906085 55001195039341521732391)
                  ·
                    rfl

theorem cell22_482015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 4].length) (baseStart_482015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482015 prefixEnd_482015 := by exact prefixLift 482015
  have htrace : WordTrace (prefixWord ++ tailWord_482015) baseStart_482015 baseEnd_482015 := by
    simpa [prefixWord, tailWord_482015, baseEnd_482015] using wordTrace_append hprefix tailTrace_482015
  have hstable : (prefixWord ++ tailWord_482015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482015).length < 2 ^ (prefixWord ++ tailWord_482015).sum := by decide
  have hdescent : baseEnd_482015 < baseStart_482015 := by decide
  rcases family_descends (prefixWord ++ tailWord_482015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482030 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_482030 : Nat := 118140960795 + 482030 * 2 ^ 59
def prefixEnd_482030 : Nat := 4983230072969 + 3 ^ 40 * 482030 * 2
def baseEnd_482030 : Nat := 165008719924569526072127

theorem tailTrace_482030 : CollatzResearch.WordTrace tailWord_482030 prefixEnd_482030 165008719924569526072127 := by
  unfold tailWord_482030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197634805461888626868443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11720718962463406009965029 2197634805461888626868443)
  ·
    refine ⟨3296452208192832940302665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197634805461888626868443 3296452208192832940302665)
    ·
      refine ⟨2472339156144624705226999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296452208192832940302665 2472339156144624705226999)
      ·
        refine ⟨3708508734216937057840499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472339156144624705226999 3708508734216937057840499)
        ·
          refine ⟨5562763101325405586760749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708508734216937057840499 5562763101325405586760749)
          ·
            refine ⟨2086036162997027095035281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5562763101325405586760749 2086036162997027095035281)
            ·
              refine ⟨1564527122247770321276461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086036162997027095035281 1564527122247770321276461)
              ·
                refine ⟨586697670842913870478673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564527122247770321276461 586697670842913870478673)
                ·
                  refine ⟨440023253132185402859005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586697670842913870478673 440023253132185402859005)
                  ·
                    refine ⟨165008719924569526072127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440023253132185402859005 165008719924569526072127)
                    ·
                      rfl

theorem cell22_482030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_482030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482030 prefixEnd_482030 := by exact prefixLift 482030
  have htrace : WordTrace (prefixWord ++ tailWord_482030) baseStart_482030 baseEnd_482030 := by
    simpa [prefixWord, tailWord_482030, baseEnd_482030] using wordTrace_append hprefix tailTrace_482030
  have hstable : (prefixWord ++ tailWord_482030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482030).length < 2 ^ (prefixWord ++ tailWord_482030).sum := by decide
  have hdescent : baseEnd_482030 < baseStart_482030 := by decide
  rcases family_descends (prefixWord ++ tailWord_482030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482058 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_482058 : Nat := 118140960795 + 482058 * 2 ^ 59
def prefixEnd_482058 : Nat := 4983230072969 + 3 ^ 40 * 482058 * 2
def baseEnd_482058 : Nat := 165018304896786786372041

theorem tailTrace_482058 : CollatzResearch.WordTrace tailWord_482058 prefixEnd_482058 165018304896786786372041 := by
  unfold tailWord_482058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395524921898417449241707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11721399791729113197977885 4395524921898417449241707)
  ·
    refine ⟨6593287382847626173862561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395524921898417449241707 6593287382847626173862561)
    ·
      refine ⟨4944965537135719630396921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6593287382847626173862561 4944965537135719630396921)
      ·
        refine ⟨3708724152851789722797691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4944965537135719630396921 3708724152851789722797691)
        ·
          refine ⟨5563086229277684584196537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708724152851789722797691 5563086229277684584196537)
          ·
            refine ⟨4172314671958263438147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563086229277684584196537 4172314671958263438147403)
            ·
              refine ⟨6258472007937395157221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172314671958263438147403 6258472007937395157221105)
              ·
                refine ⟨4693854005953046367915829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258472007937395157221105 4693854005953046367915829)
                ·
                  refine ⟨440048813058098096992109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693854005953046367915829 440048813058098096992109)
                  ·
                    refine ⟨165018304896786786372041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440048813058098096992109 165018304896786786372041)
                    ·
                      rfl

theorem cell22_482058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_482058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482058 prefixEnd_482058 := by exact prefixLift 482058
  have htrace : WordTrace (prefixWord ++ tailWord_482058) baseStart_482058 baseEnd_482058 := by
    simpa [prefixWord, tailWord_482058, baseEnd_482058] using wordTrace_append hprefix tailTrace_482058
  have hstable : (prefixWord ++ tailWord_482058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482058).length < 2 ^ (prefixWord ++ tailWord_482058).sum := by decide
  have hdescent : baseEnd_482058 < baseStart_482058 := by decide
  rcases family_descends (prefixWord ++ tailWord_482058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482152 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_482152 : Nat := 118140960795 + 482152 * 2 ^ 59
def prefixEnd_482152 : Nat := 4983230072969 + 3 ^ 40 * 482152 * 2
def baseEnd_482152 : Nat := 165050483017801874521753

theorem tailTrace_482152 : CollatzResearch.WordTrace tailWord_482152 prefixEnd_482152 165050483017801874521753 := by
  unfold tailWord_482152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792764074626561925444355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11723685432835415900592473 8792764074626561925444355)
  ·
    refine ⟨13189146111939842888166533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792764074626561925444355 13189146111939842888166533)
    ·
      refine ⟨2472964895988720541531225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13189146111939842888166533 2472964895988720541531225)
      ·
        refine ⟨1854723671991540406148419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2472964895988720541531225 1854723671991540406148419)
        ·
          refine ⟨2782085507987310609222629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854723671991540406148419 2782085507987310609222629)
          ·
            refine ⟨521641032747620739229243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2782085507987310609222629 521641032747620739229243)
            ·
              refine ⟨782461549121431108843865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521641032747620739229243 782461549121431108843865)
              ·
                refine ⟨586846161841073331632899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782461549121431108843865 586846161841073331632899)
                ·
                  refine ⟨880269242761609997449349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586846161841073331632899 880269242761609997449349)
                  ·
                    refine ⟨165050483017801874521753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880269242761609997449349 165050483017801874521753)
                    ·
                      rfl

theorem cell22_482152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_482152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482152 prefixEnd_482152 := by exact prefixLift 482152
  have htrace : WordTrace (prefixWord ++ tailWord_482152) baseStart_482152 baseEnd_482152 := by
    simpa [prefixWord, tailWord_482152, baseEnd_482152] using wordTrace_append hprefix tailTrace_482152
  have hstable : (prefixWord ++ tailWord_482152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482152).length < 2 ^ (prefixWord ++ tailWord_482152).sum := by decide
  have hdescent : baseEnd_482152 < baseStart_482152 := by decide
  rcases family_descends (prefixWord ++ tailWord_482152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482163 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_482163 : Nat := 118140960795 + 482163 * 2 ^ 59
def prefixEnd_482163 : Nat := 4983230072969 + 3 ^ 40 * 482163 * 2
def baseEnd_482163 : Nat := 165054248542601512496719

theorem tailTrace_482163 : CollatzResearch.WordTrace tailWord_482163 prefixEnd_482163 165054248542601512496719 := by
  unfold tailWord_482163
  simp only [CollatzResearch.WordTrace]
  refine ⟨17585929352213272729539143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11723952901475515153026095 17585929352213272729539143)
  ·
    refine ⟨26378894028319909094308715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17585929352213272729539143 26378894028319909094308715)
    ·
      refine ⟨39568341042479863641463073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26378894028319909094308715 39568341042479863641463073)
      ·
        refine ⟨29676255781859897731097305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39568341042479863641463073 29676255781859897731097305)
        ·
          refine ⟨22257191836394923298322979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29676255781859897731097305 22257191836394923298322979)
          ·
            refine ⟨33385787754592384947484469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22257191836394923298322979 33385787754592384947484469)
            ·
              refine ⟨3129917601993036088826669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33385787754592384947484469 3129917601993036088826669)
              ·
                refine ⟨1173719100747388533310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129917601993036088826669 1173719100747388533310001)
                ·
                  refine ⟨880289325560541399982501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173719100747388533310001 880289325560541399982501)
                  ·
                    refine ⟨165054248542601512496719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880289325560541399982501 165054248542601512496719)
                    ·
                      rfl

theorem cell22_482163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_482163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482163 prefixEnd_482163 := by exact prefixLift 482163
  have htrace : WordTrace (prefixWord ++ tailWord_482163) baseStart_482163 baseEnd_482163 := by
    simpa [prefixWord, tailWord_482163, baseEnd_482163] using wordTrace_append hprefix tailTrace_482163
  have hstable : (prefixWord ++ tailWord_482163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482163).length < 2 ^ (prefixWord ++ tailWord_482163).sum := by decide
  have hdescent : baseEnd_482163 < baseStart_482163 := by decide
  rcases family_descends (prefixWord ++ tailWord_482163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482165 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_482165 : Nat := 118140960795 + 482165 * 2 ^ 59
def prefixEnd_482165 : Nat := 4983230072969 + 3 ^ 40 * 482165 * 2
def baseEnd_482165 : Nat := 165054933183474173946713

theorem tailTrace_482165 : CollatzResearch.WordTrace tailWord_482165 prefixEnd_482165 165054933183474173946713 := by
  unfold tailWord_482165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586002298206027071111949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11724001532137351380741299 17586002298206027071111949)
  ·
    refine ⟨6594750861827260151666981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17586002298206027071111949 6594750861827260151666981)
    ·
      refine ⟨1236515786592611278437559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6594750861827260151666981 1236515786592611278437559)
      ·
        refine ⟨1854773679888916917656339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236515786592611278437559 1854773679888916917656339)
        ·
          refine ⟨2782160519833375376484509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854773679888916917656339 2782160519833375376484509)
          ·
            refine ⟨1043310194937515766181691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2782160519833375376484509 1043310194937515766181691)
            ·
              refine ⟨1564965292406273649272537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043310194937515766181691 1564965292406273649272537)
              ·
                refine ⟨1173723969304705236954403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564965292406273649272537 1173723969304705236954403)
                ·
                  refine ⟨1760585953957057855431605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173723969304705236954403 1760585953957057855431605)
                  ·
                    refine ⟨165054933183474173946713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1760585953957057855431605 165054933183474173946713)
                    ·
                      rfl

theorem cell22_482165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_482165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482165 prefixEnd_482165 := by exact prefixLift 482165
  have htrace : WordTrace (prefixWord ++ tailWord_482165) baseStart_482165 baseEnd_482165 := by
    simpa [prefixWord, tailWord_482165, baseEnd_482165] using wordTrace_append hprefix tailTrace_482165
  have hstable : (prefixWord ++ tailWord_482165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482165).length < 2 ^ (prefixWord ++ tailWord_482165).sum := by decide
  have hdescent : baseEnd_482165 < baseStart_482165 := by decide
  rcases family_descends (prefixWord ++ tailWord_482165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482184 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_482184 : Nat := 118140960795 + 482184 * 2 ^ 59
def prefixEnd_482184 : Nat := 4983230072969 + 3 ^ 40 * 482184 * 2
def baseEnd_482184 : Nat := 55020479090588152573885

theorem tailTrace_482184 : CollatzResearch.WordTrace tailWord_482184 prefixEnd_482184 55020479090588152573885 := by
  unfold tailWord_482184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793347642568596658026803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11724463523424795544035737 8793347642568596658026803)
  ·
    refine ⟨13190021463852894987040205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8793347642568596658026803 13190021463852894987040205)
    ·
      refine ⟨4946258048944835620140077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13190021463852894987040205 4946258048944835620140077)
      ·
        refine ⟨1854846768354313357552529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4946258048944835620140077 1854846768354313357552529)
        ·
          refine ⟨1391135076265735018164397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854846768354313357552529 1391135076265735018164397)
          ·
            refine ⟨521675653599650631811649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391135076265735018164397 521675653599650631811649)
            ·
              refine ⟨391256740199737973858737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521675653599650631811649 391256740199737973858737)
              ·
                refine ⟨293442555149803480394053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391256740199737973858737 293442555149803480394053)
                ·
                  refine ⟨55020479090588152573885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293442555149803480394053 55020479090588152573885)
                  ·
                    rfl

theorem cell22_482184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_482184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482184 prefixEnd_482184 := by exact prefixLift 482184
  have htrace : WordTrace (prefixWord ++ tailWord_482184) baseStart_482184 baseEnd_482184 := by
    simpa [prefixWord, tailWord_482184, baseEnd_482184] using wordTrace_append hprefix tailTrace_482184
  have hstable : (prefixWord ++ tailWord_482184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482184).length < 2 ^ (prefixWord ++ tailWord_482184).sum := by decide
  have hdescent : baseEnd_482184 < baseStart_482184 := by decide
  rcases family_descends (prefixWord ++ tailWord_482184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482240 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_482240 : Nat := 118140960795 + 482240 * 2 ^ 59
def prefixEnd_482240 : Nat := 4983230072969 + 3 ^ 40 * 482240 * 2
def baseEnd_482240 : Nat := 55026869072066326107161

theorem tailTrace_482240 : CollatzResearch.WordTrace tailWord_482240 prefixEnd_482240 55026869072066326107161 := by
  unfold tailWord_482240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794368886467157440046087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11725825181956209920061449 8794368886467157440046087)
  ·
    refine ⟨13191553329700736160069131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794368886467157440046087 13191553329700736160069131)
    ·
      refine ⟨19787329994551104240103697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191553329700736160069131 19787329994551104240103697)
      ·
        refine ⟨14840497495913328180077773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19787329994551104240103697 14840497495913328180077773)
        ·
          refine ⟨5565186560967498067529165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14840497495913328180077773 5565186560967498067529165)
          ·
            refine ⟨2086944960362811775323437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5565186560967498067529165 2086944960362811775323437)
            ·
              refine ⟨782604360136054415746289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2086944960362811775323437 782604360136054415746289)
              ·
                refine ⟨586953270102040811809717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782604360136054415746289 586953270102040811809717)
                ·
                  refine ⟨55026869072066326107161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 586953270102040811809717 55026869072066326107161)
                  ·
                    rfl

theorem cell22_482240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_482240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482240 prefixEnd_482240 := by exact prefixLift 482240
  have htrace : WordTrace (prefixWord ++ tailWord_482240) baseStart_482240 baseEnd_482240 := by
    simpa [prefixWord, tailWord_482240, baseEnd_482240] using wordTrace_append hprefix tailTrace_482240
  have hstable : (prefixWord ++ tailWord_482240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482240).length < 2 ^ (prefixWord ++ tailWord_482240).sum := by decide
  have hdescent : baseEnd_482240 < baseStart_482240 := by decide
  rcases family_descends (prefixWord ++ tailWord_482240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482360 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_482360 : Nat := 118140960795 + 482360 * 2 ^ 59
def prefixEnd_482360 : Nat := 4983230072969 + 3 ^ 40 * 482360 * 2
def baseEnd_482360 : Nat := 165121685668558665321115

theorem tailTrace_482360 : CollatzResearch.WordTrace tailWord_482360 prefixEnd_482360 165121685668558665321115 := by
  unfold tailWord_482360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796557266249787687230267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11728743021666383582973689 8796557266249787687230267)
  ·
    refine ⟨13194835899374681530845401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8796557266249787687230267 13194835899374681530845401)
    ·
      refine ⟨9896126924531011148134051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13194835899374681530845401 9896126924531011148134051)
      ·
        refine ⟨14844190386796516722201077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896126924531011148134051 14844190386796516722201077)
        ·
          refine ⟨1391642848762173442706351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14844190386796516722201077 1391642848762173442706351)
          ·
            refine ⟨2087464273143260164059527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391642848762173442706351 2087464273143260164059527)
            ·
              refine ⟨3131196409714890246089291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087464273143260164059527 3131196409714890246089291)
              ·
                refine ⟨4696794614572335369133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131196409714890246089291 4696794614572335369133937)
                ·
                  refine ⟨3522595960929251526850453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696794614572335369133937 3522595960929251526850453)
                  ·
                    refine ⟨165121685668558665321115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3522595960929251526850453 165121685668558665321115)
                    ·
                      rfl

theorem cell22_482360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_482360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482360 prefixEnd_482360 := by exact prefixLift 482360
  have htrace : WordTrace (prefixWord ++ tailWord_482360) baseStart_482360 baseEnd_482360 := by
    simpa [prefixWord, tailWord_482360, baseEnd_482360] using wordTrace_append hprefix tailTrace_482360
  have hstable : (prefixWord ++ tailWord_482360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482360).length < 2 ^ (prefixWord ++ tailWord_482360).sum := by decide
  have hdescent : baseEnd_482360 < baseStart_482360 := by decide
  rcases family_descends (prefixWord ++ tailWord_482360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482396 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_482396 : Nat := 118140960795 + 482396 * 2 ^ 59
def prefixEnd_482396 : Nat := 4983230072969 + 3 ^ 40 * 482396 * 2
def baseEnd_482396 : Nat := 165134009204266571421005

theorem tailTrace_482396 : CollatzResearch.WordTrace tailWord_482396 prefixEnd_482396 165134009204266571421005 := by
  unfold tailWord_482396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797213780184576761385521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11729618373579435681847361 8797213780184576761385521)
  ·
    refine ⟨6597910335138432571039141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8797213780184576761385521 6597910335138432571039141)
    ·
      refine ⟨1237108187838456107069839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6597910335138432571039141 1237108187838456107069839)
      ·
        refine ⟨1855662281757684160604759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237108187838456107069839 1855662281757684160604759)
        ·
          refine ⟨2783493422636526240907139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855662281757684160604759 2783493422636526240907139)
          ·
            refine ⟨4175240133954789361360709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783493422636526240907139 4175240133954789361360709)
            ·
              refine ⟨782857525116523005255133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4175240133954789361360709 782857525116523005255133)
              ·
                refine ⟨293571571918696126970675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 782857525116523005255133 293571571918696126970675)
                ·
                  refine ⟨440357357878044190456013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293571571918696126970675 440357357878044190456013)
                  ·
                    refine ⟨165134009204266571421005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440357357878044190456013 165134009204266571421005)
                    ·
                      rfl

theorem cell22_482396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_482396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482396 prefixEnd_482396 := by exact prefixLift 482396
  have htrace : WordTrace (prefixWord ++ tailWord_482396) baseStart_482396 baseEnd_482396 := by
    simpa [prefixWord, tailWord_482396, baseEnd_482396] using wordTrace_append hprefix tailTrace_482396
  have hstable : (prefixWord ++ tailWord_482396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482396).length < 2 ^ (prefixWord ++ tailWord_482396).sum := by decide
  have hdescent : baseEnd_482396 < baseStart_482396 := by decide
  rcases family_descends (prefixWord ++ tailWord_482396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482482 : List Nat := [3, 2, 1, 1, 1, 5, 2, 7]
def baseStart_482482 : Nat := 118140960795 + 482482 * 2 ^ 59
def prefixEnd_482482 : Nat := 4983230072969 + 3 ^ 40 * 482482 * 2
def baseEnd_482482 : Nat := 18351494306865668196749

theorem tailTrace_482482 : CollatzResearch.WordTrace tailWord_482482 prefixEnd_482482 18351494306865668196749 := by
  unfold tailWord_482482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399391059514397552600425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11731709492038393473601133 4399391059514397552600425)
  ·
    refine ⟨3299543294635798164450319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4399391059514397552600425 3299543294635798164450319)
    ·
      refine ⟨4949314941953697246675479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299543294635798164450319 4949314941953697246675479)
      ·
        refine ⟨7423972412930545870013219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4949314941953697246675479 7423972412930545870013219)
        ·
          refine ⟨11135958619395818805019829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423972412930545870013219 11135958619395818805019829)
          ·
            refine ⟨1043996120568358012970609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11135958619395818805019829 1043996120568358012970609)
            ·
              refine ⟨782997090426268509727957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043996120568358012970609 782997090426268509727957)
              ·
                refine ⟨18351494306865668196749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 782997090426268509727957 18351494306865668196749)
                ·
                  rfl

theorem cell22_482482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_482482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482482 prefixEnd_482482 := by exact prefixLift 482482
  have htrace : WordTrace (prefixWord ++ tailWord_482482) baseStart_482482 baseEnd_482482 := by
    simpa [prefixWord, tailWord_482482, baseEnd_482482] using wordTrace_append hprefix tailTrace_482482
  have hstable : (prefixWord ++ tailWord_482482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482482).length < 2 ^ (prefixWord ++ tailWord_482482).sum := by decide
  have hdescent : baseEnd_482482 < baseStart_482482 := by decide
  rcases family_descends (prefixWord ++ tailWord_482482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482527 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 5]
def baseStart_482527 : Nat := 118140960795 + 482527 * 2 ^ 59
def prefixEnd_482527 : Nat := 4983230072969 + 3 ^ 40 * 482527 * 2
def baseEnd_482527 : Nat := 55059617727141965465201

theorem tailTrace_482527 : CollatzResearch.WordTrace tailWord_482527 prefixEnd_482527 55059617727141965465201 := by
  unfold tailWord_482527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599205522894562895789835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11732803681929708597193223 17599205522894562895789835)
  ·
    refine ⟨26398808284341844343684753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17599205522894562895789835 26398808284341844343684753)
    ·
      refine ⟨19799106213256383257763565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26398808284341844343684753 19799106213256383257763565)
      ·
        refine ⟨7424664829971143721661337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19799106213256383257763565 7424664829971143721661337)
        ·
          refine ⟨5568498622478357791246003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7424664829971143721661337 5568498622478357791246003)
          ·
            refine ⟨8352747933717536686869005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568498622478357791246003 8352747933717536686869005)
            ·
              refine ⟨3132280475144076257575877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8352747933717536686869005 3132280475144076257575877)
              ·
                refine ⟨587302589089514298295477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3132280475144076257575877 587302589089514298295477)
                ·
                  refine ⟨55059617727141965465201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587302589089514298295477 55059617727141965465201)
                  ·
                    rfl

theorem cell22_482527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].length) (baseStart_482527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482527 prefixEnd_482527 := by exact prefixLift 482527
  have htrace : WordTrace (prefixWord ++ tailWord_482527) baseStart_482527 baseEnd_482527 := by
    simpa [prefixWord, tailWord_482527, baseEnd_482527] using wordTrace_append hprefix tailTrace_482527
  have hstable : (prefixWord ++ tailWord_482527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482527).length < 2 ^ (prefixWord ++ tailWord_482527).sum := by decide
  have hdescent : baseEnd_482527 < baseStart_482527 := by decide
  rcases family_descends (prefixWord ++ tailWord_482527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482542 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_482542 : Nat := 118140960795 + 482542 * 2 ^ 59
def prefixEnd_482542 : Nat := 4983230072969 + 3 ^ 40 * 482542 * 2
def baseEnd_482542 : Nat := 165183987987970857270557

theorem tailTrace_482542 : CollatzResearch.WordTrace tailWord_482542 prefixEnd_482542 165183987987970857270557 := by
  unfold tailWord_482542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199969077230027557198235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11733168411893480305057253 2199969077230027557198235)
  ·
    refine ⟨3299953615845041335797353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199969077230027557198235 3299953615845041335797353)
    ·
      refine ⟨2474965211883781001848015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3299953615845041335797353 2474965211883781001848015)
      ·
        refine ⟨3712447817825671502772023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474965211883781001848015 3712447817825671502772023)
        ·
          refine ⟨5568671726738507254158035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712447817825671502772023 5568671726738507254158035)
          ·
            refine ⟨8353007590107760881237053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568671726738507254158035 8353007590107760881237053)
            ·
              refine ⟨3132377846290410330463895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8353007590107760881237053 3132377846290410330463895)
              ·
                refine ⟨4698566769435615495695843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132377846290410330463895 4698566769435615495695843)
                ·
                  refine ⟨7047850154153423243543765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698566769435615495695843 7047850154153423243543765)
                  ·
                    refine ⟨165183987987970857270557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7047850154153423243543765 165183987987970857270557)
                    ·
                      rfl

theorem cell22_482542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_482542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482542 prefixEnd_482542 := by exact prefixLift 482542
  have htrace : WordTrace (prefixWord ++ tailWord_482542) baseStart_482542 baseEnd_482542 := by
    simpa [prefixWord, tailWord_482542, baseEnd_482542] using wordTrace_append hprefix tailTrace_482542
  have hstable : (prefixWord ++ tailWord_482542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482542).length < 2 ^ (prefixWord ++ tailWord_482542).sum := by decide
  have hdescent : baseEnd_482542 < baseStart_482542 := by decide
  rcases family_descends (prefixWord ++ tailWord_482542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482589 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 6]
def baseStart_482589 : Nat := 118140960795 + 482589 * 2 ^ 59
def prefixEnd_482589 : Nat := 4983230072969 + 3 ^ 40 * 482589 * 2
def baseEnd_482589 : Nat := 55066692349492800448471

theorem tailTrace_482589 : CollatzResearch.WordTrace tailWord_482589 prefixEnd_482589 55066692349492800448471 := by
  unfold tailWord_482589
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601466848669947484546821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11734311232446631656364547 17601466848669947484546821)
  ·
    refine ⟨3300275034125615153352529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17601466848669947484546821 3300275034125615153352529)
    ·
      refine ⟨2475206275594211365014397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3300275034125615153352529 2475206275594211365014397)
      ·
        refine ⟨928202353347829261880399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2475206275594211365014397 928202353347829261880399)
        ·
          refine ⟨1392303530021743892820599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928202353347829261880399 1392303530021743892820599)
          ·
            refine ⟨2088455295032615839230899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392303530021743892820599 2088455295032615839230899)
            ·
              refine ⟨3132682942548923758846349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088455295032615839230899 3132682942548923758846349)
              ·
                refine ⟨1174756103455846409567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3132682942548923758846349 1174756103455846409567381)
                ·
                  refine ⟨55066692349492800448471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1174756103455846409567381 55066692349492800448471)
                  ·
                    rfl

theorem cell22_482589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_482589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482589 prefixEnd_482589 := by exact prefixLift 482589
  have htrace : WordTrace (prefixWord ++ tailWord_482589) baseStart_482589 baseEnd_482589 := by
    simpa [prefixWord, tailWord_482589, baseEnd_482589] using wordTrace_append hprefix tailTrace_482589
  have hstable : (prefixWord ++ tailWord_482589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482589).length < 2 ^ (prefixWord ++ tailWord_482589).sum := by decide
  have hdescent : baseEnd_482589 < baseStart_482589 := by decide
  rcases family_descends (prefixWord ++ tailWord_482589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482696 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_482696 : Nat := 118140960795 + 482696 * 2 ^ 59
def prefixEnd_482696 : Nat := 4983230072969 + 3 ^ 40 * 482696 * 2
def baseEnd_482696 : Nat := 55078901778388596306695

theorem tailTrace_482696 : CollatzResearch.WordTrace tailWord_482696 prefixEnd_482696 55078901778388596306695 := by
  unfold tailWord_482696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802684729641152379345971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11736912972854869839127961 8802684729641152379345971)
  ·
    refine ⟨13204027094461728569018957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802684729641152379345971 13204027094461728569018957)
    ·
      refine ⟨4951510160423148213382109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13204027094461728569018957 4951510160423148213382109)
      ·
        refine ⟨1856816310158680580018291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4951510160423148213382109 1856816310158680580018291)
        ·
          refine ⟨2785224465238020870027437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856816310158680580018291 2785224465238020870027437)
          ·
            refine ⟨1044459174464257826260289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785224465238020870027437 1044459174464257826260289)
            ·
              refine ⟨783344380848193369695217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044459174464257826260289 783344380848193369695217)
              ·
                refine ⟨587508285636145027271413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783344380848193369695217 587508285636145027271413)
                ·
                  refine ⟨55078901778388596306695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587508285636145027271413 55078901778388596306695)
                  ·
                    rfl

theorem cell22_482696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_482696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482696 prefixEnd_482696 := by exact prefixLift 482696
  have htrace : WordTrace (prefixWord ++ tailWord_482696) baseStart_482696 baseEnd_482696 := by
    simpa [prefixWord, tailWord_482696, baseEnd_482696] using wordTrace_append hprefix tailTrace_482696
  have hstable : (prefixWord ++ tailWord_482696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482696).length < 2 ^ (prefixWord ++ tailWord_482696).sum := by decide
  have hdescent : baseEnd_482696 < baseStart_482696 := by decide
  rcases family_descends (prefixWord ++ tailWord_482696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482707 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 12]
def baseStart_482707 : Nat := 118140960795 + 482707 * 2 ^ 59
def prefixEnd_482707 : Nat := 4983230072969 + 3 ^ 40 * 482707 * 2
def baseEnd_482707 : Nat := 55080156953321808965017

theorem tailTrace_482707 : CollatzResearch.WordTrace tailWord_482707 prefixEnd_482707 55080156953321808965017 := by
  unfold tailWord_482707
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605770662242453637342375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11737180441494969091561583 17605770662242453637342375)
  ·
    refine ⟨26408655993363680456013563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17605770662242453637342375 26408655993363680456013563)
    ·
      refine ⟨39612983990045520684020345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26408655993363680456013563 39612983990045520684020345)
      ·
        refine ⟨29709737992534140513015259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39612983990045520684020345 29709737992534140513015259)
        ·
          refine ⟨44564606988801210769522889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29709737992534140513015259 44564606988801210769522889)
          ·
            refine ⟨33423455241600908077142167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44564606988801210769522889 33423455241600908077142167)
            ·
              refine ⟨50135182862401362115713251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33423455241600908077142167 50135182862401362115713251)
              ·
                refine ⟨75202774293602043173569877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50135182862401362115713251 75202774293602043173569877)
                ·
                  refine ⟨55080156953321808965017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 75202774293602043173569877 55080156953321808965017)
                  ·
                    rfl

theorem cell22_482707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_482707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482707 prefixEnd_482707 := by exact prefixLift 482707
  have htrace : WordTrace (prefixWord ++ tailWord_482707) baseStart_482707 baseEnd_482707 := by
    simpa [prefixWord, tailWord_482707, baseEnd_482707] using wordTrace_append hprefix tailTrace_482707
  have hstable : (prefixWord ++ tailWord_482707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482707).length < 2 ^ (prefixWord ++ tailWord_482707).sum := by decide
  have hdescent : baseEnd_482707 < baseStart_482707 := by decide
  rcases family_descends (prefixWord ++ tailWord_482707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482709 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_482709 : Nat := 118140960795 + 482709 * 2 ^ 59
def prefixEnd_482709 : Nat := 4983230072969 + 3 ^ 40 * 482709 * 2
def baseEnd_482709 : Nat := 165241155500838088345045

theorem tailTrace_482709 : CollatzResearch.WordTrace tailWord_482709 prefixEnd_482709 165241155500838088345045 := by
  unfold tailWord_482709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605843608235207978915181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11737229072156805319276787 17605843608235207978915181)
  ·
    refine ⟨6602191353088202992093193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17605843608235207978915181 6602191353088202992093193)
    ·
      refine ⟨4951643514816152244069895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6602191353088202992093193 4951643514816152244069895)
      ·
        refine ⟨7427465272224228366104843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951643514816152244069895 7427465272224228366104843)
        ·
          refine ⟨11141197908336342549157265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427465272224228366104843 11141197908336342549157265)
          ·
            refine ⟨8355898431252256911867949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11141197908336342549157265 8355898431252256911867949)
            ·
              refine ⟨3133461911719596341950481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8355898431252256911867949 3133461911719596341950481)
              ·
                refine ⟨2350096433789697256462861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133461911719596341950481 2350096433789697256462861)
                ·
                  refine ⟨881286162671136471173573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2350096433789697256462861 881286162671136471173573)
                  ·
                    refine ⟨165241155500838088345045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 881286162671136471173573 165241155500838088345045)
                    ·
                      rfl

theorem cell22_482709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_482709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482709 prefixEnd_482709 := by exact prefixLift 482709
  have htrace : WordTrace (prefixWord ++ tailWord_482709) baseStart_482709 baseEnd_482709 := by
    simpa [prefixWord, tailWord_482709, baseEnd_482709] using wordTrace_append hprefix tailTrace_482709
  have hstable : (prefixWord ++ tailWord_482709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482709).length < 2 ^ (prefixWord ++ tailWord_482709).sum := by decide
  have hdescent : baseEnd_482709 < baseStart_482709 := by decide
  rcases family_descends (prefixWord ++ tailWord_482709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482891 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 6, 3]
def baseStart_482891 : Nat := 118140960795 + 482891 * 2 ^ 59
def prefixEnd_482891 : Nat := 4983230072969 + 3 ^ 40 * 482891 * 2
def baseEnd_482891 : Nat := 165303457820250280294487

theorem tailTrace_482891 : CollatzResearch.WordTrace tailWord_482891 prefixEnd_482891 165303457820250280294487 := by
  unfold tailWord_482891
  simp only [CollatzResearch.WordTrace]
  refine ⟨17612481693575853062040527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11741654462383902041360351 17612481693575853062040527)
  ·
    refine ⟨26418722540363779593060791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17612481693575853062040527 26418722540363779593060791)
    ·
      refine ⟨39628083810545669389591187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26418722540363779593060791 39628083810545669389591187)
      ·
        refine ⟨59442125715818504084386781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39628083810545669389591187 59442125715818504084386781)
        ·
          refine ⟨22290797143431939031645043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59442125715818504084386781 22290797143431939031645043)
          ·
            refine ⟨33436195715147908547467565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290797143431939031645043 33436195715147908547467565)
            ·
              refine ⟨12538573393180465705300337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33436195715147908547467565 12538573393180465705300337)
              ·
                refine ⟨9403930044885349278975253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538573393180465705300337 9403930044885349278975253)
                ·
                  refine ⟨440809220854000747451965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9403930044885349278975253 440809220854000747451965)
                  ·
                    refine ⟨165303457820250280294487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440809220854000747451965 165303457820250280294487)
                    ·
                      rfl

theorem cell22_482891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].length) (baseStart_482891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482891 prefixEnd_482891 := by exact prefixLift 482891
  have htrace : WordTrace (prefixWord ++ tailWord_482891) baseStart_482891 baseEnd_482891 := by
    simpa [prefixWord, tailWord_482891, baseEnd_482891] using wordTrace_append hprefix tailTrace_482891
  have hstable : (prefixWord ++ tailWord_482891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482891).length < 2 ^ (prefixWord ++ tailWord_482891).sum := by decide
  have hdescent : baseEnd_482891 < baseStart_482891 := by decide
  rcases family_descends (prefixWord ++ tailWord_482891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482908 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_482908 : Nat := 118140960795 + 482908 * 2 ^ 59
def prefixEnd_482908 : Nat := 4983230072969 + 3 ^ 40 * 482908 * 2
def baseEnd_482908 : Nat := 165309277267667902619435

theorem tailTrace_482908 : CollatzResearch.WordTrace tailWord_482908 prefixEnd_482908 165309277267667902619435 := by
  unfold tailWord_482908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806550867257132482704689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11742067823009509976939585 8806550867257132482704689)
  ·
    refine ⟨6604913150442849362028517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8806550867257132482704689 6604913150442849362028517)
    ·
      refine ⟨1238421215708034255380347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6604913150442849362028517 1238421215708034255380347)
      ·
        refine ⟨1857631823562051383070521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238421215708034255380347 1857631823562051383070521)
        ·
          refine ⟨1393223867671538537302891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857631823562051383070521 1393223867671538537302891)
          ·
            refine ⟨2089835801507307805954337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393223867671538537302891 2089835801507307805954337)
            ·
              refine ⟨1567376851130480854465753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089835801507307805954337 1567376851130480854465753)
              ·
                refine ⟨1175532638347860640849315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567376851130480854465753 1175532638347860640849315)
                ·
                  refine ⟨1763298957521790961273973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175532638347860640849315 1763298957521790961273973)
                  ·
                    refine ⟨165309277267667902619435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1763298957521790961273973 165309277267667902619435)
                    ·
                      rfl

theorem cell22_482908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_482908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482908 prefixEnd_482908 := by exact prefixLift 482908
  have htrace : WordTrace (prefixWord ++ tailWord_482908) baseStart_482908 baseEnd_482908 := by
    simpa [prefixWord, tailWord_482908, baseEnd_482908] using wordTrace_append hprefix tailTrace_482908
  have hstable : (prefixWord ++ tailWord_482908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482908).length < 2 ^ (prefixWord ++ tailWord_482908).sum := by decide
  have hdescent : baseEnd_482908 < baseStart_482908 := by decide
  rcases family_descends (prefixWord ++ tailWord_482908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482925 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_482925 : Nat := 118140960795 + 482925 * 2 ^ 59
def prefixEnd_482925 : Nat := 4983230072969 + 3 ^ 40 * 482925 * 2
def baseEnd_482925 : Nat := 165315096715085524944383

theorem tailTrace_482925 : CollatzResearch.WordTrace tailWord_482925 prefixEnd_482925 165315096715085524944383 := by
  unfold tailWord_482925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17613721775452676868778229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11742481183635117912518819 17613721775452676868778229)
  ·
    refine ⟨1651286416448688456447959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17613721775452676868778229 1651286416448688456447959)
    ·
      refine ⟨2476929624673032684671939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651286416448688456447959 2476929624673032684671939)
      ·
        refine ⟨3715394437009549027007909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476929624673032684671939 3715394437009549027007909)
        ·
          refine ⟨696636456939290442563983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3715394437009549027007909 696636456939290442563983)
          ·
            refine ⟨1044954685408935663845975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696636456939290442563983 1044954685408935663845975)
            ·
              refine ⟨1567432028113403495768963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044954685408935663845975 1567432028113403495768963)
              ·
                refine ⟨2351148042170105243653445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567432028113403495768963 2351148042170105243653445)
                ·
                  refine ⟨440840257906894733185021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351148042170105243653445 440840257906894733185021)
                  ·
                    refine ⟨165315096715085524944383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440840257906894733185021 165315096715085524944383)
                    ·
                      rfl

theorem cell22_482925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_482925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482925 prefixEnd_482925 := by exact prefixLift 482925
  have htrace : WordTrace (prefixWord ++ tailWord_482925) baseStart_482925 baseEnd_482925 := by
    simpa [prefixWord, tailWord_482925, baseEnd_482925] using wordTrace_append hprefix tailTrace_482925
  have hstable : (prefixWord ++ tailWord_482925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482925).length < 2 ^ (prefixWord ++ tailWord_482925).sum := by decide
  have hdescent : baseEnd_482925 < baseStart_482925 := by decide
  rcases family_descends (prefixWord ++ tailWord_482925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482953 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_482953 : Nat := 118140960795 + 482953 * 2 ^ 59
def prefixEnd_482953 : Nat := 4983230072969 + 3 ^ 40 * 482953 * 2
def baseEnd_482953 : Nat := 165324681687302785244297

theorem tailTrace_482953 : CollatzResearch.WordTrace tailWord_482953 prefixEnd_482953 165324681687302785244297 := by
  unfold tailWord_482953
  simp only [CollatzResearch.WordTrace]
  refine ⟨17614743019351237650797513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11743162012900825100531675 17614743019351237650797513)
  ·
    refine ⟨13211057264513428238098135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17614743019351237650797513 13211057264513428238098135)
    ·
      refine ⟨19816585896770142357147203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13211057264513428238098135 19816585896770142357147203)
      ·
        refine ⟨29724878845155213535720805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19816585896770142357147203 29724878845155213535720805)
        ·
          refine ⟨5573414783466602537947651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29724878845155213535720805 5573414783466602537947651)
          ·
            refine ⟨8360122175199903806921477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573414783466602537947651 8360122175199903806921477)
            ·
              refine ⟨1567522907849981963797777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8360122175199903806921477 1567522907849981963797777)
              ·
                refine ⟨1175642180887486472848333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567522907849981963797777 1175642180887486472848333)
                ·
                  refine ⟨440865817832807427318125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175642180887486472848333 440865817832807427318125)
                  ·
                    refine ⟨165324681687302785244297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440865817832807427318125 165324681687302785244297)
                    ·
                      rfl

theorem cell22_482953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_482953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482953 prefixEnd_482953 := by exact prefixLift 482953
  have htrace : WordTrace (prefixWord ++ tailWord_482953) baseStart_482953 baseEnd_482953 := by
    simpa [prefixWord, tailWord_482953, baseEnd_482953] using wordTrace_append hprefix tailTrace_482953
  have hstable : (prefixWord ++ tailWord_482953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482953).length < 2 ^ (prefixWord ++ tailWord_482953).sum := by decide
  have hdescent : baseEnd_482953 < baseStart_482953 := by decide
  rcases family_descends (prefixWord ++ tailWord_482953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482981 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_482981 : Nat := 118140960795 + 482981 * 2 ^ 59
def prefixEnd_482981 : Nat := 4983230072969 + 3 ^ 40 * 482981 * 2
def baseEnd_482981 : Nat := 165334266659520045544211

theorem tailTrace_482981 : CollatzResearch.WordTrace tailWord_482981 prefixEnd_482981 165334266659520045544211 := by
  unfold tailWord_482981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615764263249798432816797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11743842842166532288544531 17615764263249798432816797)
  ·
    refine ⟨6605911598718674412306299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17615764263249798432816797 6605911598718674412306299)
    ·
      refine ⟨9908867398078011618459449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605911598718674412306299 9908867398078011618459449)
      ·
        refine ⟨7431650548558508713844587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9908867398078011618459449 7431650548558508713844587)
        ·
          refine ⟨11147475822837763070766881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431650548558508713844587 11147475822837763070766881)
          ·
            refine ⟨8360606867128322303075161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147475822837763070766881 8360606867128322303075161)
            ·
              refine ⟨6270455150346241727306371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8360606867128322303075161 6270455150346241727306371)
              ·
                refine ⟨9405682725519362590959557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270455150346241727306371 9405682725519362590959557)
                ·
                  refine ⟨1763565511034880485804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9405682725519362590959557 1763565511034880485804917)
                  ·
                    refine ⟨165334266659520045544211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1763565511034880485804917 165334266659520045544211)
                    ·
                      rfl

theorem cell22_482981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_482981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_482981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_482981 prefixEnd_482981 := by exact prefixLift 482981
  have htrace : WordTrace (prefixWord ++ tailWord_482981) baseStart_482981 baseEnd_482981 := by
    simpa [prefixWord, tailWord_482981, baseEnd_482981] using wordTrace_append hprefix tailTrace_482981
  have hstable : (prefixWord ++ tailWord_482981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482981).length < 2 ^ (prefixWord ++ tailWord_482981).sum := by decide
  have hdescent : baseEnd_482981 < baseStart_482981 := by decide
  rcases family_descends (prefixWord ++ tailWord_482981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483045 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 4]
def baseStart_483045 : Nat := 118140960795 + 483045 * 2 ^ 59
def prefixEnd_483045 : Nat := 4983230072969 + 3 ^ 40 * 483045 * 2
def baseEnd_483045 : Nat := 55118725055815070648005

theorem tailTrace_483045 : CollatzResearch.WordTrace tailWord_483045 prefixEnd_483045 55118725055815070648005 := by
  unfold tailWord_483045
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618098535017937363146589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745399023345291575431059 17618098535017937363146589)
  ·
    refine ⟨6606786950631726511179971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17618098535017937363146589 6606786950631726511179971)
    ·
      refine ⟨9910180425947589766769957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606786950631726511179971 9910180425947589766769957)
      ·
        refine ⟨1858158829865173081269367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9910180425947589766769957 1858158829865173081269367)
        ·
          refine ⟨2787238244797759621904051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858158829865173081269367 2787238244797759621904051)
          ·
            refine ⟨4180857367196639432856077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787238244797759621904051 4180857367196639432856077)
            ·
              refine ⟨1567821512698739787321029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180857367196639432856077 1567821512698739787321029)
              ·
                refine ⟨293966533631013710122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1567821512698739787321029 293966533631013710122693)
                ·
                  refine ⟨55118725055815070648005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293966533631013710122693 55118725055815070648005)
                  ·
                    rfl

theorem cell22_483045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_483045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483045 prefixEnd_483045 := by exact prefixLift 483045
  have htrace : WordTrace (prefixWord ++ tailWord_483045) baseStart_483045 baseEnd_483045 := by
    simpa [prefixWord, tailWord_483045, baseEnd_483045] using wordTrace_append hprefix tailTrace_483045
  have hstable : (prefixWord ++ tailWord_483045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483045).length < 2 ^ (prefixWord ++ tailWord_483045).sum := by decide
  have hdescent : baseEnd_483045 < baseStart_483045 := by decide
  rcases family_descends (prefixWord ++ tailWord_483045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483056 : List Nat := [2, 1, 1, 1, 3, 1, 2, 11]
def baseStart_483056 : Nat := 118140960795 + 483056 * 2 ^ 59
def prefixEnd_483056 : Nat := 4983230072969 + 3 ^ 40 * 483056 * 2
def baseEnd_483056 : Nat := 18373326743582761102109

theorem tailTrace_483056 : CollatzResearch.WordTrace tailWord_483056 prefixEnd_483056 18373326743582761102109 := by
  unfold tailWord_483056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809249868989043120898511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11745666491985390827864681 8809249868989043120898511)
  ·
    refine ⟨13213874803483564681347767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8809249868989043120898511 13213874803483564681347767)
    ·
      refine ⟨19820812205225347022021651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213874803483564681347767 19820812205225347022021651)
      ·
        refine ⟨29731218307838020533032477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19820812205225347022021651 29731218307838020533032477)
        ·
          refine ⟨11149206865439257699887179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29731218307838020533032477 11149206865439257699887179)
          ·
            refine ⟨16723810298158886549830769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149206865439257699887179 16723810298158886549830769)
            ·
              refine ⟨12542857723619164912373077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16723810298158886549830769 12542857723619164912373077)
              ·
                refine ⟨18373326743582761102109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12542857723619164912373077 18373326743582761102109)
                ·
                  rfl

theorem cell22_483056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_483056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483056 prefixEnd_483056 := by exact prefixLift 483056
  have htrace : WordTrace (prefixWord ++ tailWord_483056) baseStart_483056 baseEnd_483056 := by
    simpa [prefixWord, tailWord_483056, baseEnd_483056] using wordTrace_append hprefix tailTrace_483056
  have hstable : (prefixWord ++ tailWord_483056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483056).length < 2 ^ (prefixWord ++ tailWord_483056).sum := by decide
  have hdescent : baseEnd_483056 < baseStart_483056 := by decide
  rcases family_descends (prefixWord ++ tailWord_483056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483058 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_483058 : Nat := 118140960795 + 483058 * 2 ^ 59
def prefixEnd_483058 : Nat := 4983230072969 + 3 ^ 40 * 483058 * 2
def baseEnd_483058 : Nat := 165360625333117511368975

theorem tailTrace_483058 : CollatzResearch.WordTrace tailWord_483058 prefixEnd_483058 165360625333117511368975 := by
  unfold tailWord_483058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404643170992710145842457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11745715122647227055579885 4404643170992710145842457)
  ·
    refine ⟨3303482378244532609381843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4404643170992710145842457 3303482378244532609381843)
    ·
      refine ⟨4955223567366798914072765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303482378244532609381843 4955223567366798914072765)
      ·
        refine ⟨1858208837762549592777287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4955223567366798914072765 1858208837762549592777287)
        ·
          refine ⟨2787313256643824389165931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858208837762549592777287 2787313256643824389165931)
          ·
            refine ⟨4180969884965736583748897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787313256643824389165931 4180969884965736583748897)
            ·
              refine ⟨3135727413724302437811673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180969884965736583748897 3135727413724302437811673)
              ·
                refine ⟨2351795560293226828358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135727413724302437811673 2351795560293226828358755)
                ·
                  refine ⟨3527693340439840242538133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351795560293226828358755 3527693340439840242538133)
                  ·
                    refine ⟨165360625333117511368975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3527693340439840242538133 165360625333117511368975)
                    ·
                      rfl

theorem cell22_483058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_483058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483058 prefixEnd_483058 := by exact prefixLift 483058
  have htrace : WordTrace (prefixWord ++ tailWord_483058) baseStart_483058 baseEnd_483058 := by
    simpa [prefixWord, tailWord_483058, baseEnd_483058] using wordTrace_append hprefix tailTrace_483058
  have hstable : (prefixWord ++ tailWord_483058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483058).length < 2 ^ (prefixWord ++ tailWord_483058).sum := by decide
  have hdescent : baseEnd_483058 < baseStart_483058 := by decide
  rcases family_descends (prefixWord ++ tailWord_483058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483090 : List Nat := [3, 2, 4, 1, 1, 2, 9]
def baseStart_483090 : Nat := 118140960795 + 483090 * 2 ^ 59
def prefixEnd_483090 : Nat := 4983230072969 + 3 ^ 40 * 483090 * 2
def baseEnd_483090 : Nat := 6124873318040003502551

theorem tailTrace_483090 : CollatzResearch.WordTrace tailWord_483090 prefixEnd_483090 6124873318040003502551 := by
  unfold tailWord_483090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404934954963727512133681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11746493213236606699023149 4404934954963727512133681)
  ·
    refine ⟨3303701216222795634100261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4404934954963727512133681 3303701216222795634100261)
    ·
      refine ⟨619443978041774181393799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3303701216222795634100261 619443978041774181393799)
      ·
        refine ⟨929165967062661272090699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619443978041774181393799 929165967062661272090699)
        ·
          refine ⟨1393748950593991908136049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929165967062661272090699 1393748950593991908136049)
          ·
            refine ⟨1045311712945493931102037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393748950593991908136049 1045311712945493931102037)
            ·
              refine ⟨6124873318040003502551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1045311712945493931102037 6124873318040003502551)
              ·
                rfl

theorem cell22_483090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 9].length) (baseStart_483090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483090 prefixEnd_483090 := by exact prefixLift 483090
  have htrace : WordTrace (prefixWord ++ tailWord_483090) baseStart_483090 baseEnd_483090 := by
    simpa [prefixWord, tailWord_483090, baseEnd_483090] using wordTrace_append hprefix tailTrace_483090
  have hstable : (prefixWord ++ tailWord_483090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483090).length < 2 ^ (prefixWord ++ tailWord_483090).sum := by decide
  have hdescent : baseEnd_483090 < baseStart_483090 := by decide
  rcases family_descends (prefixWord ++ tailWord_483090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483105 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_483105 : Nat := 118140960795 + 483105 * 2 ^ 59
def prefixEnd_483105 : Nat := 4983230072969 + 3 ^ 40 * 483105 * 2
def baseEnd_483105 : Nat := 165376714393625055443831

theorem tailTrace_483105 : CollatzResearch.WordTrace tailWord_483105 prefixEnd_483105 165376714393625055443831 := by
  unfold tailWord_483105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620286914800567610330769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746857943200378406887179 17620286914800567610330769)
  ·
    refine ⟨13215215186100425707748077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17620286914800567610330769 13215215186100425707748077)
    ·
      refine ⟨4955705694787659640405529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13215215186100425707748077 4955705694787659640405529)
      ·
        refine ⟨3716779271090744730304147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4955705694787659640405529 3716779271090744730304147)
        ·
          refine ⟨5575168906636117095456221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716779271090744730304147 5575168906636117095456221)
          ·
            refine ⟨2090688339988543910796083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5575168906636117095456221 2090688339988543910796083)
            ·
              refine ⟨3136032509982815866194125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090688339988543910796083 3136032509982815866194125)
              ·
                refine ⟨1176012191243555949822797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136032509982815866194125 1176012191243555949822797)
                ·
                  refine ⟨441004571716333481183549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176012191243555949822797 441004571716333481183549)
                  ·
                    refine ⟨165376714393625055443831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441004571716333481183549 165376714393625055443831)
                    ·
                      rfl

theorem cell22_483105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_483105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483105 prefixEnd_483105 := by exact prefixLift 483105
  have htrace : WordTrace (prefixWord ++ tailWord_483105) baseStart_483105 baseEnd_483105 := by
    simpa [prefixWord, tailWord_483105, baseEnd_483105] using wordTrace_append hprefix tailTrace_483105
  have hstable : (prefixWord ++ tailWord_483105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483105).length < 2 ^ (prefixWord ++ tailWord_483105).sum := by decide
  have hdescent : baseEnd_483105 < baseStart_483105 := by decide
  rcases family_descends (prefixWord ++ tailWord_483105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483139 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 1, 3]
def baseStart_483139 : Nat := 118140960795 + 483139 * 2 ^ 59
def prefixEnd_483139 : Nat := 4983230072969 + 3 ^ 40 * 483139 * 2
def baseEnd_483139 : Nat := 165388353288460300093727

theorem tailTrace_483139 : CollatzResearch.WordTrace tailWord_483139 prefixEnd_483139 165388353288460300093727 := by
  unfold tailWord_483139
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621526996677391417068471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11747684664451594278045647 17621526996677391417068471)
  ·
    refine ⟨26432290495016087125602707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17621526996677391417068471 26432290495016087125602707)
    ·
      refine ⟨39648435742524130688404061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26432290495016087125602707 39648435742524130688404061)
      ·
        refine ⟨14868163403446549008151523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39648435742524130688404061 14868163403446549008151523)
        ·
          refine ⟨22302245105169823512227285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868163403446549008151523 22302245105169823512227285)
          ·
            refine ⟨522708869652417738567827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22302245105169823512227285 522708869652417738567827)
            ·
              refine ⟨784063304478626607851741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522708869652417738567827 784063304478626607851741)
              ·
                refine ⟨294023739179484977944403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784063304478626607851741 294023739179484977944403)
                ·
                  refine ⟨441035608769227466916605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294023739179484977944403 441035608769227466916605)
                  ·
                    refine ⟨165388353288460300093727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441035608769227466916605 165388353288460300093727)
                    ·
                      rfl

theorem cell22_483139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 3].length) (baseStart_483139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483139 prefixEnd_483139 := by exact prefixLift 483139
  have htrace : WordTrace (prefixWord ++ tailWord_483139) baseStart_483139 baseEnd_483139 := by
    simpa [prefixWord, tailWord_483139, baseEnd_483139] using wordTrace_append hprefix tailTrace_483139
  have hstable : (prefixWord ++ tailWord_483139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483139).length < 2 ^ (prefixWord ++ tailWord_483139).sum := by decide
  have hdescent : baseEnd_483139 < baseStart_483139 := by decide
  rcases family_descends (prefixWord ++ tailWord_483139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483156 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_483156 : Nat := 118140960795 + 483156 * 2 ^ 59
def prefixEnd_483156 : Nat := 4983230072969 + 3 ^ 40 * 483156 * 2
def baseEnd_483156 : Nat := 165394172735877922418675

theorem tailTrace_483156 : CollatzResearch.WordTrace tailWord_483156 prefixEnd_483156 165394172735877922418675 := by
  unfold tailWord_483156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811073518807901660218661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11748098025077202213624881 8811073518807901660218661)
  ·
    refine ⟨1652076284776481561290999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8811073518807901660218661 1652076284776481561290999)
    ·
      refine ⟨2478114427164722341936499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652076284776481561290999 2478114427164722341936499)
      ·
        refine ⟨3717171640747083512904749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478114427164722341936499 3717171640747083512904749)
        ·
          refine ⟨1393939365280156317339281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3717171640747083512904749 1393939365280156317339281)
          ·
            refine ⟨1045454523960117238004461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393939365280156317339281 1045454523960117238004461)
            ·
              refine ⟨392045446485043964251673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045454523960117238004461 392045446485043964251673)
              ·
                refine ⟨294034084863782973188755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392045446485043964251673 294034084863782973188755)
                ·
                  refine ⟨441051127295674459783133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294034084863782973188755 441051127295674459783133)
                  ·
                    refine ⟨165394172735877922418675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441051127295674459783133 165394172735877922418675)
                    ·
                      rfl

theorem cell22_483156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_483156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483156 prefixEnd_483156 := by exact prefixLift 483156
  have htrace : WordTrace (prefixWord ++ tailWord_483156) baseStart_483156 baseEnd_483156 := by
    simpa [prefixWord, tailWord_483156, baseEnd_483156] using wordTrace_append hprefix tailTrace_483156
  have hstable : (prefixWord ++ tailWord_483156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483156).length < 2 ^ (prefixWord ++ tailWord_483156).sum := by decide
  have hdescent : baseEnd_483156 < baseStart_483156 := by decide
  rcases family_descends (prefixWord ++ tailWord_483156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483182 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_483182 : Nat := 118140960795 + 483182 * 2 ^ 59
def prefixEnd_483182 : Nat := 4983230072969 + 3 ^ 40 * 483182 * 2
def baseEnd_483182 : Nat := 165403073067222521268595

theorem tailTrace_483182 : CollatzResearch.WordTrace tailWord_483182 prefixEnd_483182 165403073067222521268595 := by
  unfold tailWord_483182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202886916940201220110475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11748730223681073173922533 2202886916940201220110475)
  ·
    refine ⟨3304330375410301830165713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202886916940201220110475 3304330375410301830165713)
    ·
      refine ⟨2478247781557726372624285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3304330375410301830165713 2478247781557726372624285)
      ·
        refine ⟨929342918084147389734107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2478247781557726372624285 929342918084147389734107)
        ·
          refine ⟨1394014377126221084601161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929342918084147389734107 1394014377126221084601161)
          ·
            refine ⟨1045510782844665813450871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394014377126221084601161 1045510782844665813450871)
            ·
              refine ⟨1568266174266998720176307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045510782844665813450871 1568266174266998720176307)
              ·
                refine ⟨2352399261400498080264461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568266174266998720176307 2352399261400498080264461)
                ·
                  refine ⟨882149723025186780099173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2352399261400498080264461 882149723025186780099173)
                  ·
                    refine ⟨165403073067222521268595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882149723025186780099173 165403073067222521268595)
                    ·
                      rfl

theorem cell22_483182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_483182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483182 prefixEnd_483182 := by exact prefixLift 483182
  have htrace : WordTrace (prefixWord ++ tailWord_483182) baseStart_483182 baseEnd_483182 := by
    simpa [prefixWord, tailWord_483182, baseEnd_483182] using wordTrace_append hprefix tailTrace_483182
  have hstable : (prefixWord ++ tailWord_483182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483182).length < 2 ^ (prefixWord ++ tailWord_483182).sum := by decide
  have hdescent : baseEnd_483182 < baseStart_483182 := by decide
  rcases family_descends (prefixWord ++ tailWord_483182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483208 : List Nat := [2, 1, 3, 3, 13]
def baseStart_483208 : Nat := 118140960795 + 483208 * 2 ^ 59
def prefixEnd_483208 : Nat := 4983230072969 + 3 ^ 40 * 483208 * 2
def baseEnd_483208 : Nat := 680707709459123951105

theorem tailTrace_483208 : CollatzResearch.WordTrace tailWord_483208 prefixEnd_483208 680707709459123951105 := by
  unfold tailWord_483208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812021816713708100665139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11749362422284944134220185 8812021816713708100665139)
  ·
    refine ⟨13218032725070562150997709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8812021816713708100665139 13218032725070562150997709)
    ·
      refine ⟨4956762271901460806624141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13218032725070562150997709 4956762271901460806624141)
      ·
        refine ⟨1858785851963047802484053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4956762271901460806624141 1858785851963047802484053)
        ·
          refine ⟨680707709459123951105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1858785851963047802484053 680707709459123951105)
          ·
            rfl

theorem cell22_483208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 13].length) (baseStart_483208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483208 prefixEnd_483208 := by exact prefixLift 483208
  have htrace : WordTrace (prefixWord ++ tailWord_483208) baseStart_483208 baseEnd_483208 := by
    simpa [prefixWord, tailWord_483208, baseEnd_483208] using wordTrace_append hprefix tailTrace_483208
  have hstable : (prefixWord ++ tailWord_483208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483208).length < 2 ^ (prefixWord ++ tailWord_483208).sum := by decide
  have hdescent : baseEnd_483208 < baseStart_483208 := by decide
  rcases family_descends (prefixWord ++ tailWord_483208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483274 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_483274 : Nat := 118140960795 + 483274 * 2 ^ 59
def prefixEnd_483274 : Nat := 4983230072969 + 3 ^ 40 * 483274 * 2
def baseEnd_483274 : Nat := 165434566547364947968313

theorem tailTrace_483274 : CollatzResearch.WordTrace tailWord_483274 prefixEnd_483274 165434566547364947968313 := by
  unfold tailWord_483274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406612712797077368308219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11750967234125539648821917 4406612712797077368308219)
  ·
    refine ⟨6609919069195616052462329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406612712797077368308219 6609919069195616052462329)
    ·
      refine ⟨4957439301896712039346747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609919069195616052462329 4957439301896712039346747)
      ·
        refine ⟨7436158952845068059020121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957439301896712039346747 7436158952845068059020121)
        ·
          refine ⟨5577119214633801044265091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7436158952845068059020121 5577119214633801044265091)
          ·
            refine ⟨8365678821950701566397637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577119214633801044265091 8365678821950701566397637)
            ·
              refine ⟨1568564779115756543699557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8365678821950701566397637 1568564779115756543699557)
              ·
                refine ⟨294105896084204351943667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1568564779115756543699557 294105896084204351943667)
                ·
                  refine ⟨441158844126306527915501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294105896084204351943667 441158844126306527915501)
                  ·
                    refine ⟨165434566547364947968313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441158844126306527915501 165434566547364947968313)
                    ·
                      rfl

theorem cell22_483274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_483274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483274 prefixEnd_483274 := by exact prefixLift 483274
  have htrace : WordTrace (prefixWord ++ tailWord_483274) baseStart_483274 baseEnd_483274 := by
    simpa [prefixWord, tailWord_483274, baseEnd_483274] using wordTrace_append hprefix tailTrace_483274
  have hstable : (prefixWord ++ tailWord_483274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483274).length < 2 ^ (prefixWord ++ tailWord_483274).sum := by decide
  have hdescent : baseEnd_483274 < baseStart_483274 := by decide
  rcases family_descends (prefixWord ++ tailWord_483274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483287 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 5]
def baseStart_483287 : Nat := 118140960795 + 483287 * 2 ^ 59
def prefixEnd_483287 : Nat := 4983230072969 + 3 ^ 40 * 483287 * 2
def baseEnd_483287 : Nat := 55146338904345749131091

theorem tailTrace_483287 : CollatzResearch.WordTrace tailWord_483287 prefixEnd_483287 55146338904345749131091 := by
  unfold tailWord_483287
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626925000141212693456115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751283333427475128970743 17626925000141212693456115)
  ·
    refine ⟨26440387500211819040184173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17626925000141212693456115 26440387500211819040184173)
    ·
      refine ⟨9915145312579432140069065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26440387500211819040184173 9915145312579432140069065)
      ·
        refine ⟨7436358984434574105051799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9915145312579432140069065 7436358984434574105051799)
        ·
          refine ⟨11154538476651861157577699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436358984434574105051799 11154538476651861157577699)
          ·
            refine ⟨16731807714977791736366549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154538476651861157577699 16731807714977791736366549)
            ·
              refine ⟨392151743319791993821091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16731807714977791736366549 392151743319791993821091)
              ·
                refine ⟨588227614979687990731637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392151743319791993821091 588227614979687990731637)
                ·
                  refine ⟨55146338904345749131091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588227614979687990731637 55146338904345749131091)
                  ·
                    rfl

theorem cell22_483287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 5].length) (baseStart_483287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483287 prefixEnd_483287 := by exact prefixLift 483287
  have htrace : WordTrace (prefixWord ++ tailWord_483287) baseStart_483287 baseEnd_483287 := by
    simpa [prefixWord, tailWord_483287, baseEnd_483287] using wordTrace_append hprefix tailTrace_483287
  have hstable : (prefixWord ++ tailWord_483287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483287).length < 2 ^ (prefixWord ++ tailWord_483287).sum := by decide
  have hdescent : baseEnd_483287 < baseStart_483287 := by decide
  rcases family_descends (prefixWord ++ tailWord_483287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483351 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 1, 4]
def baseStart_483351 : Nat := 118140960795 + 483351 * 2 ^ 59
def prefixEnd_483351 : Nat := 4983230072969 + 3 ^ 40 * 483351 * 2
def baseEnd_483351 : Nat := 165460925220962413793077

theorem tailTrace_483351 : CollatzResearch.WordTrace tailWord_483351 prefixEnd_483351 165460925220962413793077 := by
  unfold tailWord_483351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629259271909351623785907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11752839514606234415857271 17629259271909351623785907)
  ·
    refine ⟨26443888907864027435678861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17629259271909351623785907 26443888907864027435678861)
    ·
      refine ⟨9916458340449010288379573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26443888907864027435678861 9916458340449010288379573)
      ·
        refine ⟨929667969417094714535585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9916458340449010288379573 929667969417094714535585)
        ·
          refine ⟨697250977062821035901689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929667969417094714535585 697250977062821035901689)
          ·
            refine ⟨522938232797115776926267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697250977062821035901689 522938232797115776926267)
            ·
              refine ⟨784407349195673665389401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522938232797115776926267 784407349195673665389401)
              ·
                refine ⟨588305511896755249042051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784407349195673665389401 588305511896755249042051)
                ·
                  refine ⟨882458267845132873563077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588305511896755249042051 882458267845132873563077)
                  ·
                    refine ⟨165460925220962413793077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882458267845132873563077 165460925220962413793077)
                    ·
                      rfl

theorem cell22_483351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_483351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483351 prefixEnd_483351 := by exact prefixLift 483351
  have htrace : WordTrace (prefixWord ++ tailWord_483351) baseStart_483351 baseEnd_483351 := by
    simpa [prefixWord, tailWord_483351, baseEnd_483351] using wordTrace_append hprefix tailTrace_483351
  have hstable : (prefixWord ++ tailWord_483351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483351).length < 2 ^ (prefixWord ++ tailWord_483351).sum := by decide
  have hdescent : baseEnd_483351 < baseStart_483351 := by decide
  rcases family_descends (prefixWord ++ tailWord_483351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483364 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_483364 : Nat := 118140960795 + 483364 * 2 ^ 59
def prefixEnd_483364 : Nat := 4983230072969 + 3 ^ 40 * 483364 * 2
def baseEnd_483364 : Nat := 165465375386634713218037

theorem tailTrace_483364 : CollatzResearch.WordTrace tailWord_483364 prefixEnd_483364 165465375386634713218037 := by
  unfold tailWord_483364
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814866710431127422004573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11753155613908169896006097 8814866710431127422004573)
  ·
    refine ⟨3305575016411672783251715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8814866710431127422004573 3305575016411672783251715)
    ·
      refine ⟨4958362524617509174877573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305575016411672783251715 4958362524617509174877573)
      ·
        refine ⟨929692973365782970289545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4958362524617509174877573 929692973365782970289545)
        ·
          refine ⟨697269730024337227717159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929692973365782970289545 697269730024337227717159)
          ·
            refine ⟨1045904595036505841575739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697269730024337227717159 1045904595036505841575739)
            ·
              refine ⟨1568856892554758762363609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045904595036505841575739 1568856892554758762363609)
              ·
                refine ⟨1176642669416069071772707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568856892554758762363609 1176642669416069071772707)
                ·
                  refine ⟨1764964004124103607659061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176642669416069071772707 1764964004124103607659061)
                  ·
                    refine ⟨165465375386634713218037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1764964004124103607659061 165465375386634713218037)
                    ·
                      rfl

theorem cell22_483364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_483364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483364 prefixEnd_483364 := by exact prefixLift 483364
  have htrace : WordTrace (prefixWord ++ tailWord_483364) baseStart_483364 baseEnd_483364 := by
    simpa [prefixWord, tailWord_483364, baseEnd_483364] using wordTrace_append hprefix tailTrace_483364
  have hstable : (prefixWord ++ tailWord_483364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483364).length < 2 ^ (prefixWord ++ tailWord_483364).sum := by decide
  have hdescent : baseEnd_483364 < baseStart_483364 := by decide
  rcases family_descends (prefixWord ++ tailWord_483364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483368 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_483368 : Nat := 118140960795 + 483368 * 2 ^ 59
def prefixEnd_483368 : Nat := 4983230072969 + 3 ^ 40 * 483368 * 2
def baseEnd_483368 : Nat := 165466744668380036118025

theorem tailTrace_483368 : CollatzResearch.WordTrace tailWord_483368 prefixEnd_483368 165466744668380036118025 := by
  unfold tailWord_483368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814939656423881763577379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11753252875231842351436505 8814939656423881763577379)
  ·
    refine ⟨13222409484635822645366069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8814939656423881763577379 13222409484635822645366069)
    ·
      refine ⟨1239600889184608373003069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13222409484635822645366069 1239600889184608373003069)
      ·
        refine ⟨464850333444228139876151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1239600889184608373003069 464850333444228139876151)
        ·
          refine ⟨697275500166342209814227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464850333444228139876151 697275500166342209814227)
          ·
            refine ⟨1045913250249513314721341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697275500166342209814227 1045913250249513314721341)
            ·
              refine ⟨392217468843567493020503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045913250249513314721341 392217468843567493020503)
              ·
                refine ⟨588326203265351239530755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392217468843567493020503 588326203265351239530755)
                ·
                  refine ⟨882489304898026859296133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588326203265351239530755 882489304898026859296133)
                  ·
                    refine ⟨165466744668380036118025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882489304898026859296133 165466744668380036118025)
                    ·
                      rfl

theorem cell22_483368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_483368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483368 prefixEnd_483368 := by exact prefixLift 483368
  have htrace : WordTrace (prefixWord ++ tailWord_483368) baseStart_483368 baseEnd_483368 := by
    simpa [prefixWord, tailWord_483368, baseEnd_483368] using wordTrace_append hprefix tailTrace_483368
  have hstable : (prefixWord ++ tailWord_483368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483368).length < 2 ^ (prefixWord ++ tailWord_483368).sum := by decide
  have hdescent : baseEnd_483368 < baseStart_483368 := by decide
  rcases family_descends (prefixWord ++ tailWord_483368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483437 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_483437 : Nat := 118140960795 + 483437 * 2 ^ 59
def prefixEnd_483437 : Nat := 4983230072969 + 3 ^ 40 * 483437 * 2
def baseEnd_483437 : Nat := 165490364778486856142813

theorem tailTrace_483437 : CollatzResearch.WordTrace tailWord_483437 prefixEnd_483437 165490364778486856142813 := by
  unfold tailWord_483437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632395949597788311416565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11754930633065192207611043 17632395949597788311416565)
  ·
    refine ⟨1653037120274792654195303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17632395949597788311416565 1653037120274792654195303)
    ·
      refine ⟨2479555680412188981292955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653037120274792654195303 2479555680412188981292955)
      ·
        refine ⟨3719333520618283471939433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479555680412188981292955 3719333520618283471939433)
        ·
          refine ⟨2789500140463712603954575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3719333520618283471939433 2789500140463712603954575)
          ·
            refine ⟨4184250210695568905931863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789500140463712603954575 4184250210695568905931863)
            ·
              refine ⟨6276375316043353358897795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184250210695568905931863 6276375316043353358897795)
              ·
                refine ⟨9414562974065030038346693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276375316043353358897795 9414562974065030038346693)
                ·
                  refine ⟨1765230557637193132190005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9414562974065030038346693 1765230557637193132190005)
                  ·
                    refine ⟨165490364778486856142813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1765230557637193132190005 165490364778486856142813)
                    ·
                      rfl

theorem cell22_483437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_483437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483437 prefixEnd_483437 := by exact prefixLift 483437
  have htrace : WordTrace (prefixWord ++ tailWord_483437) baseStart_483437 baseEnd_483437 := by
    simpa [prefixWord, tailWord_483437, baseEnd_483437] using wordTrace_append hprefix tailTrace_483437
  have hstable : (prefixWord ++ tailWord_483437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483437).length < 2 ^ (prefixWord ++ tailWord_483437).sum := by decide
  have hdescent : baseEnd_483437 < baseStart_483437 := by decide
  rcases family_descends (prefixWord ++ tailWord_483437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483439 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 5]
def baseStart_483439 : Nat := 118140960795 + 483439 * 2 ^ 59
def prefixEnd_483439 : Nat := 4983230072969 + 3 ^ 40 * 483439 * 2
def baseEnd_483439 : Nat := 55163683139786505864269

theorem tailTrace_483439 : CollatzResearch.WordTrace tailWord_483439 prefixEnd_483439 55163683139786505864269 := by
  unfold tailWord_483439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632468895590542652989371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11754979263727028435326247 17632468895590542652989371)
  ·
    refine ⟨26448703343385813979484057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17632468895590542652989371 26448703343385813979484057)
    ·
      refine ⟨19836527507539360484613043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26448703343385813979484057 19836527507539360484613043)
      ·
        refine ⟨29754791261309040726919565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19836527507539360484613043 29754791261309040726919565)
        ·
          refine ⟨11158046722990890272594837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29754791261309040726919565 11158046722990890272594837)
          ·
            refine ⟨523033440140197981527883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11158046722990890272594837 523033440140197981527883)
            ·
              refine ⟨784550160210296972291825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523033440140197981527883 784550160210296972291825)
              ·
                refine ⟨588412620157722729218869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784550160210296972291825 588412620157722729218869)
                ·
                  refine ⟨55163683139786505864269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588412620157722729218869 55163683139786505864269)
                  ·
                    rfl

theorem cell22_483439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].length) (baseStart_483439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483439 prefixEnd_483439 := by exact prefixLift 483439
  have htrace : WordTrace (prefixWord ++ tailWord_483439) baseStart_483439 baseEnd_483439 := by
    simpa [prefixWord, tailWord_483439, baseEnd_483439] using wordTrace_append hprefix tailTrace_483439
  have hstable : (prefixWord ++ tailWord_483439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483439).length < 2 ^ (prefixWord ++ tailWord_483439).sum := by decide
  have hdescent : baseEnd_483439 < baseStart_483439 := by decide
  rcases family_descends (prefixWord ++ tailWord_483439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483501 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 6]
def baseStart_483501 : Nat := 118140960795 + 483501 * 2 ^ 59
def prefixEnd_483501 : Nat := 4983230072969 + 3 ^ 40 * 483501 * 2
def baseEnd_483501 : Nat := 55170757762137340847539

theorem tailTrace_483501 : CollatzResearch.WordTrace tailWord_483501 prefixEnd_483501 55170757762137340847539 := by
  unfold tailWord_483501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17634730221365927241746357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11756486814243951494497571 17634730221365927241746357)
  ·
    refine ⟨1653255958253055678913721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17634730221365927241746357 1653255958253055678913721)
    ·
      refine ⟨1239941968689791759185291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653255958253055678913721 1239941968689791759185291)
      ·
        refine ⟨1859912953034687638777937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239941968689791759185291 1859912953034687638777937)
        ·
          refine ⟨1394934714776015729083453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859912953034687638777937 1394934714776015729083453)
          ·
            refine ⟨523100518041005898406295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1394934714776015729083453 523100518041005898406295)
            ·
              refine ⟨784650777061508847609443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523100518041005898406295 784650777061508847609443)
              ·
                refine ⟨1176976165592263271414165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784650777061508847609443 1176976165592263271414165)
                ·
                  refine ⟨55170757762137340847539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1176976165592263271414165 55170757762137340847539)
                  ·
                    rfl

theorem cell22_483501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_483501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483501 prefixEnd_483501 := by exact prefixLift 483501
  have htrace : WordTrace (prefixWord ++ tailWord_483501) baseStart_483501 baseEnd_483501 := by
    simpa [prefixWord, tailWord_483501, baseEnd_483501] using wordTrace_append hprefix tailTrace_483501
  have hstable : (prefixWord ++ tailWord_483501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483501).length < 2 ^ (prefixWord ++ tailWord_483501).sum := by decide
  have hdescent : baseEnd_483501 < baseStart_483501 := by decide
  rcases family_descends (prefixWord ++ tailWord_483501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483512 : List Nat := [2, 1, 2, 1, 2, 1, 6, 7]
def baseStart_483512 : Nat := 118140960795 + 483512 * 2 ^ 59
def prefixEnd_483512 : Nat := 4983230072969 + 3 ^ 40 * 483512 * 2
def baseEnd_483512 : Nat := 18390670979023517835287

theorem tailTrace_483512 : CollatzResearch.WordTrace tailWord_483512 prefixEnd_483512 18390670979023517835287 := by
  unfold tailWord_483512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8817565712163038060198395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11756754282884050746931193 8817565712163038060198395)
  ·
    refine ⟨13226348568244557090297593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8817565712163038060198395 13226348568244557090297593)
    ·
      refine ⟨9919761426183417817723195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13226348568244557090297593 9919761426183417817723195)
      ·
        refine ⟨14879642139275126726584793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919761426183417817723195 14879642139275126726584793)
        ·
          refine ⟨11159731604456345044938595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879642139275126726584793 11159731604456345044938595)
          ·
            refine ⟨16739597406684517567407893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159731604456345044938595 16739597406684517567407893)
            ·
              refine ⟨784668628438336760972245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16739597406684517567407893 784668628438336760972245)
              ·
                refine ⟨18390670979023517835287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 784668628438336760972245 18390670979023517835287)
                ·
                  rfl

theorem cell22_483512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_483512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483512 prefixEnd_483512 := by exact prefixLift 483512
  have htrace : WordTrace (prefixWord ++ tailWord_483512) baseStart_483512 baseEnd_483512 := by
    simpa [prefixWord, tailWord_483512, baseEnd_483512] using wordTrace_append hprefix tailTrace_483512
  have hstable : (prefixWord ++ tailWord_483512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483512).length < 2 ^ (prefixWord ++ tailWord_483512).sum := by decide
  have hdescent : baseEnd_483512 < baseStart_483512 := by decide
  rcases family_descends (prefixWord ++ tailWord_483512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483559 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_483559 : Nat := 118140960795 + 483559 * 2 ^ 59
def prefixEnd_483559 : Nat := 4983230072969 + 3 ^ 40 * 483559 * 2
def baseEnd_483559 : Nat := 165532127871719204592439

theorem tailTrace_483559 : CollatzResearch.WordTrace tailWord_483559 prefixEnd_483559 165532127871719204592439 := by
  unfold tailWord_483559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636845655155803147357731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11757897103437202098238487 17636845655155803147357731)
  ·
    refine ⟨26455268482733704721036597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17636845655155803147357731 26455268482733704721036597)
    ·
      refine ⟨2480181420256284817597181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26455268482733704721036597 2480181420256284817597181)
      ·
        refine ⟨930068032596106806598943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2480181420256284817597181 930068032596106806598943)
        ·
          refine ⟨1395102048894160209898415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930068032596106806598943 1395102048894160209898415)
          ·
            refine ⟨2092653073341240314847623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395102048894160209898415 2092653073341240314847623)
            ·
              refine ⟨3138979610011860472271435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092653073341240314847623 3138979610011860472271435)
              ·
                refine ⟨4708469415017790708407153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138979610011860472271435 4708469415017790708407153)
                ·
                  refine ⟨3531352061263343031305365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708469415017790708407153 3531352061263343031305365)
                  ·
                    refine ⟨165532127871719204592439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3531352061263343031305365 165532127871719204592439)
                    ·
                      rfl

theorem cell22_483559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_483559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483559 prefixEnd_483559 := by exact prefixLift 483559
  have htrace : WordTrace (prefixWord ++ tailWord_483559) baseStart_483559 baseEnd_483559 := by
    simpa [prefixWord, tailWord_483559, baseEnd_483559] using wordTrace_append hprefix tailTrace_483559
  have hstable : (prefixWord ++ tailWord_483559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483559).length < 2 ^ (prefixWord ++ tailWord_483559).sum := by decide
  have hdescent : baseEnd_483559 < baseStart_483559 := by decide
  rcases family_descends (prefixWord ++ tailWord_483559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483561 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_483561 : Nat := 118140960795 + 483561 * 2 ^ 59
def prefixEnd_483561 : Nat := 4983230072969 + 3 ^ 40 * 483561 * 2
def baseEnd_483561 : Nat := 165532812512591866042433

theorem tailTrace_483561 : CollatzResearch.WordTrace tailWord_483561 prefixEnd_483561 165532812512591866042433 := by
  unfold tailWord_483561
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636918601148557488930537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11757945734099038325953691 17636918601148557488930537)
  ·
    refine ⟨13227688950861418116697903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17636918601148557488930537 13227688950861418116697903)
    ·
      refine ⟨19841533426292127175046855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227688950861418116697903 19841533426292127175046855)
      ·
        refine ⟨29762300139438190762570283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841533426292127175046855 29762300139438190762570283)
        ·
          refine ⟨44643450209157286143855425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29762300139438190762570283 44643450209157286143855425)
          ·
            refine ⟨33482587656867964607891569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44643450209157286143855425 33482587656867964607891569)
            ·
              refine ⟨25111940742650973455918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33482587656867964607891569 25111940742650973455918677)
              ·
                refine ⟨294280555577941095186547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 25111940742650973455918677 294280555577941095186547)
                ·
                  refine ⟨441420833366911642779821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294280555577941095186547 441420833366911642779821)
                  ·
                    refine ⟨165532812512591866042433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441420833366911642779821 165532812512591866042433)
                    ·
                      rfl

theorem cell22_483561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_483561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483561 prefixEnd_483561 := by exact prefixLift 483561
  have htrace : WordTrace (prefixWord ++ tailWord_483561) baseStart_483561 baseEnd_483561 := by
    simpa [prefixWord, tailWord_483561, baseEnd_483561] using wordTrace_append hprefix tailTrace_483561
  have hstable : (prefixWord ++ tailWord_483561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483561).length < 2 ^ (prefixWord ++ tailWord_483561).sum := by decide
  have hdescent : baseEnd_483561 < baseStart_483561 := by decide
  rcases family_descends (prefixWord ++ tailWord_483561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483619 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 6]
def baseStart_483619 : Nat := 118140960795 + 483619 * 2 ^ 59
def prefixEnd_483619 : Nat := 4983230072969 + 3 ^ 40 * 483619 * 2
def baseEnd_483619 : Nat := 55184222365966349364085

theorem tailTrace_483619 : CollatzResearch.WordTrace tailWord_483619 prefixEnd_483619 55184222365966349364085 := by
  unfold tailWord_483619
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639034034938433394541911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11759356023292288929694607 17639034034938433394541911)
  ·
    refine ⟨26458551052407650091812867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17639034034938433394541911 26458551052407650091812867)
    ·
      refine ⟨39687826578611475137719301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26458551052407650091812867 39687826578611475137719301)
      ·
        refine ⟨7441467483489651588322369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39687826578611475137719301 7441467483489651588322369)
        ·
          refine ⟨5581100612617238691241777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441467483489651588322369 5581100612617238691241777)
          ·
            refine ⟨4185825459462929018431333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5581100612617238691241777 4185825459462929018431333)
            ·
              refine ⟨784842273649299190955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4185825459462929018431333 784842273649299190955875)
              ·
                refine ⟨1177263410473948786433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784842273649299190955875 1177263410473948786433813)
                ·
                  refine ⟨55184222365966349364085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177263410473948786433813 55184222365966349364085)
                  ·
                    rfl

theorem cell22_483619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_483619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483619 prefixEnd_483619 := by exact prefixLift 483619
  have htrace : WordTrace (prefixWord ++ tailWord_483619) baseStart_483619 baseEnd_483619 := by
    simpa [prefixWord, tailWord_483619, baseEnd_483619] using wordTrace_append hprefix tailTrace_483619
  have hstable : (prefixWord ++ tailWord_483619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483619).length < 2 ^ (prefixWord ++ tailWord_483619).sum := by decide
  have hdescent : baseEnd_483619 < baseStart_483619 := by decide
  rcases family_descends (prefixWord ++ tailWord_483619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483636 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_483636 : Nat := 118140960795 + 483636 * 2 ^ 59
def prefixEnd_483636 : Nat := 4983230072969 + 3 ^ 40 * 483636 * 2
def baseEnd_483636 : Nat := 55186162181772223472401

theorem tailTrace_483636 : CollatzResearch.WordTrace tailWord_483636 prefixEnd_483636 55186162181772223472401 := by
  unfold tailWord_483636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819827037938422648955381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11759769383917896865273841 8819827037938422648955381)
  ·
    refine ⟨826858784806727123339567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8819827037938422648955381 826858784806727123339567)
    ·
      refine ⟨1240288177210090685009351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826858784806727123339567 1240288177210090685009351)
      ·
        refine ⟨1860432265815136027514027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240288177210090685009351 1860432265815136027514027)
        ·
          refine ⟨2790648398722704041271041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860432265815136027514027 2790648398722704041271041)
          ·
            refine ⟨2092986299042028030953281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790648398722704041271041 2092986299042028030953281)
            ·
              refine ⟨1569739724281521023214961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092986299042028030953281 1569739724281521023214961)
              ·
                refine ⟨1177304793211140767411221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569739724281521023214961 1177304793211140767411221)
                ·
                  refine ⟨55186162181772223472401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177304793211140767411221 55186162181772223472401)
                  ·
                    rfl

theorem cell22_483636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_483636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483636 prefixEnd_483636 := by exact prefixLift 483636
  have htrace : WordTrace (prefixWord ++ tailWord_483636) baseStart_483636 baseEnd_483636 := by
    simpa [prefixWord, tailWord_483636, baseEnd_483636] using wordTrace_append hprefix tailTrace_483636
  have hstable : (prefixWord ++ tailWord_483636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483636).length < 2 ^ (prefixWord ++ tailWord_483636).sum := by decide
  have hdescent : baseEnd_483636 < baseStart_483636 := by decide
  rcases family_descends (prefixWord ++ tailWord_483636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483664 : List Nat := [2, 1, 1, 1, 1, 8, 8]
def baseStart_483664 : Nat := 118140960795 + 483664 * 2 ^ 59
def prefixEnd_483664 : Nat := 4983230072969 + 3 ^ 40 * 483664 * 2
def baseEnd_483664 : Nat := 6132150796945701137671

theorem tailTrace_483664 : CollatzResearch.WordTrace tailWord_483664 prefixEnd_483664 6132150796945701137671 := by
  unfold tailWord_483664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820337659887703039965023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11760450213183604053286697 8820337659887703039965023)
  ·
    refine ⟨13230506489831554559947535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8820337659887703039965023 13230506489831554559947535)
    ·
      refine ⟨19845759734747331839921303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230506489831554559947535 19845759734747331839921303)
      ·
        refine ⟨29768639602120997759881955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19845759734747331839921303 29768639602120997759881955)
        ·
          refine ⟨44652959403181496639822933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29768639602120997759881955 44652959403181496639822933)
          ·
            refine ⟨523276868006033163747925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 44652959403181496639822933 523276868006033163747925)
            ·
              refine ⟨6132150796945701137671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 523276868006033163747925 6132150796945701137671)
              ·
                rfl

theorem cell22_483664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 8].length) (baseStart_483664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483664 prefixEnd_483664 := by exact prefixLift 483664
  have htrace : WordTrace (prefixWord ++ tailWord_483664) baseStart_483664 baseEnd_483664 := by
    simpa [prefixWord, tailWord_483664, baseEnd_483664] using wordTrace_append hprefix tailTrace_483664
  have hstable : (prefixWord ++ tailWord_483664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483664).length < 2 ^ (prefixWord ++ tailWord_483664).sum := by decide
  have hdescent : baseEnd_483664 < baseStart_483664 := by decide
  rcases family_descends (prefixWord ++ tailWord_483664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483685 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_483685 : Nat := 118140960795 + 483685 * 2 ^ 59
def prefixEnd_483685 : Nat := 4983230072969 + 3 ^ 40 * 483685 * 2
def baseEnd_483685 : Nat := 165575260246696875942053

theorem tailTrace_483685 : CollatzResearch.WordTrace tailWord_483685 prefixEnd_483685 165575260246696875942053 := by
  unfold tailWord_483685
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641441252699326666444509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11760960835132884444296339 17641441252699326666444509)
  ·
    refine ⟨6615540469762247499916691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17641441252699326666444509 6615540469762247499916691)
    ·
      refine ⟨9923310704643371249875037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615540469762247499916691 9923310704643371249875037)
      ·
        refine ⟨3721241514241264218703139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9923310704643371249875037 3721241514241264218703139)
        ·
          refine ⟨5581862271361896328054709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721241514241264218703139 5581862271361896328054709)
          ·
            refine ⟨523299587940177780755129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5581862271361896328054709 523299587940177780755129)
            ·
              refine ⟨392474690955133335566347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523299587940177780755129 392474690955133335566347)
              ·
                refine ⟨588712036432700003349521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392474690955133335566347 588712036432700003349521)
                ·
                  refine ⟨441534027324525002512141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588712036432700003349521 441534027324525002512141)
                  ·
                    refine ⟨165575260246696875942053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441534027324525002512141 165575260246696875942053)
                    ·
                      rfl

theorem cell22_483685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_483685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483685 prefixEnd_483685 := by exact prefixLift 483685
  have htrace : WordTrace (prefixWord ++ tailWord_483685) baseStart_483685 baseEnd_483685 := by
    simpa [prefixWord, tailWord_483685, baseEnd_483685] using wordTrace_append hprefix tailTrace_483685
  have hstable : (prefixWord ++ tailWord_483685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483685).length < 2 ^ (prefixWord ++ tailWord_483685).sum := by decide
  have hdescent : baseEnd_483685 < baseStart_483685 := by decide
  rcases family_descends (prefixWord ++ tailWord_483685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483756 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_483756 : Nat := 118140960795 + 483756 * 2 ^ 59
def prefixEnd_483756 : Nat := 4983230072969 + 3 ^ 40 * 483756 * 2
def baseEnd_483756 : Nat := 165599564997676357416835

theorem tailTrace_483756 : CollatzResearch.WordTrace tailWord_483756 prefixEnd_483756 165599564997676357416835 := by
  unfold tailWord_483756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822015417721052896139561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11762687223628070528186081 8822015417721052896139561)
  ·
    refine ⟨6616511563290789672104671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8822015417721052896139561 6616511563290789672104671)
    ·
      refine ⟨9924767344936184508157007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616511563290789672104671 9924767344936184508157007)
      ·
        refine ⟨14887151017404276762235511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924767344936184508157007 14887151017404276762235511)
        ·
          refine ⟨22330726526106415143353267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887151017404276762235511 22330726526106415143353267)
          ·
            refine ⟨33496089789159622715029901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22330726526106415143353267 33496089789159622715029901)
            ·
              refine ⟨12561033670934858518136213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33496089789159622715029901 12561033670934858518136213)
              ·
                refine ⟨588798453325071493037635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12561033670934858518136213 588798453325071493037635)
                ·
                  refine ⟨883197679987607239556453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588798453325071493037635 883197679987607239556453)
                  ·
                    refine ⟨165599564997676357416835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883197679987607239556453 165599564997676357416835)
                    ·
                      rfl

theorem cell22_483756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_483756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483756 prefixEnd_483756 := by exact prefixLift 483756
  have htrace : WordTrace (prefixWord ++ tailWord_483756) baseStart_483756 baseEnd_483756 := by
    simpa [prefixWord, tailWord_483756, baseEnd_483756] using wordTrace_append hprefix tailTrace_483756
  have hstable : (prefixWord ++ tailWord_483756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483756).length < 2 ^ (prefixWord ++ tailWord_483756).sum := by decide
  have hdescent : baseEnd_483756 < baseStart_483756 := by decide
  rcases family_descends (prefixWord ++ tailWord_483756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483773 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_483773 : Nat := 118140960795 + 483773 * 2 ^ 59
def prefixEnd_483773 : Nat := 4983230072969 + 3 ^ 40 * 483773 * 2
def baseEnd_483773 : Nat := 165605384445093979741783

theorem tailTrace_483773 : CollatzResearch.WordTrace tailWord_483773 prefixEnd_483773 165605384445093979741783 := by
  unfold tailWord_483773
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644650876380517695647973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11763100584253678463765315 17644650876380517695647973)
  ·
    refine ⟨3308372039321347067933995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17644650876380517695647973 3308372039321347067933995)
    ·
      refine ⟨4962558058982020601900993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308372039321347067933995 4962558058982020601900993)
      ·
        refine ⟨3721918544236515451425745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962558058982020601900993 3721918544236515451425745)
        ·
          refine ⟨2791438908177386588569309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721918544236515451425745 2791438908177386588569309)
          ·
            refine ⟨1046789590566519970713491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2791438908177386588569309 1046789590566519970713491)
            ·
              refine ⟨1570184385849779956070237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046789590566519970713491 1570184385849779956070237)
              ·
                refine ⟨588819144693667483526339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1570184385849779956070237 588819144693667483526339)
                ·
                  refine ⟨883228717040501225289509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588819144693667483526339 883228717040501225289509)
                  ·
                    refine ⟨165605384445093979741783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883228717040501225289509 165605384445093979741783)
                    ·
                      rfl

theorem cell22_483773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_483773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483773 prefixEnd_483773 := by exact prefixLift 483773
  have htrace : WordTrace (prefixWord ++ tailWord_483773) baseStart_483773 baseEnd_483773 := by
    simpa [prefixWord, tailWord_483773, baseEnd_483773] using wordTrace_append hprefix tailTrace_483773
  have hstable : (prefixWord ++ tailWord_483773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483773).length < 2 ^ (prefixWord ++ tailWord_483773).sum := by decide
  have hdescent : baseEnd_483773 < baseStart_483773 := by decide
  rcases family_descends (prefixWord ++ tailWord_483773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483788 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_483788 : Nat := 118140960795 + 483788 * 2 ^ 59
def prefixEnd_483788 : Nat := 4983230072969 + 3 ^ 40 * 483788 * 2
def baseEnd_483788 : Nat := 55203506417212980205579

theorem tailTrace_483788 : CollatzResearch.WordTrace tailWord_483788 prefixEnd_483788 55203506417212980205579 := by
  unfold tailWord_483788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822598985663087628722009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11763465314217450171629345 8822598985663087628722009)
  ·
    refine ⟨6616949239247315721541507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8822598985663087628722009 6616949239247315721541507)
    ·
      refine ⟨9925423858870973582312261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616949239247315721541507 9925423858870973582312261)
      ·
        refine ⟨1861016973538307546683549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9925423858870973582312261 1861016973538307546683549)
        ·
          refine ⟨697881365076865330006331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1861016973538307546683549 697881365076865330006331)
          ·
            refine ⟨1046822047615297995009497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697881365076865330006331 1046822047615297995009497)
            ·
              refine ⟨785116535711473496257123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046822047615297995009497 785116535711473496257123)
              ·
                refine ⟨1177674803567210244385685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785116535711473496257123 1177674803567210244385685)
                ·
                  refine ⟨55203506417212980205579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177674803567210244385685 55203506417212980205579)
                  ·
                    rfl

theorem cell22_483788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_483788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483788 prefixEnd_483788 := by exact prefixLift 483788
  have htrace : WordTrace (prefixWord ++ tailWord_483788) baseStart_483788 baseEnd_483788 := by
    simpa [prefixWord, tailWord_483788, baseEnd_483788] using wordTrace_append hprefix tailTrace_483788
  have hstable : (prefixWord ++ tailWord_483788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483788).length < 2 ^ (prefixWord ++ tailWord_483788).sum := by decide
  have hdescent : baseEnd_483788 < baseStart_483788 := by decide
  rcases family_descends (prefixWord ++ tailWord_483788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483816 : List Nat := [2, 1, 4, 1, 1, 4, 1, 8]
def baseStart_483816 : Nat := 118140960795 + 483816 * 2 ^ 59
def prefixEnd_483816 : Nat := 4983230072969 + 3 ^ 40 * 483816 * 2
def baseEnd_483816 : Nat := 18402233802650688990739

theorem tailTrace_483816 : CollatzResearch.WordTrace tailWord_483816 prefixEnd_483816 18402233802650688990739 := by
  unfold tailWord_483816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823109607612368019731651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11764146143483157359642201 8823109607612368019731651)
  ·
    refine ⟨13234664411418552029597477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823109607612368019731651 13234664411418552029597477)
    ·
      refine ⟨2481499577140978505549527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13234664411418552029597477 2481499577140978505549527)
      ·
        refine ⟨3722249365711467758324291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481499577140978505549527 3722249365711467758324291)
        ·
          refine ⟨5583374048567201637486437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722249365711467758324291 5583374048567201637486437)
          ·
            refine ⟨1046882634106350307028707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5583374048567201637486437 1046882634106350307028707)
            ·
              refine ⟨1570323951159525460543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046882634106350307028707 1570323951159525460543061)
              ·
                refine ⟨18402233802650688990739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1570323951159525460543061 18402233802650688990739)
                ·
                  rfl

theorem cell22_483816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_483816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483816 prefixEnd_483816 := by exact prefixLift 483816
  have htrace : WordTrace (prefixWord ++ tailWord_483816) baseStart_483816 baseEnd_483816 := by
    simpa [prefixWord, tailWord_483816, baseEnd_483816] using wordTrace_append hprefix tailTrace_483816
  have hstable : (prefixWord ++ tailWord_483816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483816).length < 2 ^ (prefixWord ++ tailWord_483816).sum := by decide
  have hdescent : baseEnd_483816 < baseStart_483816 := by decide
  rcases family_descends (prefixWord ++ tailWord_483816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483910 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_483910 : Nat := 118140960795 + 483910 * 2 ^ 59
def prefixEnd_483910 : Nat := 4983230072969 + 3 ^ 40 * 483910 * 2
def baseEnd_483910 : Nat := 165652282344871289066363

theorem tailTrace_483910 : CollatzResearch.WordTrace tailWord_483910 prefixEnd_483910 165652282344871289066363 := by
  unfold tailWord_483910
  simp only [CollatzResearch.WordTrace]
  refine ⟨551551489902630940418287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11766431784589460062256789 551551489902630940418287)
  ·
    refine ⟨827327234853946410627431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551551489902630940418287 827327234853946410627431)
    ·
      refine ⟨1240990852280919615941147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827327234853946410627431 1240990852280919615941147)
      ·
        refine ⟨1861486278421379423911721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240990852280919615941147 1861486278421379423911721)
        ·
          refine ⟨1396114708816034567933791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861486278421379423911721 1396114708816034567933791)
          ·
            refine ⟨2094172063224051851900687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396114708816034567933791 2094172063224051851900687)
            ·
              refine ⟨3141258094836077777851031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094172063224051851900687 3141258094836077777851031)
              ·
                refine ⟨4711887142254116666776547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141258094836077777851031 4711887142254116666776547)
                ·
                  refine ⟨7067830713381175000164821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711887142254116666776547 7067830713381175000164821)
                  ·
                    refine ⟨165652282344871289066363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7067830713381175000164821 165652282344871289066363)
                    ·
                      rfl

theorem cell22_483910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_483910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483910 prefixEnd_483910 := by exact prefixLift 483910
  have htrace : WordTrace (prefixWord ++ tailWord_483910) baseStart_483910 baseEnd_483910 := by
    simpa [prefixWord, tailWord_483910, baseEnd_483910] using wordTrace_append hprefix tailTrace_483910
  have hstable : (prefixWord ++ tailWord_483910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483910).length < 2 ^ (prefixWord ++ tailWord_483910).sum := by decide
  have hdescent : baseEnd_483910 < baseStart_483910 := by decide
  rcases family_descends (prefixWord ++ tailWord_483910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483940 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_483940 : Nat := 118140960795 + 483940 * 2 ^ 59
def prefixEnd_483940 : Nat := 4983230072969 + 3 ^ 40 * 483940 * 2
def baseEnd_483940 : Nat := 55220850652653736938757

theorem tailTrace_483940 : CollatzResearch.WordTrace tailWord_483940 prefixEnd_483940 55220850652653736938757 := by
  unfold tailWord_483940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825370933387752608488637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11767161244517003477984849 8825370933387752608488637)
  ·
    refine ⟨3309514100020407228183239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8825370933387752608488637 3309514100020407228183239)
    ·
      refine ⟨4964271150030610842274859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309514100020407228183239 4964271150030610842274859)
      ·
        refine ⟨7446406725045916263412289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964271150030610842274859 7446406725045916263412289)
        ·
          refine ⟨5584805043784437197559217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7446406725045916263412289 5584805043784437197559217)
          ·
            refine ⟨4188603782838327898169413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584805043784437197559217 4188603782838327898169413)
            ·
              refine ⟨785363209282186480906765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4188603782838327898169413 785363209282186480906765)
              ·
                refine ⟨294511203480819930340037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785363209282186480906765 294511203480819930340037)
                ·
                  refine ⟨55220850652653736938757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294511203480819930340037 55220850652653736938757)
                  ·
                    rfl

theorem cell22_483940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_483940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_483940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_483940 prefixEnd_483940 := by exact prefixLift 483940
  have htrace : WordTrace (prefixWord ++ tailWord_483940) baseStart_483940 baseEnd_483940 := by
    simpa [prefixWord, tailWord_483940, baseEnd_483940] using wordTrace_append hprefix tailTrace_483940
  have hstable : (prefixWord ++ tailWord_483940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483940).length < 2 ^ (prefixWord ++ tailWord_483940).sum := by decide
  have hdescent : baseEnd_483940 < baseStart_483940 := by decide
  rcases family_descends (prefixWord ++ tailWord_483940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484028 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_484028 : Nat := 118140960795 + 484028 * 2 ^ 59
def prefixEnd_484028 : Nat := 4983230072969 + 3 ^ 40 * 484028 * 2
def baseEnd_484028 : Nat := 165692676156358314616001

theorem tailTrace_484028 : CollatzResearch.WordTrace tailWord_484028 prefixEnd_484028 165692676156358314616001 := by
  unfold tailWord_484028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8826975745228348123090369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11769300993637797497453825 8826975745228348123090369)
  ·
    refine ⟨6620231808921261092317777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8826975745228348123090369 6620231808921261092317777)
    ·
      refine ⟨4965173856690945819238333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6620231808921261092317777 4965173856690945819238333)
      ·
        refine ⟨1861940196259104682214375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4965173856690945819238333 1861940196259104682214375)
        ·
          refine ⟨2792910294388657023321563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861940196259104682214375 2792910294388657023321563)
          ·
            refine ⟨4189365441582985534982345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792910294388657023321563 4189365441582985534982345)
            ·
              refine ⟨3142024081187239151236759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189365441582985534982345 3142024081187239151236759)
              ·
                refine ⟨4713036121780858726855139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142024081187239151236759 4713036121780858726855139)
                ·
                  refine ⟨7069554182671288090282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713036121780858726855139 7069554182671288090282709)
                  ·
                    refine ⟨165692676156358314616001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7069554182671288090282709 165692676156358314616001)
                    ·
                      rfl

theorem cell22_484028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_484028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484028 prefixEnd_484028 := by exact prefixLift 484028
  have htrace : WordTrace (prefixWord ++ tailWord_484028) baseStart_484028 baseEnd_484028 := by
    simpa [prefixWord, tailWord_484028, baseEnd_484028] using wordTrace_append hprefix tailTrace_484028
  have hstable : (prefixWord ++ tailWord_484028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484028).length < 2 ^ (prefixWord ++ tailWord_484028).sum := by decide
  have hdescent : baseEnd_484028 < baseStart_484028 := by decide
  rcases family_descends (prefixWord ++ tailWord_484028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484030 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_484030 : Nat := 118140960795 + 484030 * 2 ^ 59
def prefixEnd_484030 : Nat := 4983230072969 + 3 ^ 40 * 484030 * 2
def baseEnd_484030 : Nat := 55231120265743658688665

theorem tailTrace_484030 : CollatzResearch.WordTrace tailWord_484030 prefixEnd_484030 55231120265743658688665 := by
  unfold tailWord_484030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206753054556181323469193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11769349624299633725169029 2206753054556181323469193)
  ·
    refine ⟨1655064790917135992601895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2206753054556181323469193 1655064790917135992601895)
    ·
      refine ⟨2482597186375703988902843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655064790917135992601895 2482597186375703988902843)
      ·
        refine ⟨3723895779563555983354265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482597186375703988902843 3723895779563555983354265)
        ·
          refine ⟨2792921834672666987515699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723895779563555983354265 2792921834672666987515699)
          ·
            refine ⟨4189382752009000481273549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792921834672666987515699 4189382752009000481273549)
            ·
              refine ⟨1571018532003375180477581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4189382752009000481273549 1571018532003375180477581)
              ·
                refine ⟨589131949501265692679093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1571018532003375180477581 589131949501265692679093)
                ·
                  refine ⟨55231120265743658688665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589131949501265692679093 55231120265743658688665)
                  ·
                    rfl

theorem cell22_484030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_484030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484030 prefixEnd_484030 := by exact prefixLift 484030
  have htrace : WordTrace (prefixWord ++ tailWord_484030) baseStart_484030 baseEnd_484030 := by
    simpa [prefixWord, tailWord_484030, baseEnd_484030] using wordTrace_append hprefix tailTrace_484030
  have hstable : (prefixWord ++ tailWord_484030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484030).length < 2 ^ (prefixWord ++ tailWord_484030).sum := by decide
  have hdescent : baseEnd_484030 < baseStart_484030 := by decide
  rcases family_descends (prefixWord ++ tailWord_484030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484088 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_484088 : Nat := 118140960795 + 484088 * 2 ^ 59
def prefixEnd_484088 : Nat := 4983230072969 + 3 ^ 40 * 484088 * 2
def baseEnd_484088 : Nat := 165713215382538158115817

theorem tailTrace_484088 : CollatzResearch.WordTrace tailWord_484088 prefixEnd_484088 165713215382538158115817 := by
  unfold tailWord_484088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828069935119663246682459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11770759913492884328909945 8828069935119663246682459)
  ·
    refine ⟨13242104902679494870023689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8828069935119663246682459 13242104902679494870023689)
    ·
      refine ⟨9931578677009621152517767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13242104902679494870023689 9931578677009621152517767)
      ·
        refine ⟨14897368015514431728776651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931578677009621152517767 14897368015514431728776651)
        ·
          refine ⟨22346052023271647593164977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897368015514431728776651 22346052023271647593164977)
          ·
            refine ⟨16759539017453735694873733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22346052023271647593164977 16759539017453735694873733)
            ·
              refine ⟨3142413565772575442788825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16759539017453735694873733 3142413565772575442788825)
              ·
                refine ⟨2356810174329431582091619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142413565772575442788825 2356810174329431582091619)
                ·
                  refine ⟨3535215261494147373137429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356810174329431582091619 3535215261494147373137429)
                  ·
                    refine ⟨165713215382538158115817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3535215261494147373137429 165713215382538158115817)
                    ·
                      rfl

theorem cell22_484088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_484088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484088 prefixEnd_484088 := by exact prefixLift 484088
  have htrace : WordTrace (prefixWord ++ tailWord_484088) baseStart_484088 baseEnd_484088 := by
    simpa [prefixWord, tailWord_484088, baseEnd_484088] using wordTrace_append hprefix tailTrace_484088
  have hstable : (prefixWord ++ tailWord_484088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484088).length < 2 ^ (prefixWord ++ tailWord_484088).sum := by decide
  have hdescent : baseEnd_484088 < baseStart_484088 := by decide
  rcases family_descends (prefixWord ++ tailWord_484088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484105 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_484105 : Nat := 118140960795 + 484105 * 2 ^ 59
def prefixEnd_484105 : Nat := 4983230072969 + 3 ^ 40 * 484105 * 2
def baseEnd_484105 : Nat := 165719034829955780440765

theorem tailTrace_484105 : CollatzResearch.WordTrace tailWord_484105 prefixEnd_484105 165719034829955780440765 := by
  unfold tailWord_484105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656759911177738396733769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11771173274118492264489179 17656759911177738396733769)
  ·
    refine ⟨13242569933383303797550327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17656759911177738396733769 13242569933383303797550327)
    ·
      refine ⟨19863854900074955696325491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13242569933383303797550327 19863854900074955696325491)
      ·
        refine ⟨29795782350112433544488237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863854900074955696325491 29795782350112433544488237)
        ·
          refine ⟨11173418381292162579183089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29795782350112433544488237 11173418381292162579183089)
          ·
            refine ⟨8380063785969121934387317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11173418381292162579183089 8380063785969121934387317)
            ·
              refine ⟨785630979934605181348811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8380063785969121934387317 785630979934605181348811)
              ·
                refine ⟨1178446469901907772023217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785630979934605181348811 1178446469901907772023217)
                ·
                  refine ⟨883834852426430829017413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178446469901907772023217 883834852426430829017413)
                  ·
                    refine ⟨165719034829955780440765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883834852426430829017413 165719034829955780440765)
                    ·
                      rfl

theorem cell22_484105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_484105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484105 prefixEnd_484105 := by exact prefixLift 484105
  have htrace : WordTrace (prefixWord ++ tailWord_484105) baseStart_484105 baseEnd_484105 := by
    simpa [prefixWord, tailWord_484105, baseEnd_484105] using wordTrace_append hprefix tailTrace_484105
  have hstable : (prefixWord ++ tailWord_484105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484105).length < 2 ^ (prefixWord ++ tailWord_484105).sum := by decide
  have hdescent : baseEnd_484105 < baseStart_484105 := by decide
  rcases family_descends (prefixWord ++ tailWord_484105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484124 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_484124 : Nat := 118140960795 + 484124 * 2 ^ 59
def prefixEnd_484124 : Nat := 4983230072969 + 3 ^ 40 * 484124 * 2
def baseEnd_484124 : Nat := 165725538918246064215707

theorem tailTrace_484124 : CollatzResearch.WordTrace tailWord_484124 prefixEnd_484124 165725538918246064215707 := by
  unfold tailWord_484124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828726449054452320837713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11771635265405936427783617 8828726449054452320837713)
  ·
    refine ⟨6621544836790839240628285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8828726449054452320837713 6621544836790839240628285)
    ·
      refine ⟨2483079313796564715235607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6621544836790839240628285 2483079313796564715235607)
      ·
        refine ⟨3724618970694847072853411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483079313796564715235607 3724618970694847072853411)
        ·
          refine ⟨5586928456042270609280117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724618970694847072853411 5586928456042270609280117)
          ·
            refine ⟨523774542753962869620011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5586928456042270609280117 523774542753962869620011)
            ·
              refine ⟨785661814130944304430017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523774542753962869620011 785661814130944304430017)
              ·
                refine ⟨589246360598208228322513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785661814130944304430017 589246360598208228322513)
                ·
                  refine ⟨441934770448656171241885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589246360598208228322513 441934770448656171241885)
                  ·
                    refine ⟨165725538918246064215707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441934770448656171241885 165725538918246064215707)
                    ·
                      rfl

theorem cell22_484124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_484124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484124 prefixEnd_484124 := by exact prefixLift 484124
  have htrace : WordTrace (prefixWord ++ tailWord_484124) baseStart_484124 baseEnd_484124 := by
    simpa [prefixWord, tailWord_484124, baseEnd_484124] using wordTrace_append hprefix tailTrace_484124
  have hstable : (prefixWord ++ tailWord_484124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484124).length < 2 ^ (prefixWord ++ tailWord_484124).sum := by decide
  have hdescent : baseEnd_484124 < baseStart_484124 := by decide
  rcases family_descends (prefixWord ++ tailWord_484124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484141 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_484141 : Nat := 118140960795 + 484141 * 2 ^ 59
def prefixEnd_484141 : Nat := 4983230072969 + 3 ^ 40 * 484141 * 2
def baseEnd_484141 : Nat := 165731358365663686540655

theorem tailTrace_484141 : CollatzResearch.WordTrace tailWord_484141 prefixEnd_484141 165731358365663686540655 := by
  unfold tailWord_484141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658072939047316545044277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772048626031544363362851 17658072939047316545044277)
  ·
    refine ⟨1655444338035685926097901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17658072939047316545044277 1655444338035685926097901)
    ·
      refine ⟨620791626763382222286713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1655444338035685926097901 620791626763382222286713)
      ·
        refine ⟨465593720072536666715035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620791626763382222286713 465593720072536666715035)
        ·
          refine ⟨698390580108805000072553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465593720072536666715035 698390580108805000072553)
          ·
            refine ⟨523792935081603750054415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698390580108805000072553 523792935081603750054415)
            ·
              refine ⟨785689402622405625081623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523792935081603750054415 785689402622405625081623)
              ·
                refine ⟨1178534103933608437622435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785689402622405625081623 1178534103933608437622435)
                ·
                  refine ⟨1767801155900412656433653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178534103933608437622435 1767801155900412656433653)
                  ·
                    refine ⟨165731358365663686540655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1767801155900412656433653 165731358365663686540655)
                    ·
                      rfl

theorem cell22_484141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_484141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484141 prefixEnd_484141 := by exact prefixLift 484141
  have htrace : WordTrace (prefixWord ++ tailWord_484141) baseStart_484141 baseEnd_484141 := by
    simpa [prefixWord, tailWord_484141, baseEnd_484141] using wordTrace_append hprefix tailTrace_484141
  have hstable : (prefixWord ++ tailWord_484141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484141).length < 2 ^ (prefixWord ++ tailWord_484141).sum := by decide
  have hdescent : baseEnd_484141 < baseStart_484141 := by decide
  rcases family_descends (prefixWord ++ tailWord_484141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484154 : List Nat := [3, 1, 1, 1, 7, 1, 2, 6]
def baseStart_484154 : Nat := 118140960795 + 484154 * 2 ^ 59
def prefixEnd_484154 : Nat := 4983230072969 + 3 ^ 40 * 484154 * 2
def baseEnd_484154 : Nat := 18415089836815109551735

theorem tailTrace_484154 : CollatzResearch.WordTrace tailWord_484154 prefixEnd_484154 18415089836815109551735 := by
  unfold tailWord_484154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414636772000054941316879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11772364725333479843511677 4414636772000054941316879)
  ·
    refine ⟨6621955158000082411975319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414636772000054941316879 6621955158000082411975319)
    ·
      refine ⟨9932932737000123617962979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621955158000082411975319 9932932737000123617962979)
      ·
        refine ⟨14899399105500185426944469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932932737000123617962979 14899399105500185426944469)
        ·
          refine ⟨349204666535160595944011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14899399105500185426944469 349204666535160595944011)
          ·
            refine ⟨523806999802740893916017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349204666535160595944011 523806999802740893916017)
            ·
              refine ⟨392855249852055670437013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523806999802740893916017 392855249852055670437013)
              ·
                refine ⟨18415089836815109551735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 392855249852055670437013 18415089836815109551735)
                ·
                  rfl

theorem cell22_484154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_484154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484154 prefixEnd_484154 := by exact prefixLift 484154
  have htrace : WordTrace (prefixWord ++ tailWord_484154) baseStart_484154 baseEnd_484154 := by
    simpa [prefixWord, tailWord_484154, baseEnd_484154] using wordTrace_append hprefix tailTrace_484154
  have hstable : (prefixWord ++ tailWord_484154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484154).length < 2 ^ (prefixWord ++ tailWord_484154).sum := by decide
  have hdescent : baseEnd_484154 < baseStart_484154 := by decide
  rcases family_descends (prefixWord ++ tailWord_484154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484169 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_484169 : Nat := 118140960795 + 484169 * 2 ^ 59
def prefixEnd_484169 : Nat := 4983230072969 + 3 ^ 40 * 484169 * 2
def baseEnd_484169 : Nat := 165740943337880946840569

theorem tailTrace_484169 : CollatzResearch.WordTrace tailWord_484169 prefixEnd_484169 165740943337880946840569 := by
  unfold tailWord_484169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659094182945877327063561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772729455297251551375707 17659094182945877327063561)
  ·
    refine ⟨13244320637209407995297671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17659094182945877327063561 13244320637209407995297671)
    ·
      refine ⟨19866480955814111992946507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13244320637209407995297671 19866480955814111992946507)
      ·
        refine ⟨29799721433721167989419761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19866480955814111992946507 29799721433721167989419761)
        ·
          refine ⟨22349791075290875992064821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29799721433721167989419761 22349791075290875992064821)
          ·
            refine ⟨2095292913308519624256077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22349791075290875992064821 2095292913308519624256077)
            ·
              refine ⟨785734842490694859096029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095292913308519624256077 785734842490694859096029)
              ·
                refine ⟨294650565934010572161011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785734842490694859096029 294650565934010572161011)
                ·
                  refine ⟨441975848901015858241517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294650565934010572161011 441975848901015858241517)
                  ·
                    refine ⟨165740943337880946840569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441975848901015858241517 165740943337880946840569)
                    ·
                      rfl

theorem cell22_484169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_484169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484169 prefixEnd_484169 := by exact prefixLift 484169
  have htrace : WordTrace (prefixWord ++ tailWord_484169) baseStart_484169 baseEnd_484169 := by
    simpa [prefixWord, tailWord_484169, baseEnd_484169] using wordTrace_append hprefix tailTrace_484169
  have hstable : (prefixWord ++ tailWord_484169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484169).length < 2 ^ (prefixWord ++ tailWord_484169).sum := by decide
  have hdescent : baseEnd_484169 < baseStart_484169 := by decide
  rcases family_descends (prefixWord ++ tailWord_484169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484186 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_484186 : Nat := 118140960795 + 484186 * 2 ^ 59
def prefixEnd_484186 : Nat := 4983230072969 + 3 ^ 40 * 484186 * 2
def baseEnd_484186 : Nat := 165746762785298569165517

theorem tailTrace_484186 : CollatzResearch.WordTrace tailWord_484186 prefixEnd_484186 165746762785298569165517 := by
  unfold tailWord_484186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414928555971072307608103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11773142815922859486954941 4414928555971072307608103)
  ·
    refine ⟨6622392833956608461412155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414928555971072307608103 6622392833956608461412155)
    ·
      refine ⟨9933589250934912692118233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622392833956608461412155 9933589250934912692118233)
      ·
        refine ⟨7450191938201184519088675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9933589250934912692118233 7450191938201184519088675)
        ·
          refine ⟨11175287907301776778633013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450191938201184519088675 11175287907301776778633013)
          ·
            refine ⟨1047683241309541572996845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11175287907301776778633013 1047683241309541572996845)
            ·
              refine ⟨392881215491078089873817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047683241309541572996845 392881215491078089873817)
              ·
                refine ⟨294660911618308567405363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392881215491078089873817 294660911618308567405363)
                ·
                  refine ⟨441991367427462851108045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294660911618308567405363 441991367427462851108045)
                  ·
                    refine ⟨165746762785298569165517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441991367427462851108045 165746762785298569165517)
                    ·
                      rfl

theorem cell22_484186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_484186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484186 prefixEnd_484186 := by exact prefixLift 484186
  have htrace : WordTrace (prefixWord ++ tailWord_484186) baseStart_484186 baseEnd_484186 := by
    simpa [prefixWord, tailWord_484186, baseEnd_484186] using wordTrace_append hprefix tailTrace_484186
  have hstable : (prefixWord ++ tailWord_484186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484186).length < 2 ^ (prefixWord ++ tailWord_484186).sum := by decide
  have hdescent : baseEnd_484186 < baseStart_484186 := by decide
  rcases family_descends (prefixWord ++ tailWord_484186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484199 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 5]
def baseStart_484199 : Nat := 118140960795 + 484199 * 2 ^ 59
def prefixEnd_484199 : Nat := 4983230072969 + 3 ^ 40 * 484199 * 2
def baseEnd_484199 : Nat := 55250404316990289530159

theorem tailTrace_484199 : CollatzResearch.WordTrace tailWord_484199 prefixEnd_484199 55250404316990289530159 := by
  unfold tailWord_484199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660188372837192450655651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11773458915224794967103767 17660188372837192450655651)
  ·
    refine ⟨26490282559255788675983477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660188372837192450655651 26490282559255788675983477)
    ·
      refine ⟨2483463989930230188373451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26490282559255788675983477 2483463989930230188373451)
      ·
        refine ⟨3725195984895345282560177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483463989930230188373451 3725195984895345282560177)
        ·
          refine ⟨2793896988671508961920133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725195984895345282560177 2793896988671508961920133)
          ·
            refine ⟨523855685375907930360025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2793896988671508961920133 523855685375907930360025)
            ·
              refine ⟨392891764031930947770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523855685375907930360025 392891764031930947770019)
              ·
                refine ⟨589337646047896421655029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392891764031930947770019 589337646047896421655029)
                ·
                  refine ⟨55250404316990289530159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589337646047896421655029 55250404316990289530159)
                  ·
                    rfl

theorem cell22_484199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 5].length) (baseStart_484199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484199 prefixEnd_484199 := by exact prefixLift 484199
  have htrace : WordTrace (prefixWord ++ tailWord_484199) baseStart_484199 baseEnd_484199 := by
    simpa [prefixWord, tailWord_484199, baseEnd_484199] using wordTrace_append hprefix tailTrace_484199
  have hstable : (prefixWord ++ tailWord_484199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484199).length < 2 ^ (prefixWord ++ tailWord_484199).sum := by decide
  have hdescent : baseEnd_484199 < baseStart_484199 := by decide
  rcases family_descends (prefixWord ++ tailWord_484199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484210 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_484210 : Nat := 118140960795 + 484210 * 2 ^ 59
def prefixEnd_484210 : Nat := 4983230072969 + 3 ^ 40 * 484210 * 2
def baseEnd_484210 : Nat := 55251659491923502188481

theorem tailTrace_484210 : CollatzResearch.WordTrace tailWord_484210 prefixEnd_484210 55251659491923502188481 := by
  unfold tailWord_484210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415147393949335332326521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11773726383864894219537389 4415147393949335332326521)
  ·
    refine ⟨3311360545462001499244891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4415147393949335332326521 3311360545462001499244891)
    ·
      refine ⟨4967040818193002248867337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311360545462001499244891 4967040818193002248867337)
      ·
        refine ⟨3725280613644751686650503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4967040818193002248867337 3725280613644751686650503)
        ·
          refine ⟨5587920920467127529975755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725280613644751686650503 5587920920467127529975755)
          ·
            refine ⟨8381881380700691294963633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587920920467127529975755 8381881380700691294963633)
            ·
              refine ⟨6286411035525518471222725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381881380700691294963633 6286411035525518471222725)
              ·
                refine ⟨1178702069161034713354261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6286411035525518471222725 1178702069161034713354261)
                ·
                  refine ⟨55251659491923502188481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1178702069161034713354261 55251659491923502188481)
                  ·
                    rfl

theorem cell22_484210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_484210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484210 prefixEnd_484210 := by exact prefixLift 484210
  have htrace : WordTrace (prefixWord ++ tailWord_484210) baseStart_484210 baseEnd_484210 := by
    simpa [prefixWord, tailWord_484210, baseEnd_484210] using wordTrace_append hprefix tailTrace_484210
  have hstable : (prefixWord ++ tailWord_484210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484210).length < 2 ^ (prefixWord ++ tailWord_484210).sum := by decide
  have hdescent : baseEnd_484210 < baseStart_484210 := by decide
  rcases family_descends (prefixWord ++ tailWord_484210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484227 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 4]
def baseStart_484227 : Nat := 118140960795 + 484227 * 2 ^ 59
def prefixEnd_484227 : Nat := 4983230072969 + 3 ^ 40 * 484227 * 2
def baseEnd_484227 : Nat := 55253599307729376296797

theorem tailTrace_484227 : CollatzResearch.WordTrace tailWord_484227 prefixEnd_484227 55253599307729376296797 := by
  unfold tailWord_484227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661209616735753232674935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11774139744490502155116623 17661209616735753232674935)
  ·
    refine ⟨26491814425103629849012403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17661209616735753232674935 26491814425103629849012403)
    ·
      refine ⟨39737721637655444773518605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26491814425103629849012403 39737721637655444773518605)
      ·
        refine ⟨14901645614120791790069477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39737721637655444773518605 14901645614120791790069477)
        ·
          refine ⟨2794058552647648460638027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14901645614120791790069477 2794058552647648460638027)
          ·
            refine ⟨4191087828971472690957041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794058552647648460638027 4191087828971472690957041)
            ·
              refine ⟨3143315871728604518217781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191087828971472690957041 3143315871728604518217781)
              ·
                refine ⟨294685862974556673582917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3143315871728604518217781 294685862974556673582917)
                ·
                  refine ⟨55253599307729376296797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294685862974556673582917 55253599307729376296797)
                  ·
                    rfl

theorem cell22_484227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 4].length) (baseStart_484227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484227 prefixEnd_484227 := by exact prefixLift 484227
  have htrace : WordTrace (prefixWord ++ tailWord_484227) baseStart_484227 baseEnd_484227 := by
    simpa [prefixWord, tailWord_484227, baseEnd_484227] using wordTrace_append hprefix tailTrace_484227
  have hstable : (prefixWord ++ tailWord_484227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484227).length < 2 ^ (prefixWord ++ tailWord_484227).sum := by decide
  have hdescent : baseEnd_484227 < baseStart_484227 := by decide
  rcases family_descends (prefixWord ++ tailWord_484227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484229 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_484229 : Nat := 118140960795 + 484229 * 2 ^ 59
def prefixEnd_484229 : Nat := 4983230072969 + 3 ^ 40 * 484229 * 2
def baseEnd_484229 : Nat := 165761482564060790340385

theorem tailTrace_484229 : CollatzResearch.WordTrace tailWord_484229 prefixEnd_484229 165761482564060790340385 := by
  unfold tailWord_484229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661282562728507574247741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11774188375152338382831827 17661282562728507574247741)
  ·
    refine ⟨6622980961023190340342903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17661282562728507574247741 6622980961023190340342903)
    ·
      refine ⟨9934471441534785510514355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622980961023190340342903 9934471441534785510514355)
      ·
        refine ⟨14901707162302178265771533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9934471441534785510514355 14901707162302178265771533)
        ·
          refine ⟨5588140185863316849664325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14901707162302178265771533 5588140185863316849664325)
          ·
            refine ⟨1047776284849371909312061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5588140185863316849664325 1047776284849371909312061)
            ·
              refine ⟨392916106818514465992023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047776284849371909312061 392916106818514465992023)
              ·
                refine ⟨589374160227771698988035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392916106818514465992023 589374160227771698988035)
                ·
                  refine ⟨884061240341657548482053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589374160227771698988035 884061240341657548482053)
                  ·
                    refine ⟨165761482564060790340385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884061240341657548482053 165761482564060790340385)
                    ·
                      rfl

theorem cell22_484229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_484229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484229 prefixEnd_484229 := by exact prefixLift 484229
  have htrace : WordTrace (prefixWord ++ tailWord_484229) baseStart_484229 baseEnd_484229 := by
    simpa [prefixWord, tailWord_484229, baseEnd_484229] using wordTrace_append hprefix tailTrace_484229
  have hstable : (prefixWord ++ tailWord_484229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484229).length < 2 ^ (prefixWord ++ tailWord_484229).sum := by decide
  have hdescent : baseEnd_484229 < baseStart_484229 := by decide
  rcases family_descends (prefixWord ++ tailWord_484229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484244 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_484244 : Nat := 118140960795 + 484244 * 2 ^ 59
def prefixEnd_484244 : Nat := 4983230072969 + 3 ^ 40 * 484244 * 2
def baseEnd_484244 : Nat := 55255539123535250405113

theorem tailTrace_484244 : CollatzResearch.WordTrace tailWord_484244 prefixEnd_484244 55255539123535250405113 := by
  unfold tailWord_484244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830914828837082568021893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11774553105116110090695857 8830914828837082568021893)
  ·
    refine ⟨1655796530406952981504105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8830914828837082568021893 1655796530406952981504105)
    ·
      refine ⟨1241847397805214736128079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1655796530406952981504105 1241847397805214736128079)
      ·
        refine ⟨1862771096707822104192119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241847397805214736128079 1862771096707822104192119)
        ·
          refine ⟨2794156645061733156288179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862771096707822104192119 2794156645061733156288179)
          ·
            refine ⟨4191234967592599734432269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794156645061733156288179 4191234967592599734432269)
            ·
              refine ⟨1571713112847224900412101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4191234967592599734432269 1571713112847224900412101)
              ·
                refine ⟨294696208658854668827269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1571713112847224900412101 294696208658854668827269)
                ·
                  refine ⟨55255539123535250405113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294696208658854668827269 55255539123535250405113)
                  ·
                    rfl

theorem cell22_484244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_484244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484244 prefixEnd_484244 := by exact prefixLift 484244
  have htrace : WordTrace (prefixWord ++ tailWord_484244) baseStart_484244 baseEnd_484244 := by
    simpa [prefixWord, tailWord_484244, baseEnd_484244] using wordTrace_append hprefix tailTrace_484244
  have hstable : (prefixWord ++ tailWord_484244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484244).length < 2 ^ (prefixWord ++ tailWord_484244).sum := by decide
  have hdescent : baseEnd_484244 < baseStart_484244 := by decide
  rcases family_descends (prefixWord ++ tailWord_484244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484246 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_484246 : Nat := 118140960795 + 484246 * 2 ^ 59
def prefixEnd_484246 : Nat := 4983230072969 + 3 ^ 40 * 484246 * 2
def baseEnd_484246 : Nat := 165767302011478412665333

theorem tailTrace_484246 : CollatzResearch.WordTrace tailWord_484246 prefixEnd_484246 165767302011478412665333 := by
  unfold tailWord_484246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103868912729182467351037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11774601735777946318411061 1103868912729182467351037)
  ·
    refine ⟨413950842273443425256639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1103868912729182467351037 413950842273443425256639)
    ·
      refine ⟨620926263410165137884959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413950842273443425256639 620926263410165137884959)
      ·
        refine ⟨931389395115247706827439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620926263410165137884959 931389395115247706827439)
        ·
          refine ⟨1397084092672871560241159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931389395115247706827439 1397084092672871560241159)
          ·
            refine ⟨2095626139009307340361739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397084092672871560241159 2095626139009307340361739)
            ·
              refine ⟨3143439208513961010542609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095626139009307340361739 3143439208513961010542609)
              ·
                refine ⟨2357579406385470757906957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3143439208513961010542609 2357579406385470757906957)
                ·
                  refine ⟨884092277394551534215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2357579406385470757906957 884092277394551534215109)
                  ·
                    refine ⟨165767302011478412665333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884092277394551534215109 165767302011478412665333)
                    ·
                      rfl

theorem cell22_484246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_484246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484246 prefixEnd_484246 := by exact prefixLift 484246
  have htrace : WordTrace (prefixWord ++ tailWord_484246) baseStart_484246 baseEnd_484246 := by
    simpa [prefixWord, tailWord_484246, baseEnd_484246] using wordTrace_append hprefix tailTrace_484246
  have hstable : (prefixWord ++ tailWord_484246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484246).length < 2 ^ (prefixWord ++ tailWord_484246).sum := by decide
  have hdescent : baseEnd_484246 < baseStart_484246 := by decide
  rcases family_descends (prefixWord ++ tailWord_484246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484340 : List Nat := [2, 6, 2, 1, 2, 1, 8]
def baseStart_484340 : Nat := 118140960795 + 484340 * 2 ^ 59
def prefixEnd_484340 : Nat := 4983230072969 + 3 ^ 40 * 484340 * 2
def baseEnd_484340 : Nat := 6140721486388648178335

theorem tailTrace_484340 : CollatzResearch.WordTrace tailWord_484340 prefixEnd_484340 6140721486388648178335 := by
  unfold tailWord_484340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832665532663186765769237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11776887376884249021025649 8832665532663186765769237)
  ·
    refine ⟨414031196843586879645433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8832665532663186765769237 414031196843586879645433)
    ·
      refine ⟨310523397632690159734075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414031196843586879645433 310523397632690159734075)
      ·
        refine ⟨465785096449035239601113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310523397632690159734075 465785096449035239601113)
        ·
          refine ⟨349338822336776429700835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465785096449035239601113 349338822336776429700835)
          ·
            refine ⟨524008233505164644551253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349338822336776429700835 524008233505164644551253)
            ·
              refine ⟨6140721486388648178335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 524008233505164644551253 6140721486388648178335)
              ·
                rfl

theorem cell22_484340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 8].length) (baseStart_484340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484340 prefixEnd_484340 := by exact prefixLift 484340
  have htrace : WordTrace (prefixWord ++ tailWord_484340) baseStart_484340 baseEnd_484340 := by
    simpa [prefixWord, tailWord_484340, baseEnd_484340] using wordTrace_append hprefix tailTrace_484340
  have hstable : (prefixWord ++ tailWord_484340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484340).length < 2 ^ (prefixWord ++ tailWord_484340).sum := by decide
  have hdescent : baseEnd_484340 < baseStart_484340 := by decide
  rcases family_descends (prefixWord ++ tailWord_484340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484409 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_484409 : Nat := 118140960795 + 484409 * 2 ^ 59
def prefixEnd_484409 : Nat := 4983230072969 + 3 ^ 40 * 484409 * 2
def baseEnd_484409 : Nat := 165823100242600320839833

theorem tailTrace_484409 : CollatzResearch.WordTrace tailWord_484409 prefixEnd_484409 165823100242600320839833 := by
  unfold tailWord_484409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667847702076398315800281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11778565134717598877200187 17667847702076398315800281)
  ·
    refine ⟨13250885776557298736850211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17667847702076398315800281 13250885776557298736850211)
    ·
      refine ⟨19876328664835948105275317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13250885776557298736850211 19876328664835948105275317)
      ·
        refine ⟨1863405812328370134869561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19876328664835948105275317 1863405812328370134869561)
        ·
          refine ⟨1397554359246277601152171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863405812328370134869561 1397554359246277601152171)
          ·
            refine ⟨2096331538869416401728257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397554359246277601152171 2096331538869416401728257)
            ·
              refine ⟨1572248654152062301296193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096331538869416401728257 1572248654152062301296193)
              ·
                refine ⟨1179186490614046725972145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572248654152062301296193 1179186490614046725972145)
                ·
                  refine ⟨884389867960535044479109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179186490614046725972145 884389867960535044479109)
                  ·
                    refine ⟨165823100242600320839833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884389867960535044479109 165823100242600320839833)
                    ·
                      rfl

theorem cell22_484409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_484409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484409 prefixEnd_484409 := by exact prefixLift 484409
  have htrace : WordTrace (prefixWord ++ tailWord_484409) baseStart_484409 baseEnd_484409 := by
    simpa [prefixWord, tailWord_484409, baseEnd_484409] using wordTrace_append hprefix tailTrace_484409
  have hstable : (prefixWord ++ tailWord_484409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484409).length < 2 ^ (prefixWord ++ tailWord_484409).sum := by decide
  have hdescent : baseEnd_484409 < baseStart_484409 := by decide
  rcases family_descends (prefixWord ++ tailWord_484409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484413 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 4]
def baseStart_484413 : Nat := 118140960795 + 484413 * 2 ^ 59
def prefixEnd_484413 : Nat := 4983230072969 + 3 ^ 40 * 484413 * 2
def baseEnd_484413 : Nat := 55274823174781881246607

theorem tailTrace_484413 : CollatzResearch.WordTrace tailWord_484413 prefixEnd_484413 55274823174781881246607 := by
  unfold tailWord_484413
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667993594061906998945893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11778662396041271332630595 17667993594061906998945893)
  ·
    refine ⟨3312748798886607562302355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17667993594061906998945893 3312748798886607562302355)
    ·
      refine ⟨4969123198329911343453533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312748798886607562302355 4969123198329911343453533)
      ·
        refine ⟨1863421199373716753795075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4969123198329911343453533 1863421199373716753795075)
        ·
          refine ⟨2795131799060575130692613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863421199373716753795075 2795131799060575130692613)
          ·
            refine ⟨524087212323857837004865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2795131799060575130692613 524087212323857837004865)
            ·
              refine ⟨393065409242893377753649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524087212323857837004865 393065409242893377753649)
              ·
                refine ⟨294799056932170033315237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393065409242893377753649 294799056932170033315237)
                ·
                  refine ⟨55274823174781881246607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294799056932170033315237 55274823174781881246607)
                  ·
                    rfl

theorem cell22_484413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_484413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484413 prefixEnd_484413 := by exact prefixLift 484413
  have htrace : WordTrace (prefixWord ++ tailWord_484413) baseStart_484413 baseEnd_484413 := by
    simpa [prefixWord, tailWord_484413, baseEnd_484413] using wordTrace_append hprefix tailTrace_484413
  have hstable : (prefixWord ++ tailWord_484413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484413).length < 2 ^ (prefixWord ++ tailWord_484413).sum := by decide
  have hdescent : baseEnd_484413 < baseStart_484413 := by decide
  rcases family_descends (prefixWord ++ tailWord_484413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484437 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_484437 : Nat := 118140960795 + 484437 * 2 ^ 59
def prefixEnd_484437 : Nat := 4983230072969 + 3 ^ 40 * 484437 * 2
def baseEnd_484437 : Nat := 165832685214817581139747

theorem tailTrace_484437 : CollatzResearch.WordTrace tailWord_484437 prefixEnd_484437 165832685214817581139747 := by
  unfold tailWord_484437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668868945974959097819565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11779245963983306065213043 17668868945974959097819565)
  ·
    refine ⟨6625825854740609661682337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17668868945974959097819565 6625825854740609661682337)
    ·
      refine ⟨4969369391055457246261753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625825854740609661682337 4969369391055457246261753)
      ·
        refine ⟨3727027043291592934696315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969369391055457246261753 3727027043291592934696315)
        ·
          refine ⟨5590540564937389402044473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727027043291592934696315 5590540564937389402044473)
          ·
            refine ⟨4192905423703042051533355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590540564937389402044473 4192905423703042051533355)
            ·
              refine ⟨6289358135554563077300033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192905423703042051533355 6289358135554563077300033)
              ·
                refine ⟨4717018601665922307975025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6289358135554563077300033 4717018601665922307975025)
                ·
                  refine ⟨3537763951249441730981269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717018601665922307975025 3537763951249441730981269)
                  ·
                    refine ⟨165832685214817581139747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3537763951249441730981269 165832685214817581139747)
                    ·
                      rfl

theorem cell22_484437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_484437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484437 prefixEnd_484437 := by exact prefixLift 484437
  have htrace : WordTrace (prefixWord ++ tailWord_484437) baseStart_484437 baseEnd_484437 := by
    simpa [prefixWord, tailWord_484437, baseEnd_484437] using wordTrace_append hprefix tailTrace_484437
  have hstable : (prefixWord ++ tailWord_484437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484437).length < 2 ^ (prefixWord ++ tailWord_484437).sum := by decide
  have hdescent : baseEnd_484437 < baseStart_484437 := by decide
  rcases family_descends (prefixWord ++ tailWord_484437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484452 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_484452 : Nat := 118140960795 + 484452 * 2 ^ 59
def prefixEnd_484452 : Nat := 4983230072969 + 3 ^ 40 * 484452 * 2
def baseEnd_484452 : Nat := 55279273340454180671567

theorem tailTrace_484452 : CollatzResearch.WordTrace tailWord_484452 prefixEnd_484452 55279273340454180671567 := by
  unfold tailWord_484452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834708020460308329807805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11779610693947077773077073 8834708020460308329807805)
  ·
    refine ⟨3313015507672615623677927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8834708020460308329807805 3313015507672615623677927)
    ·
      refine ⟨4969523261508923435516891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313015507672615623677927 4969523261508923435516891)
      ·
        refine ⟨7454284892263385153275337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969523261508923435516891 7454284892263385153275337)
        ·
          refine ⟨5590713669197538864956503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7454284892263385153275337 5590713669197538864956503)
          ·
            refine ⟨8386070503796308297434755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590713669197538864956503 8386070503796308297434755)
            ·
              refine ⟨12579105755694462446152133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386070503796308297434755 12579105755694462446152133)
              ·
                refine ⟨2358582329192711708653525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12579105755694462446152133 2358582329192711708653525)
                ·
                  refine ⟨55279273340454180671567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2358582329192711708653525 55279273340454180671567)
                  ·
                    rfl

theorem cell22_484452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_484452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484452 prefixEnd_484452 := by exact prefixLift 484452
  have htrace : WordTrace (prefixWord ++ tailWord_484452) baseStart_484452 baseEnd_484452 := by
    simpa [prefixWord, tailWord_484452, baseEnd_484452] using wordTrace_append hprefix tailTrace_484452
  have hstable : (prefixWord ++ tailWord_484452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484452).length < 2 ^ (prefixWord ++ tailWord_484452).sum := by decide
  have hdescent : baseEnd_484452 < baseStart_484452 := by decide
  rcases family_descends (prefixWord ++ tailWord_484452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484484 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_484484 : Nat := 118140960795 + 484484 * 2 ^ 59
def prefixEnd_484484 : Nat := 4983230072969 + 3 ^ 40 * 484484 * 2
def baseEnd_484484 : Nat := 165848774275325125214603

theorem tailTrace_484484 : CollatzResearch.WordTrace tailWord_484484 prefixEnd_484484 165848774275325125214603 := by
  unfold tailWord_484484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835291588402343062390253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11780388784536457416520337 8835291588402343062390253)
  ·
    refine ⟨3313234345650878648396345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8835291588402343062390253 3313234345650878648396345)
    ·
      refine ⟨2484925759238158986297259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3313234345650878648396345 2484925759238158986297259)
      ·
        refine ⟨3727388638857238479445889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484925759238158986297259 3727388638857238479445889)
        ·
          refine ⟨2795541479142928859584417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3727388638857238479445889 2795541479142928859584417)
          ·
            refine ⟨2096656109357196644688313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795541479142928859584417 2096656109357196644688313)
            ·
              refine ⟨1572492082017897483516235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096656109357196644688313 1572492082017897483516235)
              ·
                refine ⟨2358738123026846225274353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572492082017897483516235 2358738123026846225274353)
                ·
                  refine ⟨1769053592270134668955765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358738123026846225274353 1769053592270134668955765)
                  ·
                    refine ⟨165848774275325125214603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1769053592270134668955765 165848774275325125214603)
                    ·
                      rfl

theorem cell22_484484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_484484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484484 prefixEnd_484484 := by exact prefixLift 484484
  have htrace : WordTrace (prefixWord ++ tailWord_484484) baseStart_484484 baseEnd_484484 := by
    simpa [prefixWord, tailWord_484484, baseEnd_484484] using wordTrace_append hprefix tailTrace_484484
  have hstable : (prefixWord ++ tailWord_484484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484484).length < 2 ^ (prefixWord ++ tailWord_484484).sum := by decide
  have hdescent : baseEnd_484484 < baseStart_484484 := by decide
  rcases family_descends (prefixWord ++ tailWord_484484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484499 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 1, 4]
def baseStart_484499 : Nat := 118140960795 + 484499 * 2 ^ 59
def prefixEnd_484499 : Nat := 4983230072969 + 3 ^ 40 * 484499 * 2
def baseEnd_484499 : Nat := 165853909081870086089557

theorem tailTrace_484499 : CollatzResearch.WordTrace tailWord_484499 prefixEnd_484499 165853909081870086089557 := by
  unfold tailWord_484499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671130271750343686576551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11780753514500229124384367 17671130271750343686576551)
  ·
    refine ⟨26506695407625515529864827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17671130271750343686576551 26506695407625515529864827)
    ·
      refine ⟨39760043111438273294797241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26506695407625515529864827 39760043111438273294797241)
      ·
        refine ⟨29820032333578704971097931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39760043111438273294797241 29820032333578704971097931)
        ·
          refine ⟨44730048500368057456646897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29820032333578704971097931 44730048500368057456646897)
          ·
            refine ⟨33547536375276043092485173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44730048500368057456646897 33547536375276043092485173)
            ·
              refine ⟨3145081535182129039920485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33547536375276043092485173 3145081535182129039920485)
              ·
                refine ⟨589702787846649194985091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3145081535182129039920485 589702787846649194985091)
                ·
                  refine ⟨884554181769973792477637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589702787846649194985091 884554181769973792477637)
                  ·
                    refine ⟨165853909081870086089557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884554181769973792477637 165853909081870086089557)
                    ·
                      rfl

theorem cell22_484499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_484499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484499 prefixEnd_484499 := by exact prefixLift 484499
  have htrace : WordTrace (prefixWord ++ tailWord_484499) baseStart_484499 baseEnd_484499 := by
    simpa [prefixWord, tailWord_484499, baseEnd_484499] using wordTrace_append hprefix tailTrace_484499
  have hstable : (prefixWord ++ tailWord_484499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484499).length < 2 ^ (prefixWord ++ tailWord_484499).sum := by decide
  have hdescent : baseEnd_484499 < baseStart_484499 := by decide
  rcases family_descends (prefixWord ++ tailWord_484499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484516 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_484516 : Nat := 118140960795 + 484516 * 2 ^ 59
def prefixEnd_484516 : Nat := 4983230072969 + 3 ^ 40 * 484516 * 2
def baseEnd_484516 : Nat := 165859728529287708414505

theorem tailTrace_484516 : CollatzResearch.WordTrace tailWord_484516 prefixEnd_484516 165859728529287708414505 := by
  unfold tailWord_484516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835875156344377794972701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11781166875125837059963601 8835875156344377794972701)
  ·
    refine ⟨3313453183629141673114763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8835875156344377794972701 3313453183629141673114763)
    ·
      refine ⟨4970179775443712509672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313453183629141673114763 4970179775443712509672145)
      ·
        refine ⟨3727634831582784382254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4970179775443712509672145 3727634831582784382254109)
        ·
          refine ⟨1397863061843544143345291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3727634831582784382254109 1397863061843544143345291)
          ·
            refine ⟨2096794592765316215017937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397863061843544143345291 2096794592765316215017937)
            ·
              refine ⟨1572595944573987161263453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096794592765316215017937 1572595944573987161263453)
              ·
                refine ⟨589723479215245185473795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572595944573987161263453 589723479215245185473795)
                ·
                  refine ⟨884585218822867778210693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589723479215245185473795 884585218822867778210693)
                  ·
                    refine ⟨165859728529287708414505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884585218822867778210693 165859728529287708414505)
                    ·
                      rfl

theorem cell22_484516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_484516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484516 prefixEnd_484516 := by exact prefixLift 484516
  have htrace : WordTrace (prefixWord ++ tailWord_484516) baseStart_484516 baseEnd_484516 := by
    simpa [prefixWord, tailWord_484516, baseEnd_484516] using wordTrace_append hprefix tailTrace_484516
  have hstable : (prefixWord ++ tailWord_484516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484516).length < 2 ^ (prefixWord ++ tailWord_484516).sum := by decide
  have hdescent : baseEnd_484516 < baseStart_484516 := by decide
  rcases family_descends (prefixWord ++ tailWord_484516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484653 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_484653 : Nat := 118140960795 + 484653 * 2 ^ 59
def prefixEnd_484653 : Nat := 4983230072969 + 3 ^ 40 * 484653 * 2
def baseEnd_484653 : Nat := 165906626429065017739085

theorem tailTrace_484653 : CollatzResearch.WordTrace tailWord_484653 prefixEnd_484653 165906626429065017739085 := by
  unfold tailWord_484653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676747113192427987682613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11784498075461618658455075 17676747113192427987682613)
  ·
    refine ⟨1657195041861790123845245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17676747113192427987682613 1657195041861790123845245)
    ·
      refine ⟨621448140698171296441967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1657195041861790123845245 621448140698171296441967)
      ·
        refine ⟨932172211047256944662951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621448140698171296441967 932172211047256944662951)
        ·
          refine ⟨1398258316570885416994427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932172211047256944662951 1398258316570885416994427)
          ·
            refine ⟨2097387474856328125491641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398258316570885416994427 2097387474856328125491641)
            ·
              refine ⟨1573040606142246094118731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097387474856328125491641 1573040606142246094118731)
              ·
                refine ⟨2359560909213369141178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573040606142246094118731 2359560909213369141178097)
                ·
                  refine ⟨1769670681910026855883573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359560909213369141178097 1769670681910026855883573)
                  ·
                    refine ⟨165906626429065017739085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1769670681910026855883573 165906626429065017739085)
                    ·
                      rfl

theorem cell22_484653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_484653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484653 prefixEnd_484653 := by exact prefixLift 484653
  have htrace : WordTrace (prefixWord ++ tailWord_484653) baseStart_484653 baseEnd_484653 := by
    simpa [prefixWord, tailWord_484653, baseEnd_484653] using wordTrace_append hprefix tailTrace_484653
  have hstable : (prefixWord ++ tailWord_484653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484653).length < 2 ^ (prefixWord ++ tailWord_484653).sum := by decide
  have hdescent : baseEnd_484653 < baseStart_484653 := by decide
  rcases family_descends (prefixWord ++ tailWord_484653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484668 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_484668 : Nat := 118140960795 + 484668 * 2 ^ 59
def prefixEnd_484668 : Nat := 4983230072969 + 3 ^ 40 * 484668 * 2
def baseEnd_484668 : Nat := 165911761235609978614039

theorem tailTrace_484668 : CollatzResearch.WordTrace tailWord_484668 prefixEnd_484668 165911761235609978614039 := by
  unfold tailWord_484668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838647104069042774739329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11784862805425390366319105 8838647104069042774739329)
  ·
    refine ⟨6628985328051782081054497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8838647104069042774739329 6628985328051782081054497)
    ·
      refine ⟨4971738996038836560790873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6628985328051782081054497 4971738996038836560790873)
      ·
        refine ⟨3728804247029127420593155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4971738996038836560790873 3728804247029127420593155)
        ·
          refine ⟨5593206370543691130889733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728804247029127420593155 5593206370543691130889733)
          ·
            refine ⟨1048726194476942087041825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5593206370543691130889733 1048726194476942087041825)
            ·
              refine ⟨786544645857706565281369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048726194476942087041825 786544645857706565281369)
              ·
                refine ⟨589908484393279923961027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786544645857706565281369 589908484393279923961027)
                ·
                  refine ⟨884862726589919885941541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589908484393279923961027 884862726589919885941541)
                  ·
                    refine ⟨165911761235609978614039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884862726589919885941541 165911761235609978614039)
                    ·
                      rfl

theorem cell22_484668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_484668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484668 prefixEnd_484668 := by exact prefixLift 484668
  have htrace : WordTrace (prefixWord ++ tailWord_484668) baseStart_484668 baseEnd_484668 := by
    simpa [prefixWord, tailWord_484668, baseEnd_484668] using wordTrace_append hprefix tailTrace_484668
  have hstable : (prefixWord ++ tailWord_484668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484668).length < 2 ^ (prefixWord ++ tailWord_484668).sum := by decide
  have hdescent : baseEnd_484668 < baseStart_484668 := by decide
  rcases family_descends (prefixWord ++ tailWord_484668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484681 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_484681 : Nat := 118140960795 + 484681 * 2 ^ 59
def prefixEnd_484681 : Nat := 4983230072969 + 3 ^ 40 * 484681 * 2
def baseEnd_484681 : Nat := 165916211401282278038999

theorem tailTrace_484681 : CollatzResearch.WordTrace tailWord_484681 prefixEnd_484681 165916211401282278038999 := by
  unfold tailWord_484681
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677768357090988769701897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11785178904727325846467931 17677768357090988769701897)
  ·
    refine ⟨13258326267818241577276423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17677768357090988769701897 13258326267818241577276423)
    ·
      refine ⟨19887489401727362365914635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13258326267818241577276423 19887489401727362365914635)
      ·
        refine ⟨29831234102591043548871953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19887489401727362365914635 29831234102591043548871953)
        ·
          refine ⟨22373425576943282661653965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29831234102591043548871953 22373425576943282661653965)
          ·
            refine ⟨8390034591353730998120237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22373425576943282661653965 8390034591353730998120237)
            ·
              refine ⟨3146262971757649124295089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8390034591353730998120237 3146262971757649124295089)
              ·
                refine ⟨2359697228818236843221317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146262971757649124295089 2359697228818236843221317)
                ·
                  refine ⟨442443230403419408103997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359697228818236843221317 442443230403419408103997)
                  ·
                    refine ⟨165916211401282278038999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442443230403419408103997 165916211401282278038999)
                    ·
                      rfl

theorem cell22_484681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_484681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484681 prefixEnd_484681 := by exact prefixLift 484681
  have htrace : WordTrace (prefixWord ++ tailWord_484681) baseStart_484681 baseEnd_484681 := by
    simpa [prefixWord, tailWord_484681, baseEnd_484681] using wordTrace_append hprefix tailTrace_484681
  have hstable : (prefixWord ++ tailWord_484681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484681).length < 2 ^ (prefixWord ++ tailWord_484681).sum := by decide
  have hdescent : baseEnd_484681 < baseStart_484681 := by decide
  rcases family_descends (prefixWord ++ tailWord_484681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484696 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_484696 : Nat := 118140960795 + 484696 * 2 ^ 59
def prefixEnd_484696 : Nat := 4983230072969 + 3 ^ 40 * 484696 * 2
def baseEnd_484696 : Nat := 165921346207827238913953

theorem tailTrace_484696 : CollatzResearch.WordTrace tailWord_484696 prefixEnd_484696 165921346207827238913953 := by
  unfold tailWord_484696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839157726018323165748971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11785543634691097554331961 8839157726018323165748971)
  ·
    refine ⟨13258736589027484748623457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839157726018323165748971 13258736589027484748623457)
    ·
      refine ⟨9944052441770613561467593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13258736589027484748623457 9944052441770613561467593)
      ·
        refine ⟨7458039331327960171100695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9944052441770613561467593 7458039331327960171100695)
        ·
          refine ⟨11187058996991940256651043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458039331327960171100695 11187058996991940256651043)
          ·
            refine ⟨16780588495487910384976565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187058996991940256651043 16780588495487910384976565)
            ·
              refine ⟨1573180171451991598591553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16780588495487910384976565 1573180171451991598591553)
              ·
                refine ⟨1179885128588993698943665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573180171451991598591553 1179885128588993698943665)
                ·
                  refine ⟨884913846441745274207749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179885128588993698943665 884913846441745274207749)
                  ·
                    refine ⟨165921346207827238913953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884913846441745274207749 165921346207827238913953)
                    ·
                      rfl

theorem cell22_484696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_484696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484696 prefixEnd_484696 := by exact prefixLift 484696
  have htrace : WordTrace (prefixWord ++ tailWord_484696) baseStart_484696 baseEnd_484696 := by
    simpa [prefixWord, tailWord_484696, baseEnd_484696] using wordTrace_append hprefix tailTrace_484696
  have hstable : (prefixWord ++ tailWord_484696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484696).length < 2 ^ (prefixWord ++ tailWord_484696).sum := by decide
  have hdescent : baseEnd_484696 < baseStart_484696 := by decide
  rcases family_descends (prefixWord ++ tailWord_484696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484771 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_484771 : Nat := 118140960795 + 484771 * 2 ^ 59
def prefixEnd_484771 : Nat := 4983230072969 + 3 ^ 40 * 484771 * 2
def baseEnd_484771 : Nat := 165947020240552043288723

theorem tailTrace_484771 : CollatzResearch.WordTrace tailWord_484771 prefixEnd_484771 165947020240552043288723 := by
  unfold tailWord_484771
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681050926764934140478167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11787367284509956093652111 17681050926764934140478167)
  ·
    refine ⟨26521576390147401210717251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17681050926764934140478167 26521576390147401210717251)
    ·
      refine ⟨39782364585221101816075877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26521576390147401210717251 39782364585221101816075877)
      ·
        refine ⟨7459193359728956590514227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39782364585221101816075877 7459193359728956590514227)
        ·
          refine ⟨11188790039593434885771341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459193359728956590514227 11188790039593434885771341)
          ·
            refine ⟨4195796264847538082164253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11188790039593434885771341 4195796264847538082164253)
            ·
              refine ⟨1573423599317826780811595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4195796264847538082164253 1573423599317826780811595)
              ·
                refine ⟨2360135398976740171217393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573423599317826780811595 2360135398976740171217393)
                ·
                  refine ⟨1770101549232555128413045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360135398976740171217393 1770101549232555128413045)
                  ·
                    refine ⟨165947020240552043288723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770101549232555128413045 165947020240552043288723)
                    ·
                      rfl

theorem cell22_484771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_484771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484771 prefixEnd_484771 := by exact prefixLift 484771
  have htrace : WordTrace (prefixWord ++ tailWord_484771) baseStart_484771 baseEnd_484771 := by
    simpa [prefixWord, tailWord_484771, baseEnd_484771] using wordTrace_append hprefix tailTrace_484771
  have hstable : (prefixWord ++ tailWord_484771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484771).length < 2 ^ (prefixWord ++ tailWord_484771).sum := by decide
  have hdescent : baseEnd_484771 < baseStart_484771 := by decide
  rcases family_descends (prefixWord ++ tailWord_484771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484831 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_484831 : Nat := 118140960795 + 484831 * 2 ^ 59
def prefixEnd_484831 : Nat := 4983230072969 + 3 ^ 40 * 484831 * 2
def baseEnd_484831 : Nat := 165967559466731886788539

theorem tailTrace_484831 : CollatzResearch.WordTrace tailWord_484831 prefixEnd_484831 165967559466731886788539 := by
  unfold tailWord_484831
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683239306547564387662347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11788826204365042925108231 17683239306547564387662347)
  ·
    refine ⟨26524858959821346581493521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17683239306547564387662347 26524858959821346581493521)
    ·
      refine ⟨19893644219866009936120141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26524858959821346581493521 19893644219866009936120141)
      ·
        refine ⟨7460116582449753726045053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19893644219866009936120141 7460116582449753726045053)
        ·
          refine ⟨2797543718418657647266895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7460116582449753726045053 2797543718418657647266895)
          ·
            refine ⟨4196315577627986470900343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797543718418657647266895 4196315577627986470900343)
            ·
              refine ⟨6294473366441979706350515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196315577627986470900343 6294473366441979706350515)
              ·
                refine ⟨9441710049662969559525773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294473366441979706350515 9441710049662969559525773)
                ·
                  refine ⟨3540641268623613584822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9441710049662969559525773 3540641268623613584822165)
                  ·
                    refine ⟨165967559466731886788539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3540641268623613584822165 165967559466731886788539)
                    ·
                      rfl

theorem cell22_484831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_484831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484831 prefixEnd_484831 := by exact prefixLift 484831
  have htrace : WordTrace (prefixWord ++ tailWord_484831) baseStart_484831 baseEnd_484831 := by
    simpa [prefixWord, tailWord_484831, baseEnd_484831] using wordTrace_append hprefix tailTrace_484831
  have hstable : (prefixWord ++ tailWord_484831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484831).length < 2 ^ (prefixWord ++ tailWord_484831).sum := by decide
  have hdescent : baseEnd_484831 < baseStart_484831 := by decide
  rcases family_descends (prefixWord ++ tailWord_484831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484833 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_484833 : Nat := 118140960795 + 484833 * 2 ^ 59
def prefixEnd_484833 : Nat := 4983230072969 + 3 ^ 40 * 484833 * 2
def baseEnd_484833 : Nat := 165968244107604548238533

theorem tailTrace_484833 : CollatzResearch.WordTrace tailWord_484833 prefixEnd_484833 165968244107604548238533 := by
  unfold tailWord_484833
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683312252540318729235153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11788874835026879152823435 17683312252540318729235153)
  ·
    refine ⟨13262484189405239046926365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17683312252540318729235153 13262484189405239046926365)
    ·
      refine ⟨4973431571026964642597387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13262484189405239046926365 4973431571026964642597387)
      ·
        refine ⟨7460147356540446963896081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973431571026964642597387 7460147356540446963896081)
        ·
          refine ⟨5595110517405335222922061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460147356540446963896081 5595110517405335222922061)
          ·
            refine ⟨2098166444027000708595773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5595110517405335222922061 2098166444027000708595773)
            ·
              refine ⟨786812416510125265723415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098166444027000708595773 786812416510125265723415)
              ·
                refine ⟨1180218624765187898585123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786812416510125265723415 1180218624765187898585123)
                ·
                  refine ⟨1770327937147781847877685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180218624765187898585123 1770327937147781847877685)
                  ·
                    refine ⟨165968244107604548238533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770327937147781847877685 165968244107604548238533)
                    ·
                      rfl

theorem cell22_484833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_484833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484833 prefixEnd_484833 := by exact prefixLift 484833
  have htrace : WordTrace (prefixWord ++ tailWord_484833) baseStart_484833 baseEnd_484833 := by
    simpa [prefixWord, tailWord_484833, baseEnd_484833] using wordTrace_append hprefix tailTrace_484833
  have hstable : (prefixWord ++ tailWord_484833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484833).length < 2 ^ (prefixWord ++ tailWord_484833).sum := by decide
  have hdescent : baseEnd_484833 < baseStart_484833 := by decide
  rcases family_descends (prefixWord ++ tailWord_484833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484850 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_484850 : Nat := 118140960795 + 484850 * 2 ^ 59
def prefixEnd_484850 : Nat := 4983230072969 + 3 ^ 40 * 484850 * 2
def baseEnd_484850 : Nat := 165974063555022170563481

theorem tailTrace_484850 : CollatzResearch.WordTrace tailWord_484850 prefixEnd_484850 165974063555022170563481 := by
  unfold tailWord_484850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420983073369682658151001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11789288195652487088402669 4420983073369682658151001)
  ·
    refine ⟨3315737305027261993613251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4420983073369682658151001 3315737305027261993613251)
    ·
      refine ⟨4973605957540892990419877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315737305027261993613251 4973605957540892990419877)
      ·
        refine ⟨932551117038917435703727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4973605957540892990419877 932551117038917435703727)
        ·
          refine ⟨1398826675558376153555591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932551117038917435703727 1398826675558376153555591)
          ·
            refine ⟨2098240013337564230333387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398826675558376153555591 2098240013337564230333387)
            ·
              refine ⟨3147360020006346345500081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098240013337564230333387 3147360020006346345500081)
              ·
                refine ⟨2360520015004759759125061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147360020006346345500081 2360520015004759759125061)
                ·
                  refine ⟨442597502813392454835949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360520015004759759125061 442597502813392454835949)
                  ·
                    refine ⟨165974063555022170563481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442597502813392454835949 165974063555022170563481)
                    ·
                      rfl

theorem cell22_484850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_484850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484850 prefixEnd_484850 := by exact prefixLift 484850
  have htrace : WordTrace (prefixWord ++ tailWord_484850) baseStart_484850 baseEnd_484850 := by
    simpa [prefixWord, tailWord_484850, baseEnd_484850] using wordTrace_append hprefix tailTrace_484850
  have hstable : (prefixWord ++ tailWord_484850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484850).length < 2 ^ (prefixWord ++ tailWord_484850).sum := by decide
  have hdescent : baseEnd_484850 < baseStart_484850 := by decide
  rcases family_descends (prefixWord ++ tailWord_484850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484865 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_484865 : Nat := 118140960795 + 484865 * 2 ^ 59
def prefixEnd_484865 : Nat := 4983230072969 + 3 ^ 40 * 484865 * 2
def baseEnd_484865 : Nat := 165979198361567131438435

theorem tailTrace_484865 : CollatzResearch.WordTrace tailWord_484865 prefixEnd_484865 165979198361567131438435 := by
  unfold tailWord_484865
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684479388424388194400049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789652925616258796266699 17684479388424388194400049)
  ·
    refine ⟨13263359541318291145800037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17684479388424388194400049 13263359541318291145800037)
    ·
      refine ⟨2486879913997179589837507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13263359541318291145800037 2486879913997179589837507)
      ·
        refine ⟨3730319870995769384756261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486879913997179589837507 3730319870995769384756261)
        ·
          refine ⟨699434975811706759641799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3730319870995769384756261 699434975811706759641799)
          ·
            refine ⟨1049152463717560139462699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699434975811706759641799 1049152463717560139462699)
            ·
              refine ⟨1573728695576340209194049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049152463717560139462699 1573728695576340209194049)
              ·
                refine ⟨1180296521682255156895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573728695576340209194049 1180296521682255156895537)
                ·
                  refine ⟨885222391261691367671653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180296521682255156895537 885222391261691367671653)
                  ·
                    refine ⟨165979198361567131438435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885222391261691367671653 165979198361567131438435)
                    ·
                      rfl

theorem cell22_484865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_484865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484865 prefixEnd_484865 := by exact prefixLift 484865
  have htrace : WordTrace (prefixWord ++ tailWord_484865) baseStart_484865 baseEnd_484865 := by
    simpa [prefixWord, tailWord_484865, baseEnd_484865] using wordTrace_append hprefix tailTrace_484865
  have hstable : (prefixWord ++ tailWord_484865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484865).length < 2 ^ (prefixWord ++ tailWord_484865).sum := by decide
  have hdescent : baseEnd_484865 < baseStart_484865 := by decide
  rcases family_descends (prefixWord ++ tailWord_484865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484884 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_484884 : Nat := 118140960795 + 484884 * 2 ^ 59
def prefixEnd_484884 : Nat := 4983230072969 + 3 ^ 40 * 484884 * 2
def baseEnd_484884 : Nat := 165985702449857415213377

theorem tailTrace_484884 : CollatzResearch.WordTrace tailWord_484884 prefixEnd_484884 165985702449857415213377 := by
  unfold tailWord_484884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842586187677777219670853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11790114916903702959561137 8842586187677777219670853)
  ·
    refine ⟨1657984910189583228688285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8842586187677777219670853 1657984910189583228688285)
    ·
      refine ⟨621744341321093710758107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1657984910189583228688285 621744341321093710758107)
      ·
        refine ⟨932616511981640566137161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621744341321093710758107 932616511981640566137161)
        ·
          refine ⟨699462383986230424602871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932616511981640566137161 699462383986230424602871)
          ·
            refine ⟨1049193575979345636904307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699462383986230424602871 1049193575979345636904307)
            ·
              refine ⟨1573790363969018455356461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049193575979345636904307 1573790363969018455356461)
              ·
                refine ⟨590171386488381920758673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573790363969018455356461 590171386488381920758673)
                ·
                  refine ⟨442628539866286440569005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590171386488381920758673 442628539866286440569005)
                  ·
                    refine ⟨165985702449857415213377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442628539866286440569005 165985702449857415213377)
                    ·
                      rfl

theorem cell22_484884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_484884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484884 prefixEnd_484884 := by exact prefixLift 484884
  have htrace : WordTrace (prefixWord ++ tailWord_484884) baseStart_484884 baseEnd_484884 := by
    simpa [prefixWord, tailWord_484884, baseEnd_484884] using wordTrace_append hprefix tailTrace_484884
  have hstable : (prefixWord ++ tailWord_484884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484884).length < 2 ^ (prefixWord ++ tailWord_484884).sum := by decide
  have hdescent : baseEnd_484884 < baseStart_484884 := by decide
  rcases family_descends (prefixWord ++ tailWord_484884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484938 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_484938 : Nat := 118140960795 + 484938 * 2 ^ 59
def prefixEnd_484938 : Nat := 4983230072969 + 3 ^ 40 * 484938 * 2
def baseEnd_484938 : Nat := 166004187753419274363211

theorem tailTrace_484938 : CollatzResearch.WordTrace tailWord_484938 prefixEnd_484938 166004187753419274363211 := by
  unfold tailWord_484938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421785479289980415451867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11791427944773281107871645 4421785479289980415451867)
  ·
    refine ⟨6632678218934970623177801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421785479289980415451867 6632678218934970623177801)
    ·
      refine ⟨4974508664201227967383351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6632678218934970623177801 4974508664201227967383351)
      ·
        refine ⟨7461762996301841951075027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974508664201227967383351 7461762996301841951075027)
        ·
          refine ⟨11192644494452762926612541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461762996301841951075027 11192644494452762926612541)
          ·
            refine ⟨4197241685419786097479703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11192644494452762926612541 4197241685419786097479703)
            ·
              refine ⟨6295862528129679146219555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197241685419786097479703 6295862528129679146219555)
              ·
                refine ⟨9443793792194518719329333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295862528129679146219555 9443793792194518719329333)
                ·
                  refine ⟨885355668018236129937125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9443793792194518719329333 885355668018236129937125)
                  ·
                    refine ⟨166004187753419274363211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885355668018236129937125 166004187753419274363211)
                    ·
                      rfl

theorem cell22_484938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_484938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484938 prefixEnd_484938 := by exact prefixLift 484938
  have htrace : WordTrace (prefixWord ++ tailWord_484938) baseStart_484938 baseEnd_484938 := by
    simpa [prefixWord, tailWord_484938, baseEnd_484938] using wordTrace_append hprefix tailTrace_484938
  have hstable : (prefixWord ++ tailWord_484938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484938).length < 2 ^ (prefixWord ++ tailWord_484938).sum := by decide
  have hdescent : baseEnd_484938 < baseStart_484938 := by decide
  rcases family_descends (prefixWord ++ tailWord_484938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484983 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_484983 : Nat := 118140960795 + 484983 * 2 ^ 59
def prefixEnd_484983 : Nat := 4983230072969 + 3 ^ 40 * 484983 * 2
def baseEnd_484983 : Nat := 166019592173054156988073

theorem tailTrace_484983 : CollatzResearch.WordTrace tailWord_484983 prefixEnd_484983 166019592173054156988073 := by
  unfold tailWord_484983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688783201996894347195603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11792522134664596231463735 17688783201996894347195603)
  ·
    refine ⟨26533174802995341520793405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17688783201996894347195603 26533174802995341520793405)
    ·
      refine ⟨9949940551123253070297527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26533174802995341520793405 9949940551123253070297527)
      ·
        refine ⟨14924910826684879605446291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9949940551123253070297527 14924910826684879605446291)
        ·
          refine ⟨22387366240027319408169437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924910826684879605446291 22387366240027319408169437)
          ·
            refine ⟨8395262340010244778063539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22387366240027319408169437 8395262340010244778063539)
            ·
              refine ⟨12592893510015367167095309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395262340010244778063539 12592893510015367167095309)
              ·
                refine ⟨4722335066255762687660741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12592893510015367167095309 4722335066255762687660741)
                ·
                  refine ⟨885437824922955503936389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4722335066255762687660741 885437824922955503936389)
                  ·
                    refine ⟨166019592173054156988073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885437824922955503936389 166019592173054156988073)
                    ·
                      rfl

theorem cell22_484983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_484983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484983 prefixEnd_484983 := by exact prefixLift 484983
  have htrace : WordTrace (prefixWord ++ tailWord_484983) baseStart_484983 baseEnd_484983 := by
    simpa [prefixWord, tailWord_484983, baseEnd_484983] using wordTrace_append hprefix tailTrace_484983
  have hstable : (prefixWord ++ tailWord_484983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484983).length < 2 ^ (prefixWord ++ tailWord_484983).sum := by decide
  have hdescent : baseEnd_484983 < baseStart_484983 := by decide
  rcases family_descends (prefixWord ++ tailWord_484983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484985 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_484985 : Nat := 118140960795 + 484985 * 2 ^ 59
def prefixEnd_484985 : Nat := 4983230072969 + 3 ^ 40 * 484985 * 2
def baseEnd_484985 : Nat := 166020276813926818438067

theorem tailTrace_484985 : CollatzResearch.WordTrace tailWord_484985 prefixEnd_484985 166020276813926818438067 := by
  unfold tailWord_484985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688856147989648688768409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11792570765326432459178939 17688856147989648688768409)
  ·
    refine ⟨13266642110992236516576307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17688856147989648688768409 13266642110992236516576307)
    ·
      refine ⟨19899963166488354774864461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13266642110992236516576307 19899963166488354774864461)
      ·
        refine ⟨7462486187433133040574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19899963166488354774864461 7462486187433133040574173)
        ·
          refine ⟨2798432320287424890215315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7462486187433133040574173 2798432320287424890215315)
          ·
            refine ⟨4197648480431137335322973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798432320287424890215315 4197648480431137335322973)
            ·
              refine ⟨1574118180161676500746115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4197648480431137335322973 1574118180161676500746115)
              ·
                refine ⟨2361177270242514751119173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574118180161676500746115 2361177270242514751119173)
                ·
                  refine ⟨442720738170471515834845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361177270242514751119173 442720738170471515834845)
                  ·
                    refine ⟨166020276813926818438067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442720738170471515834845 166020276813926818438067)
                    ·
                      rfl

theorem cell22_484985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_484985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_484985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_484985 prefixEnd_484985 := by exact prefixLift 484985
  have htrace : WordTrace (prefixWord ++ tailWord_484985) baseStart_484985 baseEnd_484985 := by
    simpa [prefixWord, tailWord_484985, baseEnd_484985] using wordTrace_append hprefix tailTrace_484985
  have hstable : (prefixWord ++ tailWord_484985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484985).length < 2 ^ (prefixWord ++ tailWord_484985).sum := by decide
  have hdescent : baseEnd_484985 < baseStart_484985 := by decide
  rcases family_descends (prefixWord ++ tailWord_484985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485002 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_485002 : Nat := 118140960795 + 485002 * 2 ^ 59
def prefixEnd_485002 : Nat := 4983230072969 + 3 ^ 40 * 485002 * 2
def baseEnd_485002 : Nat := 166026096261344440763015

theorem tailTrace_485002 : CollatzResearch.WordTrace tailWord_485002 prefixEnd_485002 166026096261344440763015 := by
  unfold tailWord_485002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422369047232015148034315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11792984125952040394758173 4422369047232015148034315)
  ·
    refine ⟨6633553570848022722051473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422369047232015148034315 6633553570848022722051473)
    ·
      refine ⟨4975165178136017041538605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633553570848022722051473 4975165178136017041538605)
      ·
        refine ⟨1865686941801006390576977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4975165178136017041538605 1865686941801006390576977)
        ·
          refine ⟨1399265206350754792932733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865686941801006390576977 1399265206350754792932733)
          ·
            refine ⟨524724452381533047349775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1399265206350754792932733 524724452381533047349775)
            ·
              refine ⟨787086678572299571024663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524724452381533047349775 787086678572299571024663)
              ·
                refine ⟨1180630017858449356536995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787086678572299571024663 1180630017858449356536995)
                ·
                  refine ⟨1770945026787674034805493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180630017858449356536995 1770945026787674034805493)
                  ·
                    refine ⟨166026096261344440763015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770945026787674034805493 166026096261344440763015)
                    ·
                      rfl

theorem cell22_485002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_485002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485002 prefixEnd_485002 := by exact prefixLift 485002
  have htrace : WordTrace (prefixWord ++ tailWord_485002) baseStart_485002 baseEnd_485002 := by
    simpa [prefixWord, tailWord_485002, baseEnd_485002] using wordTrace_append hprefix tailTrace_485002
  have hstable : (prefixWord ++ tailWord_485002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485002).length < 2 ^ (prefixWord ++ tailWord_485002).sum := by decide
  have hdescent : baseEnd_485002 < baseStart_485002 := by decide
  rcases family_descends (prefixWord ++ tailWord_485002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485015 : List Nat := [1, 1, 3, 3, 2, 2, 4, 6]
def baseStart_485015 : Nat := 118140960795 + 485015 * 2 ^ 59
def prefixEnd_485015 : Nat := 4983230072969 + 3 ^ 40 * 485015 * 2
def baseEnd_485015 : Nat := 18447838491890748909775

theorem tailTrace_485015 : CollatzResearch.WordTrace tailWord_485015 prefixEnd_485015 18447838491890748909775 := by
  unfold tailWord_485015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689950337880963812360499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11793300225253975874906999 17689950337880963812360499)
  ·
    refine ⟨26534925506821445718540749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17689950337880963812360499 26534925506821445718540749)
    ·
      refine ⟨9950597065058042144452781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26534925506821445718540749 9950597065058042144452781)
      ·
        refine ⟨3731473899396765804169793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9950597065058042144452781 3731473899396765804169793)
        ·
          refine ⟨2798605424547574353127345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731473899396765804169793 2798605424547574353127345)
          ·
            refine ⟨2098954068410680764845509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798605424547574353127345 2098954068410680764845509)
            ·
              refine ⟨393553887827002643408533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2098954068410680764845509 393553887827002643408533)
              ·
                refine ⟨18447838491890748909775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 393553887827002643408533 18447838491890748909775)
                ·
                  rfl

theorem cell22_485015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 6].length) (baseStart_485015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485015 prefixEnd_485015 := by exact prefixLift 485015
  have htrace : WordTrace (prefixWord ++ tailWord_485015) baseStart_485015 baseEnd_485015 := by
    simpa [prefixWord, tailWord_485015, baseEnd_485015] using wordTrace_append hprefix tailTrace_485015
  have hstable : (prefixWord ++ tailWord_485015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485015).length < 2 ^ (prefixWord ++ tailWord_485015).sum := by decide
  have hdescent : baseEnd_485015 < baseStart_485015 := by decide
  rcases family_descends (prefixWord ++ tailWord_485015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485043 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 7]
def baseStart_485043 : Nat := 118140960795 + 485043 * 2 ^ 59
def prefixEnd_485043 : Nat := 4983230072969 + 3 ^ 40 * 485043 * 2
def baseEnd_485043 : Nat := 55346710466411333495963

theorem tailTrace_485043 : CollatzResearch.WordTrace tailWord_485043 prefixEnd_485043 55346710466411333495963 := by
  unfold tailWord_485043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690971581779524594379783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11793981054519683062919855 17690971581779524594379783)
  ·
    refine ⟨26536457372669286891569675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17690971581779524594379783 26536457372669286891569675)
    ·
      refine ⟨39804686059003930337354513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26536457372669286891569675 39804686059003930337354513)
      ·
        refine ⟨29853514544252947753015885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39804686059003930337354513 29853514544252947753015885)
        ·
          refine ⟨11195067954094855407380957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29853514544252947753015885 11195067954094855407380957)
          ·
            refine ⟨4198150482785570777767859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11195067954094855407380957 4198150482785570777767859)
            ·
              refine ⟨6297225724178356166651789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198150482785570777767859 6297225724178356166651789)
              ·
                refine ⟨2361459646566883562494421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6297225724178356166651789 2361459646566883562494421)
                ·
                  refine ⟨55346710466411333495963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2361459646566883562494421 55346710466411333495963)
                  ·
                    rfl

theorem cell22_485043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_485043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485043 prefixEnd_485043 := by exact prefixLift 485043
  have htrace : WordTrace (prefixWord ++ tailWord_485043) baseStart_485043 baseEnd_485043 := by
    simpa [prefixWord, tailWord_485043, baseEnd_485043] using wordTrace_append hprefix tailTrace_485043
  have hstable : (prefixWord ++ tailWord_485043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485043).length < 2 ^ (prefixWord ++ tailWord_485043).sum := by decide
  have hdescent : baseEnd_485043 < baseStart_485043 := by decide
  rcases family_descends (prefixWord ++ tailWord_485043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485047 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 3, 3]
def baseStart_485047 : Nat := 118140960795 + 485047 * 2 ^ 59
def prefixEnd_485047 : Nat := 4983230072969 + 3 ^ 40 * 485047 * 2
def baseEnd_485047 : Nat := 166041500680979323387877

theorem tailTrace_485047 : CollatzResearch.WordTrace tailWord_485047 prefixEnd_485047 166041500680979323387877 := by
  unfold tailWord_485047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691117473765033277525395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11794078315843355518350263 17691117473765033277525395)
  ·
    refine ⟨26536676210647549916288093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17691117473765033277525395 26536676210647549916288093)
    ·
      refine ⟨9951253578992831218608035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26536676210647549916288093 9951253578992831218608035)
      ·
        refine ⟨14926880368489246827912053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951253578992831218608035 14926880368489246827912053)
        ·
          refine ⟨1399395034545866890116755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14926880368489246827912053 1399395034545866890116755)
          ·
            refine ⟨2099092551818800335175133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399395034545866890116755 2099092551818800335175133)
            ·
              refine ⟨787159706932050125690675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099092551818800335175133 787159706932050125690675)
              ·
                refine ⟨1180739560398075188536013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787159706932050125690675 1180739560398075188536013)
                ·
                  refine ⟨442777335149278195701005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180739560398075188536013 442777335149278195701005)
                  ·
                    refine ⟨166041500680979323387877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442777335149278195701005 166041500680979323387877)
                    ·
                      rfl

theorem cell22_485047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_485047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485047 prefixEnd_485047 := by exact prefixLift 485047
  have htrace : WordTrace (prefixWord ++ tailWord_485047) baseStart_485047 baseEnd_485047 := by
    simpa [prefixWord, tailWord_485047, baseEnd_485047] using wordTrace_append hprefix tailTrace_485047
  have hstable : (prefixWord ++ tailWord_485047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485047).length < 2 ^ (prefixWord ++ tailWord_485047).sum := by decide
  have hdescent : baseEnd_485047 < baseStart_485047 := by decide
  rcases family_descends (prefixWord ++ tailWord_485047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485122 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_485122 : Nat := 118140960795 + 485122 * 2 ^ 59
def prefixEnd_485122 : Nat := 4983230072969 + 3 ^ 40 * 485122 * 2
def baseEnd_485122 : Nat := 55355724904568042587549

theorem tailTrace_485122 : CollatzResearch.WordTrace tailWord_485122 prefixEnd_485122 55355724904568042587549 := by
  unfold tailWord_485122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423463237123330271626405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11795901965662214057670413 4423463237123330271626405)
  ·
    refine ⟨829399356960624425929951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4423463237123330271626405 829399356960624425929951)
    ·
      refine ⟨1244099035440936638894927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829399356960624425929951 1244099035440936638894927)
      ·
        refine ⟨1866148553161404958342391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244099035440936638894927 1866148553161404958342391)
        ·
          refine ⟨2799222829742107437513587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866148553161404958342391 2799222829742107437513587)
          ·
            refine ⟨4198834244613161156270381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799222829742107437513587 4198834244613161156270381)
            ·
              refine ⟨1574562841729935433601393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198834244613161156270381 1574562841729935433601393)
              ·
                refine ⟨1180922131297451575201045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574562841729935433601393 1180922131297451575201045)
                ·
                  refine ⟨55355724904568042587549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1180922131297451575201045 55355724904568042587549)
                  ·
                    rfl

theorem cell22_485122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_485122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485122 prefixEnd_485122 := by exact prefixLift 485122
  have htrace : WordTrace (prefixWord ++ tailWord_485122) baseStart_485122 baseEnd_485122 := by
    simpa [prefixWord, tailWord_485122, baseEnd_485122] using wordTrace_append hprefix tailTrace_485122
  have hstable : (prefixWord ++ tailWord_485122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485122).length < 2 ^ (prefixWord ++ tailWord_485122).sum := by decide
  have hdescent : baseEnd_485122 < baseStart_485122 := by decide
  rcases family_descends (prefixWord ++ tailWord_485122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485135 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_485135 : Nat := 118140960795 + 485135 * 2 ^ 59
def prefixEnd_485135 : Nat := 4983230072969 + 3 ^ 40 * 485135 * 2
def baseEnd_485135 : Nat := 166071624879376427187607

theorem tailTrace_485135 : CollatzResearch.WordTrace tailWord_485135 prefixEnd_485135 166071624879376427187607 := by
  unfold tailWord_485135
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694327097446224306728859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796218064964149537819239 17694327097446224306728859)
  ·
    refine ⟨26541490646169336460093289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694327097446224306728859 26541490646169336460093289)
    ·
      refine ⟨19906117984627002345069967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26541490646169336460093289 19906117984627002345069967)
      ·
        refine ⟨29859176976940503517604951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19906117984627002345069967 29859176976940503517604951)
        ·
          refine ⟨44788765465410755276407427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29859176976940503517604951 44788765465410755276407427)
          ·
            refine ⟨67183148198116132914611141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44788765465410755276407427 67183148198116132914611141)
            ·
              refine ⟨12596840287146774921489589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67183148198116132914611141 12596840287146774921489589)
              ·
                refine ⟨1180953776920010148889649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12596840287146774921489589 1180953776920010148889649)
                ·
                  refine ⟨885715332690007611667237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180953776920010148889649 885715332690007611667237)
                  ·
                    refine ⟨166071624879376427187607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885715332690007611667237 166071624879376427187607)
                    ·
                      rfl

theorem cell22_485135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_485135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485135 prefixEnd_485135 := by exact prefixLift 485135
  have htrace : WordTrace (prefixWord ++ tailWord_485135) baseStart_485135 baseEnd_485135 := by
    simpa [prefixWord, tailWord_485135, baseEnd_485135] using wordTrace_append hprefix tailTrace_485135
  have hstable : (prefixWord ++ tailWord_485135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485135).length < 2 ^ (prefixWord ++ tailWord_485135).sum := by decide
  have hdescent : baseEnd_485135 < baseStart_485135 := by decide
  rcases family_descends (prefixWord ++ tailWord_485135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485171 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 2, 3]
def baseStart_485171 : Nat := 118140960795 + 485171 * 2 ^ 59
def prefixEnd_485171 : Nat := 4983230072969 + 3 ^ 40 * 485171 * 2
def baseEnd_485171 : Nat := 166083948415084333287497

theorem tailTrace_485171 : CollatzResearch.WordTrace tailWord_485171 prefixEnd_485171 166083948415084333287497 := by
  unfold tailWord_485171
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695640125315802455039367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11797093416877201636692911 17695640125315802455039367)
  ·
    refine ⟨26543460187973703682559051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695640125315802455039367 26543460187973703682559051)
    ·
      refine ⟨39815190281960555523838577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26543460187973703682559051 39815190281960555523838577)
      ·
        refine ⟨29861392711470416642878933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39815190281960555523838577 29861392711470416642878933)
        ·
          refine ⟨699876391675087890067475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29861392711470416642878933 699876391675087890067475)
          ·
            refine ⟨1049814587512631835101213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699876391675087890067475 1049814587512631835101213)
            ·
              refine ⟨393680470317236938162955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1049814587512631835101213 393680470317236938162955)
              ·
                refine ⟨590520705475855407244433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393680470317236938162955 590520705475855407244433)
                ·
                  refine ⟨442890529106891555433325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590520705475855407244433 442890529106891555433325)
                  ·
                    refine ⟨166083948415084333287497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442890529106891555433325 166083948415084333287497)
                    ·
                      rfl

theorem cell22_485171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 3].length) (baseStart_485171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485171 prefixEnd_485171 := by exact prefixLift 485171
  have htrace : WordTrace (prefixWord ++ tailWord_485171) baseStart_485171 baseEnd_485171 := by
    simpa [prefixWord, tailWord_485171, baseEnd_485171] using wordTrace_append hprefix tailTrace_485171
  have hstable : (prefixWord ++ tailWord_485171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485171).length < 2 ^ (prefixWord ++ tailWord_485171).sum := by decide
  have hdescent : baseEnd_485171 < baseStart_485171 := by decide
  rcases family_descends (prefixWord ++ tailWord_485171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485180 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_485180 : Nat := 118140960795 + 485180 * 2 ^ 59
def prefixEnd_485180 : Nat := 4983230072969 + 3 ^ 40 * 485180 * 2
def baseEnd_485180 : Nat := 166087029299011309812469

theorem tailTrace_485180 : CollatzResearch.WordTrace tailWord_485180 prefixEnd_485180 166087029299011309812469 := by
  unfold tailWord_485180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847984191141598496058497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11797312254855464661411329 8847984191141598496058497)
  ·
    refine ⟨6635988143356198872043873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8847984191141598496058497 6635988143356198872043873)
    ·
      refine ⟨4976991107517149154032905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635988143356198872043873 4976991107517149154032905)
      ·
        refine ⟨3732743330637861865524679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4976991107517149154032905 3732743330637861865524679)
        ·
          refine ⟨5599114995956792798287019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732743330637861865524679 5599114995956792798287019)
          ·
            refine ⟨8398672493935189197430529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599114995956792798287019 8398672493935189197430529)
            ·
              refine ⟨6299004370451391898072897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398672493935189197430529 6299004370451391898072897)
              ·
                refine ⟨4724253277838543923554673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299004370451391898072897 4724253277838543923554673)
                ·
                  refine ⟨3543189958378907942666005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724253277838543923554673 3543189958378907942666005)
                  ·
                    refine ⟨166087029299011309812469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3543189958378907942666005 166087029299011309812469)
                    ·
                      rfl

theorem cell22_485180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_485180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485180 prefixEnd_485180 := by exact prefixLift 485180
  have htrace : WordTrace (prefixWord ++ tailWord_485180) baseStart_485180 baseEnd_485180 := by
    simpa [prefixWord, tailWord_485180, baseEnd_485180] using wordTrace_append hprefix tailTrace_485180
  have hstable : (prefixWord ++ tailWord_485180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485180).length < 2 ^ (prefixWord ++ tailWord_485180).sum := by decide
  have hdescent : baseEnd_485180 < baseStart_485180 := by decide
  rcases family_descends (prefixWord ++ tailWord_485180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485229 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 5]
def baseStart_485229 : Nat := 118140960795 + 485229 * 2 ^ 59
def prefixEnd_485229 : Nat := 4983230072969 + 3 ^ 40 * 485229 * 2
def baseEnd_485229 : Nat := 55367934333463838445773

theorem tailTrace_485229 : CollatzResearch.WordTrace tailWord_485229 prefixEnd_485229 55367934333463838445773 := by
  unfold tailWord_485229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697755559105678360650741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11798503706070452240433827 17697755559105678360650741)
  ·
    refine ⟨1659164583666157346311007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17697755559105678360650741 1659164583666157346311007)
    ·
      refine ⟨2488746875499236019466511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659164583666157346311007 2488746875499236019466511)
      ·
        refine ⟨3733120313248854029199767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488746875499236019466511 3733120313248854029199767)
        ·
          refine ⟨5599680469873281043799651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733120313248854029199767 5599680469873281043799651)
          ·
            refine ⟨8399520704809921565699477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599680469873281043799651 8399520704809921565699477)
            ·
              refine ⟨393727533037965073392163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8399520704809921565699477 393727533037965073392163)
              ·
                refine ⟨590591299556947610088245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393727533037965073392163 590591299556947610088245)
                ·
                  refine ⟨55367934333463838445773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590591299556947610088245 55367934333463838445773)
                  ·
                    rfl

theorem cell22_485229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_485229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485229 prefixEnd_485229 := by exact prefixLift 485229
  have htrace : WordTrace (prefixWord ++ tailWord_485229) baseStart_485229 baseEnd_485229 := by
    simpa [prefixWord, tailWord_485229, baseEnd_485229] using wordTrace_append hprefix tailTrace_485229
  have hstable : (prefixWord ++ tailWord_485229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485229).length < 2 ^ (prefixWord ++ tailWord_485229).sum := by decide
  have hdescent : baseEnd_485229 < baseStart_485229 := by decide
  rcases family_descends (prefixWord ++ tailWord_485229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485308 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_485308 : Nat := 118140960795 + 485308 * 2 ^ 59
def prefixEnd_485308 : Nat := 4983230072969 + 3 ^ 40 * 485308 * 2
def baseEnd_485308 : Nat := 55376948771620547537359

theorem tailTrace_485308 : CollatzResearch.WordTrace tailWord_485308 prefixEnd_485308 55376948771620547537359 := by
  unfold tailWord_485308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850318462909737426388289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11800424617212983235184385 8850318462909737426388289)
  ·
    refine ⟨6637738847182303069791217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850318462909737426388289 6637738847182303069791217)
    ·
      refine ⟨4978304135386727302343413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637738847182303069791217 4978304135386727302343413)
      ·
        refine ⟨466716012692505684594695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4978304135386727302343413 466716012692505684594695)
        ·
          refine ⟨700074019038758526892043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466716012692505684594695 700074019038758526892043)
          ·
            refine ⟨1050111028558137790338065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700074019038758526892043 1050111028558137790338065)
            ·
              refine ⟨787583271418603342753549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050111028558137790338065 787583271418603342753549)
              ·
                refine ⟨295343726781976253532581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787583271418603342753549 295343726781976253532581)
                ·
                  refine ⟨55376948771620547537359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295343726781976253532581 55376948771620547537359)
                  ·
                    rfl

theorem cell22_485308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_485308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485308 prefixEnd_485308 := by exact prefixLift 485308
  have htrace : WordTrace (prefixWord ++ tailWord_485308) baseStart_485308 baseEnd_485308 := by
    simpa [prefixWord, tailWord_485308, baseEnd_485308] using wordTrace_append hprefix tailTrace_485308
  have hstable : (prefixWord ++ tailWord_485308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485308).length < 2 ^ (prefixWord ++ tailWord_485308).sum := by decide
  have hdescent : baseEnd_485308 < baseStart_485308 := by decide
  rcases family_descends (prefixWord ++ tailWord_485308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485340 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_485340 : Nat := 118140960795 + 485340 * 2 ^ 59
def prefixEnd_485340 : Nat := 4983230072969 + 3 ^ 40 * 485340 * 2
def baseEnd_485340 : Nat := 166141800568824225811979

theorem tailTrace_485340 : CollatzResearch.WordTrace tailWord_485340 prefixEnd_485340 166141800568824225811979 := by
  unfold tailWord_485340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850902030851772158970737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11801202707802362878627649 8850902030851772158970737)
  ·
    refine ⟨6638176523138829119228053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850902030851772158970737 6638176523138829119228053)
    ·
      refine ⟨311164524522132614963815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6638176523138829119228053 311164524522132614963815)
      ·
        refine ⟨466746786783198922445723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311164524522132614963815 466746786783198922445723)
        ·
          refine ⟨700120180174798383668585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466746786783198922445723 700120180174798383668585)
          ·
            refine ⟨525090135131098787751439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700120180174798383668585 525090135131098787751439)
            ·
              refine ⟨787635202696648181627159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525090135131098787751439 787635202696648181627159)
              ·
                refine ⟨1181452804044972272440739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787635202696648181627159 1181452804044972272440739)
                ·
                  refine ⟨1772179206067458408661109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181452804044972272440739 1772179206067458408661109)
                  ·
                    refine ⟨166141800568824225811979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1772179206067458408661109 166141800568824225811979)
                    ·
                      rfl

theorem cell22_485340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_485340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485340 prefixEnd_485340 := by exact prefixLift 485340
  have htrace : WordTrace (prefixWord ++ tailWord_485340) baseStart_485340 baseEnd_485340 := by
    simpa [prefixWord, tailWord_485340, baseEnd_485340] using wordTrace_append hprefix tailTrace_485340
  have hstable : (prefixWord ++ tailWord_485340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485340).length < 2 ^ (prefixWord ++ tailWord_485340).sum := by decide
  have hdescent : baseEnd_485340 < baseStart_485340 := by decide
  rcases family_descends (prefixWord ++ tailWord_485340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485424 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_485424 : Nat := 118140960795 + 485424 * 2 ^ 59
def prefixEnd_485424 : Nat := 4983230072969 + 3 ^ 40 * 485424 * 2
def baseEnd_485424 : Nat := 166170555485476006711721

theorem tailTrace_485424 : CollatzResearch.WordTrace tailWord_485424 prefixEnd_485424 166170555485476006711721 := by
  unfold tailWord_485424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852433896699613331999663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11803245195599484442666217 8852433896699613331999663)
  ·
    refine ⟨13278650845049419997999495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8852433896699613331999663 13278650845049419997999495)
    ·
      refine ⟨19917976267574129996999243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13278650845049419997999495 19917976267574129996999243)
      ·
        refine ⟨29876964401361194995498865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19917976267574129996999243 29876964401361194995498865)
        ·
          refine ⟨22407723301020896246624149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29876964401361194995498865 22407723301020896246624149)
          ·
            refine ⟨1050362029735354511560507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22407723301020896246624149 1050362029735354511560507)
            ·
              refine ⟨1575543044603031767340761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050362029735354511560507 1575543044603031767340761)
              ·
                refine ⟨1181657283452273825505571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575543044603031767340761 1181657283452273825505571)
                ·
                  refine ⟨1772485925178410738258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181657283452273825505571 1772485925178410738258357)
                  ·
                    refine ⟨166170555485476006711721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1772485925178410738258357 166170555485476006711721)
                    ·
                      rfl

theorem cell22_485424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_485424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485424 prefixEnd_485424 := by exact prefixLift 485424
  have htrace : WordTrace (prefixWord ++ tailWord_485424) baseStart_485424 baseEnd_485424 := by
    simpa [prefixWord, tailWord_485424, baseEnd_485424] using wordTrace_append hprefix tailTrace_485424
  have hstable : (prefixWord ++ tailWord_485424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485424).length < 2 ^ (prefixWord ++ tailWord_485424).sum := by decide
  have hdescent : baseEnd_485424 < baseStart_485424 := by decide
  rcases family_descends (prefixWord ++ tailWord_485424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485439 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_485439 : Nat := 118140960795 + 485439 * 2 ^ 59
def prefixEnd_485439 : Nat := 4983230072969 + 3 ^ 40 * 485439 * 2
def baseEnd_485439 : Nat := 166175690292020967586675

theorem tailTrace_485439 : CollatzResearch.WordTrace tailWord_485439 prefixEnd_485439 166175690292020967586675 := by
  unfold tailWord_485439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705414888344884225795371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11803609925563256150530247 17705414888344884225795371)
  ·
    refine ⟨26558122332517326338693057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17705414888344884225795371 26558122332517326338693057)
    ·
      refine ⟨19918591749387994754019793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26558122332517326338693057 19918591749387994754019793)
      ·
        refine ⟨14938943812040996065514845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19918591749387994754019793 14938943812040996065514845)
        ·
          refine ⟨5602103929515373524568067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14938943812040996065514845 5602103929515373524568067)
          ·
            refine ⟨8403155894273060286852101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602103929515373524568067 8403155894273060286852101)
            ·
              refine ⟨1575591730176198803784769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8403155894273060286852101 1575591730176198803784769)
              ·
                refine ⟨1181693797632149102838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575591730176198803784769 1181693797632149102838577)
                ·
                  refine ⟨886270348224111827128933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181693797632149102838577 886270348224111827128933)
                  ·
                    refine ⟨166175690292020967586675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 886270348224111827128933 166175690292020967586675)
                    ·
                      rfl

theorem cell22_485439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_485439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485439 prefixEnd_485439 := by exact prefixLift 485439
  have htrace : WordTrace (prefixWord ++ tailWord_485439) baseStart_485439 baseEnd_485439 := by
    simpa [prefixWord, tailWord_485439, baseEnd_485439] using wordTrace_append hprefix tailTrace_485439
  have hstable : (prefixWord ++ tailWord_485439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485439).length < 2 ^ (prefixWord ++ tailWord_485439).sum := by decide
  have hdescent : baseEnd_485439 < baseStart_485439 := by decide
  rcases family_descends (prefixWord ++ tailWord_485439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485454 : List Nat := [4, 1, 1, 1, 1, 4, 3, 7]
def baseStart_485454 : Nat := 118140960795 + 485454 * 2 ^ 59
def prefixEnd_485454 : Nat := 4983230072969 + 3 ^ 40 * 485454 * 2
def baseEnd_485454 : Nat := 18464536122062880940181

theorem tailTrace_485454 : CollatzResearch.WordTrace tailWord_485454 prefixEnd_485454 18464536122062880940181 := by
  unfold tailWord_485454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213245247911317723448927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11803974655527027858394277 2213245247911317723448927)
  ·
    refine ⟨3319867871866976585173391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213245247911317723448927 3319867871866976585173391)
    ·
      refine ⟨4979801807800464877760087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319867871866976585173391 4979801807800464877760087)
      ·
        refine ⟨7469702711700697316640131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979801807800464877760087 7469702711700697316640131)
        ·
          refine ⟨11204554067551045974960197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469702711700697316640131 11204554067551045974960197)
          ·
            refine ⟨2100853887665821120305037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11204554067551045974960197 2100853887665821120305037)
            ·
              refine ⟨787820207874682920114389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2100853887665821120305037 787820207874682920114389)
              ·
                refine ⟨18464536122062880940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 787820207874682920114389 18464536122062880940181)
                ·
                  rfl

theorem cell22_485454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_485454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485454 prefixEnd_485454 := by exact prefixLift 485454
  have htrace : WordTrace (prefixWord ++ tailWord_485454) baseStart_485454 baseEnd_485454 := by
    simpa [prefixWord, tailWord_485454, baseEnd_485454] using wordTrace_append hprefix tailTrace_485454
  have hstable : (prefixWord ++ tailWord_485454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485454).length < 2 ^ (prefixWord ++ tailWord_485454).sum := by decide
  have hdescent : baseEnd_485454 < baseStart_485454 := by decide
  rcases family_descends (prefixWord ++ tailWord_485454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485486 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_485486 : Nat := 118140960795 + 485486 * 2 ^ 59
def prefixEnd_485486 : Nat := 4983230072969 + 3 ^ 40 * 485486 * 2
def baseEnd_485486 : Nat := 166191779352528511661531

theorem tailTrace_485486 : CollatzResearch.WordTrace tailWord_485486 prefixEnd_485486 166191779352528511661531 := by
  unfold tailWord_485486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213391139896826406594539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11804752746116407501837541 2213391139896826406594539)
  ·
    refine ⟨3320086709845239609891809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213391139896826406594539 3320086709845239609891809)
    ·
      refine ⟨2490065032383929707418857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3320086709845239609891809 2490065032383929707418857)
      ·
        refine ⟨1867548774287947280564143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490065032383929707418857 1867548774287947280564143)
        ·
          refine ⟨2801323161431920920846215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867548774287947280564143 2801323161431920920846215)
          ·
            refine ⟨4201984742147881381269323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801323161431920920846215 4201984742147881381269323)
            ·
              refine ⟨6302977113221822071903985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201984742147881381269323 6302977113221822071903985)
              ·
                refine ⟨4727232834916366553927989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302977113221822071903985 4727232834916366553927989)
                ·
                  refine ⟨443178078273409364430749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727232834916366553927989 443178078273409364430749)
                  ·
                    refine ⟨166191779352528511661531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443178078273409364430749 166191779352528511661531)
                    ·
                      rfl

theorem cell22_485486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_485486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485486 prefixEnd_485486 := by exact prefixLift 485486
  have htrace : WordTrace (prefixWord ++ tailWord_485486) baseStart_485486 baseEnd_485486 := by
    simpa [prefixWord, tailWord_485486, baseEnd_485486] using wordTrace_append hprefix tailTrace_485486
  have hstable : (prefixWord ++ tailWord_485486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485486).length < 2 ^ (prefixWord ++ tailWord_485486).sum := by decide
  have hdescent : baseEnd_485486 < baseStart_485486 := by decide
  rcases family_descends (prefixWord ++ tailWord_485486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485529 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_485529 : Nat := 118140960795 + 485529 * 2 ^ 59
def prefixEnd_485529 : Nat := 4983230072969 + 3 ^ 40 * 485529 * 2
def baseEnd_485529 : Nat := 166206499131290732836399

theorem tailTrace_485529 : CollatzResearch.WordTrace tailWord_485529 prefixEnd_485529 166206499131290732836399 := by
  unfold tailWord_485529
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708697458018829596571641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11805798305345886397714427 17708697458018829596571641)
  ·
    refine ⟨13281523093514122197428731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17708697458018829596571641 13281523093514122197428731)
    ·
      refine ⟨19922284640271183296143097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13281523093514122197428731 19922284640271183296143097)
      ·
        refine ⟨14941713480203387472107323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19922284640271183296143097 14941713480203387472107323)
        ·
          refine ⟨22412570220305081208160985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14941713480203387472107323 22412570220305081208160985)
          ·
            refine ⟨16809427665228810906120739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412570220305081208160985 16809427665228810906120739)
            ·
              refine ⟨25214141497843216359181109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16809427665228810906120739 25214141497843216359181109)
              ·
                refine ⟨2363825765422801533673229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25214141497843216359181109 2363825765422801533673229)
                ·
                  refine ⟨886434662033550575127461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2363825765422801533673229 886434662033550575127461)
                  ·
                    refine ⟨166206499131290732836399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 886434662033550575127461 166206499131290732836399)
                    ·
                      rfl

theorem cell22_485529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_485529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485529 prefixEnd_485529 := by exact prefixLift 485529
  have htrace : WordTrace (prefixWord ++ tailWord_485529) baseStart_485529 baseEnd_485529 := by
    simpa [prefixWord, tailWord_485529, baseEnd_485529] using wordTrace_append hprefix tailTrace_485529
  have hstable : (prefixWord ++ tailWord_485529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485529).length < 2 ^ (prefixWord ++ tailWord_485529).sum := by decide
  have hdescent : baseEnd_485529 < baseStart_485529 := by decide
  rcases family_descends (prefixWord ++ tailWord_485529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485619 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_485619 : Nat := 118140960795 + 485619 * 2 ^ 59
def prefixEnd_485619 : Nat := 4983230072969 + 3 ^ 40 * 485619 * 2
def baseEnd_485619 : Nat := 166237307970560498086123

theorem tailTrace_485619 : CollatzResearch.WordTrace tailWord_485619 prefixEnd_485619 166237307970560498086123 := by
  unfold tailWord_485619
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711980027692774967347911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11807986685128516644898607 17711980027692774967347911)
  ·
    refine ⟨26567970041539162451021867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711980027692774967347911 26567970041539162451021867)
    ·
      refine ⟨39851955062308743676532801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26567970041539162451021867 39851955062308743676532801)
      ·
        refine ⟨29888966296731557757399601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39851955062308743676532801 29888966296731557757399601)
        ·
          refine ⟨22416724722548668318049701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29888966296731557757399601 22416724722548668318049701)
          ·
            refine ⟨4203135885477875309634319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22416724722548668318049701 4203135885477875309634319)
            ·
              refine ⟨6304703828216812964451479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203135885477875309634319 6304703828216812964451479)
              ·
                refine ⟨9457055742325219446677219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304703828216812964451479 9457055742325219446677219)
                ·
                  refine ⟨14185583613487829170015829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9457055742325219446677219 14185583613487829170015829)
                  ·
                    refine ⟨166237307970560498086123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14185583613487829170015829 166237307970560498086123)
                    ·
                      rfl

theorem cell22_485619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_485619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_485619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_485619 prefixEnd_485619 := by exact prefixLift 485619
  have htrace : WordTrace (prefixWord ++ tailWord_485619) baseStart_485619 baseEnd_485619 := by
    simpa [prefixWord, tailWord_485619, baseEnd_485619] using wordTrace_append hprefix tailTrace_485619
  have hstable : (prefixWord ++ tailWord_485619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485619).length < 2 ^ (prefixWord ++ tailWord_485619).sum := by decide
  have hdescent : baseEnd_485619 < baseStart_485619 := by decide
  rcases family_descends (prefixWord ++ tailWord_485619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
