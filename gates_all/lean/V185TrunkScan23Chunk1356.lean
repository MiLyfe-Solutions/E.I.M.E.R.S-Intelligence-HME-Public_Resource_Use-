import V185TrunkScan23Chunk1355

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8029955 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 4, 4]
def baseStart_8029955 : Nat := 118140960795 + 8029955 * 2 ^ 59
def prefixEnd_8029955 : Nat := 4983230072969 + 3 ^ 40 * 8029955 * 2
def baseEnd_8029955 : Nat := 1374408849658078499277805

theorem tailTrace_8029955 : CollatzResearch.WordTrace tailWord_8029955 prefixEnd_8029955 1374408849658078499277805 := by
  unfold tailWord_8029955
  simp only [CollatzResearch.WordTrace]
  refine ⟨292876519623851916975811319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195251013082567944650540879 292876519623851916975811319)
  ·
    refine ⟨439314779435777875463716979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292876519623851916975811319 439314779435777875463716979)
    ·
      refine ⟨658972169153666813195575469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439314779435777875463716979 658972169153666813195575469)
      ·
        refine ⟨247114563432625054948340801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 658972169153666813195575469 247114563432625054948340801)
        ·
          refine ⟨185335922574468791211255601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247114563432625054948340801 185335922574468791211255601)
          ·
            refine ⟨139001941930851593408441701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185335922574468791211255601 139001941930851593408441701)
            ·
              refine ⟨26062864112034673764082819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139001941930851593408441701 26062864112034673764082819)
              ·
                refine ⟨39094296168052010646124229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26062864112034673764082819 39094296168052010646124229)
                ·
                  refine ⟨7330180531509751996148293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39094296168052010646124229 7330180531509751996148293)
                  ·
                    refine ⟨1374408849658078499277805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330180531509751996148293 1374408849658078499277805)
                    ·
                      rfl

theorem cell23_8029955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 4].length) (baseStart_8029955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029955 prefixEnd_8029955 := by exact prefixLift 8029955
  have htrace : WordTrace (prefixWord ++ tailWord_8029955) baseStart_8029955 baseEnd_8029955 := by
    simpa [prefixWord, tailWord_8029955, baseEnd_8029955] using wordTrace_append hprefix tailTrace_8029955
  have hstable : (prefixWord ++ tailWord_8029955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029955).length < 2 ^ (prefixWord ++ tailWord_8029955).sum := by decide
  have hdescent : baseEnd_8029955 < baseStart_8029955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029975 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_8029975 : Nat := 118140960795 + 8029975 * 2 ^ 59
def prefixEnd_8029975 : Nat := 4983230072969 + 3 ^ 40 * 8029975 * 2
def baseEnd_8029975 : Nat := 4123236818587325419583323

theorem tailTrace_8029975 : CollatzResearch.WordTrace tailWord_8029975 prefixEnd_8029975 4123236818587325419583323 := by
  unfold tailWord_8029975
  simp only [CollatzResearch.WordTrace]
  refine ⟨292877249083779460391539379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195251499389186306927692919 292877249083779460391539379)
  ·
    refine ⟨439315873625669190587309069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292877249083779460391539379 439315873625669190587309069)
    ·
      refine ⟨164743452609625946470240901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439315873625669190587309069 164743452609625946470240901)
      ·
        refine ⟨30889397364304864963170169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164743452609625946470240901 30889397364304864963170169)
        ·
          refine ⟨23167048023228648722377627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30889397364304864963170169 23167048023228648722377627)
          ·
            refine ⟨34750572034842973083566441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23167048023228648722377627 34750572034842973083566441)
            ·
              refine ⟨26062929026132229812674831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34750572034842973083566441 26062929026132229812674831)
              ·
                refine ⟨39094393539198344719012247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26062929026132229812674831 39094393539198344719012247)
                ·
                  refine ⟨58641590308797517078518371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39094393539198344719012247 58641590308797517078518371)
                  ·
                    refine ⟨87962385463196275617777557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58641590308797517078518371 87962385463196275617777557)
                    ·
                      refine ⟨4123236818587325419583323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87962385463196275617777557 4123236818587325419583323)
                      ·
                        rfl

theorem cell23_8029975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_8029975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029975 prefixEnd_8029975 := by exact prefixLift 8029975
  have htrace : WordTrace (prefixWord ++ tailWord_8029975) baseStart_8029975 baseEnd_8029975 := by
    simpa [prefixWord, tailWord_8029975, baseEnd_8029975] using wordTrace_append hprefix tailTrace_8029975
  have hstable : (prefixWord ++ tailWord_8029975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029975).length < 2 ^ (prefixWord ++ tailWord_8029975).sum := by decide
  have hdescent : baseEnd_8029975 < baseStart_8029975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8029992 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_8029992 : Nat := 118140960795 + 8029992 * 2 ^ 59
def prefixEnd_8029992 : Nat := 4983230072969 + 3 ^ 40 * 8029992 * 2
def baseEnd_8029992 : Nat := 4123245547758451853070745

theorem tailTrace_8029992 : CollatzResearch.WordTrace tailWord_8029992 prefixEnd_8029992 4123245547758451853070745 := by
  unfold tailWord_8029992
  simp only [CollatzResearch.WordTrace]
  refine ⟨146438934562358936147454115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195251912749811914863272153 146438934562358936147454115)
  ·
    refine ⟨219658401843538404221181173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146438934562358936147454115 219658401843538404221181173)
    ·
      refine ⟨20592975172831725395735735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219658401843538404221181173 20592975172831725395735735)
      ·
        refine ⟨30889462759247588093603603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20592975172831725395735735 30889462759247588093603603)
        ·
          refine ⟨46334194138871382140405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30889462759247588093603603 46334194138871382140405405)
          ·
            refine ⟨17375322802076768302652027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46334194138871382140405405 17375322802076768302652027)
            ·
              refine ⟨26062984203115152453978041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17375322802076768302652027 26062984203115152453978041)
              ·
                refine ⟨19547238152336364340483531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26062984203115152453978041 19547238152336364340483531)
                ·
                  refine ⟨29320857228504546510725297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19547238152336364340483531 29320857228504546510725297)
                  ·
                    refine ⟨21990642921378409883043973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29320857228504546510725297 21990642921378409883043973)
                    ·
                      refine ⟨4123245547758451853070745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21990642921378409883043973 4123245547758451853070745)
                      ·
                        rfl

theorem cell23_8029992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_8029992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8029992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8029992 prefixEnd_8029992 := by exact prefixLift 8029992
  have htrace : WordTrace (prefixWord ++ tailWord_8029992) baseStart_8029992 baseEnd_8029992 := by
    simpa [prefixWord, tailWord_8029992, baseEnd_8029992] using wordTrace_append hprefix tailTrace_8029992
  have hstable : (prefixWord ++ tailWord_8029992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8029992).length < 2 ^ (prefixWord ++ tailWord_8029992).sum := by decide
  have hdescent : baseEnd_8029992 < baseStart_8029992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8029992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030006 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_8030006 : Nat := 118140960795 + 8030006 * 2 ^ 59
def prefixEnd_8030006 : Nat := 4983230072969 + 3 ^ 40 * 8030006 * 2
def baseEnd_8030006 : Nat := 1374417578829204932765227

theorem tailTrace_8030006 : CollatzResearch.WordTrace tailWord_8030006 prefixEnd_8030006 1374417578829204932765227 := by
  unfold tailWord_8030006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304898734166697042869867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195252253164444768457278581 18304898734166697042869867)
  ·
    refine ⟨27457348101250045564304801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18304898734166697042869867 27457348101250045564304801)
    ·
      refine ⟨20593011075937534173228601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27457348101250045564304801 20593011075937534173228601)
      ·
        refine ⟨15444758306953150629921451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20593011075937534173228601 15444758306953150629921451)
        ·
          refine ⟨23167137460429725944882177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444758306953150629921451 23167137460429725944882177)
          ·
            refine ⟨17375353095322294458661633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23167137460429725944882177 17375353095322294458661633)
            ·
              refine ⟨13031514821491720843996225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17375353095322294458661633 13031514821491720843996225)
              ·
                refine ⟨9773636116118790632997169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13031514821491720843996225 9773636116118790632997169)
                ·
                  refine ⟨7330227087089092974747877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9773636116118790632997169 7330227087089092974747877)
                  ·
                    refine ⟨1374417578829204932765227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330227087089092974747877 1374417578829204932765227)
                    ·
                      rfl

theorem cell23_8030006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_8030006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030006 prefixEnd_8030006 := by exact prefixLift 8030006
  have htrace : WordTrace (prefixWord ++ tailWord_8030006) baseStart_8030006 baseEnd_8030006 := by
    simpa [prefixWord, tailWord_8030006, baseEnd_8030006] using wordTrace_append hprefix tailTrace_8030006
  have hstable : (prefixWord ++ tailWord_8030006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030006).length < 2 ^ (prefixWord ++ tailWord_8030006).sum := by decide
  have hdescent : baseEnd_8030006 < baseStart_8030006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030012 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_8030012 : Nat := 118140960795 + 8030012 * 2 ^ 59
def prefixEnd_8030012 : Nat := 4983230072969 + 3 ^ 40 * 8030012 * 2
def baseEnd_8030012 : Nat := 4123255817371541774820653

theorem tailTrace_8030012 : CollatzResearch.WordTrace tailWord_8030012 prefixEnd_8030012 4123255817371541774820653 := by
  unfold tailWord_8030012
  simp only [CollatzResearch.WordTrace]
  refine ⟨146439299292322707855318145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195252399056430277140424193 146439299292322707855318145)
  ·
    refine ⟨109829474469242030891488609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146439299292322707855318145 109829474469242030891488609)
    ·
      refine ⟨82372105851931523168616457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109829474469242030891488609 82372105851931523168616457)
      ·
        refine ⟨61779079388948642376462343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82372105851931523168616457 61779079388948642376462343)
        ·
          refine ⟨92668619083422963564693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61779079388948642376462343 92668619083422963564693515)
          ·
            refine ⟨139002928625134445347040273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92668619083422963564693515 139002928625134445347040273)
            ·
              refine ⟨104252196468850834010280205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139002928625134445347040273 104252196468850834010280205)
              ·
                refine ⟨39094573675819062753855077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104252196468850834010280205 39094573675819062753855077)
                ·
                  refine ⟨7330232564216074266347827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39094573675819062753855077 7330232564216074266347827)
                  ·
                    refine ⟨10995348846324111399521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7330232564216074266347827 10995348846324111399521741)
                    ·
                      refine ⟨4123255817371541774820653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995348846324111399521741 4123255817371541774820653)
                      ·
                        rfl

theorem cell23_8030012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_8030012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030012 prefixEnd_8030012 := by exact prefixLift 8030012
  have htrace : WordTrace (prefixWord ++ tailWord_8030012) baseStart_8030012 baseEnd_8030012 := by
    simpa [prefixWord, tailWord_8030012, baseEnd_8030012] using wordTrace_append hprefix tailTrace_8030012
  have hstable : (prefixWord ++ tailWord_8030012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030012).length < 2 ^ (prefixWord ++ tailWord_8030012).sum := by decide
  have hdescent : baseEnd_8030012 < baseStart_8030012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030013 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8030013 : Nat := 118140960795 + 8030013 * 2 ^ 59
def prefixEnd_8030013 : Nat := 4983230072969 + 3 ^ 40 * 8030013 * 2
def baseEnd_8030013 : Nat := 4123256330852196270908149

theorem tailTrace_8030013 : CollatzResearch.WordTrace tailWord_8030013 prefixEnd_8030013 4123256330852196270908149 := by
  unfold tailWord_8030013
  simp only [CollatzResearch.WordTrace]
  refine ⟨292878635057641792881422693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195252423371761195254281795 292878635057641792881422693)
  ·
    refine ⟨54914744073307836165266755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292878635057641792881422693 54914744073307836165266755)
    ·
      refine ⟨82372116109961754247900133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914744073307836165266755 82372116109961754247900133)
      ·
        refine ⟨15444771770617828921481275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82372116109961754247900133 15444771770617828921481275)
        ·
          refine ⟨23167157655926743382221913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444771770617828921481275 23167157655926743382221913)
          ·
            refine ⟨17375368241945057536666435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23167157655926743382221913 17375368241945057536666435)
            ·
              refine ⟨26063052362917586304999653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17375368241945057536666435 26063052362917586304999653)
              ·
                refine ⟨4886822318047047432187435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26063052362917586304999653 4886822318047047432187435)
                ·
                  refine ⟨7330233477070571148281153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886822318047047432187435 7330233477070571148281153)
                  ·
                    refine ⟨5497675107802928361210865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330233477070571148281153 5497675107802928361210865)
                    ·
                      refine ⟨4123256330852196270908149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497675107802928361210865 4123256330852196270908149)
                      ·
                        rfl

theorem cell23_8030013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8030013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030013 prefixEnd_8030013 := by exact prefixLift 8030013
  have htrace : WordTrace (prefixWord ++ tailWord_8030013) baseStart_8030013 baseEnd_8030013 := by
    simpa [prefixWord, tailWord_8030013, baseEnd_8030013] using wordTrace_append hprefix tailTrace_8030013
  have hstable : (prefixWord ++ tailWord_8030013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030013).length < 2 ^ (prefixWord ++ tailWord_8030013).sum := by decide
  have hdescent : baseEnd_8030013 < baseStart_8030013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030029 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8030029 : Nat := 118140960795 + 8030029 * 2 ^ 59
def prefixEnd_8030029 : Nat := 4983230072969 + 3 ^ 40 * 8030029 * 2
def baseEnd_8030029 : Nat := 4123264546542668208308075

theorem tailTrace_8030029 : CollatzResearch.WordTrace tailWord_8030029 prefixEnd_8030029 4123264546542668208308075 := by
  unfold tailWord_8030029
  simp only [CollatzResearch.WordTrace]
  refine ⟨292879218625583827614005141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195252812417055885076003427 292879218625583827614005141)
  ·
    refine ⟨13728713373074241919406491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292879218625583827614005141 13728713373074241919406491)
    ·
      refine ⟨20593070059611362879109737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13728713373074241919406491 20593070059611362879109737)
      ·
        refine ⟨15444802544708522159332303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20593070059611362879109737 15444802544708522159332303)
        ·
          refine ⟨23167203817062783238998455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444802544708522159332303 23167203817062783238998455)
          ·
            refine ⟨34750805725594174858497683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23167203817062783238998455 34750805725594174858497683)
            ·
              refine ⟨52126208588391262287746525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34750805725594174858497683 52126208588391262287746525)
              ·
                refine ⟨19547328220646723357904947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52126208588391262287746525 19547328220646723357904947)
                ·
                  refine ⟨29320992330970085036857421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19547328220646723357904947 29320992330970085036857421)
                  ·
                    refine ⟨10995372124113781888821533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29320992330970085036857421 10995372124113781888821533)
                    ·
                      refine ⟨4123264546542668208308075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995372124113781888821533 4123264546542668208308075)
                      ·
                        rfl

theorem cell23_8030029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8030029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030029 prefixEnd_8030029 := by exact prefixLift 8030029
  have htrace : WordTrace (prefixWord ++ tailWord_8030029) baseStart_8030029 baseEnd_8030029 := by
    simpa [prefixWord, tailWord_8030029, baseEnd_8030029] using wordTrace_append hprefix tailTrace_8030029
  have hstable : (prefixWord ++ tailWord_8030029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030029).length < 2 ^ (prefixWord ++ tailWord_8030029).sum := by decide
  have hdescent : baseEnd_8030029 < baseStart_8030029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030055 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_8030055 : Nat := 118140960795 + 8030055 * 2 ^ 59
def prefixEnd_8030055 : Nat := 4983230072969 + 3 ^ 40 * 8030055 * 2
def baseEnd_8030055 : Nat := 4123277897039685106582955

theorem tailTrace_8030055 : CollatzResearch.WordTrace tailWord_8030055 prefixEnd_8030055 4123277897039685106582955 := by
  unfold tailWord_8030055
  simp only [CollatzResearch.WordTrace]
  refine ⟨292880166923489634054451619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195253444615659756036301079 292880166923489634054451619)
  ·
    refine ⟨439320250385234451081677429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292880166923489634054451619 439320250385234451081677429)
    ·
      refine ⟨41186273473615729788907259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439320250385234451081677429 41186273473615729788907259)
      ·
        refine ⟨61779410210423594683360889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41186273473615729788907259 61779410210423594683360889)
        ·
          refine ⟨46334557657817696012520667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61779410210423594683360889 46334557657817696012520667)
          ·
            refine ⟨69501836486726544018781001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46334557657817696012520667 69501836486726544018781001)
            ·
              refine ⟨52126377365044908014085751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69501836486726544018781001 52126377365044908014085751)
              ·
                refine ⟨78189566047567362021128627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52126377365044908014085751 78189566047567362021128627)
                ·
                  refine ⟨117284349071351043031692941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78189566047567362021128627 117284349071351043031692941)
                  ·
                    refine ⟨43981630901756641136884853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117284349071351043031692941 43981630901756641136884853)
                    ·
                      refine ⟨4123277897039685106582955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43981630901756641136884853 4123277897039685106582955)
                      ·
                        rfl

theorem cell23_8030055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_8030055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030055 prefixEnd_8030055 := by exact prefixLift 8030055
  have htrace : WordTrace (prefixWord ++ tailWord_8030055) baseStart_8030055 baseEnd_8030055 := by
    simpa [prefixWord, tailWord_8030055, baseEnd_8030055] using wordTrace_append hprefix tailTrace_8030055
  have hstable : (prefixWord ++ tailWord_8030055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030055).length < 2 ^ (prefixWord ++ tailWord_8030055).sum := by decide
  have hdescent : baseEnd_8030055 < baseStart_8030055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030062 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_8030062 : Nat := 118140960795 + 8030062 * 2 ^ 59
def prefixEnd_8030062 : Nat := 4983230072969 + 3 ^ 40 * 8030062 * 2
def baseEnd_8030062 : Nat := 1374427163801422193065141

theorem tailTrace_8030062 : CollatzResearch.WordTrace tailWord_8030062 prefixEnd_8030062 1374427163801422193065141 := by
  unfold tailWord_8030062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36610052779308034281244555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195253614822976182833304293 36610052779308034281244555)
  ·
    refine ⟨54915079168962051421866833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36610052779308034281244555 54915079168962051421866833)
    ·
      refine ⟨41186309376721538566400125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54915079168962051421866833 41186309376721538566400125)
      ·
        refine ⟨15444866016270576962400047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41186309376721538566400125 15444866016270576962400047)
        ·
          refine ⟨23167299024405865443600071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15444866016270576962400047 23167299024405865443600071)
          ·
            refine ⟨34750948536608798165400107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23167299024405865443600071 34750948536608798165400107)
            ·
              refine ⟨52126422804913197248100161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34750948536608798165400107 52126422804913197248100161)
              ·
                refine ⟨39094817103684897936075121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52126422804913197248100161 39094817103684897936075121)
                ·
                  refine ⟨29321112827763673452056341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39094817103684897936075121 29321112827763673452056341)
                  ·
                    refine ⟨1374427163801422193065141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29321112827763673452056341 1374427163801422193065141)
                    ·
                      rfl

theorem cell23_8030062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_8030062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030062 prefixEnd_8030062 := by exact prefixLift 8030062
  have htrace : WordTrace (prefixWord ++ tailWord_8030062) baseStart_8030062 baseEnd_8030062 := by
    simpa [prefixWord, tailWord_8030062, baseEnd_8030062] using wordTrace_append hprefix tailTrace_8030062
  have hstable : (prefixWord ++ tailWord_8030062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030062).length < 2 ^ (prefixWord ++ tailWord_8030062).sum := by decide
  have hdescent : baseEnd_8030062 < baseStart_8030062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030065 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_8030065 : Nat := 118140960795 + 8030065 * 2 ^ 59
def prefixEnd_8030065 : Nat := 4983230072969 + 3 ^ 40 * 8030065 * 2
def baseEnd_8030065 : Nat := 4123283031846230067457909

theorem tailTrace_8030065 : CollatzResearch.WordTrace tailWord_8030065 prefixEnd_8030065 4123283031846230067457909 := by
  unfold tailWord_8030065
  simp only [CollatzResearch.WordTrace]
  refine ⟨292880531653453405762315649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195253687768968937174877099 292880531653453405762315649)
  ·
    refine ⟨219660398740090054321736737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292880531653453405762315649 219660398740090054321736737)
    ·
      refine ⟨164745299055067540741302553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219660398740090054321736737 164745299055067540741302553)
      ·
        refine ⟨123558974291300655555976915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164745299055067540741302553 123558974291300655555976915)
        ·
          refine ⟨185338461436950983333965373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123558974291300655555976915 185338461436950983333965373)
          ·
            refine ⟨69501923038856618750237015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185338461436950983333965373 69501923038856618750237015)
            ·
              refine ⟨104252884558284928125355523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69501923038856618750237015 104252884558284928125355523)
              ·
                refine ⟨156379326837427392188033285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104252884558284928125355523 156379326837427392188033285)
                ·
                  refine ⟨29321123782017636035256241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156379326837427392188033285 29321123782017636035256241)
                  ·
                    refine ⟨21990842836513227026442181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29321123782017636035256241 21990842836513227026442181)
                    ·
                      refine ⟨4123283031846230067457909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21990842836513227026442181 4123283031846230067457909)
                      ·
                        rfl

theorem cell23_8030065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_8030065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030065 prefixEnd_8030065 := by exact prefixLift 8030065
  have htrace : WordTrace (prefixWord ++ tailWord_8030065) baseStart_8030065 baseEnd_8030065 := by
    simpa [prefixWord, tailWord_8030065, baseEnd_8030065] using wordTrace_append hprefix tailTrace_8030065
  have hstable : (prefixWord ++ tailWord_8030065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030065).length < 2 ^ (prefixWord ++ tailWord_8030065).sum := by decide
  have hdescent : baseEnd_8030065 < baseStart_8030065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030105 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_8030105 : Nat := 118140960795 + 8030105 * 2 ^ 59
def prefixEnd_8030105 : Nat := 4983230072969 + 3 ^ 40 * 8030105 * 2
def baseEnd_8030105 : Nat := 1374434523690803303652575

theorem tailTrace_8030105 : CollatzResearch.WordTrace tailWord_8030105 prefixEnd_8030105 1374434523690803303652575 := by
  unfold tailWord_8030105
  simp only [CollatzResearch.WordTrace]
  refine ⟨292881990573308492593771769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195254660382205661729181179 292881990573308492593771769)
  ·
    refine ⟨219661492929981369445328827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292881990573308492593771769 219661492929981369445328827)
    ·
      refine ⟨329492239394972054167993241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219661492929981369445328827 329492239394972054167993241)
      ·
        refine ⟨247119179546229040625994931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329492239394972054167993241 247119179546229040625994931)
        ·
          refine ⟨370678769319343560938992397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247119179546229040625994931 370678769319343560938992397)
          ·
            refine ⟨139004538494753835352122149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370678769319343560938992397 139004538494753835352122149)
            ·
              refine ⟨26063350967766344128522903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139004538494753835352122149 26063350967766344128522903)
              ·
                refine ⟨39095026451649516192784355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26063350967766344128522903 39095026451649516192784355)
                ·
                  refine ⟨58642539677474274289176533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39095026451649516192784355 58642539677474274289176533)
                  ·
                    refine ⟨1374434523690803303652575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58642539677474274289176533 1374434523690803303652575)
                    ·
                      rfl

theorem cell23_8030105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_8030105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030105 prefixEnd_8030105 := by exact prefixLift 8030105
  have htrace : WordTrace (prefixWord ++ tailWord_8030105) baseStart_8030105 baseEnd_8030105 := by
    simpa [prefixWord, tailWord_8030105, baseEnd_8030105] using wordTrace_append hprefix tailTrace_8030105
  have hstable : (prefixWord ++ tailWord_8030105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030105).length < 2 ^ (prefixWord ++ tailWord_8030105).sum := by decide
  have hdescent : baseEnd_8030105 < baseStart_8030105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030109 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 5]
def baseStart_8030109 : Nat := 118140960795 + 8030109 * 2 ^ 59
def prefixEnd_8030109 : Nat := 4983230072969 + 3 ^ 40 * 8030109 * 2
def baseEnd_8030109 : Nat := 458145069443891988367523

theorem tailTrace_8030109 : CollatzResearch.WordTrace tailWord_8030109 prefixEnd_8030109 458145069443891988367523 := by
  unfold tailWord_8030109
  simp only [CollatzResearch.WordTrace]
  refine ⟨292882136465294001276917381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195254757643529334184611587 292882136465294001276917381)
  ·
    refine ⟨54915400587242625239422009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292882136465294001276917381 54915400587242625239422009)
    ·
      refine ⟨41186550440431968929566507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54915400587242625239422009 41186550440431968929566507)
      ·
        refine ⟨61779825660647953394349761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41186550440431968929566507 61779825660647953394349761)
        ·
          refine ⟨46334869245485965045762321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61779825660647953394349761 46334869245485965045762321)
          ·
            refine ⟨34751151934114473784321741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46334869245485965045762321 34751151934114473784321741)
            ·
              refine ⟨13031681975292927669120653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34751151934114473784321741 13031681975292927669120653)
              ·
                refine ⟨4886880740734847875920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13031681975292927669120653 4886880740734847875920245)
                ·
                  refine ⟨458145069443891988367523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4886880740734847875920245 458145069443891988367523)
                  ·
                    rfl

theorem cell23_8030109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_8030109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030109 prefixEnd_8030109 := by exact prefixLift 8030109
  have htrace : WordTrace (prefixWord ++ tailWord_8030109) baseStart_8030109 baseEnd_8030109 := by
    simpa [prefixWord, tailWord_8030109, baseEnd_8030109] using wordTrace_append hprefix tailTrace_8030109
  have hstable : (prefixWord ++ tailWord_8030109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030109).length < 2 ^ (prefixWord ++ tailWord_8030109).sum := by decide
  have hdescent : baseEnd_8030109 < baseStart_8030109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030112 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2]
def baseStart_8030112 : Nat := 118140960795 + 8030112 * 2 ^ 59
def prefixEnd_8030112 : Nat := 4983230072969 + 3 ^ 40 * 8030112 * 2
def baseEnd_8030112 : Nat := 4123307165436991383570193

theorem tailTrace_8030112 : CollatzResearch.WordTrace tailWord_8030112 prefixEnd_8030112 4123307165436991383570193 := by
  unfold tailWord_8030112
  simp only [CollatzResearch.WordTrace]
  refine ⟨146441122942141566394638295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195254830589522088526184393 146441122942141566394638295)
  ·
    refine ⟨219661684413212349591957443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146441122942141566394638295 219661684413212349591957443)
    ·
      refine ⟨329492526619818524387936165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219661684413212349591957443 329492526619818524387936165)
      ·
        refine ⟨61779848741215973322738031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329492526619818524387936165 61779848741215973322738031)
        ·
          refine ⟨92669773111823959984107047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61779848741215973322738031 92669773111823959984107047)
          ·
            refine ⟨139004659667735939976160571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92669773111823959984107047 139004659667735939976160571)
            ·
              refine ⟨208506989501603909964240857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139004659667735939976160571 208506989501603909964240857)
              ·
                refine ⟨156380242126202932473180643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208506989501603909964240857 156380242126202932473180643)
                ·
                  refine ⟨234570363189304398709770965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156380242126202932473180643 234570363189304398709770965)
                  ·
                    refine ⟨5497742887249321844760257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234570363189304398709770965 5497742887249321844760257)
                    ·
                      refine ⟨4123307165436991383570193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497742887249321844760257 4123307165436991383570193)
                      ·
                        rfl

theorem cell23_8030112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_8030112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030112 prefixEnd_8030112 := by exact prefixLift 8030112
  have htrace : WordTrace (prefixWord ++ tailWord_8030112) baseStart_8030112 baseEnd_8030112 := by
    simpa [prefixWord, tailWord_8030112, baseEnd_8030112] using wordTrace_append hprefix tailTrace_8030112
  have hstable : (prefixWord ++ tailWord_8030112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030112).length < 2 ^ (prefixWord ++ tailWord_8030112).sum := by decide
  have hdescent : baseEnd_8030112 < baseStart_8030112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030115 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_8030115 : Nat := 118140960795 + 8030115 * 2 ^ 59
def prefixEnd_8030115 : Nat := 4983230072969 + 3 ^ 40 * 8030115 * 2
def baseEnd_8030115 : Nat := 4123308705878954871832679

theorem tailTrace_8030115 : CollatzResearch.WordTrace tailWord_8030115 prefixEnd_8030115 4123308705878954871832679 := by
  unfold tailWord_8030115
  simp only [CollatzResearch.WordTrace]
  refine ⟨292882355303272264301635799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195254903535514842867757199 292882355303272264301635799)
  ·
    refine ⟨439323532954908396452453699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292882355303272264301635799 439323532954908396452453699)
    ·
      refine ⟨658985299432362594678680549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439323532954908396452453699 658985299432362594678680549)
      ·
        refine ⟨123559743643567986502252603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 658985299432362594678680549 123559743643567986502252603)
        ·
          refine ⟨185339615465351979753378905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123559743643567986502252603 185339615465351979753378905)
          ·
            refine ⟨139004711599013984815034179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185339615465351979753378905 139004711599013984815034179)
            ·
              refine ⟨208507067398520977222551269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139004711599013984815034179 208507067398520977222551269)
              ·
                refine ⟨39095075137222683229228363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208507067398520977222551269 39095075137222683229228363)
                ·
                  refine ⟨58642612705834024843842545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39095075137222683229228363 58642612705834024843842545)
                  ·
                    refine ⟨43981959529375518632881909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58642612705834024843842545 43981959529375518632881909)
                    ·
                      refine ⟨4123308705878954871832679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43981959529375518632881909 4123308705878954871832679)
                      ·
                        rfl

theorem cell23_8030115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_8030115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030115 prefixEnd_8030115 := by exact prefixLift 8030115
  have htrace : WordTrace (prefixWord ++ tailWord_8030115) baseStart_8030115 baseEnd_8030115 := by
    simpa [prefixWord, tailWord_8030115, baseEnd_8030115] using wordTrace_append hprefix tailTrace_8030115
  have hstable : (prefixWord ++ tailWord_8030115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030115).length < 2 ^ (prefixWord ++ tailWord_8030115).sum := by decide
  have hdescent : baseEnd_8030115 < baseStart_8030115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030179 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3]
def baseStart_8030179 : Nat := 118140960795 + 8030179 * 2 ^ 59
def prefixEnd_8030179 : Nat := 4983230072969 + 3 ^ 40 * 8030179 * 2
def baseEnd_8030179 : Nat := 4123341568640842621432385

theorem tailTrace_8030179 : CollatzResearch.WordTrace tailWord_8030179 prefixEnd_8030179 4123341568640842621432385 := by
  unfold tailWord_8030179
  simp only [CollatzResearch.WordTrace]
  refine ⟨292884689575040403231965591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195256459716693602154643727 292884689575040403231965591)
  ·
    refine ⟨439327034362560604847948387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292884689575040403231965591 439327034362560604847948387)
    ·
      refine ⟨658990551543840907271922581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439327034362560604847948387 658990551543840907271922581)
      ·
        refine ⟨30890182103617542528371371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 658990551543840907271922581 30890182103617542528371371)
        ·
          refine ⟨46335273155426313792557057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890182103617542528371371 46335273155426313792557057)
          ·
            refine ⟨34751454866569735344417793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46335273155426313792557057 34751454866569735344417793)
            ·
              refine ⟨26063591149927301508313345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34751454866569735344417793 26063591149927301508313345)
              ·
                refine ⟨19547693362445476131235009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26063591149927301508313345 19547693362445476131235009)
                ·
                  refine ⟨14660770021834107098426257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19547693362445476131235009 14660770021834107098426257)
                  ·
                    refine ⟨10995577516375580323819693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14660770021834107098426257 10995577516375580323819693)
                    ·
                      refine ⟨4123341568640842621432385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995577516375580323819693 4123341568640842621432385)
                      ·
                        rfl

theorem cell23_8030179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_8030179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030179 prefixEnd_8030179 := by exact prefixLift 8030179
  have htrace : WordTrace (prefixWord ++ tailWord_8030179) baseStart_8030179 baseEnd_8030179 := by
    simpa [prefixWord, tailWord_8030179, baseEnd_8030179] using wordTrace_append hprefix tailTrace_8030179
  have hstable : (prefixWord ++ tailWord_8030179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030179).length < 2 ^ (prefixWord ++ tailWord_8030179).sum := by decide
  have hdescent : baseEnd_8030179 < baseStart_8030179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030186 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_8030186 : Nat := 118140960795 + 8030186 * 2 ^ 59
def prefixEnd_8030186 : Nat := 4983230072969 + 3 ^ 40 * 8030186 * 2
def baseEnd_8030186 : Nat := 1374448387668474698014951

theorem tailTrace_8030186 : CollatzResearch.WordTrace tailWord_8030186 prefixEnd_8030186 1374448387668474698014951 := by
  unfold tailWord_8030186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73221236221503760856867603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195256629924010028951646941 73221236221503760856867603)
  ·
    refine ⟨109831854332255641285301405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73221236221503760856867603 109831854332255641285301405)
    ·
      refine ⟨41186945374595865481988027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109831854332255641285301405 41186945374595865481988027)
      ·
        refine ⟨61780418061893798222982041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41186945374595865481988027 61780418061893798222982041)
        ·
          refine ⟨46335313546420348667236531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61780418061893798222982041 46335313546420348667236531)
          ·
            refine ⟨69502970319630523000854797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46335313546420348667236531 69502970319630523000854797)
            ·
              refine ⟨26063613869861446125320549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69502970319630523000854797 26063613869861446125320549)
              ·
                refine ⟨4886927600599021148497603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26063613869861446125320549 4886927600599021148497603)
                ·
                  refine ⟨7330391400898531722746405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886927600599021148497603 7330391400898531722746405)
                  ·
                    refine ⟨1374448387668474698014951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330391400898531722746405 1374448387668474698014951)
                    ·
                      rfl

theorem cell23_8030186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_8030186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030186 prefixEnd_8030186 := by exact prefixLift 8030186
  have htrace : WordTrace (prefixWord ++ tailWord_8030186) baseStart_8030186 baseEnd_8030186 := by
    simpa [prefixWord, tailWord_8030186, baseEnd_8030186] using wordTrace_append hprefix tailTrace_8030186
  have hstable : (prefixWord ++ tailWord_8030186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030186).length < 2 ^ (prefixWord ++ tailWord_8030186).sum := by decide
  have hdescent : baseEnd_8030186 < baseStart_8030186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030219 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 5, 2]
def baseStart_8030219 : Nat := 118140960795 + 8030219 * 2 ^ 59
def prefixEnd_8030219 : Nat := 4983230072969 + 3 ^ 40 * 8030219 * 2
def baseEnd_8030219 : Nat := 4123362107867022464932201

theorem tailTrace_8030219 : CollatzResearch.WordTrace tailWord_8030219 prefixEnd_8030219 4123362107867022464932201 := by
  unfold tailWord_8030219
  simp only [CollatzResearch.WordTrace]
  refine ⟨292886148494895490063421711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195257432329930326708947807 292886148494895490063421711)
  ·
    refine ⟨439329222742343235095132567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292886148494895490063421711 439329222742343235095132567)
    ·
      refine ⟨658993834113514852642698851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439329222742343235095132567 658993834113514852642698851)
      ·
        refine ⟨988490751170272278964048277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658993834113514852642698851 988490751170272278964048277)
        ·
          refine ⟨46335503961106513076439763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 988490751170272278964048277 46335503961106513076439763)
          ·
            refine ⟨69503255941659769614659645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46335503961106513076439763 69503255941659769614659645)
            ·
              refine ⟨26063720978122413605497367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69503255941659769614659645 26063720978122413605497367)
              ·
                refine ⟨39095581467183620408246051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26063720978122413605497367 39095581467183620408246051)
                ·
                  refine ⟨58643372200775430612369077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39095581467183620408246051 58643372200775430612369077)
                  ·
                    refine ⟨5497816143822696619909601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58643372200775430612369077 5497816143822696619909601)
                    ·
                      refine ⟨4123362107867022464932201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497816143822696619909601 4123362107867022464932201)
                      ·
                        rfl

theorem cell23_8030219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5, 2].length) (baseStart_8030219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030219 prefixEnd_8030219 := by exact prefixLift 8030219
  have htrace : WordTrace (prefixWord ++ tailWord_8030219) baseStart_8030219 baseEnd_8030219 := by
    simpa [prefixWord, tailWord_8030219, baseEnd_8030219] using wordTrace_append hprefix tailTrace_8030219
  have hstable : (prefixWord ++ tailWord_8030219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030219).length < 2 ^ (prefixWord ++ tailWord_8030219).sum := by decide
  have hdescent : baseEnd_8030219 < baseStart_8030219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030252 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_8030252 : Nat := 118140960795 + 8030252 * 2 ^ 59
def prefixEnd_8030252 : Nat := 4983230072969 + 3 ^ 40 * 8030252 * 2
def baseEnd_8030252 : Nat := 4123379052728620835819549

theorem tailTrace_8030252 : CollatzResearch.WordTrace tailWord_8030252 prefixEnd_8030252 4123379052728620835819549 := by
  unfold tailWord_8030252
  simp only [CollatzResearch.WordTrace]
  refine ⟨146443676051887968349686505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195258234735850624466248673 146443676051887968349686505)
  ·
    refine ⟨109832757038915976262264879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146443676051887968349686505 109832757038915976262264879)
    ·
      refine ⟨164749135558373964393397319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109832757038915976262264879 164749135558373964393397319)
      ·
        refine ⟨247123703337560946590095979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164749135558373964393397319 247123703337560946590095979)
        ·
          refine ⟨370685555006341419885143969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247123703337560946590095979 370685555006341419885143969)
          ·
            refine ⟨278014166254756064913857977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370685555006341419885143969 278014166254756064913857977)
            ·
              refine ⟨208510624691067048685393483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278014166254756064913857977 208510624691067048685393483)
              ·
                refine ⟨312765937036600573028090225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208510624691067048685393483 312765937036600573028090225)
                ·
                  refine ⟨234574452777450429771067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312765937036600573028090225 234574452777450429771067669)
                  ·
                    refine ⟨10995677473942988895518797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234574452777450429771067669 10995677473942988895518797)
                    ·
                      refine ⟨4123379052728620835819549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995677473942988895518797 4123379052728620835819549)
                      ·
                        rfl

theorem cell23_8030252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_8030252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030252 prefixEnd_8030252 := by exact prefixLift 8030252
  have htrace : WordTrace (prefixWord ++ tailWord_8030252) baseStart_8030252 baseEnd_8030252 := by
    simpa [prefixWord, tailWord_8030252, baseEnd_8030252] using wordTrace_append hprefix tailTrace_8030252
  have hstable : (prefixWord ++ tailWord_8030252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030252).length < 2 ^ (prefixWord ++ tailWord_8030252).sum := by decide
  have hdescent : baseEnd_8030252 < baseStart_8030252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030259 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 2, 4]
def baseStart_8030259 : Nat := 118140960795 + 8030259 * 2 ^ 59
def prefixEnd_8030259 : Nat := 4983230072969 + 3 ^ 40 * 8030259 * 2
def baseEnd_8030259 : Nat := 1374460882364400769477339

theorem tailTrace_8030259 : CollatzResearch.WordTrace tailWord_8030259 prefixEnd_8030259 1374460882364400769477339 := by
  unfold tailWord_8030259
  simp only [CollatzResearch.WordTrace]
  refine ⟨292887607414750576894877831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195258404943167051263251887 292887607414750576894877831)
  ·
    refine ⟨439331411122125865342316747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292887607414750576894877831 439331411122125865342316747)
    ·
      refine ⟨658997116683188798013475121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439331411122125865342316747 658997116683188798013475121)
      ·
        refine ⟨494247837512391598510106341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658997116683188798013475121 494247837512391598510106341)
        ·
          refine ⟨92671469533573424720644939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494247837512391598510106341 92671469533573424720644939)
          ·
            refine ⟨139007204300360137080967409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92671469533573424720644939 139007204300360137080967409)
            ·
              refine ⟨104255403225270102810725557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139007204300360137080967409 104255403225270102810725557)
              ·
                refine ⟨9773944052369072138505521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104255403225270102810725557 9773944052369072138505521)
                ·
                  refine ⟨7330458039276804103879141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9773944052369072138505521 7330458039276804103879141)
                  ·
                    refine ⟨1374460882364400769477339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330458039276804103879141 1374460882364400769477339)
                    ·
                      rfl

theorem cell23_8030259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 4].length) (baseStart_8030259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030259 prefixEnd_8030259 := by exact prefixLift 8030259
  have htrace : WordTrace (prefixWord ++ tailWord_8030259) baseStart_8030259 baseEnd_8030259 := by
    simpa [prefixWord, tailWord_8030259, baseEnd_8030259] using wordTrace_append hprefix tailTrace_8030259
  have hstable : (prefixWord ++ tailWord_8030259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030259).length < 2 ^ (prefixWord ++ tailWord_8030259).sum := by decide
  have hdescent : baseEnd_8030259 < baseStart_8030259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030272 : List Nat := [2, 1, 1, 2, 2, 5, 1, 9]
def baseStart_8030272 : Nat := 118140960795 + 8030272 * 2 ^ 59
def prefixEnd_8030272 : Nat := 4983230072969 + 3 ^ 40 * 8030272 * 2
def baseEnd_8030272 : Nat := 152718123049692991021091

theorem tailTrace_8030272 : CollatzResearch.WordTrace tailWord_8030272 prefixEnd_8030272 152718123049692991021091 := by
  unfold tailWord_8030272
  simp only [CollatzResearch.WordTrace]
  refine ⟨146444040781851740057550535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195258721042468986743400713 146444040781851740057550535)
  ·
    refine ⟨219666061172777610086325803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146444040781851740057550535 219666061172777610086325803)
    ·
      refine ⟨329499091759166415129488705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219666061172777610086325803 329499091759166415129488705)
      ·
        refine ⟨247124318819374811347116529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329499091759166415129488705 247124318819374811347116529)
        ·
          refine ⟨185343239114531108510337397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247124318819374811347116529 185343239114531108510337397)
          ·
            refine ⟨17375928666987291422844131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185343239114531108510337397 17375928666987291422844131)
            ·
              refine ⟨26063893000480937134266197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17375928666987291422844131 26063893000480937134266197)
              ·
                refine ⟨152718123049692991021091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26063893000480937134266197 152718123049692991021091)
                ·
                  rfl

theorem cell23_8030272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_8030272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030272 prefixEnd_8030272 := by exact prefixLift 8030272
  have htrace : WordTrace (prefixWord ++ tailWord_8030272) baseStart_8030272 baseEnd_8030272 := by
    simpa [prefixWord, tailWord_8030272, baseEnd_8030272] using wordTrace_append hprefix tailTrace_8030272
  have hstable : (prefixWord ++ tailWord_8030272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030272).length < 2 ^ (prefixWord ++ tailWord_8030272).sum := by decide
  have hdescent : baseEnd_8030272 < baseStart_8030272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030286 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_8030286 : Nat := 118140960795 + 8030286 * 2 ^ 59
def prefixEnd_8030286 : Nat := 4983230072969 + 3 ^ 40 * 8030286 * 2
def baseEnd_8030286 : Nat := 4123396511070873702794393

theorem tailTrace_8030286 : CollatzResearch.WordTrace tailWord_8030286 prefixEnd_8030286 4123396511070873702794393 := by
  unfold tailWord_8030286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611074023206595063263839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195259061457101840337407141 36611074023206595063263839)
  ·
    refine ⟨54916611034809892594895759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36611074023206595063263839 54916611034809892594895759)
    ·
      refine ⟨82374916552214838892343639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54916611034809892594895759 82374916552214838892343639)
      ·
        refine ⟨123562374828322258338515459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82374916552214838892343639 123562374828322258338515459)
        ·
          refine ⟨185343562242483387507773189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123562374828322258338515459 185343562242483387507773189)
          ·
            refine ⟨34751917920465635157707473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185343562242483387507773189 34751917920465635157707473)
            ·
              refine ⟨26063938440349226368280605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34751917920465635157707473 26063938440349226368280605)
              ·
                refine ⟨9773976915130959888105227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26063938440349226368280605 9773976915130959888105227)
                ·
                  refine ⟨14660965372696439832157841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9773976915130959888105227 14660965372696439832157841)
                  ·
                    refine ⟨10995724029522329874118381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14660965372696439832157841 10995724029522329874118381)
                    ·
                      refine ⟨4123396511070873702794393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995724029522329874118381 4123396511070873702794393)
                      ·
                        rfl

theorem cell23_8030286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_8030286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030286 prefixEnd_8030286 := by exact prefixLift 8030286
  have htrace : WordTrace (prefixWord ++ tailWord_8030286) baseStart_8030286 baseEnd_8030286 := by
    simpa [prefixWord, tailWord_8030286, baseEnd_8030286] using wordTrace_append hprefix tailTrace_8030286
  have hstable : (prefixWord ++ tailWord_8030286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030286).length < 2 ^ (prefixWord ++ tailWord_8030286).sum := by decide
  have hdescent : baseEnd_8030286 < baseStart_8030286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030294 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_8030294 : Nat := 118140960795 + 8030294 * 2 ^ 59
def prefixEnd_8030294 : Nat := 4983230072969 + 3 ^ 40 * 8030294 * 2
def baseEnd_8030294 : Nat := 4123400618916109671494357

theorem tailTrace_8030294 : CollatzResearch.WordTrace tailWord_8030294 prefixEnd_8030294 4123400618916109671494357 := by
  unfold tailWord_8030294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305555248101486117025121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195259255979749185248267957 18305555248101486117025121)
  ·
    refine ⟨13729166436076114587768841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18305555248101486117025121 13729166436076114587768841)
    ·
      refine ⟨10296874827057085940826631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13729166436076114587768841 10296874827057085940826631)
      ·
        refine ⟨15445312240585628911239947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296874827057085940826631 15445312240585628911239947)
        ·
          refine ⟨23167968360878443366859921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15445312240585628911239947 23167968360878443366859921)
          ·
            refine ⟨17375976270658832525144941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23167968360878443366859921 17375976270658832525144941)
            ·
              refine ⟨6515991101497062196929353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17375976270658832525144941 6515991101497062196929353)
              ·
                refine ⟨4886993326122796647697015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515991101497062196929353 4886993326122796647697015)
                ·
                  refine ⟨7330489989184194971545523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886993326122796647697015 7330489989184194971545523)
                  ·
                    refine ⟨10995734983776292457318285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7330489989184194971545523 10995734983776292457318285)
                    ·
                      refine ⟨4123400618916109671494357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995734983776292457318285 4123400618916109671494357)
                      ·
                        rfl

theorem cell23_8030294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_8030294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030294 prefixEnd_8030294 := by exact prefixLift 8030294
  have htrace : WordTrace (prefixWord ++ tailWord_8030294) baseStart_8030294 baseEnd_8030294 := by
    simpa [prefixWord, tailWord_8030294, baseEnd_8030294] using wordTrace_append hprefix tailTrace_8030294
  have hstable : (prefixWord ++ tailWord_8030294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030294).length < 2 ^ (prefixWord ++ tailWord_8030294).sum := by decide
  have hdescent : baseEnd_8030294 < baseStart_8030294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030300 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_8030300 : Nat := 118140960795 + 8030300 * 2 ^ 59
def prefixEnd_8030300 : Nat := 4983230072969 + 3 ^ 40 * 8030300 * 2
def baseEnd_8030300 : Nat := 4123403699800036648019329

theorem tailTrace_8030300 : CollatzResearch.WordTrace tailWord_8030300 prefixEnd_8030300 4123403699800036648019329 := by
  unfold tailWord_8030300
  simp only [CollatzResearch.WordTrace]
  refine ⟨146444551403801020448560177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195259401871734693931413569 146444551403801020448560177)
  ·
    refine ⟨109833413552850765336420133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146444551403801020448560177 109833413552850765336420133)
    ·
      refine ⟨20593765041159518500578775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109833413552850765336420133 20593765041159518500578775)
      ·
        refine ⟨30890647561739277750868163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593765041159518500578775 30890647561739277750868163)
        ·
          refine ⟨46335971342608916626302245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890647561739277750868163 46335971342608916626302245)
          ·
            refine ⟨8687994626739171867431671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46335971342608916626302245 8687994626739171867431671)
            ·
              refine ⟨13031991940108757801147507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687994626739171867431671 13031991940108757801147507)
              ·
                refine ⟨19547987910163136701721261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13031991940108757801147507 19547987910163136701721261)
                ·
                  refine ⟨7330495466311176263145473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19547987910163136701721261 7330495466311176263145473)
                  ·
                    refine ⟨5497871599733382197359105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330495466311176263145473 5497871599733382197359105)
                    ·
                      refine ⟨4123403699800036648019329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497871599733382197359105 4123403699800036648019329)
                      ·
                        rfl

theorem cell23_8030300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_8030300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030300 prefixEnd_8030300 := by exact prefixLift 8030300
  have htrace : WordTrace (prefixWord ++ tailWord_8030300) baseStart_8030300 baseEnd_8030300 := by
    simpa [prefixWord, tailWord_8030300, baseEnd_8030300] using wordTrace_append hprefix tailTrace_8030300
  have hstable : (prefixWord ++ tailWord_8030300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030300).length < 2 ^ (prefixWord ++ tailWord_8030300).sum := by decide
  have hdescent : baseEnd_8030300 < baseStart_8030300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030306 : List Nat := [3, 3, 2, 2, 2, 1, 2, 8]
def baseStart_8030306 : Nat := 118140960795 + 8030306 * 2 ^ 59
def prefixEnd_8030306 : Nat := 4983230072969 + 3 ^ 40 * 8030306 * 2
def baseEnd_8030306 : Nat := 152718769654961615723863

theorem tailTrace_8030306 : CollatzResearch.WordTrace tailWord_8030306 prefixEnd_8030306 152718769654961615723863 := by
  unfold tailWord_8030306
  simp only [CollatzResearch.WordTrace]
  refine ⟨73222330411395075980459693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195259547763720202614559181 73222330411395075980459693)
  ·
    refine ⟨27458373904273153492672385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73222330411395075980459693 27458373904273153492672385)
    ·
      refine ⟨20593780428204865119504289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27458373904273153492672385 20593780428204865119504289)
      ·
        refine ⟨15445335321153648839628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20593780428204865119504289 15445335321153648839628217)
        ·
          refine ⟨11584001490865236629721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15445335321153648839628217 11584001490865236629721163)
          ·
            refine ⟨17376002236297854944581745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584001490865236629721163 17376002236297854944581745)
            ·
              refine ⟨13032001677223391208436309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376002236297854944581745 13032001677223391208436309)
              ·
                refine ⟨152718769654961615723863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13032001677223391208436309 152718769654961615723863)
                ·
                  rfl

theorem cell23_8030306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_8030306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030306 prefixEnd_8030306 := by exact prefixLift 8030306
  have htrace : WordTrace (prefixWord ++ tailWord_8030306) baseStart_8030306 baseEnd_8030306 := by
    simpa [prefixWord, tailWord_8030306, baseEnd_8030306] using wordTrace_append hprefix tailTrace_8030306
  have hstable : (prefixWord ++ tailWord_8030306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030306).length < 2 ^ (prefixWord ++ tailWord_8030306).sum := by decide
  have hdescent : baseEnd_8030306 < baseStart_8030306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030350 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_8030350 : Nat := 118140960795 + 8030350 * 2 ^ 59
def prefixEnd_8030350 : Nat := 4983230072969 + 3 ^ 40 * 8030350 * 2
def baseEnd_8030350 : Nat := 4123429373832761452394099

theorem tailTrace_8030350 : CollatzResearch.WordTrace tailWord_8030350 prefixEnd_8030350 4123429373832761452394099 := by
  unfold tailWord_8030350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611365807177612429555063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195260617638280599624293669 36611365807177612429555063)
  ·
    refine ⟨54917048710766418644332595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36611365807177612429555063 54917048710766418644332595)
    ·
      refine ⟨82375573066149627966498893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54917048710766418644332595 82375573066149627966498893)
      ·
        refine ⟨30890839899806110487437085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82375573066149627966498893 30890839899806110487437085)
        ·
          refine ⟨11584064962427291432788907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30890839899806110487437085 11584064962427291432788907)
          ·
            refine ⟨17376097443640937149183361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584064962427291432788907 17376097443640937149183361)
            ·
              refine ⟨13032073082730702861887521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376097443640937149183361 13032073082730702861887521)
              ·
                refine ⟨9774054812048027146415641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13032073082730702861887521 9774054812048027146415641)
                ·
                  refine ⟨7330541109036020359811731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9774054812048027146415641 7330541109036020359811731)
                  ·
                    refine ⟨10995811663554030539717597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7330541109036020359811731 10995811663554030539717597)
                    ·
                      refine ⟨4123429373832761452394099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10995811663554030539717597 4123429373832761452394099)
                      ·
                        rfl

theorem cell23_8030350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_8030350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030350 prefixEnd_8030350 := by exact prefixLift 8030350
  have htrace : WordTrace (prefixWord ++ tailWord_8030350) baseStart_8030350 baseEnd_8030350 := by
    simpa [prefixWord, tailWord_8030350, baseEnd_8030350] using wordTrace_append hprefix tailTrace_8030350
  have hstable : (prefixWord ++ tailWord_8030350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030350).length < 2 ^ (prefixWord ++ tailWord_8030350).sum := by decide
  have hdescent : baseEnd_8030350 < baseStart_8030350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030369 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8030369 : Nat := 118140960795 + 8030369 * 2 ^ 59
def prefixEnd_8030369 : Nat := 4983230072969 + 3 ^ 40 * 8030369 * 2
def baseEnd_8030369 : Nat := 4123439129965196878056511

theorem tailTrace_8030369 : CollatzResearch.WordTrace tailWord_8030369 prefixEnd_8030369 4123439129965196878056511 := by
  unfold tailWord_8030369
  simp only [CollatzResearch.WordTrace]
  refine ⟨292891619444352065681382161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195261079629568043787588107 292891619444352065681382161)
  ·
    refine ⟨219668714583264049261036621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292891619444352065681382161 219668714583264049261036621)
    ·
      refine ⟨82375767968724018472888733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219668714583264049261036621 82375767968724018472888733)
      ·
        refine ⟨30890912988271506927333275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82375767968724018472888733 30890912988271506927333275)
        ·
          refine ⟨46336369482407260390999913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890912988271506927333275 46336369482407260390999913)
          ·
            refine ⟨34752277111805445293249935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46336369482407260390999913 34752277111805445293249935)
            ·
              refine ⟨52128415667708167939874903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34752277111805445293249935 52128415667708167939874903)
              ·
                refine ⟨78192623501562251909812355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52128415667708167939874903 78192623501562251909812355)
                ·
                  refine ⟨117288935252343377864718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78192623501562251909812355 117288935252343377864718533)
                  ·
                    refine ⟨21991675359814383349634725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117288935252343377864718533 21991675359814383349634725)
                    ·
                      refine ⟨4123439129965196878056511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21991675359814383349634725 4123439129965196878056511)
                      ·
                        rfl

theorem cell23_8030369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8030369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030369 prefixEnd_8030369 := by exact prefixLift 8030369
  have htrace : WordTrace (prefixWord ++ tailWord_8030369) baseStart_8030369 baseEnd_8030369 := by
    simpa [prefixWord, tailWord_8030369, baseEnd_8030369] using wordTrace_append hprefix tailTrace_8030369
  have hstable : (prefixWord ++ tailWord_8030369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030369).length < 2 ^ (prefixWord ++ tailWord_8030369).sum := by decide
  have hdescent : baseEnd_8030369 < baseStart_8030369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030373 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_8030373 : Nat := 118140960795 + 8030373 * 2 ^ 59
def prefixEnd_8030373 : Nat := 4983230072969 + 3 ^ 40 * 8030373 * 2
def baseEnd_8030373 : Nat := 4123441183887814862406493

theorem tailTrace_8030373 : CollatzResearch.WordTrace tailWord_8030373 prefixEnd_8030373 4123441183887814862406493 := by
  unfold tailWord_8030373
  simp only [CollatzResearch.WordTrace]
  refine ⟨292891765336337574364527773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195261176890891716243018515 292891765336337574364527773)
  ·
    refine ⟨109834412001126590386697915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292891765336337574364527773 109834412001126590386697915)
    ·
      refine ⟨164751618001689885580046873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109834412001126590386697915 164751618001689885580046873)
      ·
        refine ⟨123563713501267414185035155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164751618001689885580046873 123563713501267414185035155)
        ·
          refine ⟨185345570251901121277552733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123563713501267414185035155 185345570251901121277552733)
          ·
            refine ⟨69504588844462920479082275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185345570251901121277552733 69504588844462920479082275)
            ·
              refine ⟨104256883266694380718623413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69504588844462920479082275 104256883266694380718623413)
              ·
                refine ⟨9774082806252598192370945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104256883266694380718623413 9774082806252598192370945)
                ·
                  refine ⟨7330562104689448644278209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9774082806252598192370945 7330562104689448644278209)
                  ·
                    refine ⟨5497921578517086483208657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330562104689448644278209 5497921578517086483208657)
                    ·
                      refine ⟨4123441183887814862406493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5497921578517086483208657 4123441183887814862406493)
                      ·
                        rfl

theorem cell23_8030373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_8030373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030373 prefixEnd_8030373 := by exact prefixLift 8030373
  have htrace : WordTrace (prefixWord ++ tailWord_8030373) baseStart_8030373 baseEnd_8030373 := by
    simpa [prefixWord, tailWord_8030373, baseEnd_8030373] using wordTrace_append hprefix tailTrace_8030373
  have hstable : (prefixWord ++ tailWord_8030373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030373).length < 2 ^ (prefixWord ++ tailWord_8030373).sum := by decide
  have hdescent : baseEnd_8030373 < baseStart_8030373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030446 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_8030446 : Nat := 118140960795 + 8030446 * 2 ^ 59
def prefixEnd_8030446 : Nat := 4983230072969 + 3 ^ 40 * 8030446 * 2
def baseEnd_8030446 : Nat := 4123478667975593076793657

theorem tailTrace_8030446 : CollatzResearch.WordTrace tailWord_8030446 prefixEnd_8030446 4123478667975593076793657 := by
  unfold tailWord_8030446
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611803483134138478991899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195262951910048738554623461 36611803483134138478991899)
  ·
    refine ⟨54917705224701207718487849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36611803483134138478991899 54917705224701207718487849)
    ·
      refine ⟨41188278918525905788865887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54917705224701207718487849 41188278918525905788865887)
      ·
        refine ⟨61782418377788858683298831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41188278918525905788865887 61782418377788858683298831)
        ·
          refine ⟨92673627566683288024948247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61782418377788858683298831 92673627566683288024948247)
          ·
            refine ⟨139010441350024932037422371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92673627566683288024948247 139010441350024932037422371)
            ·
              refine ⟨208515662025037398056133557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139010441350024932037422371 208515662025037398056133557)
              ·
                refine ⟨19548343314847256067762521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208515662025037398056133557 19548343314847256067762521)
                ·
                  refine ⟨14661257486135442050821891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19548343314847256067762521 14661257486135442050821891)
                  ·
                    refine ⟨21991886229203163076232837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14661257486135442050821891 21991886229203163076232837)
                    ·
                      refine ⟨4123478667975593076793657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21991886229203163076232837 4123478667975593076793657)
                      ·
                        rfl

theorem cell23_8030446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_8030446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030446 prefixEnd_8030446 := by exact prefixLift 8030446
  have htrace : WordTrace (prefixWord ++ tailWord_8030446) baseStart_8030446 baseEnd_8030446 := by
    simpa [prefixWord, tailWord_8030446, baseEnd_8030446] using wordTrace_append hprefix tailTrace_8030446
  have hstable : (prefixWord ++ tailWord_8030446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030446).length < 2 ^ (prefixWord ++ tailWord_8030446).sum := by decide
  have hdescent : baseEnd_8030446 < baseStart_8030446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030473 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_8030473 : Nat := 118140960795 + 8030473 * 2 ^ 59
def prefixEnd_8030473 : Nat := 4983230072969 + 3 ^ 40 * 8030473 * 2
def baseEnd_8030473 : Nat := 1374497510651088157052011

theorem tailTrace_8030473 : CollatzResearch.WordTrace tailWord_8030473 prefixEnd_8030473 1374497510651088157052011 := by
  unfold tailWord_8030473
  simp only [CollatzResearch.WordTrace]
  refine ⟨292895412635975291443168073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195263608423983527628778715 292895412635975291443168073)
  ·
    refine ⟨219671559476981468582376055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292895412635975291443168073 219671559476981468582376055)
    ·
      refine ⟨329507339215472202873564083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219671559476981468582376055 329507339215472202873564083)
      ·
        refine ⟨494261008823208304310346125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329507339215472202873564083 494261008823208304310346125)
        ·
          refine ⟨185347878308703114116379797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494261008823208304310346125 185347878308703114116379797)
          ·
            refine ⟨8688181795720458474205303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185347878308703114116379797 8688181795720458474205303)
            ·
              refine ⟨13032272693580687711307955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688181795720458474205303 13032272693580687711307955)
              ·
                refine ⟨19548409040371031566961933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13032272693580687711307955 19548409040371031566961933)
                ·
                  refine ⟨7330653390139136837610725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19548409040371031566961933 7330653390139136837610725)
                  ·
                    refine ⟨1374497510651088157052011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330653390139136837610725 1374497510651088157052011)
                    ·
                      rfl

theorem cell23_8030473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_8030473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030473 prefixEnd_8030473 := by exact prefixLift 8030473
  have htrace : WordTrace (prefixWord ++ tailWord_8030473) baseStart_8030473 baseEnd_8030473 := by
    simpa [prefixWord, tailWord_8030473, baseEnd_8030473] using wordTrace_append hprefix tailTrace_8030473
  have hstable : (prefixWord ++ tailWord_8030473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030473).length < 2 ^ (prefixWord ++ tailWord_8030473).sum := by decide
  have hdescent : baseEnd_8030473 < baseStart_8030473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030536 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_8030536 : Nat := 118140960795 + 8030536 * 2 ^ 59
def prefixEnd_8030536 : Nat := 4983230072969 + 3 ^ 40 * 8030536 * 2
def baseEnd_8030536 : Nat := 4123524881234497724668243

theorem tailTrace_8030536 : CollatzResearch.WordTrace tailWord_8030536 prefixEnd_8030536 4123524881234497724668243 := by
  unfold tailWord_8030536
  simp only [CollatzResearch.WordTrace]
  refine ⟨146448855217373526601355731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195265140289831368801807641 146448855217373526601355731)
  ·
    refine ⟨219673282826060289902033597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146448855217373526601355731 219673282826060289902033597)
    ·
      refine ⟨82377481059772608713262599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219673282826060289902033597 82377481059772608713262599)
      ·
        refine ⟨123566221589658913069893899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82377481059772608713262599 123566221589658913069893899)
        ·
          refine ⟨185349332384488369604840849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123566221589658913069893899 185349332384488369604840849)
          ·
            refine ⟨139011999288366277203630637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185349332384488369604840849 139011999288366277203630637)
            ·
              refine ⟨52129499733137353951361489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139011999288366277203630637 52129499733137353951361489)
              ·
                refine ⟨39097124799853015463521117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52129499733137353951361489 39097124799853015463521117)
                ·
                  refine ⟨14661421799944880798820419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39097124799853015463521117 14661421799944880798820419)
                  ·
                    refine ⟨21992132699917321198230629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14661421799944880798820419 21992132699917321198230629)
                    ·
                      refine ⟨4123524881234497724668243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21992132699917321198230629 4123524881234497724668243)
                      ·
                        rfl

theorem cell23_8030536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_8030536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030536 prefixEnd_8030536 := by exact prefixLift 8030536
  have htrace : WordTrace (prefixWord ++ tailWord_8030536) baseStart_8030536 baseEnd_8030536 := by
    simpa [prefixWord, tailWord_8030536, baseEnd_8030536] using wordTrace_append hprefix tailTrace_8030536
  have hstable : (prefixWord ++ tailWord_8030536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030536).length < 2 ^ (prefixWord ++ tailWord_8030536).sum := by decide
  have hdescent : baseEnd_8030536 < baseStart_8030536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030546 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_8030546 : Nat := 118140960795 + 8030546 * 2 ^ 59
def prefixEnd_8030546 : Nat := 4983230072969 + 3 ^ 40 * 8030546 * 2
def baseEnd_8030546 : Nat := 1374510005347014228514399

theorem tailTrace_8030546 : CollatzResearch.WordTrace tailWord_8030546 prefixEnd_8030546 1374510005347014228514399 := by
  unfold tailWord_8030546
  simp only [CollatzResearch.WordTrace]
  refine ⟨73224518791177706227643873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195265383443140549940383661 73224518791177706227643873)
  ·
    refine ⟨54918389093383279670732905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73224518791177706227643873 54918389093383279670732905)
    ·
      refine ⟨41188791820037459753049679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54918389093383279670732905 41188791820037459753049679)
      ·
        refine ⟨61783187730056189629574519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41188791820037459753049679 61783187730056189629574519)
        ·
          refine ⟨92674781595084284444361779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61783187730056189629574519 92674781595084284444361779)
          ·
            refine ⟨139012172392626426666542669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92674781595084284444361779 139012172392626426666542669)
            ·
              refine ⟨52129564647234909999953501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139012172392626426666542669 52129564647234909999953501)
              ·
                refine ⟨19548586742713091249982563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52129564647234909999953501 19548586742713091249982563)
                ·
                  refine ⟨29322880114069636874973845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19548586742713091249982563 29322880114069636874973845)
                  ·
                    refine ⟨1374510005347014228514399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29322880114069636874973845 1374510005347014228514399)
                    ·
                      rfl

theorem cell23_8030546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_8030546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030546 prefixEnd_8030546 := by exact prefixLift 8030546
  have htrace : WordTrace (prefixWord ++ tailWord_8030546) baseStart_8030546 baseEnd_8030546 := by
    simpa [prefixWord, tailWord_8030546, baseEnd_8030546] using wordTrace_append hprefix tailTrace_8030546
  have hstable : (prefixWord ++ tailWord_8030546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030546).length < 2 ^ (prefixWord ++ tailWord_8030546).sum := by decide
  have hdescent : baseEnd_8030546 < baseStart_8030546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030558 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_8030558 : Nat := 118140960795 + 8030558 * 2 ^ 59
def prefixEnd_8030558 : Nat := 4983230072969 + 3 ^ 40 * 8030558 * 2
def baseEnd_8030558 : Nat := 1374512059269632212864381

theorem tailTrace_8030558 : CollatzResearch.WordTrace tailWord_8030558 prefixEnd_8030558 1374512059269632212864381 := by
  unfold tailWord_8030558
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612314105083418870001541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195265675227111567306674885 36612314105083418870001541)
  ·
    refine ⟨6864808894703141038125289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36612314105083418870001541 6864808894703141038125289)
    ·
      refine ⟨5148606671027355778593967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6864808894703141038125289 5148606671027355778593967)
      ·
        refine ⟨7722910006541033667890951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148606671027355778593967 7722910006541033667890951)
        ·
          refine ⟨11584365009811550501836427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722910006541033667890951 11584365009811550501836427)
          ·
            refine ⟨17376547514717325752754641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584365009811550501836427 17376547514717325752754641)
            ·
              refine ⟨13032410636037994314565981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376547514717325752754641 13032410636037994314565981)
              ·
                refine ⟨4887153988514247867962243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032410636037994314565981 4887153988514247867962243)
                ·
                  refine ⟨7330730982771371801943365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887153988514247867962243 7330730982771371801943365)
                  ·
                    refine ⟨1374512059269632212864381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330730982771371801943365 1374512059269632212864381)
                    ·
                      rfl

theorem cell23_8030558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_8030558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030558 prefixEnd_8030558 := by exact prefixLift 8030558
  have htrace : WordTrace (prefixWord ++ tailWord_8030558) baseStart_8030558 baseEnd_8030558 := by
    simpa [prefixWord, tailWord_8030558, baseEnd_8030558] using wordTrace_append hprefix tailTrace_8030558
  have hstable : (prefixWord ++ tailWord_8030558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030558).length < 2 ^ (prefixWord ++ tailWord_8030558).sum := by decide
  have hdescent : baseEnd_8030558 < baseStart_8030558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030559 : List Nat := [1, 1, 2, 3, 1, 2, 2, 11]
def baseStart_8030559 : Nat := 118140960795 + 8030559 * 2 ^ 59
def prefixEnd_8030559 : Nat := 4983230072969 + 3 ^ 40 * 8030559 * 2
def baseEnd_8030559 : Nat := 152723581158872264247431

theorem tailTrace_8030559 : CollatzResearch.WordTrace tailWord_8030559 prefixEnd_8030559 152723581158872264247431 := by
  unfold tailWord_8030559
  simp only [CollatzResearch.WordTrace]
  refine ⟨292898549313663728130798731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195265699542442485420532487 292898549313663728130798731)
  ·
    refine ⟨439347823970495592196198097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292898549313663728130798731 439347823970495592196198097)
    ·
      refine ⟨329510867977871694147148573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439347823970495592196198097 329510867977871694147148573)
      ·
        refine ⟨123566575491701885305180715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329510867977871694147148573 123566575491701885305180715)
        ·
          refine ⟨185349863237552827957771073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123566575491701885305180715 185349863237552827957771073)
          ·
            refine ⟨139012397428164620968328305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185349863237552827957771073 139012397428164620968328305)
            ·
              refine ⟨104259298071123465726246229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139012397428164620968328305 104259298071123465726246229)
              ·
                refine ⟨152723581158872264247431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104259298071123465726246229 152723581158872264247431)
                ·
                  rfl

theorem cell23_8030559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 11].length) (baseStart_8030559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030559 prefixEnd_8030559 := by exact prefixLift 8030559
  have htrace : WordTrace (prefixWord ++ tailWord_8030559) baseStart_8030559 baseEnd_8030559 := by
    simpa [prefixWord, tailWord_8030559, baseEnd_8030559] using wordTrace_append hprefix tailTrace_8030559
  have hstable : (prefixWord ++ tailWord_8030559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030559).length < 2 ^ (prefixWord ++ tailWord_8030559).sum := by decide
  have hdescent : baseEnd_8030559 < baseStart_8030559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030570 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_8030570 : Nat := 118140960795 + 8030570 * 2 ^ 59
def prefixEnd_8030570 : Nat := 4983230072969 + 3 ^ 40 * 8030570 * 2
def baseEnd_8030570 : Nat := 4123542339576750591643087

theorem tailTrace_8030570 : CollatzResearch.WordTrace tailWord_8030570 prefixEnd_8030570 4123542339576750591643087 := by
  unfold tailWord_8030570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73224737629155969252362291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195265967011082584672966109 73224737629155969252362291)
  ·
    refine ⟨109837106443733953878543437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73224737629155969252362291 109837106443733953878543437)
    ·
      refine ⟨41188914916400232704453789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109837106443733953878543437 41188914916400232704453789)
      ·
        refine ⟨15445843093650087264170171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41188914916400232704453789 15445843093650087264170171)
        ·
          refine ⟨23168764640475130896255257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15445843093650087264170171 23168764640475130896255257)
          ·
            refine ⟨17376573480356348172191443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23168764640475130896255257 17376573480356348172191443)
            ·
              refine ⟨26064860220534522258287165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17376573480356348172191443 26064860220534522258287165)
              ·
                refine ⟨9774322582700445846857687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26064860220534522258287165 9774322582700445846857687)
                ·
                  refine ⟨14661483874050668770286531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9774322582700445846857687 14661483874050668770286531)
                  ·
                    refine ⟨21992225811076003155429797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14661483874050668770286531 21992225811076003155429797)
                    ·
                      refine ⟨4123542339576750591643087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21992225811076003155429797 4123542339576750591643087)
                      ·
                        rfl

theorem cell23_8030570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_8030570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030570 prefixEnd_8030570 := by exact prefixLift 8030570
  have htrace : WordTrace (prefixWord ++ tailWord_8030570) baseStart_8030570 baseEnd_8030570 := by
    simpa [prefixWord, tailWord_8030570, baseEnd_8030570] using wordTrace_append hprefix tailTrace_8030570
  have hstable : (prefixWord ++ tailWord_8030570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030570).length < 2 ^ (prefixWord ++ tailWord_8030570).sum := by decide
  have hdescent : baseEnd_8030570 < baseStart_8030570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030587 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 1, 2, 2]
def baseStart_8030587 : Nat := 118140960795 + 8030587 * 2 ^ 59
def prefixEnd_8030587 : Nat := 4983230072969 + 3 ^ 40 * 8030587 * 2
def baseEnd_8030587 : Nat := 4123551068747877025130509

theorem tailTrace_8030587 : CollatzResearch.WordTrace tailWord_8030587 prefixEnd_8030587 4123551068747877025130509 := by
  unfold tailWord_8030587
  simp only [CollatzResearch.WordTrace]
  refine ⟨292899570557562288912818015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195266380371708192608545343 292899570557562288912818015)
  ·
    refine ⟨439349355836343433369227023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292899570557562288912818015 439349355836343433369227023)
    ·
      refine ⟨659024033754515150053840535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439349355836343433369227023 659024033754515150053840535)
      ·
        refine ⟨988536050631772725080760803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659024033754515150053840535 988536050631772725080760803)
        ·
          refine ⟨1482804075947659087621141205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988536050631772725080760803 1482804075947659087621141205)
          ·
            refine ⟨34753220530023259866120497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1482804075947659087621141205 34753220530023259866120497)
            ·
              refine ⟨26064915397517444899590373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34753220530023259866120497 26064915397517444899590373)
              ·
                refine ⟨4887171637034520918673195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26064915397517444899590373 4887171637034520918673195)
                ·
                  refine ⟨7330757455551781378009793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887171637034520918673195 7330757455551781378009793)
                  ·
                    refine ⟨5498068091663836033507345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330757455551781378009793 5498068091663836033507345)
                    ·
                      refine ⟨4123551068747877025130509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498068091663836033507345 4123551068747877025130509)
                      ·
                        rfl

theorem cell23_8030587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 2, 2].length) (baseStart_8030587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030587 prefixEnd_8030587 := by exact prefixLift 8030587
  have htrace : WordTrace (prefixWord ++ tailWord_8030587) baseStart_8030587 baseEnd_8030587 := by
    simpa [prefixWord, tailWord_8030587, baseEnd_8030587] using wordTrace_append hprefix tailTrace_8030587
  have hstable : (prefixWord ++ tailWord_8030587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030587).length < 2 ^ (prefixWord ++ tailWord_8030587).sum := by decide
  have hdescent : baseEnd_8030587 < baseStart_8030587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030603 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3]
def baseStart_8030603 : Nat := 118140960795 + 8030603 * 2 ^ 59
def prefixEnd_8030603 : Nat := 4983230072969 + 3 ^ 40 * 8030603 * 2
def baseEnd_8030603 : Nat := 4123559284438348962530435

theorem tailTrace_8030603 : CollatzResearch.WordTrace tailWord_8030603 prefixEnd_8030603 4123559284438348962530435 := by
  unfold tailWord_8030603
  simp only [CollatzResearch.WordTrace]
  refine ⟨292900154125504323645400463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195266769417002882430266975 292900154125504323645400463)
  ·
    refine ⟨439350231188256485468100695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292900154125504323645400463 439350231188256485468100695)
    ·
      refine ⟨659025346782384728202151043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439350231188256485468100695 659025346782384728202151043)
      ·
        refine ⟨988538020173577092303226565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659025346782384728202151043 988538020173577092303226565)
        ·
          refine ⟨185350878782545704806854981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 988538020173577092303226565 185350878782545704806854981)
          ·
            refine ⟨34753289771727319651285309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185350878782545704806854981 34753289771727319651285309)
            ·
              refine ⟨13032483664397744869231991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34753289771727319651285309 13032483664397744869231991)
              ·
                refine ⟨19548725496596617303847987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13032483664397744869231991 19548725496596617303847987)
                ·
                  refine ⟨29323088244894925955771981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19548725496596617303847987 29323088244894925955771981)
                  ·
                    refine ⟨10996158091835597233414493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29323088244894925955771981 10996158091835597233414493)
                    ·
                      refine ⟨4123559284438348962530435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996158091835597233414493 4123559284438348962530435)
                      ·
                        rfl

theorem cell23_8030603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 3].length) (baseStart_8030603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030603 prefixEnd_8030603 := by exact prefixLift 8030603
  have htrace : WordTrace (prefixWord ++ tailWord_8030603) baseStart_8030603 baseEnd_8030603 := by
    simpa [prefixWord, tailWord_8030603, baseEnd_8030603] using wordTrace_append hprefix tailTrace_8030603
  have hstable : (prefixWord ++ tailWord_8030603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030603).length < 2 ^ (prefixWord ++ tailWord_8030603).sum := by decide
  have hdescent : baseEnd_8030603 < baseStart_8030603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030621 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_8030621 : Nat := 118140960795 + 8030621 * 2 ^ 59
def prefixEnd_8030621 : Nat := 4983230072969 + 3 ^ 40 * 8030621 * 2
def baseEnd_8030621 : Nat := 4123568527090129892105353

theorem tailTrace_8030621 : CollatzResearch.WordTrace tailWord_8030621 prefixEnd_8030621 4123568527090129892105353 := by
  unfold tailWord_8030621
  simp only [CollatzResearch.WordTrace]
  refine ⟨292900810639439112719555717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195267207092959408479703811 292900810639439112719555717)
  ·
    refine ⟨54918901994894833634916697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292900810639439112719555717 54918901994894833634916697)
    ·
      refine ⟨41189176496171125226187523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54918901994894833634916697 41189176496171125226187523)
      ·
        refine ⟨61783764744256687839281285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41189176496171125226187523 61783764744256687839281285)
        ·
          refine ⟨11584455889548128969865241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61783764744256687839281285 11584455889548128969865241)
          ·
            refine ⟨8688341917161096727398931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584455889548128969865241 8688341917161096727398931)
            ·
              refine ⟨13032512875741645091098397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688341917161096727398931 13032512875741645091098397)
              ·
                refine ⟨4887192328403116909161899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032512875741645091098397 4887192328403116909161899)
                ·
                  refine ⟨7330788492604675363742849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887192328403116909161899 7330788492604675363742849)
                  ·
                    refine ⟨5498091369453506522807137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7330788492604675363742849 5498091369453506522807137)
                    ·
                      refine ⟨4123568527090129892105353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498091369453506522807137 4123568527090129892105353)
                      ·
                        rfl

theorem cell23_8030621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_8030621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030621 prefixEnd_8030621 := by exact prefixLift 8030621
  have htrace : WordTrace (prefixWord ++ tailWord_8030621) baseStart_8030621 baseEnd_8030621 := by
    simpa [prefixWord, tailWord_8030621, baseEnd_8030621] using wordTrace_append hprefix tailTrace_8030621
  have hstable : (prefixWord ++ tailWord_8030621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030621).length < 2 ^ (prefixWord ++ tailWord_8030621).sum := by decide
  have hdescent : baseEnd_8030621 < baseStart_8030621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030656 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_8030656 : Nat := 118140960795 + 8030656 * 2 ^ 59
def prefixEnd_8030656 : Nat := 4983230072969 + 3 ^ 40 * 8030656 * 2
def baseEnd_8030656 : Nat := 4123586498913037255167691

theorem tailTrace_8030656 : CollatzResearch.WordTrace tailWord_8030656 prefixEnd_8030656 4123586498913037255167691 := by
  unfold tailWord_8030656
  simp only [CollatzResearch.WordTrace]
  refine ⟨146451043597156156848539911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195268058129541542464719881 146451043597156156848539911)
  ·
    refine ⟨219676565395734235272809867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146451043597156156848539911 219676565395734235272809867)
    ·
      refine ⟨329514848093601352909214801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219676565395734235272809867 329514848093601352909214801)
      ·
        refine ⟨247136136070201014681911101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329514848093601352909214801 247136136070201014681911101)
        ·
          refine ⟨92676051026325380505716663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247136136070201014681911101 92676051026325380505716663)
          ·
            refine ⟨139014076539488070758574995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92676051026325380505716663 139014076539488070758574995)
            ·
              refine ⟨208521114809232106137862493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139014076539488070758574995 208521114809232106137862493)
              ·
                refine ⟨78195418053462039801698435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208521114809232106137862493 78195418053462039801698435)
                ·
                  refine ⟨117293127080193059702547653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78195418053462039801698435 117293127080193059702547653)
                  ·
                    refine ⟨21992461327536198694227685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117293127080193059702547653 21992461327536198694227685)
                    ·
                      refine ⟨4123586498913037255167691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21992461327536198694227685 4123586498913037255167691)
                      ·
                        rfl

theorem cell23_8030656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_8030656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030656 prefixEnd_8030656 := by exact prefixLift 8030656
  have htrace : WordTrace (prefixWord ++ tailWord_8030656) baseStart_8030656 baseEnd_8030656 := by
    simpa [prefixWord, tailWord_8030656, baseEnd_8030656] using wordTrace_append hprefix tailTrace_8030656
  have hstable : (prefixWord ++ tailWord_8030656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030656).length < 2 ^ (prefixWord ++ tailWord_8030656).sum := by decide
  have hdescent : baseEnd_8030656 < baseStart_8030656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030666 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_8030666 : Nat := 118140960795 + 8030666 * 2 ^ 59
def prefixEnd_8030666 : Nat := 4983230072969 + 3 ^ 40 * 8030666 * 2
def baseEnd_8030666 : Nat := 458176848191064690671405

theorem tailTrace_8030666 : CollatzResearch.WordTrace tailWord_8030666 prefixEnd_8030666 458176848191064690671405 := by
  unfold tailWord_8030666
  simp only [CollatzResearch.WordTrace]
  refine ⟨73225612981069021351235963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195268301282850723603295901 73225612981069021351235963)
  ·
    refine ⟨109838419471603532026853945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73225612981069021351235963 109838419471603532026853945)
    ·
      refine ⟨82378814603702649020140459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109838419471603532026853945 82378814603702649020140459)
      ·
        refine ⟨123568221905553973530210689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82378814603702649020140459 123568221905553973530210689)
        ·
          refine ⟨92676166429165480147658017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123568221905553973530210689 92676166429165480147658017)
          ·
            refine ⟨69507124821874110110743513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92676166429165480147658017 69507124821874110110743513)
            ·
              refine ⟨52130343616405582583057635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69507124821874110110743513 52130343616405582583057635)
              ·
                refine ⟨78195515424608373874586453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52130343616405582583057635 78195515424608373874586453)
                ·
                  refine ⟨458176848191064690671405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78195515424608373874586453 458176848191064690671405)
                  ·
                    rfl

theorem cell23_8030666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_8030666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030666 prefixEnd_8030666 := by exact prefixLift 8030666
  have htrace : WordTrace (prefixWord ++ tailWord_8030666) baseStart_8030666 baseEnd_8030666 := by
    simpa [prefixWord, tailWord_8030666, baseEnd_8030666] using wordTrace_append hprefix tailTrace_8030666
  have hstable : (prefixWord ++ tailWord_8030666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030666).length < 2 ^ (prefixWord ++ tailWord_8030666).sum := by decide
  have hdescent : baseEnd_8030666 < baseStart_8030666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030710 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_8030710 : Nat := 118140960795 + 8030710 * 2 ^ 59
def prefixEnd_8030710 : Nat := 4983230072969 + 3 ^ 40 * 8030710 * 2
def baseEnd_8030710 : Nat := 4123614226868380043892443

theorem tailTrace_8030710 : CollatzResearch.WordTrace tailWord_8030710 prefixEnd_8030710 4123614226868380043892443 := by
  unfold tailWord_8030710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306503546007292557471599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195269371157411120613030389 18306503546007292557471599)
  ·
    refine ⟨27459755319010938836207399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306503546007292557471599 27459755319010938836207399)
    ·
      refine ⟨41189632978516408254311099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27459755319010938836207399 41189632978516408254311099)
      ·
        refine ⟨61784449467774612381466649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41189632978516408254311099 61784449467774612381466649)
        ·
          refine ⟨46338337100830959286099987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61784449467774612381466649 46338337100830959286099987)
          ·
            refine ⟨69507505651246438929149981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46338337100830959286099987 69507505651246438929149981)
            ·
              refine ⟨26065314619217414598431243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69507505651246438929149981 26065314619217414598431243)
              ·
                refine ⟨39097971928826121897646865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26065314619217414598431243 39097971928826121897646865)
                ·
                  refine ⟨29323478946619591423235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39097971928826121897646865 29323478946619591423235149)
                  ·
                    refine ⟨10996304604982346783713181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29323478946619591423235149 10996304604982346783713181)
                    ·
                      refine ⟨4123614226868380043892443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996304604982346783713181 4123614226868380043892443)
                      ·
                        rfl

theorem cell23_8030710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_8030710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030710 prefixEnd_8030710 := by exact prefixLift 8030710
  have htrace : WordTrace (prefixWord ++ tailWord_8030710) baseStart_8030710 baseEnd_8030710 := by
    simpa [prefixWord, tailWord_8030710, baseEnd_8030710] using wordTrace_append hprefix tailTrace_8030710
  have hstable : (prefixWord ++ tailWord_8030710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030710).length < 2 ^ (prefixWord ++ tailWord_8030710).sum := by decide
  have hdescent : baseEnd_8030710 < baseStart_8030710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030736 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_8030736 : Nat := 118140960795 + 8030736 * 2 ^ 59
def prefixEnd_8030736 : Nat := 4983230072969 + 3 ^ 40 * 8030736 * 2
def baseEnd_8030736 : Nat := 4123627577365396942167323

theorem tailTrace_8030736 : CollatzResearch.WordTrace tailWord_8030736 prefixEnd_8030736 4123627577365396942167323 := by
  unfold tailWord_8030736
  simp only [CollatzResearch.WordTrace]
  refine ⟨146452502517011243679996031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195270003356014991573328041 146452502517011243679996031)
  ·
    refine ⟨219678753775516865519994047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146452502517011243679996031 219678753775516865519994047)
    ·
      refine ⟨329518130663275298279991071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219678753775516865519994047 329518130663275298279991071)
      ·
        refine ⟨494277195994912947419986607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329518130663275298279991071 494277195994912947419986607)
        ·
          refine ⟨741415793992369421129979911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494277195994912947419986607 741415793992369421129979911)
          ·
            refine ⟨1112123690988554131694969867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741415793992369421129979911 1112123690988554131694969867)
            ·
              refine ⟨1668185536482831197542454801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112123690988554131694969867 1668185536482831197542454801)
              ·
                refine ⟨1251139152362123398156841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668185536482831197542454801 1251139152362123398156841101)
                ·
                  refine ⟨469177182135796274308815413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251139152362123398156841101 469177182135796274308815413)
                  ·
                    refine ⟨43985360825230900716451445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469177182135796274308815413 43985360825230900716451445)
                    ·
                      refine ⟨4123627577365396942167323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43985360825230900716451445 4123627577365396942167323)
                      ·
                        rfl

theorem cell23_8030736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_8030736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030736 prefixEnd_8030736 := by exact prefixLift 8030736
  have htrace : WordTrace (prefixWord ++ tailWord_8030736) baseStart_8030736 baseEnd_8030736 := by
    simpa [prefixWord, tailWord_8030736, baseEnd_8030736] using wordTrace_append hprefix tailTrace_8030736
  have hstable : (prefixWord ++ tailWord_8030736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030736).length < 2 ^ (prefixWord ++ tailWord_8030736).sum := by decide
  have hdescent : baseEnd_8030736 < baseStart_8030736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030783 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_8030783 : Nat := 118140960795 + 8030783 * 2 ^ 59
def prefixEnd_8030783 : Nat := 4983230072969 + 3 ^ 40 * 8030783 * 2
def baseEnd_8030783 : Nat := 4123651710956158258279607

theorem tailTrace_8030783 : CollatzResearch.WordTrace tailWord_8030783 prefixEnd_8030783 4123651710956158258279607 := by
  unfold tailWord_8030783
  simp only [CollatzResearch.WordTrace]
  refine ⟨292906719264852214386953003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195271146176568142924635335 292906719264852214386953003)
  ·
    refine ⟨439360078897278321580429505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292906719264852214386953003 439360078897278321580429505)
    ·
      refine ⟨329520059172958741185322129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439360078897278321580429505 329520059172958741185322129)
      ·
        refine ⟨247140044379719055888991597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329520059172958741185322129 247140044379719055888991597)
        ·
          refine ⟨92677516642394645958371849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247140044379719055888991597 92677516642394645958371849)
          ·
            refine ⟨69508137481795984468778887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92677516642394645958371849 69508137481795984468778887)
            ·
              refine ⟨104262206222693976703168331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69508137481795984468778887 104262206222693976703168331)
              ·
                refine ⟨156393309334040965054752497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104262206222693976703168331 156393309334040965054752497)
                ·
                  refine ⟨117294982000530723791064373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156393309334040965054752497 117294982000530723791064373)
                  ·
                    refine ⟨10996404562549755355412285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117294982000530723791064373 10996404562549755355412285)
                    ·
                      refine ⟨4123651710956158258279607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996404562549755355412285 4123651710956158258279607)
                      ·
                        rfl

theorem cell23_8030783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_8030783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030783 prefixEnd_8030783 := by exact prefixLift 8030783
  have htrace : WordTrace (prefixWord ++ tailWord_8030783) baseStart_8030783 baseEnd_8030783 := by
    simpa [prefixWord, tailWord_8030783, baseEnd_8030783] using wordTrace_append hprefix tailTrace_8030783
  have hstable : (prefixWord ++ tailWord_8030783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030783).length < 2 ^ (prefixWord ++ tailWord_8030783).sum := by decide
  have hdescent : baseEnd_8030783 < baseStart_8030783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030794 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_8030794 : Nat := 118140960795 + 8030794 * 2 ^ 59
def prefixEnd_8030794 : Nat := 4983230072969 + 3 ^ 40 * 8030794 * 2
def baseEnd_8030794 : Nat := 1374552453081119238414019

theorem tailTrace_8030794 : CollatzResearch.WordTrace tailWord_8030794 prefixEnd_8030794 1374552453081119238414019 := by
  unfold tailWord_8030794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73226780116953090816400859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195271413645208242177068957 73226780116953090816400859)
  ·
    refine ⟨109840170175429636224601289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73226780116953090816400859 109840170175429636224601289)
    ·
      refine ⟨82380127631572227168450967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109840170175429636224601289 82380127631572227168450967)
      ·
        refine ⟨123570191447358340752676451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82380127631572227168450967 123570191447358340752676451)
        ·
          refine ⟨185355287171037511129014677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123570191447358340752676451 185355287171037511129014677)
          ·
            refine ⟨8688529086142383334172563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185355287171037511129014677 8688529086142383334172563)
            ·
              refine ⟨13032793629213575001258845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688529086142383334172563 13032793629213575001258845)
              ·
                refine ⟨4887297610955090625472067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032793629213575001258845 4887297610955090625472067)
                ·
                  refine ⟨7330946416432635938208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887297610955090625472067 7330946416432635938208101)
                  ·
                    refine ⟨1374552453081119238414019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330946416432635938208101 1374552453081119238414019)
                    ·
                      rfl

theorem cell23_8030794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_8030794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030794 prefixEnd_8030794 := by exact prefixLift 8030794
  have htrace : WordTrace (prefixWord ++ tailWord_8030794) baseStart_8030794 baseEnd_8030794 := by
    simpa [prefixWord, tailWord_8030794, baseEnd_8030794] using wordTrace_append hprefix tailTrace_8030794
  have hstable : (prefixWord ++ tailWord_8030794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030794).length < 2 ^ (prefixWord ++ tailWord_8030794).sum := by decide
  have hdescent : baseEnd_8030794 < baseStart_8030794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030817 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_8030817 : Nat := 118140960795 + 8030817 * 2 ^ 59
def prefixEnd_8030817 : Nat := 4983230072969 + 3 ^ 40 * 8030817 * 2
def baseEnd_8030817 : Nat := 4123669169298411125254451

theorem tailTrace_8030817 : CollatzResearch.WordTrace tailWord_8030817 prefixEnd_8030817 4123669169298411125254451 := by
  unfold tailWord_8030817
  simp only [CollatzResearch.WordTrace]
  refine ⟨292907959346729038193690705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195271972897819358795793803 292907959346729038193690705)
  ·
    refine ⟨219680969510046778645268029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292907959346729038193690705 219680969510046778645268029)
    ·
      refine ⟨82380363566267541991975511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219680969510046778645268029 82380363566267541991975511)
      ·
        refine ⟨123570545349401312987963267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82380363566267541991975511 123570545349401312987963267)
        ·
          refine ⟨185355818024101969481944901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123570545349401312987963267 185355818024101969481944901)
          ·
            refine ⟨34754215879519119277864669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185355818024101969481944901 34754215879519119277864669)
            ·
              refine ⟨13032830954819669729199251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34754215879519119277864669 13032830954819669729199251)
              ·
                refine ⟨19549246432229504593798877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13032830954819669729199251 19549246432229504593798877)
                ·
                  refine ⟨7330967412086064222674579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19549246432229504593798877 7330967412086064222674579)
                  ·
                    refine ⟨10996451118129096334011869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7330967412086064222674579 10996451118129096334011869)
                    ·
                      refine ⟨4123669169298411125254451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996451118129096334011869 4123669169298411125254451)
                      ·
                        rfl

theorem cell23_8030817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_8030817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030817 prefixEnd_8030817 := by exact prefixLift 8030817
  have htrace : WordTrace (prefixWord ++ tailWord_8030817) baseStart_8030817 baseEnd_8030817 := by
    simpa [prefixWord, tailWord_8030817, baseEnd_8030817] using wordTrace_append hprefix tailTrace_8030817
  have hstable : (prefixWord ++ tailWord_8030817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030817).length < 2 ^ (prefixWord ++ tailWord_8030817).sum := by decide
  have hdescent : baseEnd_8030817 < baseStart_8030817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030823 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_8030823 : Nat := 118140960795 + 8030823 * 2 ^ 59
def prefixEnd_8030823 : Nat := 4983230072969 + 3 ^ 40 * 8030823 * 2
def baseEnd_8030823 : Nat := 4123672250182338101779423

theorem tailTrace_8030823 : CollatzResearch.WordTrace tailWord_8030823 prefixEnd_8030823 4123672250182338101779423 := by
  unfold tailWord_8030823
  simp only [CollatzResearch.WordTrace]
  refine ⟨292908178184707301218409123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195272118789804867478939415 292908178184707301218409123)
  ·
    refine ⟨439362267277060951827613685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292908178184707301218409123 439362267277060951827613685)
    ·
      refine ⟨41190212557224464233838783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439362267277060951827613685 41190212557224464233838783)
      ·
        refine ⟨61785318835836696350758175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41190212557224464233838783 61785318835836696350758175)
        ·
          refine ⟨92677978253755044526137263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61785318835836696350758175 92677978253755044526137263)
          ·
            refine ⟨139016967380632566789205895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92677978253755044526137263 139016967380632566789205895)
            ·
              refine ⟨208525451070948850183808843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139016967380632566789205895 208525451070948850183808843)
              ·
                refine ⟨312788176606423275275713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208525451070948850183808843 312788176606423275275713265)
                ·
                  refine ⟨234591132454817456456784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312788176606423275275713265 234591132454817456456784949)
                  ·
                    refine ⟨21992918667639136542823589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234591132454817456456784949 21992918667639136542823589)
                    ·
                      refine ⟨4123672250182338101779423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21992918667639136542823589 4123672250182338101779423)
                      ·
                        rfl

theorem cell23_8030823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_8030823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030823 prefixEnd_8030823 := by exact prefixLift 8030823
  have htrace : WordTrace (prefixWord ++ tailWord_8030823) baseStart_8030823 baseEnd_8030823 := by
    simpa [prefixWord, tailWord_8030823, baseEnd_8030823] using wordTrace_append hprefix tailTrace_8030823
  have hstable : (prefixWord ++ tailWord_8030823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030823).length < 2 ^ (prefixWord ++ tailWord_8030823).sum := by decide
  have hdescent : baseEnd_8030823 < baseStart_8030823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030824 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 6]
def baseStart_8030824 : Nat := 118140960795 + 8030824 * 2 ^ 59
def prefixEnd_8030824 : Nat := 4983230072969 + 3 ^ 40 * 8030824 * 2
def baseEnd_8030824 : Nat := 458185862629221399762991

theorem tailTrace_8030824 : CollatzResearch.WordTrace tailWord_8030824 prefixEnd_8030824 458185862629221399762991 := by
  unfold tailWord_8030824
  simp only [CollatzResearch.WordTrace]
  refine ⟨146454107328851839194597763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195272143105135785592797017 146454107328851839194597763)
  ·
    refine ⟨219681160993277758791896645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146454107328851839194597763 219681160993277758791896645)
    ·
      refine ⟨41190217686239579773480621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219681160993277758791896645 41190217686239579773480621)
      ·
        refine ⟨15446331632339842415055233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41190217686239579773480621 15446331632339842415055233)
        ·
          refine ⟨11584748724254881811291425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15446331632339842415055233 11584748724254881811291425)
          ·
            refine ⟨8688561543191161358468569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584748724254881811291425 8688561543191161358468569)
            ·
              refine ⟨6516421157393371018851427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688561543191161358468569 6516421157393371018851427)
              ·
                refine ⟨9774631736090056528277141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516421157393371018851427 9774631736090056528277141)
                ·
                  refine ⟨458185862629221399762991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9774631736090056528277141 458185862629221399762991)
                  ·
                    rfl

theorem cell23_8030824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_8030824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030824 prefixEnd_8030824 := by exact prefixLift 8030824
  have htrace : WordTrace (prefixWord ++ tailWord_8030824) baseStart_8030824 baseEnd_8030824 := by
    simpa [prefixWord, tailWord_8030824, baseEnd_8030824] using wordTrace_append hprefix tailTrace_8030824
  have hstable : (prefixWord ++ tailWord_8030824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030824).length < 2 ^ (prefixWord ++ tailWord_8030824).sum := by decide
  have hdescent : baseEnd_8030824 < baseStart_8030824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030837 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_8030837 : Nat := 118140960795 + 8030837 * 2 ^ 59
def prefixEnd_8030837 : Nat := 4983230072969 + 3 ^ 40 * 8030837 * 2
def baseEnd_8030837 : Nat := 1374559812970500349001453

theorem tailTrace_8030837 : CollatzResearch.WordTrace tailWord_8030837 prefixEnd_8030837 1374559812970500349001453 := by
  unfold tailWord_8030837
  simp only [CollatzResearch.WordTrace]
  refine ⟨292908688806656581609418765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195272459204437721072945843 292908688806656581609418765)
  ·
    refine ⟨109840758302496218103532037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292908688806656581609418765 109840758302496218103532037)
    ·
      refine ⟨20595142181718040894412257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109840758302496218103532037 20595142181718040894412257)
      ·
        refine ⟨15446356636288530670809193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20595142181718040894412257 15446356636288530670809193)
        ·
          refine ⟨11584767477216398003106895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15446356636288530670809193 11584767477216398003106895)
          ·
            refine ⟨17377151215824597004660343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584767477216398003106895 17377151215824597004660343)
            ·
              refine ⟨26065726823736895506990515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377151215824597004660343 26065726823736895506990515)
              ·
                refine ⟨39098590235605343260485773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26065726823736895506990515 39098590235605343260485773)
                ·
                  refine ⟨14661971338352003722682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39098590235605343260485773 14661971338352003722682165)
                  ·
                    refine ⟨1374559812970500349001453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14661971338352003722682165 1374559812970500349001453)
                    ·
                      rfl

theorem cell23_8030837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_8030837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030837 prefixEnd_8030837 := by exact prefixLift 8030837
  have htrace : WordTrace (prefixWord ++ tailWord_8030837) baseStart_8030837 baseEnd_8030837 := by
    simpa [prefixWord, tailWord_8030837, baseEnd_8030837] using wordTrace_append hprefix tailTrace_8030837
  have hstable : (prefixWord ++ tailWord_8030837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030837).length < 2 ^ (prefixWord ++ tailWord_8030837).sum := by decide
  have hdescent : baseEnd_8030837 < baseStart_8030837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030868 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_8030868 : Nat := 118140960795 + 8030868 * 2 ^ 59
def prefixEnd_8030868 : Nat := 4983230072969 + 3 ^ 40 * 8030868 * 2
def baseEnd_8030868 : Nat := 4123695356811790425716717

theorem tailTrace_8030868 : CollatzResearch.WordTrace tailWord_8030868 prefixEnd_8030868 4123695356811790425716717 := by
  unfold tailWord_8030868
  simp only [CollatzResearch.WordTrace]
  refine ⟨146454909734772136951898629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195273212979696182602531505 146454909734772136951898629)
  ·
    refine ⟨27460295575269775678480993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146454909734772136951898629 27460295575269775678480993)
    ·
      refine ⟨20595221681452331758860745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27460295575269775678480993 20595221681452331758860745)
      ·
        refine ⟨15446416261089248819145559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20595221681452331758860745 15446416261089248819145559)
        ·
          refine ⟨23169624391633873228718339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446416261089248819145559 23169624391633873228718339)
          ·
            refine ⟨34754436587450809843077509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23169624391633873228718339 34754436587450809843077509)
            ·
              refine ⟨6516456860147026845577033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34754436587450809843077509 6516456860147026845577033)
              ·
                refine ⟨4887342645110270134182775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516456860147026845577033 4887342645110270134182775)
                ·
                  refine ⟨7331013967665405201274163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887342645110270134182775 7331013967665405201274163)
                  ·
                    refine ⟨10996520951498107801911245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331013967665405201274163 10996520951498107801911245)
                    ·
                      refine ⟨4123695356811790425716717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996520951498107801911245 4123695356811790425716717)
                      ·
                        rfl

theorem cell23_8030868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_8030868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030868 prefixEnd_8030868 := by exact prefixLift 8030868
  have htrace : WordTrace (prefixWord ++ tailWord_8030868) baseStart_8030868 baseEnd_8030868 := by
    simpa [prefixWord, tailWord_8030868, baseEnd_8030868] using wordTrace_append hprefix tailTrace_8030868
  have hstable : (prefixWord ++ tailWord_8030868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030868).length < 2 ^ (prefixWord ++ tailWord_8030868).sum := by decide
  have hdescent : baseEnd_8030868 < baseStart_8030868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030894 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_8030894 : Nat := 118140960795 + 8030894 * 2 ^ 59
def prefixEnd_8030894 : Nat := 4983230072969 + 3 ^ 40 * 8030894 * 2
def baseEnd_8030894 : Nat := 4123708707308807323991597

theorem tailTrace_8030894 : CollatzResearch.WordTrace tailWord_8030894 prefixEnd_8030894 4123708707308807323991597 := by
  unfold tailWord_8030894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36613845970931260043030467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195273845178300053562829157 36613845970931260043030467)
  ·
    refine ⟨54920768956396890064545701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36613845970931260043030467 54920768956396890064545701)
    ·
      refine ⟨10297644179324416887102319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54920768956396890064545701 10297644179324416887102319)
      ·
        refine ⟨15446466268986625330653479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10297644179324416887102319 15446466268986625330653479)
        ·
          refine ⟨23169699403479937995980219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446466268986625330653479 23169699403479937995980219)
          ·
            refine ⟨34754549105219906993970329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23169699403479937995980219 34754549105219906993970329)
            ·
              refine ⟨26065911828914930245477747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34754549105219906993970329 26065911828914930245477747)
              ·
                refine ⟨39098867743372395368216621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26065911828914930245477747 39098867743372395368216621)
                ·
                  refine ⟨14662075403764648263081233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39098867743372395368216621 14662075403764648263081233)
                  ·
                    refine ⟨10996556552823486197310925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14662075403764648263081233 10996556552823486197310925)
                    ·
                      refine ⟨4123708707308807323991597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996556552823486197310925 4123708707308807323991597)
                      ·
                        rfl

theorem cell23_8030894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_8030894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030894 prefixEnd_8030894 := by exact prefixLift 8030894
  have htrace : WordTrace (prefixWord ++ tailWord_8030894) baseStart_8030894 baseEnd_8030894 := by
    simpa [prefixWord, tailWord_8030894, baseEnd_8030894] using wordTrace_append hprefix tailTrace_8030894
  have hstable : (prefixWord ++ tailWord_8030894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030894).length < 2 ^ (prefixWord ++ tailWord_8030894).sum := by decide
  have hdescent : baseEnd_8030894 < baseStart_8030894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030924 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_8030924 : Nat := 118140960795 + 8030924 * 2 ^ 59
def prefixEnd_8030924 : Nat := 4983230072969 + 3 ^ 40 * 8030924 * 2
def baseEnd_8030924 : Nat := 4123724111728442206616459

theorem tailTrace_8030924 : CollatzResearch.WordTrace tailWord_8030924 prefixEnd_8030924 4123724111728442206616459 := by
  unfold tailWord_8030924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146455930978670697733917913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195274574638227596978557217 146455930978670697733917913)
  ·
    refine ⟨109841948234003023300438435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146455930978670697733917913 109841948234003023300438435)
    ·
      refine ⟨164762922351004534950657653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109841948234003023300438435 164762922351004534950657653)
      ·
        refine ⟨15446523970406675151624155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164762922351004534950657653 15446523970406675151624155)
        ·
          refine ⟨23169785955610012727436233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446523970406675151624155 23169785955610012727436233)
          ·
            refine ⟨17377339466707509545577175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23169785955610012727436233 17377339466707509545577175)
            ·
              refine ⟨26066009200061264318365763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377339466707509545577175 26066009200061264318365763)
              ·
                refine ⟨39099013800091896477548645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26066009200061264318365763 39099013800091896477548645)
                ·
                  refine ⟨7331065087517230589540371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39099013800091896477548645 7331065087517230589540371)
                  ·
                    refine ⟨10996597631275845884310557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331065087517230589540371 10996597631275845884310557)
                    ·
                      refine ⟨4123724111728442206616459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996597631275845884310557 4123724111728442206616459)
                      ·
                        rfl

theorem cell23_8030924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_8030924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030924 prefixEnd_8030924 := by exact prefixLift 8030924
  have htrace : WordTrace (prefixWord ++ tailWord_8030924) baseStart_8030924 baseEnd_8030924 := by
    simpa [prefixWord, tailWord_8030924, baseEnd_8030924] using wordTrace_append hprefix tailTrace_8030924
  have hstable : (prefixWord ++ tailWord_8030924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030924).length < 2 ^ (prefixWord ++ tailWord_8030924).sum := by decide
  have hdescent : baseEnd_8030924 < baseStart_8030924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8030980 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_8030980 : Nat := 118140960795 + 8030980 * 2 ^ 59
def prefixEnd_8030980 : Nat := 4983230072969 + 3 ^ 40 * 8030980 * 2
def baseEnd_8030980 : Nat := 4123752866645093987516201

theorem tailTrace_8030980 : CollatzResearch.WordTrace tailWord_8030980 prefixEnd_8030980 4123752866645093987516201 := by
  unfold tailWord_8030980
  simp only [CollatzResearch.WordTrace]
  refine ⟨146456952222569258515937197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195275936296759011354582929 146456952222569258515937197)
  ·
    refine ⟨54921357083463471943476449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146456952222569258515937197 54921357083463471943476449)
    ·
      refine ⟨41191017812597603957607337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54921357083463471943476449 41191017812597603957607337)
      ·
        refine ⟨30893263359448202968205503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41191017812597603957607337 30893263359448202968205503)
        ·
          refine ⟨46339895039172304452308255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30893263359448202968205503 46339895039172304452308255)
          ·
            refine ⟨69509842558758456678462383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46339895039172304452308255 69509842558758456678462383)
            ·
              refine ⟨104264763838137685017693575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69509842558758456678462383 104264763838137685017693575)
              ·
                refine ⟨156397145757206527526540363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104264763838137685017693575 156397145757206527526540363)
                ·
                  refine ⟨234595718635809791289810545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156397145757206527526540363 234595718635809791289810545)
                  ·
                    refine ⟨175946788976857343467357909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234595718635809791289810545 175946788976857343467357909)
                    ·
                      refine ⟨4123752866645093987516201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175946788976857343467357909 4123752866645093987516201)
                      ·
                        rfl

theorem cell23_8030980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_8030980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8030980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8030980 prefixEnd_8030980 := by exact prefixLift 8030980
  have htrace : WordTrace (prefixWord ++ tailWord_8030980) baseStart_8030980 baseEnd_8030980 := by
    simpa [prefixWord, tailWord_8030980, baseEnd_8030980] using wordTrace_append hprefix tailTrace_8030980
  have hstable : (prefixWord ++ tailWord_8030980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8030980).length < 2 ^ (prefixWord ++ tailWord_8030980).sum := by decide
  have hdescent : baseEnd_8030980 < baseStart_8030980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8030980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031000 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_8031000 : Nat := 118140960795 + 8031000 * 2 ^ 59
def prefixEnd_8031000 : Nat := 4983230072969 + 3 ^ 40 * 8031000 * 2
def baseEnd_8031000 : Nat := 1374587712086061303088703

theorem tailTrace_8031000 : CollatzResearch.WordTrace tailWord_8031000 prefixEnd_8031000 1374587712086061303088703 := by
  unfold tailWord_8031000
  simp only [CollatzResearch.WordTrace]
  refine ⟨146457316952533030223801227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195276422603377373631734969 146457316952533030223801227)
  ·
    refine ⟨219685975428799545335701841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146457316952533030223801227 219685975428799545335701841)
    ·
      refine ⟨164764481571599659001776381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219685975428799545335701841 164764481571599659001776381)
      ·
        refine ⟨61786680589349872125666143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164764481571599659001776381 61786680589349872125666143)
        ·
          refine ⟨92680020884024808188499215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61786680589349872125666143 92680020884024808188499215)
          ·
            refine ⟨139020031326037212282748823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92680020884024808188499215 139020031326037212282748823)
            ·
              refine ⟨208530046989055818424123235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139020031326037212282748823 208530046989055818424123235)
              ·
                refine ⟨312795070483583727636184853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208530046989055818424123235 312795070483583727636184853)
                ·
                  refine ⟨14662268928917987232946165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312795070483583727636184853 14662268928917987232946165)
                  ·
                    refine ⟨1374587712086061303088703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14662268928917987232946165 1374587712086061303088703)
                    ·
                      rfl

theorem cell23_8031000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_8031000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031000 prefixEnd_8031000 := by exact prefixLift 8031000
  have htrace : WordTrace (prefixWord ++ tailWord_8031000) baseStart_8031000 baseEnd_8031000 := by
    simpa [prefixWord, tailWord_8031000, baseEnd_8031000] using wordTrace_append hprefix tailTrace_8031000
  have hstable : (prefixWord ++ tailWord_8031000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031000).length < 2 ^ (prefixWord ++ tailWord_8031000).sum := by decide
  have hdescent : baseEnd_8031000 < baseStart_8031000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031038 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_8031038 : Nat := 118140960795 + 8031038 * 2 ^ 59
def prefixEnd_8031038 : Nat := 4983230072969 + 3 ^ 40 * 8031038 * 2
def baseEnd_8031038 : Nat := 458198072058117195621215

theorem tailTrace_8031038 : CollatzResearch.WordTrace tailWord_8031038 prefixEnd_8031038 458198072058117195621215 := by
  unfold tailWord_8031038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614502484866049117185721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195277346585952261958323845 36614502484866049117185721)
  ·
    refine ⟨27460876863649536837889291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36614502484866049117185721 27460876863649536837889291)
    ·
      refine ⟨41191315295474305256833937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27460876863649536837889291 41191315295474305256833937)
      ·
        refine ⟨30893486471605728942625453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41191315295474305256833937 30893486471605728942625453)
        ·
          refine ⟨11585057426852148353484545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30893486471605728942625453 11585057426852148353484545)
          ·
            refine ⟨8688793070139111265113409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11585057426852148353484545 8688793070139111265113409)
            ·
              refine ⟨6516594802604333448835057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688793070139111265113409 6516594802604333448835057)
              ·
                refine ⟨4887446101953250086626293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516594802604333448835057 4887446101953250086626293)
                ·
                  refine ⟨458198072058117195621215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4887446101953250086626293 458198072058117195621215)
                  ·
                    rfl

theorem cell23_8031038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_8031038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031038 prefixEnd_8031038 := by exact prefixLift 8031038
  have htrace : WordTrace (prefixWord ++ tailWord_8031038) baseStart_8031038 baseEnd_8031038 := by
    simpa [prefixWord, tailWord_8031038, baseEnd_8031038] using wordTrace_append hprefix tailTrace_8031038
  have hstable : (prefixWord ++ tailWord_8031038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031038).length < 2 ^ (prefixWord ++ tailWord_8031038).sum := by decide
  have hdescent : baseEnd_8031038 < baseStart_8031038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031047 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 3, 4]
def baseStart_8031047 : Nat := 118140960795 + 8031047 * 2 ^ 59
def prefixEnd_8031047 : Nat := 4983230072969 + 3 ^ 40 * 8031047 * 2
def baseEnd_8031047 : Nat := 1374595756616315075126131

theorem tailTrace_8031047 : CollatzResearch.WordTrace tailWord_8031047 prefixEnd_8031047 1374595756616315075126131 := by
  unfold tailWord_8031047
  simp only [CollatzResearch.WordTrace]
  refine ⟨292916348135895787474563395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195277565423930524983042263 292916348135895787474563395)
  ·
    refine ⟨439374522203843681211845093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292916348135895787474563395 439374522203843681211845093)
    ·
      refine ⟨82382722913220690227220955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439374522203843681211845093 82382722913220690227220955)
      ·
        refine ⟨123574084369831035340831433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82382722913220690227220955 123574084369831035340831433)
        ·
          refine ⟨92680563277373276505623575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123574084369831035340831433 92680563277373276505623575)
          ·
            refine ⟨139020844916059914758435363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92680563277373276505623575 139020844916059914758435363)
            ·
              refine ⟨208531267374089872137653045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139020844916059914758435363 208531267374089872137653045)
              ·
                refine ⟨19549806316320925512904973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208531267374089872137653045 19549806316320925512904973)
                ·
                  refine ⟨7331177368620347067339365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19549806316320925512904973 7331177368620347067339365)
                  ·
                    refine ⟨1374595756616315075126131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7331177368620347067339365 1374595756616315075126131)
                    ·
                      rfl

theorem cell23_8031047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_8031047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031047 prefixEnd_8031047 := by exact prefixLift 8031047
  have htrace : WordTrace (prefixWord ++ tailWord_8031047) baseStart_8031047 baseEnd_8031047 := by
    simpa [prefixWord, tailWord_8031047, baseEnd_8031047] using wordTrace_append hprefix tailTrace_8031047
  have hstable : (prefixWord ++ tailWord_8031047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031047).length < 2 ^ (prefixWord ++ tailWord_8031047).sum := by decide
  have hdescent : baseEnd_8031047 < baseStart_8031047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031050 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_8031050 : Nat := 118140960795 + 8031050 * 2 ^ 59
def prefixEnd_8031050 : Nat := 4983230072969 + 3 ^ 40 * 8031050 * 2
def baseEnd_8031050 : Nat := 4123788810290908713640879

theorem tailTrace_8031050 : CollatzResearch.WordTrace tailWord_8031050 prefixEnd_8031050 4123788810290908713640879 := by
  unfold tailWord_8031050
  simp only [CollatzResearch.WordTrace]
  refine ⟨73229114388721229746730651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195277638369923279324615069 73229114388721229746730651)
  ·
    refine ⟨109843671583081844620095977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73229114388721229746730651 109843671583081844620095977)
    ·
      refine ⟨82382753687311383465071983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109843671583081844620095977 82382753687311383465071983)
      ·
        refine ⟨123574130530967075197607975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82382753687311383465071983 123574130530967075197607975)
        ·
          refine ⟨185361195796450612796411963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123574130530967075197607975 185361195796450612796411963)
          ·
            refine ⟨278041793694675919194617945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185361195796450612796411963 278041793694675919194617945)
            ·
              refine ⟨208531345271006939395963459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278041793694675919194617945 208531345271006939395963459)
              ·
                refine ⟨312797017906510409093945189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208531345271006939395963459 312797017906510409093945189)
                ·
                  refine ⟨58649440857470701705114723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312797017906510409093945189 58649440857470701705114723)
                  ·
                    refine ⟨87974161286206052557672085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58649440857470701705114723 87974161286206052557672085)
                    ·
                      refine ⟨4123788810290908713640879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87974161286206052557672085 4123788810290908713640879)
                      ·
                        rfl

theorem cell23_8031050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_8031050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031050 prefixEnd_8031050 := by exact prefixLift 8031050
  have htrace : WordTrace (prefixWord ++ tailWord_8031050) baseStart_8031050 baseEnd_8031050 := by
    simpa [prefixWord, tailWord_8031050, baseEnd_8031050] using wordTrace_append hprefix tailTrace_8031050
  have hstable : (prefixWord ++ tailWord_8031050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031050).length < 2 ^ (prefixWord ++ tailWord_8031050).sum := by decide
  have hdescent : baseEnd_8031050 < baseStart_8031050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031094 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_8031094 : Nat := 118140960795 + 8031094 * 2 ^ 59
def prefixEnd_8031094 : Nat := 4983230072969 + 3 ^ 40 * 8031094 * 2
def baseEnd_8031094 : Nat := 458201267048856282387853

theorem tailTrace_8031094 : CollatzResearch.WordTrace tailWord_8031094 prefixEnd_8031094 458201267048856282387853 := by
  unfold tailWord_8031094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18307378897920344656345271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195278708244483676334349557 18307378897920344656345271)
  ·
    refine ⟨27461068346880516984517907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18307378897920344656345271 27461068346880516984517907)
    ·
      refine ⟨41191602520320775476776861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27461068346880516984517907 41191602520320775476776861)
      ·
        refine ⟨15446850945120290803791323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41191602520320775476776861 15446850945120290803791323)
        ·
          refine ⟨23170276417680436205686985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446850945120290803791323 23170276417680436205686985)
          ·
            refine ⟨17377707313260327154265239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23170276417680436205686985 17377707313260327154265239)
            ·
              refine ⟨26066560969890490731397859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17377707313260327154265239 26066560969890490731397859)
              ·
                refine ⟨39099841454835736097096789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26066560969890490731397859 39099841454835736097096789)
                ·
                  refine ⟨458201267048856282387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39099841454835736097096789 458201267048856282387853)
                  ·
                    rfl

theorem cell23_8031094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_8031094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031094 prefixEnd_8031094 := by exact prefixLift 8031094
  have htrace : WordTrace (prefixWord ++ tailWord_8031094) baseStart_8031094 baseEnd_8031094 := by
    simpa [prefixWord, tailWord_8031094, baseEnd_8031094] using wordTrace_append hprefix tailTrace_8031094
  have hstable : (prefixWord ++ tailWord_8031094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031094).length < 2 ^ (prefixWord ++ tailWord_8031094).sum := by decide
  have hdescent : baseEnd_8031094 < baseStart_8031094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031157 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_8031157 : Nat := 118140960795 + 8031157 * 2 ^ 59
def prefixEnd_8031157 : Nat := 4983230072969 + 3 ^ 40 * 8031157 * 2
def baseEnd_8031157 : Nat := 4123843752720939795002887

theorem tailTrace_8031157 : CollatzResearch.WordTrace tailWord_8031157 prefixEnd_8031157 4123843752720939795002887 := by
  unfold tailWord_8031157
  simp only [CollatzResearch.WordTrace]
  refine ⟨292920360165497276261067725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195280240110331517507378483 292920360165497276261067725)
  ·
    refine ⟨109845135062061478597900397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292920360165497276261067725 109845135062061478597900397)
    ·
      refine ⟨41191925648273054474212649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109845135062061478597900397 41191925648273054474212649)
      ·
        refine ⟨30893944236204790855659487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41191925648273054474212649 30893944236204790855659487)
        ·
          refine ⟨46340916354307186283489231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30893944236204790855659487 46340916354307186283489231)
          ·
            refine ⟨69511374531460779425233847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46340916354307186283489231 69511374531460779425233847)
            ·
              refine ⟨104267061797191169137850771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69511374531460779425233847 104267061797191169137850771)
              ·
                refine ⟨156400592695786753706776157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104267061797191169137850771 156400592695786753706776157)
                ·
                  refine ⟨58650222260920032640041059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156400592695786753706776157 58650222260920032640041059)
                  ·
                    refine ⟨87975333391380048960061589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58650222260920032640041059 87975333391380048960061589)
                    ·
                      refine ⟨4123843752720939795002887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87975333391380048960061589 4123843752720939795002887)
                      ·
                        rfl

theorem cell23_8031157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_8031157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031157 prefixEnd_8031157 := by exact prefixLift 8031157
  have htrace : WordTrace (prefixWord ++ tailWord_8031157) baseStart_8031157 baseEnd_8031157 := by
    simpa [prefixWord, tailWord_8031157, baseEnd_8031157] using wordTrace_append hprefix tailTrace_8031157
  have hstable : (prefixWord ++ tailWord_8031157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031157).length < 2 ^ (prefixWord ++ tailWord_8031157).sum := by decide
  have hdescent : baseEnd_8031157 < baseStart_8031157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031194 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_8031194 : Nat := 118140960795 + 8031194 * 2 ^ 59
def prefixEnd_8031194 : Nat := 4983230072969 + 3 ^ 40 * 8031194 * 2
def baseEnd_8031194 : Nat := 4123862751505156150240217

theorem tailTrace_8031194 : CollatzResearch.WordTrace tailWord_8031194 prefixEnd_8031194 4123862751505156150240217 := by
  unfold tailWord_8031194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73230427416590807895041159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195281139777575487720109757 73230427416590807895041159)
  ·
    refine ⟨109845641124886211842561739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73230427416590807895041159 109845641124886211842561739)
    ·
      refine ⟨164768461687329317763842609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109845641124886211842561739 164768461687329317763842609)
      ·
        refine ⟨123576346265496988322881957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164768461687329317763842609 123576346265496988322881957)
        ·
          refine ⟨23170564924780685310540367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123576346265496988322881957 23170564924780685310540367)
          ·
            refine ⟨34755847387171027965810551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23170564924780685310540367 34755847387171027965810551)
            ·
              refine ⟨52133771080756541948715827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34755847387171027965810551 52133771080756541948715827)
              ·
                refine ⟨78200656621134812923073741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52133771080756541948715827 78200656621134812923073741)
                ·
                  refine ⟨29325246232925554846152653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78200656621134812923073741 29325246232925554846152653)
                  ·
                    refine ⟨10996967337347083067307245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29325246232925554846152653 10996967337347083067307245)
                    ·
                      refine ⟨4123862751505156150240217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10996967337347083067307245 4123862751505156150240217)
                      ·
                        rfl

theorem cell23_8031194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_8031194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031194 prefixEnd_8031194 := by exact prefixLift 8031194
  have htrace : WordTrace (prefixWord ++ tailWord_8031194) baseStart_8031194 baseEnd_8031194 := by
    simpa [prefixWord, tailWord_8031194, baseEnd_8031194] using wordTrace_append hprefix tailTrace_8031194
  have hstable : (prefixWord ++ tailWord_8031194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031194).length < 2 ^ (prefixWord ++ tailWord_8031194).sum := by decide
  have hdescent : baseEnd_8031194 < baseStart_8031194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031218 : List Nat := [3, 2, 1, 5, 2, 1, 1, 8]
def baseStart_8031218 : Nat := 118140960795 + 8031218 * 2 ^ 59
def prefixEnd_8031218 : Nat := 4983230072969 + 3 ^ 40 * 8031218 * 2
def baseEnd_8031218 : Nat := 152736113890402372457041

theorem tailTrace_8031218 : CollatzResearch.WordTrace tailWord_8031218 prefixEnd_8031218 152736113890402372457041 := by
  unfold tailWord_8031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73230646254569070919759577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195281723345517522452692205 73230646254569070919759577)
  ·
    refine ⟨54922984690926803189819683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73230646254569070919759577 54922984690926803189819683)
    ·
      refine ⟨82384477036390204784729525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54922984690926803189819683 82384477036390204784729525)
      ·
        refine ⟨7723544722161581698568393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82384477036390204784729525 7723544722161581698568393)
        ·
          refine ⟨5792658541621186273926295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7723544722161581698568393 5792658541621186273926295)
          ·
            refine ⟨8688987812431779410889443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792658541621186273926295 8688987812431779410889443)
            ·
              refine ⟨13033481718647669116334165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688987812431779410889443 13033481718647669116334165)
              ·
                refine ⟨152736113890402372457041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13033481718647669116334165 152736113890402372457041)
                ·
                  rfl

theorem cell23_8031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_8031218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031218 prefixEnd_8031218 := by exact prefixLift 8031218
  have htrace : WordTrace (prefixWord ++ tailWord_8031218) baseStart_8031218 baseEnd_8031218 := by
    simpa [prefixWord, tailWord_8031218, baseEnd_8031218] using wordTrace_append hprefix tailTrace_8031218
  have hstable : (prefixWord ++ tailWord_8031218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031218).length < 2 ^ (prefixWord ++ tailWord_8031218).sum := by decide
  have hdescent : baseEnd_8031218 < baseStart_8031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031251 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 4, 2, 2]
def baseStart_8031251 : Nat := 118140960795 + 8031251 * 2 ^ 59
def prefixEnd_8031251 : Nat := 4983230072969 + 3 ^ 40 * 8031251 * 2
def baseEnd_8031251 : Nat := 4123892019902462427227455

theorem tailTrace_8031251 : CollatzResearch.WordTrace tailWord_8031251 prefixEnd_8031251 4123892019902462427227455 := by
  unfold tailWord_8031251
  simp only [CollatzResearch.WordTrace]
  refine ⟨292923788627156730314989607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195282525751437820209993071 292923788627156730314989607)
  ·
    refine ⟨439385682940735095472484411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292923788627156730314989607 439385682940735095472484411)
    ·
      refine ⟨659078524411102643208726617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439385682940735095472484411 659078524411102643208726617)
      ·
        refine ⟨494308893308326982406544963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659078524411102643208726617 494308893308326982406544963)
        ·
          refine ⟨741463339962490473609817445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494308893308326982406544963 741463339962490473609817445)
          ·
            refine ⟨139024376242966963801840771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741463339962490473609817445 139024376242966963801840771)
            ·
              refine ⟨208536564364450445702761157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139024376242966963801840771 208536564364450445702761157)
              ·
                refine ⟨39100605818334458569267717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208536564364450445702761157 39100605818334458569267717)
                ·
                  refine ⟨7331363590937710981737697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39100605818334458569267717 7331363590937710981737697)
                  ·
                    refine ⟨5498522693203283236303273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331363590937710981737697 5498522693203283236303273)
                    ·
                      refine ⟨4123892019902462427227455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498522693203283236303273 4123892019902462427227455)
                      ·
                        rfl

theorem cell23_8031251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2, 2].length) (baseStart_8031251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031251 prefixEnd_8031251 := by exact prefixLift 8031251
  have htrace : WordTrace (prefixWord ++ tailWord_8031251) baseStart_8031251 baseEnd_8031251 := by
    simpa [prefixWord, tailWord_8031251, baseEnd_8031251] using wordTrace_append hprefix tailTrace_8031251
  have hstable : (prefixWord ++ tailWord_8031251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031251).length < 2 ^ (prefixWord ++ tailWord_8031251).sum := by decide
  have hdescent : baseEnd_8031251 < baseStart_8031251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031255 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_8031255 : Nat := 118140960795 + 8031255 * 2 ^ 59
def prefixEnd_8031255 : Nat := 4983230072969 + 3 ^ 40 * 8031255 * 2
def baseEnd_8031255 : Nat := 4123894073825080411577437

theorem tailTrace_8031255 : CollatzResearch.WordTrace tailWord_8031255 prefixEnd_8031255 4123894073825080411577437 := by
  unfold tailWord_8031255
  simp only [CollatzResearch.WordTrace]
  refine ⟨292923934519142238998135219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195282623012761492665423479 292923934519142238998135219)
  ·
    refine ⟨439385901778713358497202829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292923934519142238998135219 439385901778713358497202829)
    ·
      refine ⟨164769713167017509436451061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439385901778713358497202829 164769713167017509436451061)
      ·
        refine ⟨15447160609407891509667287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164769713167017509436451061 15447160609407891509667287)
        ·
          refine ⟨23170740914111837264500931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447160609407891509667287 23170740914111837264500931)
          ·
            refine ⟨34756111371167755896751397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23170740914111837264500931 34756111371167755896751397)
            ·
              refine ⟨6516770882093954230640887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34756111371167755896751397 6516770882093954230640887)
              ·
                refine ⟨9775156323140931345961331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516770882093954230640887 9775156323140931345961331)
                ·
                  refine ⟨14662734484711397018941997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9775156323140931345961331 14662734484711397018941997)
                  ·
                    refine ⟨5498525431766773882103249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14662734484711397018941997 5498525431766773882103249)
                    ·
                      refine ⟨4123894073825080411577437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498525431766773882103249 4123894073825080411577437)
                      ·
                        rfl

theorem cell23_8031255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_8031255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031255 prefixEnd_8031255 := by exact prefixLift 8031255
  have htrace : WordTrace (prefixWord ++ tailWord_8031255) baseStart_8031255 baseEnd_8031255 := by
    simpa [prefixWord, tailWord_8031255, baseEnd_8031255] using wordTrace_append hprefix tailTrace_8031255
  have hstable : (prefixWord ++ tailWord_8031255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031255).length < 2 ^ (prefixWord ++ tailWord_8031255).sum := by decide
  have hdescent : baseEnd_8031255 < baseStart_8031255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031304 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_8031304 : Nat := 118140960795 + 8031304 * 2 ^ 59
def prefixEnd_8031304 : Nat := 4983230072969 + 3 ^ 40 * 8031304 * 2
def baseEnd_8031304 : Nat := 1374639744792383573288237

theorem tailTrace_8031304 : CollatzResearch.WordTrace tailWord_8031304 prefixEnd_8031304 1374639744792383573288237 := by
  unfold tailWord_8031304
  simp only [CollatzResearch.WordTrace]
  refine ⟨146462860847982360183334483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195283814463976480244445977 146462860847982360183334483)
  ·
    refine ⟨219694291271973540275001725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146462860847982360183334483 219694291271973540275001725)
    ·
      refine ⟨82385359226990077603125647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219694291271973540275001725 82385359226990077603125647)
      ·
        refine ⟨123578038840485116404688471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82385359226990077603125647 123578038840485116404688471)
        ·
          refine ⟨185367058260727674607032707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123578038840485116404688471 185367058260727674607032707)
          ·
            refine ⟨278050587391091511910549061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185367058260727674607032707 278050587391091511910549061)
            ·
              refine ⟨52134485135829658483227949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278050587391091511910549061 52134485135829658483227949)
              ·
                refine ⟨19550431925936121931210481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52134485135829658483227949 19550431925936121931210481)
                ·
                  refine ⟨14662823944452091448407861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19550431925936121931210481 14662823944452091448407861)
                  ·
                    refine ⟨1374639744792383573288237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14662823944452091448407861 1374639744792383573288237)
                    ·
                      rfl

theorem cell23_8031304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_8031304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031304 prefixEnd_8031304 := by exact prefixLift 8031304
  have htrace : WordTrace (prefixWord ++ tailWord_8031304) baseStart_8031304 baseEnd_8031304 := by
    simpa [prefixWord, tailWord_8031304, baseEnd_8031304] using wordTrace_append hprefix tailTrace_8031304
  have hstable : (prefixWord ++ tailWord_8031304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031304).length < 2 ^ (prefixWord ++ tailWord_8031304).sum := by decide
  have hdescent : baseEnd_8031304 < baseStart_8031304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031325 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 7]
def baseStart_8031325 : Nat := 118140960795 + 8031325 * 2 ^ 59
def prefixEnd_8031325 : Nat := 4983230072969 + 3 ^ 40 * 8031325 * 2
def baseEnd_8031325 : Nat := 458214446385655015300235

theorem tailTrace_8031325 : CollatzResearch.WordTrace tailWord_8031325 prefixEnd_8031325 458214446385655015300235 := by
  unfold tailWord_8031325
  simp only [CollatzResearch.WordTrace]
  refine ⟨292926487628888640953183429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195284325085925760635455619 292926487628888640953183429)
  ·
    refine ⟨54923716430416620178721893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292926487628888640953183429 54923716430416620178721893)
    ·
      refine ⟨10298196830703116283510355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54923716430416620178721893 10298196830703116283510355)
      ·
        refine ⟨15447295246054674425265533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298196830703116283510355 15447295246054674425265533)
        ·
          refine ⟨5792735717270502909474575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15447295246054674425265533 5792735717270502909474575)
          ·
            refine ⟨8689103575905754364211863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792735717270502909474575 8689103575905754364211863)
            ·
              refine ⟨13033655363858631546317795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689103575905754364211863 13033655363858631546317795)
              ·
                refine ⟨19550483045787947319476693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033655363858631546317795 19550483045787947319476693)
                ·
                  refine ⟨458214446385655015300235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19550483045787947319476693 458214446385655015300235)
                  ·
                    rfl

theorem cell23_8031325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_8031325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031325 prefixEnd_8031325 := by exact prefixLift 8031325
  have htrace : WordTrace (prefixWord ++ tailWord_8031325) baseStart_8031325 baseEnd_8031325 := by
    simpa [prefixWord, tailWord_8031325, baseEnd_8031325] using wordTrace_append hprefix tailTrace_8031325
  have hstable : (prefixWord ++ tailWord_8031325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031325).length < 2 ^ (prefixWord ++ tailWord_8031325).sum := by decide
  have hdescent : baseEnd_8031325 < baseStart_8031325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031336 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8031336 : Nat := 118140960795 + 8031336 * 2 ^ 59
def prefixEnd_8031336 : Nat := 4983230072969 + 3 ^ 40 * 8031336 * 2
def baseEnd_8031336 : Nat := 4123935665758094594664565

theorem tailTrace_8031336 : CollatzResearch.WordTrace tailWord_8031336 prefixEnd_8031336 4123935665758094594664565 := by
  unfold tailWord_8031336
  simp only [CollatzResearch.WordTrace]
  refine ⟨146463444415924394915916931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195284592554565859887889241 146463444415924394915916931)
  ·
    refine ⟨219695166623886592373875397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146463444415924394915916931 219695166623886592373875397)
    ·
      refine ⟨41192843741978736070101637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219695166623886592373875397 41192843741978736070101637)
      ·
        refine ⟨7723658201621013013144057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41192843741978736070101637 7723658201621013013144057)
        ·
          refine ⟨5792743651215759759858043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7723658201621013013144057 5792743651215759759858043)
          ·
            refine ⟨8689115476823639639787065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792743651215759759858043 8689115476823639639787065)
            ·
              refine ⟨6516836607617729729840299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689115476823639639787065 6516836607617729729840299)
              ·
                refine ⟨9775254911426594594760449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516836607617729729840299 9775254911426594594760449)
                ·
                  refine ⟨7331441183569945946070337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775254911426594594760449 7331441183569945946070337)
                  ·
                    refine ⟨5498580887677459459552753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331441183569945946070337 5498580887677459459552753)
                    ·
                      refine ⟨4123935665758094594664565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498580887677459459552753 4123935665758094594664565)
                      ·
                        rfl

theorem cell23_8031336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8031336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031336 prefixEnd_8031336 := by exact prefixLift 8031336
  have htrace : WordTrace (prefixWord ++ tailWord_8031336) baseStart_8031336 baseEnd_8031336 := by
    simpa [prefixWord, tailWord_8031336, baseEnd_8031336] using wordTrace_append hprefix tailTrace_8031336
  have hstable : (prefixWord ++ tailWord_8031336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031336).length < 2 ^ (prefixWord ++ tailWord_8031336).sum := by decide
  have hdescent : baseEnd_8031336 < baseStart_8031336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031378 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_8031378 : Nat := 118140960795 + 8031378 * 2 ^ 59
def prefixEnd_8031378 : Nat := 4983230072969 + 3 ^ 40 * 8031378 * 2
def baseEnd_8031378 : Nat := 4123957231945583430339371

theorem tailTrace_8031378 : CollatzResearch.WordTrace tailWord_8031378 prefixEnd_8031378 4123957231945583430339371 := by
  unfold tailWord_8031378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73232105174424157751215697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195285613798464420669908525 73232105174424157751215697)
  ·
    refine ⟨54924078880818118313411773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73232105174424157751215697 54924078880818118313411773)
    ·
      refine ⟨20596529580306794367529415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54924078880818118313411773 20596529580306794367529415)
      ·
        refine ⟨30894794370460191551294123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20596529580306794367529415 30894794370460191551294123)
        ·
          refine ⟨46342191555690287326941185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30894794370460191551294123 46342191555690287326941185)
          ·
            refine ⟨34756643666767715495205889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46342191555690287326941185 34756643666767715495205889)
            ·
              refine ⟨26067482750075786621404417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34756643666767715495205889 26067482750075786621404417)
              ·
                refine ⟨19550612062556839966053313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26067482750075786621404417 19550612062556839966053313)
                ·
                  refine ⟨14662959046917629974539985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19550612062556839966053313 14662959046917629974539985)
                  ·
                    refine ⟨10997219285188222480904989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14662959046917629974539985 10997219285188222480904989)
                    ·
                      refine ⟨4123957231945583430339371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997219285188222480904989 4123957231945583430339371)
                      ·
                        rfl

theorem cell23_8031378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_8031378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031378 prefixEnd_8031378 := by exact prefixLift 8031378
  have htrace : WordTrace (prefixWord ++ tailWord_8031378) baseStart_8031378 baseEnd_8031378 := by
    simpa [prefixWord, tailWord_8031378, baseEnd_8031378] using wordTrace_append hprefix tailTrace_8031378
  have hstable : (prefixWord ++ tailWord_8031378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031378).length < 2 ^ (prefixWord ++ tailWord_8031378).sum := by decide
  have hdescent : baseEnd_8031378 < baseStart_8031378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031431 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_8031431 : Nat := 118140960795 + 8031431 * 2 ^ 59
def prefixEnd_8031431 : Nat := 4983230072969 + 3 ^ 40 * 8031431 * 2
def baseEnd_8031431 : Nat := 4123984446420271722976627

theorem tailTrace_8031431 : CollatzResearch.WordTrace tailWord_8031431 prefixEnd_8031431 4123984446420271722976627 := by
  unfold tailWord_8031431
  simp only [CollatzResearch.WordTrace]
  refine ⟨292930353766504621056542147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195286902511003080704361431 292930353766504621056542147)
  ·
    refine ⟨439395530649756931584813221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292930353766504621056542147 439395530649756931584813221)
    ·
      refine ⟨82386661996829424672152479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439395530649756931584813221 82386661996829424672152479)
      ·
        refine ⟨123579992995244137008228719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82386661996829424672152479 123579992995244137008228719)
        ·
          refine ⟨185369989492866205512343079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123579992995244137008228719 185369989492866205512343079)
          ·
            refine ⟨278054984239299308268514619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185369989492866205512343079 278054984239299308268514619)
            ·
              refine ⟨417082476358948962402771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278054984239299308268514619 417082476358948962402771929)
              ·
                refine ⟨312811857269211721802078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417082476358948962402771929 312811857269211721802078947)
                ·
                  refine ⟨469217785903817582703118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312811857269211721802078947 469217785903817582703118421)
                  ·
                    refine ⟨5498645928560362297302169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 469217785903817582703118421 5498645928560362297302169)
                    ·
                      refine ⟨4123984446420271722976627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498645928560362297302169 4123984446420271722976627)
                      ·
                        rfl

theorem cell23_8031431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_8031431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031431 prefixEnd_8031431 := by exact prefixLift 8031431
  have htrace : WordTrace (prefixWord ++ tailWord_8031431) baseStart_8031431 baseEnd_8031431 := by
    simpa [prefixWord, tailWord_8031431, baseEnd_8031431] using wordTrace_append hprefix tailTrace_8031431
  have hstable : (prefixWord ++ tailWord_8031431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031431).length < 2 ^ (prefixWord ++ tailWord_8031431).sum := by decide
  have hdescent : baseEnd_8031431 < baseStart_8031431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031468 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_8031468 : Nat := 118140960795 + 8031468 * 2 ^ 59
def prefixEnd_8031468 : Nat := 4983230072969 + 3 ^ 40 * 8031468 * 2
def baseEnd_8031468 : Nat := 4124003445204488078213957

theorem tailTrace_8031468 : CollatzResearch.WordTrace tailWord_8031468 prefixEnd_8031468 4124003445204488078213957 := by
  unfold tailWord_8031468
  simp only [CollatzResearch.WordTrace]
  refine ⟨146465851633685288187819529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195287802178247050917092705 146465851633685288187819529)
  ·
    refine ⟨109849388725263966140864647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146465851633685288187819529 109849388725263966140864647)
    ·
      refine ⟨164774083087895949211296971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109849388725263966140864647 164774083087895949211296971)
      ·
        refine ⟨247161124631843923816945457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164774083087895949211296971 247161124631843923816945457)
        ·
          refine ⟨185370843473882942862709093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247161124631843923816945457 185370843473882942862709093)
          ·
            refine ⟨34757033151353051786757955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185370843473882942862709093 34757033151353051786757955)
            ·
              refine ⟨52135549727029577680136933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34757033151353051786757955 52135549727029577680136933)
              ·
                refine ⟨9775415573818045815025675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52135549727029577680136933 9775415573818045815025675)
                ·
                  refine ⟨14663123360727068722538513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9775415573818045815025675 14663123360727068722538513)
                  ·
                    refine ⟨10997342520545301541903885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14663123360727068722538513 10997342520545301541903885)
                    ·
                      refine ⟨4124003445204488078213957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997342520545301541903885 4124003445204488078213957)
                      ·
                        rfl

theorem cell23_8031468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_8031468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031468 prefixEnd_8031468 := by exact prefixLift 8031468
  have htrace : WordTrace (prefixWord ++ tailWord_8031468) baseStart_8031468 baseEnd_8031468 := by
    simpa [prefixWord, tailWord_8031468, baseEnd_8031468] using wordTrace_append hprefix tailTrace_8031468
  have hstable : (prefixWord ++ tailWord_8031468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031468).length < 2 ^ (prefixWord ++ tailWord_8031468).sum := by decide
  have hdescent : baseEnd_8031468 < baseStart_8031468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031471 : List Nat := [1, 1, 2, 1, 7, 1, 1, 9]
def baseStart_8031471 : Nat := 118140960795 + 8031471 * 2 ^ 59
def prefixEnd_8031471 : Nat := 4983230072969 + 3 ^ 40 * 8031471 * 2
def baseEnd_8031471 : Nat := 152740925394313020980609

theorem tailTrace_8031471 : CollatzResearch.WordTrace tailWord_8031471 prefixEnd_8031471 152740925394313020980609 := by
  unfold tailWord_8031471
  simp only [CollatzResearch.WordTrace]
  refine ⟨292931812686359707887998267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195287875124239805258665511 292931812686359707887998267)
  ·
    refine ⟨439397719029539561831997401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292931812686359707887998267 439397719029539561831997401)
    ·
      refine ⟨329548289272154671373998051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439397719029539561831997401 329548289272154671373998051)
      ·
        refine ⟨494322433908232007060997077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329548289272154671373998051 494322433908232007060997077)
        ·
          refine ⟨11585682044724187665492119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 494322433908232007060997077 11585682044724187665492119)
          ·
            refine ⟨17378523067086281498238179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585682044724187665492119 17378523067086281498238179)
            ·
              refine ⟨26067784600629422247357269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17378523067086281498238179 26067784600629422247357269)
              ·
                refine ⟨152740925394313020980609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26067784600629422247357269 152740925394313020980609)
                ·
                  rfl

theorem cell23_8031471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 9].length) (baseStart_8031471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031471 prefixEnd_8031471 := by exact prefixLift 8031471
  have htrace : WordTrace (prefixWord ++ tailWord_8031471) baseStart_8031471 baseEnd_8031471 := by
    simpa [prefixWord, tailWord_8031471, baseEnd_8031471] using wordTrace_append hprefix tailTrace_8031471
  have hstable : (prefixWord ++ tailWord_8031471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031471).length < 2 ^ (prefixWord ++ tailWord_8031471).sum := by decide
  have hdescent : baseEnd_8031471 < baseStart_8031471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031481 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_8031481 : Nat := 118140960795 + 8031481 * 2 ^ 59
def prefixEnd_8031481 : Nat := 4983230072969 + 3 ^ 40 * 8031481 * 2
def baseEnd_8031481 : Nat := 4124010120452996527351397

theorem tailTrace_8031481 : CollatzResearch.WordTrace tailWord_8031481 prefixEnd_8031481 4124010120452996527351397 := by
  unfold tailWord_8031481
  simp only [CollatzResearch.WordTrace]
  refine ⟨292932177416323479595862297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195288118277548986397241531 292932177416323479595862297)
  ·
    refine ⟨219699133062242609696896723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292932177416323479595862297 219699133062242609696896723)
    ·
      refine ⟨329548699593363914545345085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219699133062242609696896723 329548699593363914545345085)
      ·
        refine ⟨123580762347511467954504407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329548699593363914545345085 123580762347511467954504407)
        ·
          refine ⟨185371143521267201931756611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123580762347511467954504407 185371143521267201931756611)
          ·
            refine ⟨278056715281900802897634917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185371143521267201931756611 278056715281900802897634917)
            ·
              refine ⟨52135634115356400543306547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278056715281900802897634917 52135634115356400543306547)
              ·
                refine ⟨78203451173034600814959821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52135634115356400543306547 78203451173034600814959821)
                ·
                  refine ⟨29326294189887975305609933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78203451173034600814959821 29326294189887975305609933)
                  ·
                    refine ⟨10997360321207990739603725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29326294189887975305609933 10997360321207990739603725)
                    ·
                      refine ⟨4124010120452996527351397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997360321207990739603725 4124010120452996527351397)
                      ·
                        rfl

theorem cell23_8031481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_8031481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031481 prefixEnd_8031481 := by exact prefixLift 8031481
  have htrace : WordTrace (prefixWord ++ tailWord_8031481) baseStart_8031481 baseEnd_8031481 := by
    simpa [prefixWord, tailWord_8031481, baseEnd_8031481] using wordTrace_append hprefix tailTrace_8031481
  have hstable : (prefixWord ++ tailWord_8031481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031481).length < 2 ^ (prefixWord ++ tailWord_8031481).sum := by decide
  have hdescent : baseEnd_8031481 < baseStart_8031481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031499 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 1, 2, 2]
def baseStart_8031499 : Nat := 118140960795 + 8031499 * 2 ^ 59
def prefixEnd_8031499 : Nat := 4983230072969 + 3 ^ 40 * 8031499 * 2
def baseEnd_8031499 : Nat := 4124019363104777456926315

theorem tailTrace_8031499 : CollatzResearch.WordTrace tailWord_8031499 prefixEnd_8031499 4124019363104777456926315 := by
  unfold tailWord_8031499
  simp only [CollatzResearch.WordTrace]
  refine ⟨292932833930258268670017551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195288555953505512446678367 292932833930258268670017551)
  ·
    refine ⟨439399250895387403005026327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292932833930258268670017551 439399250895387403005026327)
    ·
      refine ⟨659098876343081104507539491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439399250895387403005026327 659098876343081104507539491)
      ·
        refine ⟨988648314514621656761309237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659098876343081104507539491 988648314514621656761309237)
        ·
          refine ⟨92685779485745780321372741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 988648314514621656761309237 92685779485745780321372741)
          ·
            refine ⟨17378583653577333810257389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92685779485745780321372741 17378583653577333810257389)
            ·
              refine ⟨6516968870091500178846521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17378583653577333810257389 6516968870091500178846521)
              ·
                refine ⟨4887726652568625134134891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516968870091500178846521 4887726652568625134134891)
                ·
                  refine ⟨7331589978852937701202337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887726652568625134134891 7331589978852937701202337)
                  ·
                    refine ⟨5498692484139703275901753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331589978852937701202337 5498692484139703275901753)
                    ·
                      refine ⟨4124019363104777456926315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498692484139703275901753 4124019363104777456926315)
                      ·
                        rfl

theorem cell23_8031499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 2, 2].length) (baseStart_8031499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031499 prefixEnd_8031499 := by exact prefixLift 8031499
  have htrace : WordTrace (prefixWord ++ tailWord_8031499) baseStart_8031499 baseEnd_8031499 := by
    simpa [prefixWord, tailWord_8031499, baseEnd_8031499] using wordTrace_append hprefix tailTrace_8031499
  have hstable : (prefixWord ++ tailWord_8031499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031499).length < 2 ^ (prefixWord ++ tailWord_8031499).sum := by decide
  have hdescent : baseEnd_8031499 < baseStart_8031499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031504 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_8031504 : Nat := 118140960795 + 8031504 * 2 ^ 59
def prefixEnd_8031504 : Nat := 4983230072969 + 3 ^ 40 * 8031504 * 2
def baseEnd_8031504 : Nat := 4124021930508049937363791

theorem tailTrace_8031504 : CollatzResearch.WordTrace tailWord_8031504 prefixEnd_8031504 4124021930508049937363791 := by
  unfold tailWord_8031504
  simp only [CollatzResearch.WordTrace]
  refine ⟨146466508147620077261974783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195288677530160103015966377 146466508147620077261974783)
  ·
    refine ⟨219699762221430115892962175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146466508147620077261974783 219699762221430115892962175)
    ·
      refine ⟨329549643332145173839443263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219699762221430115892962175 329549643332145173839443263)
      ·
        refine ⟨494324464998217760759164895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329549643332145173839443263 494324464998217760759164895)
        ·
          refine ⟨741486697497326641138747343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494324464998217760759164895 741486697497326641138747343)
          ·
            refine ⟨1112230046245989961708121015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741486697497326641138747343 1112230046245989961708121015)
            ·
              refine ⟨1668345069368984942562181523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112230046245989961708121015 1668345069368984942562181523)
              ·
                refine ⟨2502517604053477413843272285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668345069368984942562181523 2502517604053477413843272285)
                ·
                  refine ⟨938444101520054030191227107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2502517604053477413843272285 938444101520054030191227107)
                  ·
                    refine ⟨1407666152280081045286840661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 938444101520054030191227107 1407666152280081045286840661)
                    ·
                      refine ⟨4124021930508049937363791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1407666152280081045286840661 4124021930508049937363791)
                      ·
                        rfl

theorem cell23_8031504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_8031504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031504 prefixEnd_8031504 := by exact prefixLift 8031504
  have htrace : WordTrace (prefixWord ++ tailWord_8031504) baseStart_8031504 baseEnd_8031504 := by
    simpa [prefixWord, tailWord_8031504, baseEnd_8031504] using wordTrace_append hprefix tailTrace_8031504
  have hstable : (prefixWord ++ tailWord_8031504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031504).length < 2 ^ (prefixWord ++ tailWord_8031504).sum := by decide
  have hdescent : baseEnd_8031504 < baseStart_8031504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031525 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_8031525 : Nat := 118140960795 + 8031525 * 2 ^ 59
def prefixEnd_8031525 : Nat := 4983230072969 + 3 ^ 40 * 8031525 * 2
def baseEnd_8031525 : Nat := 4124032713601794355201195

theorem tailTrace_8031525 : CollatzResearch.WordTrace tailWord_8031525 prefixEnd_8031525 4124032713601794355201195 := by
  unfold tailWord_8031525
  simp only [CollatzResearch.WordTrace]
  refine ⟨292933782228164075110464029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195289188152109383406976019 292933782228164075110464029)
  ·
    refine ⟨109850168335561528166424011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292933782228164075110464029 109850168335561528166424011)
    ·
      refine ⟨164775252503342292249636017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109850168335561528166424011 164775252503342292249636017)
      ·
        refine ⟨123581439377506719187227013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164775252503342292249636017 123581439377506719187227013)
        ·
          refine ⟨23171519883282509847605065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123581439377506719187227013 23171519883282509847605065)
          ·
            refine ⟨17378639912461882385703799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23171519883282509847605065 17378639912461882385703799)
            ·
              refine ⟨26067959868692823578555699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17378639912461882385703799 26067959868692823578555699)
              ·
                refine ⟨39101939803039235367833549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26067959868692823578555699 39101939803039235367833549)
                ·
                  refine ⟨14663227426139713262937581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39101939803039235367833549 14663227426139713262937581)
                  ·
                    refine ⟨5498710284802392473601593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14663227426139713262937581 5498710284802392473601593)
                    ·
                      refine ⟨4124032713601794355201195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498710284802392473601593 4124032713601794355201195)
                      ·
                        rfl

theorem cell23_8031525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_8031525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031525 prefixEnd_8031525 := by exact prefixLift 8031525
  have htrace : WordTrace (prefixWord ++ tailWord_8031525) baseStart_8031525 baseEnd_8031525 := by
    simpa [prefixWord, tailWord_8031525, baseEnd_8031525] using wordTrace_append hprefix tailTrace_8031525
  have hstable : (prefixWord ++ tailWord_8031525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031525).length < 2 ^ (prefixWord ++ tailWord_8031525).sum := by decide
  have hdescent : baseEnd_8031525 < baseStart_8031525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031549 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8031549 : Nat := 118140960795 + 8031549 * 2 ^ 59
def prefixEnd_8031549 : Nat := 4983230072969 + 3 ^ 40 * 8031549 * 2
def baseEnd_8031549 : Nat := 4124045037137502261301085

theorem tailTrace_8031549 : CollatzResearch.WordTrace tailWord_8031549 prefixEnd_8031549 4124045037137502261301085 := by
  unfold tailWord_8031549
  simp only [CollatzResearch.WordTrace]
  refine ⟨292934657580077127209337701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195289771720051418139558467 292934657580077127209337701)
  ·
    refine ⟨54925248296264461351750819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292934657580077127209337701 54925248296264461351750819)
    ·
      refine ⟨82387872444396692027626229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54925248296264461351750819 82387872444396692027626229)
      ·
        refine ⟨7723863041662189877589959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82387872444396692027626229 7723863041662189877589959)
        ·
          refine ⟨11585794562493284816384939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723863041662189877589959 11585794562493284816384939)
          ·
            refine ⟨17378691843739927224577409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585794562493284816384939 17378691843739927224577409)
            ·
              refine ⟨13034018882804945418433057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17378691843739927224577409 13034018882804945418433057)
              ·
                refine ⟨9775514162103709063824793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034018882804945418433057 9775514162103709063824793)
                ·
                  refine ⟨7331635621577781797868595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775514162103709063824793 7331635621577781797868595)
                  ·
                    refine ⟨10997453432366672696802893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331635621577781797868595 10997453432366672696802893)
                    ·
                      refine ⟨4124045037137502261301085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997453432366672696802893 4124045037137502261301085)
                      ·
                        rfl

theorem cell23_8031549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8031549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031549 prefixEnd_8031549 := by exact prefixLift 8031549
  have htrace : WordTrace (prefixWord ++ tailWord_8031549) baseStart_8031549 baseEnd_8031549 := by
    simpa [prefixWord, tailWord_8031549, baseEnd_8031549] using wordTrace_append hprefix tailTrace_8031549
  have hstable : (prefixWord ++ tailWord_8031549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031549).length < 2 ^ (prefixWord ++ tailWord_8031549).sum := by decide
  have hdescent : baseEnd_8031549 < baseStart_8031549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031572 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_8031572 : Nat := 118140960795 + 8031572 * 2 ^ 59
def prefixEnd_8031572 : Nat := 4983230072969 + 3 ^ 40 * 8031572 * 2
def baseEnd_8031572 : Nat := 4124056847192555671313479

theorem tailTrace_8031572 : CollatzResearch.WordTrace tailWord_8031572 prefixEnd_8031572 4124056847192555671313479 := by
  unfold tailWord_8031572
  simp only [CollatzResearch.WordTrace]
  refine ⟨146467748229496901068712485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195290330972662534758283313 146467748229496901068712485)
  ·
    refine ⟨27462702793030668950383591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146467748229496901068712485 27462702793030668950383591)
    ·
      refine ⟨41194054189546003425575387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27462702793030668950383591 41194054189546003425575387)
      ·
        refine ⟨61791081284319005138363081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41194054189546003425575387 61791081284319005138363081)
        ·
          refine ⟨46343310963239253853772311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61791081284319005138363081 46343310963239253853772311)
          ·
            refine ⟨69514966444858880780658467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46343310963239253853772311 69514966444858880780658467)
            ·
              refine ⟨104272449667288321170987701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69514966444858880780658467 104272449667288321170987701)
              ·
                refine ⟨9775542156308280109780097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104272449667288321170987701 9775542156308280109780097)
                ·
                  refine ⟨7331656617231210082335073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775542156308280109780097 7331656617231210082335073)
                  ·
                    refine ⟨5498742462923407561751305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331656617231210082335073 5498742462923407561751305)
                    ·
                      refine ⟨4124056847192555671313479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498742462923407561751305 4124056847192555671313479)
                      ·
                        rfl

theorem cell23_8031572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_8031572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031572 prefixEnd_8031572 := by exact prefixLift 8031572
  have htrace : WordTrace (prefixWord ++ tailWord_8031572) baseStart_8031572 baseEnd_8031572 := by
    simpa [prefixWord, tailWord_8031572, baseEnd_8031572] using wordTrace_append hprefix tailTrace_8031572
  have hstable : (prefixWord ++ tailWord_8031572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031572).length < 2 ^ (prefixWord ++ tailWord_8031572).sum := by decide
  have hdescent : baseEnd_8031572 < baseStart_8031572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031601 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_8031601 : Nat := 118140960795 + 8031601 * 2 ^ 59
def prefixEnd_8031601 : Nat := 4983230072969 + 3 ^ 40 * 8031601 * 2
def baseEnd_8031601 : Nat := 4124071738131536057850845

theorem tailTrace_8031601 : CollatzResearch.WordTrace tailWord_8031601 prefixEnd_8031601 4124071738131536057850845 := by
  unfold tailWord_8031601
  simp only [CollatzResearch.WordTrace]
  refine ⟨292936554175888740090230657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195291036117259160060153771 292936554175888740090230657)
  ·
    refine ⟨219702415631916555067672993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292936554175888740090230657 219702415631916555067672993)
    ·
      refine ⟨164776811723937416300754745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219702415631916555067672993 164776811723937416300754745)
      ·
        refine ⟨123582608792953062225566059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164776811723937416300754745 123582608792953062225566059)
        ·
          refine ⟨185373913189429593338349089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123582608792953062225566059 185373913189429593338349089)
          ·
            refine ⟨139030434892072195003761817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185373913189429593338349089 139030434892072195003761817)
            ·
              refine ⟨104272826169054146252821363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139030434892072195003761817 104272826169054146252821363)
              ·
                refine ⟨156409239253581219379232045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104272826169054146252821363 156409239253581219379232045)
                ·
                  refine ⟨58653464720092957267212017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156409239253581219379232045 58653464720092957267212017)
                  ·
                    refine ⟨43990098540069717950409013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58653464720092957267212017 43990098540069717950409013)
                    ·
                      refine ⟨4124071738131536057850845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43990098540069717950409013 4124071738131536057850845)
                      ·
                        rfl

theorem cell23_8031601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_8031601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031601 prefixEnd_8031601 := by exact prefixLift 8031601
  have htrace : WordTrace (prefixWord ++ tailWord_8031601) baseStart_8031601 baseEnd_8031601 := by
    simpa [prefixWord, tailWord_8031601, baseEnd_8031601] using wordTrace_append hprefix tailTrace_8031601
  have hstable : (prefixWord ++ tailWord_8031601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031601).length < 2 ^ (prefixWord ++ tailWord_8031601).sum := by decide
  have hdescent : baseEnd_8031601 < baseStart_8031601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031646 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_8031646 : Nat := 118140960795 + 8031646 * 2 ^ 59
def prefixEnd_8031646 : Nat := 4983230072969 + 3 ^ 40 * 8031646 * 2
def baseEnd_8031646 : Nat := 458232760528998709087571

theorem tailTrace_8031646 : CollatzResearch.WordTrace tailWord_8031646 prefixEnd_8031646 458232760528998709087571 := by
  unfold tailWord_8031646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36617274432590714096952349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195292130307150475183745861 36617274432590714096952349)
  ·
    refine ⟨13731477912221517786357131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36617274432590714096952349 13731477912221517786357131)
    ·
      refine ⟨20597216868332276679535697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731477912221517786357131 20597216868332276679535697)
      ·
        refine ⟨15447912651249207509651773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20597216868332276679535697 15447912651249207509651773)
        ·
          refine ⟨5792967244218452816119415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15447912651249207509651773 5792967244218452816119415)
          ·
            refine ⟨8689450866327679224179123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792967244218452816119415 8689450866327679224179123)
            ·
              refine ⟨13034176299491518836268685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689450866327679224179123 13034176299491518836268685)
              ·
                refine ⟨4887816112309319563600757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034176299491518836268685 4887816112309319563600757)
                ·
                  refine ⟨458232760528998709087571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4887816112309319563600757 458232760528998709087571)
                  ·
                    rfl

theorem cell23_8031646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_8031646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031646 prefixEnd_8031646 := by exact prefixLift 8031646
  have htrace : WordTrace (prefixWord ++ tailWord_8031646) baseStart_8031646 baseEnd_8031646 := by
    simpa [prefixWord, tailWord_8031646, baseEnd_8031646] using wordTrace_append hprefix tailTrace_8031646
  have hstable : (prefixWord ++ tailWord_8031646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031646).length < 2 ^ (prefixWord ++ tailWord_8031646).sum := by decide
  have hdescent : baseEnd_8031646 < baseStart_8031646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031648 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_8031648 : Nat := 118140960795 + 8031648 * 2 ^ 59
def prefixEnd_8031648 : Nat := 4983230072969 + 3 ^ 40 * 8031648 * 2
def baseEnd_8031648 : Nat := 4124095871722297373963129

theorem tailTrace_8031648 : CollatzResearch.WordTrace tailWord_8031648 prefixEnd_8031648 4124095871722297373963129 := by
  unfold tailWord_8031648
  simp only [CollatzResearch.WordTrace]
  refine ⟨146469134203359233558595799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195292178937812311411461065 146469134203359233558595799)
  ·
    refine ⟨219703701305038850337893699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146469134203359233558595799 219703701305038850337893699)
    ·
      refine ⟨329555551957558275506840549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219703701305038850337893699 329555551957558275506840549)
      ·
        refine ⟨61791665992042176657532603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329555551957558275506840549 61791665992042176657532603)
        ·
          refine ⟨92687498988063264986298905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61791665992042176657532603 92687498988063264986298905)
          ·
            refine ⟨69515624241047448739724179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92687498988063264986298905 69515624241047448739724179)
            ·
              refine ⟨104273436361571173109586269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69515624241047448739724179 104273436361571173109586269)
              ·
                refine ⟨39102538635589189916094851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104273436361571173109586269 39102538635589189916094851)
                ·
                  refine ⟨58653807953383784874142277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39102538635589189916094851 58653807953383784874142277)
                  ·
                    refine ⟨10997588991259459663901677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58653807953383784874142277 10997588991259459663901677)
                    ·
                      refine ⟨4124095871722297373963129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997588991259459663901677 4124095871722297373963129)
                      ·
                        rfl

theorem cell23_8031648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_8031648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031648 prefixEnd_8031648 := by exact prefixLift 8031648
  have htrace : WordTrace (prefixWord ++ tailWord_8031648) baseStart_8031648 baseEnd_8031648 := by
    simpa [prefixWord, tailWord_8031648, baseEnd_8031648] using wordTrace_append hprefix tailTrace_8031648
  have hstable : (prefixWord ++ tailWord_8031648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031648).length < 2 ^ (prefixWord ++ tailWord_8031648).sum := by decide
  have hdescent : baseEnd_8031648 < baseStart_8031648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031651 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 10]
def baseStart_8031651 : Nat := 118140960795 + 8031651 * 2 ^ 59
def prefixEnd_8031651 : Nat := 4983230072969 + 3 ^ 40 * 8031651 * 2
def baseEnd_8031651 : Nat := 458233045796028984691735

theorem tailTrace_8031651 : CollatzResearch.WordTrace tailWord_8031651 prefixEnd_8031651 458233045796028984691735 := by
  unfold tailWord_8031651
  simp only [CollatzResearch.WordTrace]
  refine ⟨292938377825707598629550807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195292251883805065753033871 292938377825707598629550807)
  ·
    refine ⟨439407566738561397944326211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292938377825707598629550807 439407566738561397944326211)
    ·
      refine ⟨659111350107842096916489317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439407566738561397944326211 659111350107842096916489317)
      ·
        refine ⟨123583378145220393171841747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659111350107842096916489317 123583378145220393171841747)
        ·
          refine ⟨185375067217830589757762621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123583378145220393171841747 185375067217830589757762621)
          ·
            refine ⟨69515650206686471159160983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185375067217830589757762621 69515650206686471159160983)
            ·
              refine ⟨104273475310029706738741475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69515650206686471159160983 104273475310029706738741475)
              ·
                refine ⟨156410212965044560108112213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104273475310029706738741475 156410212965044560108112213)
                ·
                  refine ⟨458233045796028984691735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156410212965044560108112213 458233045796028984691735)
                  ·
                    rfl

theorem cell23_8031651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 10].length) (baseStart_8031651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031651 prefixEnd_8031651 := by exact prefixLift 8031651
  have htrace : WordTrace (prefixWord ++ tailWord_8031651) baseStart_8031651 baseEnd_8031651 := by
    simpa [prefixWord, tailWord_8031651, baseEnd_8031651] using wordTrace_append hprefix tailTrace_8031651
  have hstable : (prefixWord ++ tailWord_8031651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031651).length < 2 ^ (prefixWord ++ tailWord_8031651).sum := by decide
  have hdescent : baseEnd_8031651 < baseStart_8031651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031665 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_8031665 : Nat := 118140960795 + 8031665 * 2 ^ 59
def prefixEnd_8031665 : Nat := 4983230072969 + 3 ^ 40 * 8031665 * 2
def baseEnd_8031665 : Nat := 4124104600893423807450551

theorem tailTrace_8031665 : CollatzResearch.WordTrace tailWord_8031665 prefixEnd_8031665 4124104600893423807450551 := by
  unfold tailWord_8031665
  simp only [CollatzResearch.WordTrace]
  refine ⟨292938888447656879020560449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195292592298437919347040299 292938888447656879020560449)
  ·
    refine ⟨219704166335742659265420337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292938888447656879020560449 219704166335742659265420337)
    ·
      refine ⟨164778124751806994449065253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219704166335742659265420337 164778124751806994449065253)
      ·
        refine ⟨30895898390963811459199735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164778124751806994449065253 30895898390963811459199735)
        ·
          refine ⟨46343847586445717188799603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30895898390963811459199735 46343847586445717188799603)
          ·
            refine ⟨69515771379668575783199405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46343847586445717188799603 69515771379668575783199405)
            ·
              refine ⟨26068414267375715918699777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69515771379668575783199405 26068414267375715918699777)
              ·
                refine ⟨19551310700531786939024833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26068414267375715918699777 19551310700531786939024833)
                ·
                  refine ⟨14663483025398840204268625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19551310700531786939024833 14663483025398840204268625)
                  ·
                    refine ⟨10997612269049130153201469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14663483025398840204268625 10997612269049130153201469)
                    ·
                      refine ⟨4124104600893423807450551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997612269049130153201469 4124104600893423807450551)
                      ·
                        rfl

theorem cell23_8031665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_8031665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031665 prefixEnd_8031665 := by exact prefixLift 8031665
  have htrace : WordTrace (prefixWord ++ tailWord_8031665) baseStart_8031665 baseEnd_8031665 := by
    simpa [prefixWord, tailWord_8031665, baseEnd_8031665] using wordTrace_append hprefix tailTrace_8031665
  have hstable : (prefixWord ++ tailWord_8031665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031665).length < 2 ^ (prefixWord ++ tailWord_8031665).sum := by decide
  have hdescent : baseEnd_8031665 < baseStart_8031665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031695 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_8031695 : Nat := 118140960795 + 8031695 * 2 ^ 59
def prefixEnd_8031695 : Nat := 4983230072969 + 3 ^ 40 * 8031695 * 2
def baseEnd_8031695 : Nat := 4124120005313058690075413

theorem tailTrace_8031695 : CollatzResearch.WordTrace tailWord_8031695 prefixEnd_8031695 4124120005313058690075413 := by
  unfold tailWord_8031695
  simp only [CollatzResearch.WordTrace]
  refine ⟨292939982637548194144152539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195293321758365462762768359 292939982637548194144152539)
  ·
    refine ⟨439409973956322291216228809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292939982637548194144152539 439409973956322291216228809)
    ·
      refine ⟨329557480467241718412171607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439409973956322291216228809 329557480467241718412171607)
      ·
        refine ⟨494336220700862577618257411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329557480467241718412171607 494336220700862577618257411)
        ·
          refine ⟨741504331051293866427386117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494336220700862577618257411 741504331051293866427386117)
          ·
            refine ⟨139032062072117599955134897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741504331051293866427386117 139032062072117599955134897)
            ·
              refine ⟨104274046554088199966351173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139032062072117599955134897 104274046554088199966351173)
              ·
                refine ⟨19551383728891537493690845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104274046554088199966351173 19551383728891537493690845)
                ·
                  refine ⟨7331768898334326560134067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19551383728891537493690845 7331768898334326560134067)
                  ·
                    refine ⟨10997653347501489840201101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331768898334326560134067 10997653347501489840201101)
                    ·
                      refine ⟨4124120005313058690075413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997653347501489840201101 4124120005313058690075413)
                      ·
                        rfl

theorem cell23_8031695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_8031695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031695 prefixEnd_8031695 := by exact prefixLift 8031695
  have htrace : WordTrace (prefixWord ++ tailWord_8031695) baseStart_8031695 baseEnd_8031695 := by
    simpa [prefixWord, tailWord_8031695, baseEnd_8031695] using wordTrace_append hprefix tailTrace_8031695
  have hstable : (prefixWord ++ tailWord_8031695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031695).length < 2 ^ (prefixWord ++ tailWord_8031695).sum := by decide
  have hdescent : baseEnd_8031695 < baseStart_8031695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031729 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_8031729 : Nat := 118140960795 + 8031729 * 2 ^ 59
def prefixEnd_8031729 : Nat := 4983230072969 + 3 ^ 40 * 8031729 * 2
def baseEnd_8031729 : Nat := 4124137463655311557050257

theorem tailTrace_8031729 : CollatzResearch.WordTrace tailWord_8031729 prefixEnd_8031729 4124137463655311557050257 := by
  unfold tailWord_8031729
  simp only [CollatzResearch.WordTrace]
  refine ⟨292941222719425017950890241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195294148479616678633926827 292941222719425017950890241)
  ·
    refine ⟨219705917039568763463167681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292941222719425017950890241 219705917039568763463167681)
    ·
      refine ⟨164779437779676572597375761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219705917039568763463167681 164779437779676572597375761)
      ·
        refine ⟨123584578334757429448031821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164779437779676572597375761 123584578334757429448031821)
        ·
          refine ⟨46344216875534036043011933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123584578334757429448031821 46344216875534036043011933)
          ·
            refine ⟨17379081328325263516129475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46344216875534036043011933 17379081328325263516129475)
            ·
              refine ⟨26068621992487895274194213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17379081328325263516129475 26068621992487895274194213)
              ·
                refine ⟨4887866623591480363911415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26068621992487895274194213 4887866623591480363911415)
                ·
                  refine ⟨7331799935387220545867123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887866623591480363911415 7331799935387220545867123)
                  ·
                    refine ⟨10997699903080830818800685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331799935387220545867123 10997699903080830818800685)
                    ·
                      refine ⟨4124137463655311557050257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997699903080830818800685 4124137463655311557050257)
                      ·
                        rfl

theorem cell23_8031729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_8031729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031729 prefixEnd_8031729 := by exact prefixLift 8031729
  have htrace : WordTrace (prefixWord ++ tailWord_8031729) baseStart_8031729 baseEnd_8031729 := by
    simpa [prefixWord, tailWord_8031729, baseEnd_8031729] using wordTrace_append hprefix tailTrace_8031729
  have hstable : (prefixWord ++ tailWord_8031729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031729).length < 2 ^ (prefixWord ++ tailWord_8031729).sum := by decide
  have hdescent : baseEnd_8031729 < baseStart_8031729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031738 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_8031738 : Nat := 118140960795 + 8031738 * 2 ^ 59
def prefixEnd_8031738 : Nat := 4983230072969 + 3 ^ 40 * 8031738 * 2
def baseEnd_8031738 : Nat := 4124142084981202021837715

theorem tailTrace_8031738 : CollatzResearch.WordTrace tailWord_8031738 prefixEnd_8031738 4124142084981202021837715 := by
  unfold tailWord_8031738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235387744098103121991967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195294367317594941658645245 73235387744098103121991967)
  ·
    refine ⟨109853081616147154682987951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73235387744098103121991967 109853081616147154682987951)
    ·
      refine ⟨164779622424220732024481927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109853081616147154682987951 164779622424220732024481927)
      ·
        refine ⟨247169433636331098036722891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164779622424220732024481927 247169433636331098036722891)
        ·
          refine ⟨370754150454496647055084337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247169433636331098036722891 370754150454496647055084337)
          ·
            refine ⟨278065612840872485291313253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370754150454496647055084337 278065612840872485291313253)
            ·
              refine ⟨52137302407663590992121235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278065612840872485291313253 52137302407663590992121235)
              ·
                refine ⟨78205953611495386488181853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52137302407663590992121235 78205953611495386488181853)
                ·
                  refine ⟨29327232604310769933068195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78205953611495386488181853 29327232604310769933068195)
                  ·
                    refine ⟨43990848906466154899602293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29327232604310769933068195 43990848906466154899602293)
                    ·
                      refine ⟨4124142084981202021837715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43990848906466154899602293 4124142084981202021837715)
                      ·
                        rfl

theorem cell23_8031738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_8031738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031738 prefixEnd_8031738 := by exact prefixLift 8031738
  have htrace : WordTrace (prefixWord ++ tailWord_8031738) baseStart_8031738 baseEnd_8031738 := by
    simpa [prefixWord, tailWord_8031738, baseEnd_8031738] using wordTrace_append hprefix tailTrace_8031738
  have hstable : (prefixWord ++ tailWord_8031738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031738).length < 2 ^ (prefixWord ++ tailWord_8031738).sum := by decide
  have hdescent : baseEnd_8031738 < baseStart_8031738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031750 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_8031750 : Nat := 118140960795 + 8031750 * 2 ^ 59
def prefixEnd_8031750 : Nat := 4983230072969 + 3 ^ 40 * 8031750 * 2
def baseEnd_8031750 : Nat := 4124148246749055974887661

theorem tailTrace_8031750 : CollatzResearch.WordTrace tailWord_8031750 prefixEnd_8031750 4124148246749055974887661 := by
  unfold tailWord_8031750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154437145385904329293897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195294659101565959024936469 9154437145385904329293897)
  ·
    refine ⟨6865827859039428246970423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9154437145385904329293897 6865827859039428246970423)
    ·
      refine ⟨10298741788559142370455635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865827859039428246970423 10298741788559142370455635)
      ·
        refine ⟨15448112682838713555683453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298741788559142370455635 15448112682838713555683453)
        ·
          refine ⟨5793042256064517583381295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448112682838713555683453 5793042256064517583381295)
          ·
            refine ⟨8689563384096776375071943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793042256064517583381295 8689563384096776375071943)
            ·
              refine ⟨13034345076145164562607915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689563384096776375071943 13034345076145164562607915)
              ·
                refine ⟨19551517614217746843911873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13034345076145164562607915 19551517614217746843911873)
                ·
                  refine ⟨14663638210663310132933905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19551517614217746843911873 14663638210663310132933905)
                  ·
                    refine ⟨10997728657997482599700429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14663638210663310132933905 10997728657997482599700429)
                    ·
                      refine ⟨4124148246749055974887661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997728657997482599700429 4124148246749055974887661)
                      ·
                        rfl

theorem cell23_8031750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_8031750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031750 prefixEnd_8031750 := by exact prefixLift 8031750
  have htrace : WordTrace (prefixWord ++ tailWord_8031750) baseStart_8031750 baseEnd_8031750 := by
    simpa [prefixWord, tailWord_8031750, baseEnd_8031750] using wordTrace_append hprefix tailTrace_8031750
  have hstable : (prefixWord ++ tailWord_8031750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031750).length < 2 ^ (prefixWord ++ tailWord_8031750).sum := by decide
  have hdescent : baseEnd_8031750 < baseStart_8031750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031752 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_8031752 : Nat := 118140960795 + 8031752 * 2 ^ 59
def prefixEnd_8031752 : Nat := 4983230072969 + 3 ^ 40 * 8031752 * 2
def baseEnd_8031752 : Nat := 4124149273710364967062651

theorem tailTrace_8031752 : CollatzResearch.WordTrace tailWord_8031752 prefixEnd_8031752 4124149273710364967062651 := by
  unfold tailWord_8031752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471030799170846439488755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195294707732227795252651673 146471030799170846439488755)
  ·
    refine ⟨219706546198756269659233133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146471030799170846439488755 219706546198756269659233133)
    ·
      refine ⟨82389954824533601122212425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219706546198756269659233133 82389954824533601122212425)
      ·
        refine ⟨61792466118400200841659319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82389954824533601122212425 61792466118400200841659319)
        ·
          refine ⟨92688699177600301262488979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61792466118400200841659319 92688699177600301262488979)
          ·
            refine ⟨139033048766400451893733469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92688699177600301262488979 139033048766400451893733469)
            ·
              refine ⟨52137393287400169460150051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139033048766400451893733469 52137393287400169460150051)
              ·
                refine ⟨78206089931100254190225077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52137393287400169460150051 78206089931100254190225077)
                ·
                  refine ⟨7331820931040648830333601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78206089931100254190225077 7331820931040648830333601)
                  ·
                    refine ⟨5498865698280486622750201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331820931040648830333601 5498865698280486622750201)
                    ·
                      refine ⟨4124149273710364967062651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498865698280486622750201 4124149273710364967062651)
                      ·
                        rfl

theorem cell23_8031752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_8031752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031752 prefixEnd_8031752 := by exact prefixLift 8031752
  have htrace : WordTrace (prefixWord ++ tailWord_8031752) baseStart_8031752 baseEnd_8031752 := by
    simpa [prefixWord, tailWord_8031752, baseEnd_8031752] using wordTrace_append hprefix tailTrace_8031752
  have hstable : (prefixWord ++ tailWord_8031752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031752).length < 2 ^ (prefixWord ++ tailWord_8031752).sum := by decide
  have hdescent : baseEnd_8031752 < baseStart_8031752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031756 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_8031756 : Nat := 118140960795 + 8031756 * 2 ^ 59
def prefixEnd_8031756 : Nat := 4983230072969 + 3 ^ 40 * 8031756 * 2
def baseEnd_8031756 : Nat := 4124151327632982951412633

theorem tailTrace_8031756 : CollatzResearch.WordTrace tailWord_8031756 prefixEnd_8031756 4124151327632982951412633 := by
  unfold tailWord_8031756
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471103745163600781061561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195294804993551467708082081 146471103745163600781061561)
  ·
    refine ⟨109853327808872700585796171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146471103745163600781061561 109853327808872700585796171)
    ·
      refine ⟨164779991713309050878694257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109853327808872700585796171 164779991713309050878694257)
      ·
        refine ⟨123584993784981788159020693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164779991713309050878694257 123584993784981788159020693)
        ·
          refine ⟨5793046583671021319954095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123584993784981788159020693 5793046583671021319954095)
          ·
            refine ⟨8689569875506531979931143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793046583671021319954095 8689569875506531979931143)
            ·
              refine ⟨13034354813259797969896715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689569875506531979931143 13034354813259797969896715)
              ·
                refine ⟨19551532219889696954845073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13034354813259797969896715 19551532219889696954845073)
                ·
                  refine ⟨14663649164917272716133805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19551532219889696954845073 14663649164917272716133805)
                  ·
                    refine ⟨5498868436843977268550177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14663649164917272716133805 5498868436843977268550177)
                    ·
                      refine ⟨4124151327632982951412633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498868436843977268550177 4124151327632982951412633)
                      ·
                        rfl

theorem cell23_8031756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_8031756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031756 prefixEnd_8031756 := by exact prefixLift 8031756
  have htrace : WordTrace (prefixWord ++ tailWord_8031756) baseStart_8031756 baseEnd_8031756 := by
    simpa [prefixWord, tailWord_8031756, baseEnd_8031756] using wordTrace_append hprefix tailTrace_8031756
  have hstable : (prefixWord ++ tailWord_8031756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031756).length < 2 ^ (prefixWord ++ tailWord_8031756).sum := by decide
  have hdescent : baseEnd_8031756 < baseStart_8031756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031765 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_8031765 : Nat := 118140960795 + 8031765 * 2 ^ 59
def prefixEnd_8031765 : Nat := 4983230072969 + 3 ^ 40 * 8031765 * 2
def baseEnd_8031765 : Nat := 4124155948958873416200091

theorem tailTrace_8031765 : CollatzResearch.WordTrace tailWord_8031765 prefixEnd_8031765 4124155948958873416200091 := by
  unfold tailWord_8031765
  simp only [CollatzResearch.WordTrace]
  refine ⟨292942535747294596099200749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195295023831529730732800499 292942535747294596099200749)
  ·
    refine ⟨109853450905235473537200281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292942535747294596099200749 109853450905235473537200281)
    ·
      refine ⟨82390088178926605152900211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109853450905235473537200281 82390088178926605152900211)
      ·
        refine ⟨123585132268389907729350317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82390088178926605152900211 123585132268389907729350317)
        ·
          refine ⟨46344424600646215398506369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123585132268389907729350317 46344424600646215398506369)
          ·
            refine ⟨34758318450484661548879777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46344424600646215398506369 34758318450484661548879777)
            ·
              refine ⟨26068738837863496161659833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34758318450484661548879777 26068738837863496161659833)
              ·
                refine ⟨19551554128397622121244875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26068738837863496161659833 19551554128397622121244875)
                ·
                  refine ⟨29327331192596433181867313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19551554128397622121244875 29327331192596433181867313)
                  ·
                    refine ⟨21995498394447324886400485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29327331192596433181867313 21995498394447324886400485)
                    ·
                      refine ⟨4124155948958873416200091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21995498394447324886400485 4124155948958873416200091)
                      ·
                        rfl

theorem cell23_8031765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_8031765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031765 prefixEnd_8031765 := by exact prefixLift 8031765
  have htrace : WordTrace (prefixWord ++ tailWord_8031765) baseStart_8031765 baseEnd_8031765 := by
    simpa [prefixWord, tailWord_8031765, baseEnd_8031765] using wordTrace_append hprefix tailTrace_8031765
  have hstable : (prefixWord ++ tailWord_8031765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031765).length < 2 ^ (prefixWord ++ tailWord_8031765).sum := by decide
  have hdescent : baseEnd_8031765 < baseStart_8031765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031772 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_8031772 : Nat := 118140960795 + 8031772 * 2 ^ 59
def prefixEnd_8031772 : Nat := 4983230072969 + 3 ^ 40 * 8031772 * 2
def baseEnd_8031772 : Nat := 4124159543323454888812559

theorem tailTrace_8031772 : CollatzResearch.WordTrace tailWord_8031772 prefixEnd_8031772 4124159543323454888812559 := by
  unfold tailWord_8031772
  simp only [CollatzResearch.WordTrace]
  refine ⟨146471395529134618147352785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195295194038846157529803713 146471395529134618147352785)
  ·
    refine ⟨109853546646850963610514589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146471395529134618147352785 109853546646850963610514589)
    ·
      refine ⟨41195079992569111353942971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109853546646850963610514589 41195079992569111353942971)
      ·
        refine ⟨61792619988853667030914457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41195079992569111353942971 61792619988853667030914457)
        ·
          refine ⟨46344464991640250273185843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61792619988853667030914457 46344464991640250273185843)
          ·
            refine ⟨69516697487460375409778765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46344464991640250273185843 69516697487460375409778765)
            ·
              refine ⟨26068761557797640778667037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69516697487460375409778765 26068761557797640778667037)
              ·
                refine ⟨9775785584174115292000139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26068761557797640778667037 9775785584174115292000139)
                ·
                  refine ⟨14663678376261172938000209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9775785584174115292000139 14663678376261172938000209)
                  ·
                    refine ⟨10997758782195879703500157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14663678376261172938000209 10997758782195879703500157)
                    ·
                      refine ⟨4124159543323454888812559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997758782195879703500157 4124159543323454888812559)
                      ·
                        rfl

theorem cell23_8031772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_8031772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031772 prefixEnd_8031772 := by exact prefixLift 8031772
  have htrace : WordTrace (prefixWord ++ tailWord_8031772) baseStart_8031772 baseEnd_8031772 := by
    simpa [prefixWord, tailWord_8031772, baseEnd_8031772] using wordTrace_append hprefix tailTrace_8031772
  have hstable : (prefixWord ++ tailWord_8031772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031772).length < 2 ^ (prefixWord ++ tailWord_8031772).sum := by decide
  have hdescent : baseEnd_8031772 < baseStart_8031772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031779 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 2, 4]
def baseStart_8031779 : Nat := 118140960795 + 8031779 * 2 ^ 59
def prefixEnd_8031779 : Nat := 4983230072969 + 3 ^ 40 * 8031779 * 2
def baseEnd_8031779 : Nat := 1374721045896012120475009

theorem tailTrace_8031779 : CollatzResearch.WordTrace tailWord_8031779 prefixEnd_8031779 1374721045896012120475009 := by
  unfold tailWord_8031779
  simp only [CollatzResearch.WordTrace]
  refine ⟨292943046369243876490210391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195295364246162584326806927 292943046369243876490210391)
  ·
    refine ⟨439414569553865814735315587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292943046369243876490210391 439414569553865814735315587)
    ·
      refine ⟨659121854330798722102973381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439414569553865814735315587 659121854330798722102973381)
      ·
        refine ⟨123585347687024760394307509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659121854330798722102973381 123585347687024760394307509)
        ·
          refine ⟨11586126345658571286966329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123585347687024760394307509 11586126345658571286966329)
          ·
            refine ⟨8689594759243928465224747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11586126345658571286966329 8689594759243928465224747)
            ·
              refine ⟨13034392138865892697837121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689594759243928465224747 13034392138865892697837121)
              ·
                refine ⟨9775794104149419523377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034392138865892697837121 9775794104149419523377841)
                ·
                  refine ⟨7331845578112064642533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775794104149419523377841 7331845578112064642533381)
                  ·
                    refine ⟨1374721045896012120475009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7331845578112064642533381 1374721045896012120475009)
                    ·
                      rfl

theorem cell23_8031779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 4].length) (baseStart_8031779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031779 prefixEnd_8031779 := by exact prefixLift 8031779
  have htrace : WordTrace (prefixWord ++ tailWord_8031779) baseStart_8031779 baseEnd_8031779 := by
    simpa [prefixWord, tailWord_8031779, baseEnd_8031779] using wordTrace_append hprefix tailTrace_8031779
  have hstable : (prefixWord ++ tailWord_8031779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031779).length < 2 ^ (prefixWord ++ tailWord_8031779).sum := by decide
  have hdescent : baseEnd_8031779 < baseStart_8031779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031786 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_8031786 : Nat := 118140960795 + 8031786 * 2 ^ 59
def prefixEnd_8031786 : Nat := 4983230072969 + 3 ^ 40 * 8031786 * 2
def baseEnd_8031786 : Nat := 4124166732052617834037495

theorem tailTrace_8031786 : CollatzResearch.WordTrace tailWord_8031786 prefixEnd_8031786 4124166732052617834037495 := by
  unfold tailWord_8031786
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235825420054629171428803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195295534453479011123810141 73235825420054629171428803)
  ·
    refine ⟨109853738130081943757143205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73235825420054629171428803 109853738130081943757143205)
    ·
      refine ⟨20597575899390364454464351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109853738130081943757143205 20597575899390364454464351)
      ·
        refine ⟨30896363849085546681696527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20597575899390364454464351 30896363849085546681696527)
        ·
          refine ⟨46344545773628320022544791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30896363849085546681696527 46344545773628320022544791)
          ·
            refine ⟨69516818660442480033817187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46344545773628320022544791 69516818660442480033817187)
            ·
              refine ⟨104275227990663720050725781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69516818660442480033817187 104275227990663720050725781)
              ·
                refine ⟨4887901312062361877377771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104275227990663720050725781 4887901312062361877377771)
                ·
                  refine ⟨7331851968093542816066657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887901312062361877377771 7331851968093542816066657)
                  ·
                    refine ⟨5498888976070157112049993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331851968093542816066657 5498888976070157112049993)
                    ·
                      refine ⟨4124166732052617834037495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498888976070157112049993 4124166732052617834037495)
                      ·
                        rfl

theorem cell23_8031786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_8031786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031786 prefixEnd_8031786 := by exact prefixLift 8031786
  have htrace : WordTrace (prefixWord ++ tailWord_8031786) baseStart_8031786 baseEnd_8031786 := by
    simpa [prefixWord, tailWord_8031786, baseEnd_8031786] using wordTrace_append hprefix tailTrace_8031786
  have hstable : (prefixWord ++ tailWord_8031786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031786).length < 2 ^ (prefixWord ++ tailWord_8031786).sum := by decide
  have hdescent : baseEnd_8031786 < baseStart_8031786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031837 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_8031837 : Nat := 118140960795 + 8031837 * 2 ^ 59
def prefixEnd_8031837 : Nat := 4983230072969 + 3 ^ 40 * 8031837 * 2
def baseEnd_8031837 : Nat := 4124192919565997134499761

theorem tailTrace_8031837 : CollatzResearch.WordTrace tailWord_8031837 prefixEnd_8031837 4124192919565997134499761 := by
  unfold tailWord_8031837
  simp only [CollatzResearch.WordTrace]
  refine ⟨292945161803033752395821765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195296774535355834930547843 292945161803033752395821765)
  ·
    refine ⟨54927217838068828574216581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292945161803033752395821765 54927217838068828574216581)
    ·
      refine ⟨10298853344637905357665609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54927217838068828574216581 10298853344637905357665609)
      ·
        refine ⟨7724140008478429018249207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10298853344637905357665609 7724140008478429018249207)
        ·
          refine ⟨11586210012717643527373811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724140008478429018249207 11586210012717643527373811)
          ·
            refine ⟨17379315019076465291060717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586210012717643527373811 17379315019076465291060717)
            ·
              refine ⟨6517243132153674484147769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17379315019076465291060717 6517243132153674484147769)
              ·
                refine ⟨4887932349115255863110827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517243132153674484147769 4887932349115255863110827)
                ·
                  refine ⟨7331898523672883794666241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887932349115255863110827 7331898523672883794666241)
                  ·
                    refine ⟨5498923892754662845999681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331898523672883794666241 5498923892754662845999681)
                    ·
                      refine ⟨4124192919565997134499761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5498923892754662845999681 4124192919565997134499761)
                      ·
                        rfl

theorem cell23_8031837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_8031837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031837 prefixEnd_8031837 := by exact prefixLift 8031837
  have htrace : WordTrace (prefixWord ++ tailWord_8031837) baseStart_8031837 baseEnd_8031837 := by
    simpa [prefixWord, tailWord_8031837, baseEnd_8031837] using wordTrace_append hprefix tailTrace_8031837
  have hstable : (prefixWord ++ tailWord_8031837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031837).length < 2 ^ (prefixWord ++ tailWord_8031837).sum := by decide
  have hdescent : baseEnd_8031837 < baseStart_8031837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031853 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_8031853 : Nat := 118140960795 + 8031853 * 2 ^ 59
def prefixEnd_8031853 : Nat := 4983230072969 + 3 ^ 40 * 8031853 * 2
def baseEnd_8031853 : Nat := 4124201135256469071899687

theorem tailTrace_8031853 : CollatzResearch.WordTrace tailWord_8031853 prefixEnd_8031853 4124201135256469071899687 := by
  unfold tailWord_8031853
  simp only [CollatzResearch.WordTrace]
  refine ⟨292945745370975787128404213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195297163580650524752269475 292945745370975787128404213)
  ·
    refine ⟨27463663628528980043287895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292945745370975787128404213 27463663628528980043287895)
    ·
      refine ⟨41195495442793470064931843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27463663628528980043287895 41195495442793470064931843)
      ·
        refine ⟨61793243164190205097397765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41195495442793470064931843 61793243164190205097397765)
        ·
          refine ⟨11586233093285663455762081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61793243164190205097397765 11586233093285663455762081)
          ·
            refine ⟨8689674819964247591821561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11586233093285663455762081 8689674819964247591821561)
            ·
              refine ⟨6517256114973185693866171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689674819964247591821561 6517256114973185693866171)
              ·
                refine ⟨9775884172459778540799257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517256114973185693866171 9775884172459778540799257)
                ·
                  refine ⟨7331913129344833905599443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775884172459778540799257 7331913129344833905599443)
                  ·
                    refine ⟨10997869694017250858399165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331913129344833905599443 10997869694017250858399165)
                    ·
                      refine ⟨4124201135256469071899687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997869694017250858399165 4124201135256469071899687)
                      ·
                        rfl

theorem cell23_8031853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_8031853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031853 prefixEnd_8031853 := by exact prefixLift 8031853
  have htrace : WordTrace (prefixWord ++ tailWord_8031853) baseStart_8031853 baseEnd_8031853 := by
    simpa [prefixWord, tailWord_8031853, baseEnd_8031853] using wordTrace_append hprefix tailTrace_8031853
  have hstable : (prefixWord ++ tailWord_8031853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031853).length < 2 ^ (prefixWord ++ tailWord_8031853).sum := by decide
  have hdescent : baseEnd_8031853 < baseStart_8031853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031862 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_8031862 : Nat := 118140960795 + 8031862 * 2 ^ 59
def prefixEnd_8031862 : Nat := 4983230072969 + 3 ^ 40 * 8031862 * 2
def baseEnd_8031862 : Nat := 4124205756582359536687145

theorem tailTrace_8031862 : CollatzResearch.WordTrace tailWord_8031862 prefixEnd_8031862 4124205756582359536687145 := by
  unfold tailWord_8031862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309129601746448854092615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195297382418628787776987893 18309129601746448854092615)
  ·
    refine ⟨27463694402619673281138923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309129601746448854092615 27463694402619673281138923)
    ·
      refine ⟨41195541603929509921708385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27463694402619673281138923 41195541603929509921708385)
      ·
        refine ⟨30896656202947132441281289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41195541603929509921708385 30896656202947132441281289)
        ·
          refine ⟨23172492152210349330960967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30896656202947132441281289 23172492152210349330960967)
          ·
            refine ⟨34758738228315523996441451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23172492152210349330960967 34758738228315523996441451)
            ·
              refine ⟨52138107342473285994662177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34758738228315523996441451 52138107342473285994662177)
              ·
                refine ⟨39103580506854964495996633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52138107342473285994662177 39103580506854964495996633)
                ·
                  refine ⟨29327685380141223371997475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39103580506854964495996633 29327685380141223371997475)
                  ·
                    refine ⟨43991528070211835057996213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29327685380141223371997475 43991528070211835057996213)
                    ·
                      refine ⟨4124205756582359536687145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43991528070211835057996213 4124205756582359536687145)
                      ·
                        rfl

theorem cell23_8031862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_8031862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031862 prefixEnd_8031862 := by exact prefixLift 8031862
  have htrace : WordTrace (prefixWord ++ tailWord_8031862) baseStart_8031862 baseEnd_8031862 := by
    simpa [prefixWord, tailWord_8031862, baseEnd_8031862] using wordTrace_append hprefix tailTrace_8031862
  have hstable : (prefixWord ++ tailWord_8031862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031862).length < 2 ^ (prefixWord ++ tailWord_8031862).sum := by decide
  have hdescent : baseEnd_8031862 < baseStart_8031862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031875 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3]
def baseStart_8031875 : Nat := 118140960795 + 8031875 * 2 ^ 59
def prefixEnd_8031875 : Nat := 4983230072969 + 3 ^ 40 * 8031875 * 2
def baseEnd_8031875 : Nat := 4124212431830867985824585

theorem tailTrace_8031875 : CollatzResearch.WordTrace tailWord_8031875 prefixEnd_8031875 4124212431830867985824585 := by
  unfold tailWord_8031875
  simp only [CollatzResearch.WordTrace]
  refine ⟨292946547776896084885705079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195297698517930723257136719 292946547776896084885705079)
  ·
    refine ⟨439419821665344127328557619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292946547776896084885705079 439419821665344127328557619)
    ·
      refine ⟨659129732498016190992836429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439419821665344127328557619 659129732498016190992836429)
      ·
        refine ⟨247173649686756071622313661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659129732498016190992836429 247173649686756071622313661)
        ·
          refine ⟨92690118632533526858367623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247173649686756071622313661 92690118632533526858367623)
          ·
            refine ⟨139035177948800290287551435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92690118632533526858367623 139035177948800290287551435)
            ·
              refine ⟨208552766923200435431327153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139035177948800290287551435 208552766923200435431327153)
              ·
                refine ⟨156414575192400326573495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208552766923200435431327153 156414575192400326573495365)
                ·
                  refine ⟨29327732848575061232530381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156414575192400326573495365 29327732848575061232530381)
                  ·
                    refine ⟨10997899818215647962198893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29327732848575061232530381 10997899818215647962198893)
                    ·
                      refine ⟨4124212431830867985824585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10997899818215647962198893 4124212431830867985824585)
                      ·
                        rfl

theorem cell23_8031875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_8031875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031875 prefixEnd_8031875 := by exact prefixLift 8031875
  have htrace : WordTrace (prefixWord ++ tailWord_8031875) baseStart_8031875 baseEnd_8031875 := by
    simpa [prefixWord, tailWord_8031875, baseEnd_8031875] using wordTrace_append hprefix tailTrace_8031875
  have hstable : (prefixWord ++ tailWord_8031875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031875).length < 2 ^ (prefixWord ++ tailWord_8031875).sum := by decide
  have hdescent : baseEnd_8031875 < baseStart_8031875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031932 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_8031932 : Nat := 118140960795 + 8031932 * 2 ^ 59
def prefixEnd_8031932 : Nat := 4983230072969 + 3 ^ 40 * 8031932 * 2
def baseEnd_8031932 : Nat := 4124241700228174262811823

theorem tailTrace_8031932 : CollatzResearch.WordTrace tailWord_8031932 prefixEnd_8031932 4124241700228174262811823 := by
  unfold tailWord_8031932
  simp only [CollatzResearch.WordTrace]
  refine ⟨146474313368844791810265025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195299084491793055747020033 146474313368844791810265025)
  ·
    refine ⟨109855735026633593857698769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146474313368844791810265025 109855735026633593857698769)
    ·
      refine ⟨82391801269975195393274077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109855735026633593857698769 82391801269975195393274077)
      ·
        refine ⟨30896925476240698272477779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82391801269975195393274077 30896925476240698272477779)
        ·
          refine ⟨46345388214361047408716669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30896925476240698272477779 46345388214361047408716669)
          ·
            refine ⟨17379520580385392778268751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46345388214361047408716669 17379520580385392778268751)
            ·
              refine ⟨26069280870578089167403127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17379520580385392778268751 26069280870578089167403127)
              ·
                refine ⟨39103921305867133751104691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26069280870578089167403127 39103921305867133751104691)
                ·
                  refine ⟨58655881958800700626657037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39103921305867133751104691 58655881958800700626657037)
                  ·
                    refine ⟨21995955734550262734996389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58655881958800700626657037 21995955734550262734996389)
                    ·
                      refine ⟨4124241700228174262811823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21995955734550262734996389 4124241700228174262811823)
                      ·
                        rfl

theorem cell23_8031932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_8031932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031932 prefixEnd_8031932 := by exact prefixLift 8031932
  have htrace : WordTrace (prefixWord ++ tailWord_8031932) baseStart_8031932 baseEnd_8031932 := by
    simpa [prefixWord, tailWord_8031932, baseEnd_8031932] using wordTrace_append hprefix tailTrace_8031932
  have hstable : (prefixWord ++ tailWord_8031932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031932).length < 2 ^ (prefixWord ++ tailWord_8031932).sum := by decide
  have hdescent : baseEnd_8031932 < baseStart_8031932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031959 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 1, 4]
def baseStart_8031959 : Nat := 118140960795 + 8031959 * 2 ^ 59
def prefixEnd_8031959 : Nat := 4983230072969 + 3 ^ 40 * 8031959 * 2
def baseEnd_8031959 : Nat := 1374751854735281885724733

theorem tailTrace_8031959 : CollatzResearch.WordTrace tailWord_8031959 prefixEnd_8031959 1374751854735281885724733 := by
  unfold tailWord_8031959
  simp only [CollatzResearch.WordTrace]
  refine ⟨292949611508591767231762931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195299741005727844821175287 292949611508591767231762931)
  ·
    refine ⟨439424417262887650847644397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292949611508591767231762931 439424417262887650847644397)
    ·
      refine ⟨164784156473582869067866649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439424417262887650847644397 164784156473582869067866649)
      ·
        refine ⟨123588117355187151800899987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164784156473582869067866649 123588117355187151800899987)
        ·
          refine ⟨185382176032780727701349981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123588117355187151800899987 185382176032780727701349981)
          ·
            refine ⟨69518316012292772888006243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185382176032780727701349981 69518316012292772888006243)
            ·
              refine ⟨104277474018439159332009365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69518316012292772888006243 104277474018439159332009365)
              ·
                refine ⟨4888006594614335593687939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104277474018439159332009365 4888006594614335593687939)
                ·
                  refine ⟨7332009891921503390531909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888006594614335593687939 7332009891921503390531909)
                  ·
                    refine ⟨1374751854735281885724733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332009891921503390531909 1374751854735281885724733)
                    ·
                      rfl

theorem cell23_8031959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_8031959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031959 prefixEnd_8031959 := by exact prefixLift 8031959
  have htrace : WordTrace (prefixWord ++ tailWord_8031959) baseStart_8031959 baseEnd_8031959 := by
    simpa [prefixWord, tailWord_8031959, baseEnd_8031959] using wordTrace_append hprefix tailTrace_8031959
  have hstable : (prefixWord ++ tailWord_8031959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031959).length < 2 ^ (prefixWord ++ tailWord_8031959).sum := by decide
  have hdescent : baseEnd_8031959 < baseStart_8031959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8031982 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_8031982 : Nat := 118140960795 + 8031982 * 2 ^ 59
def prefixEnd_8031982 : Nat := 4983230072969 + 3 ^ 40 * 8031982 * 2
def baseEnd_8031982 : Nat := 4124267374260899067186593

theorem tailTrace_8031982 : CollatzResearch.WordTrace tailWord_8031982 prefixEnd_8031982 4124267374260899067186593 := by
  unfold tailWord_8031982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36618806298438555269981275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195300300258338961439900133 36618806298438555269981275)
  ·
    refine ⟨54928209447657832904971913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36618806298438555269981275 54928209447657832904971913)
    ·
      refine ⟨41196157085743374678728935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54928209447657832904971913 41196157085743374678728935)
      ·
        refine ⟨61794235628615062018093403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41196157085743374678728935 61794235628615062018093403)
        ·
          refine ⟨92691353442922593027140105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61794235628615062018093403 92691353442922593027140105)
          ·
            refine ⟨69518515082191944770355079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92691353442922593027140105 69518515082191944770355079)
            ·
              refine ⟨104277772623287917155532619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69518515082191944770355079 104277772623287917155532619)
              ·
                refine ⟨156416658934931875733298929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104277772623287917155532619 156416658934931875733298929)
                ·
                  refine ⟨117312494201198906799974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156416658934931875733298929 117312494201198906799974197)
                  ·
                    refine ⟨10998046331362397512497581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117312494201198906799974197 10998046331362397512497581)
                    ·
                      refine ⟨4124267374260899067186593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998046331362397512497581 4124267374260899067186593)
                      ·
                        rfl

theorem cell23_8031982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_8031982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8031982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8031982 prefixEnd_8031982 := by exact prefixLift 8031982
  have htrace : WordTrace (prefixWord ++ tailWord_8031982) baseStart_8031982 baseEnd_8031982 := by
    simpa [prefixWord, tailWord_8031982, baseEnd_8031982] using wordTrace_append hprefix tailTrace_8031982
  have hstable : (prefixWord ++ tailWord_8031982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8031982).length < 2 ^ (prefixWord ++ tailWord_8031982).sum := by decide
  have hdescent : baseEnd_8031982 < baseStart_8031982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8031982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032015 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 6]
def baseStart_8032015 : Nat := 118140960795 + 8032015 * 2 ^ 59
def prefixEnd_8032015 : Nat := 4983230072969 + 3 ^ 40 * 8032015 * 2
def baseEnd_8032015 : Nat := 1374761439707499146024647

theorem tailTrace_8032015 : CollatzResearch.WordTrace tailWord_8032015 prefixEnd_8032015 1374761439707499146024647 := by
  unfold tailWord_8032015
  simp only [CollatzResearch.WordTrace]
  refine ⟨292951653996388888795801499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195301102664259259197200999 292951653996388888795801499)
  ·
    refine ⟨439427480994583333193702249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292951653996388888795801499 439427480994583333193702249)
    ·
      refine ⟨329570610745937499895276687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439427480994583333193702249 329570610745937499895276687)
      ·
        refine ⟨494355916118906249842915031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329570610745937499895276687 494355916118906249842915031)
        ·
          refine ⟨741533874178359374764372547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494355916118906249842915031 741533874178359374764372547)
          ·
            refine ⟨1112300811267539062146558821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741533874178359374764372547 1112300811267539062146558821)
            ·
              refine ⟨208556402112663574152479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1112300811267539062146558821 208556402112663574152479779)
              ·
                refine ⟨312834603168995361228719669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208556402112663574152479779 312834603168995361228719669)
                ·
                  refine ⟨29328244047093315115192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312834603168995361228719669 29328244047093315115192469)
                  ·
                    refine ⟨1374761439707499146024647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29328244047093315115192469 1374761439707499146024647)
                    ·
                      rfl

theorem cell23_8032015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_8032015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032015 prefixEnd_8032015 := by exact prefixLift 8032015
  have htrace : WordTrace (prefixWord ++ tailWord_8032015) baseStart_8032015 baseEnd_8032015 := by
    simpa [prefixWord, tailWord_8032015, baseEnd_8032015] using wordTrace_append hprefix tailTrace_8032015
  have hstable : (prefixWord ++ tailWord_8032015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032015).length < 2 ^ (prefixWord ++ tailWord_8032015).sum := by decide
  have hdescent : baseEnd_8032015 < baseStart_8032015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032025 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_8032025 : Nat := 118140960795 + 8032025 * 2 ^ 59
def prefixEnd_8032025 : Nat := 4983230072969 + 3 ^ 40 * 8032025 * 2
def baseEnd_8032025 : Nat := 4124289453929042398948895

theorem tailTrace_8032025 : CollatzResearch.WordTrace tailWord_8032025 prefixEnd_8032025 4124289453929042398948895 := by
  unfold tailWord_8032025
  simp only [CollatzResearch.WordTrace]
  refine ⟨292952018726352660503665529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195301345817568440335777019 292952018726352660503665529)
  ·
    refine ⟨219714014044764495377749147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292952018726352660503665529 219714014044764495377749147)
    ·
      refine ⟨329571021067146743066623721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219714014044764495377749147 329571021067146743066623721)
      ·
        refine ⟨247178265800360057299967791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329571021067146743066623721 247178265800360057299967791)
        ·
          refine ⟨370767398700540085949951687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247178265800360057299967791 370767398700540085949951687)
          ·
            refine ⟨556151098050810128924927531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370767398700540085949951687 556151098050810128924927531)
            ·
              refine ⟨834226647076215193387391297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556151098050810128924927531 834226647076215193387391297)
              ·
                refine ⟨625669985307161395040543473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834226647076215193387391297 625669985307161395040543473)
                ·
                  refine ⟨469252488980371046280407605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625669985307161395040543473 469252488980371046280407605)
                  ·
                    refine ⟨43992420841909785588788213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469252488980371046280407605 43992420841909785588788213)
                    ·
                      refine ⟨4124289453929042398948895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43992420841909785588788213 4124289453929042398948895)
                      ·
                        rfl

theorem cell23_8032025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_8032025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032025 prefixEnd_8032025 := by exact prefixLift 8032025
  have htrace : WordTrace (prefixWord ++ tailWord_8032025) baseStart_8032025 baseEnd_8032025 := by
    simpa [prefixWord, tailWord_8032025, baseEnd_8032025] using wordTrace_append hprefix tailTrace_8032025
  have hstable : (prefixWord ++ tailWord_8032025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032025).length < 2 ^ (prefixWord ++ tailWord_8032025).sum := by decide
  have hdescent : baseEnd_8032025 < baseStart_8032025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032032 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_8032032 : Nat := 118140960795 + 8032032 * 2 ^ 59
def prefixEnd_8032032 : Nat := 4983230072969 + 3 ^ 40 * 8032032 * 2
def baseEnd_8032032 : Nat := 1374764349431207957187121

theorem tailTrace_8032032 : CollatzResearch.WordTrace tailWord_8032032 prefixEnd_8032032 1374764349431207957187121 := by
  unfold tailWord_8032032
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476137018663650349585175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195301516024884867132780233 146476137018663650349585175)
  ·
    refine ⟨219714205527995475524377763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146476137018663650349585175 219714205527995475524377763)
    ·
      refine ⟨329571308291993213286566645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219714205527995475524377763 329571308291993213286566645)
      ·
        refine ⟨30897310152374363745615623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329571308291993213286566645 30897310152374363745615623)
        ·
          refine ⟨46345965228561545618423435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30897310152374363745615623 46345965228561545618423435)
          ·
            refine ⟨69518947842842318427635153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46345965228561545618423435 69518947842842318427635153)
            ·
              refine ⟨52139210882131738820726365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69518947842842318427635153 52139210882131738820726365)
              ·
                refine ⟨19552204080799402057772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52139210882131738820726365 19552204080799402057772387)
                ·
                  refine ⟨29328306121199103086658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19552204080799402057772387 29328306121199103086658581)
                  ·
                    refine ⟨1374764349431207957187121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29328306121199103086658581 1374764349431207957187121)
                    ·
                      rfl

theorem cell23_8032032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_8032032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032032 prefixEnd_8032032 := by exact prefixLift 8032032
  have htrace : WordTrace (prefixWord ++ tailWord_8032032) baseStart_8032032 baseEnd_8032032 := by
    simpa [prefixWord, tailWord_8032032, baseEnd_8032032] using wordTrace_append hprefix tailTrace_8032032
  have hstable : (prefixWord ++ tailWord_8032032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032032).length < 2 ^ (prefixWord ++ tailWord_8032032).sum := by decide
  have hdescent : baseEnd_8032032 < baseStart_8032032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032036 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_8032036 : Nat := 118140960795 + 8032036 * 2 ^ 59
def prefixEnd_8032036 : Nat := 4983230072969 + 3 ^ 40 * 8032036 * 2
def baseEnd_8032036 : Nat := 1374765034072080618637115

theorem tailTrace_8032036 : CollatzResearch.WordTrace tailWord_8032036 prefixEnd_8032036 1374765034072080618637115 := by
  unfold tailWord_8032036
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476209964656404691157981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195301613286208539588210641 146476209964656404691157981)
  ·
    refine ⟨54928578736746151759184243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146476209964656404691157981 54928578736746151759184243)
    ·
      refine ⟨82392868105119227638776365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54928578736746151759184243 82392868105119227638776365)
      ·
        refine ⟨30897325539419710364541137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82392868105119227638776365 30897325539419710364541137)
        ·
          refine ⟨23172994154564782773405853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30897325539419710364541137 23172994154564782773405853)
          ·
            refine ⟨8689872807961793540027195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23172994154564782773405853 8689872807961793540027195)
            ·
              refine ⟨13034809211942690310040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689872807961793540027195 13034809211942690310040793)
              ·
                refine ⟨9776106908957017732530595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13034809211942690310040793 9776106908957017732530595)
                ·
                  refine ⟨14664160363435526598795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776106908957017732530595 14664160363435526598795893)
                  ·
                    refine ⟨1374765034072080618637115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14664160363435526598795893 1374765034072080618637115)
                    ·
                      rfl

theorem cell23_8032036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_8032036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032036 prefixEnd_8032036 := by exact prefixLift 8032036
  have htrace : WordTrace (prefixWord ++ tailWord_8032036) baseStart_8032036 baseEnd_8032036 := by
    simpa [prefixWord, tailWord_8032036, baseEnd_8032036] using wordTrace_append hprefix tailTrace_8032036
  have hstable : (prefixWord ++ tailWord_8032036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032036).length < 2 ^ (prefixWord ++ tailWord_8032036).sum := by decide
  have hdescent : baseEnd_8032036 < baseStart_8032036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032056 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_8032056 : Nat := 118140960795 + 8032056 * 2 ^ 59
def prefixEnd_8032056 : Nat := 4983230072969 + 3 ^ 40 * 8032056 * 2
def baseEnd_8032056 : Nat := 4124305371829331777661253

theorem tailTrace_8032056 : CollatzResearch.WordTrace tailWord_8032056 prefixEnd_8032056 4124305371829331777661253 := by
  unfold tailWord_8032056
  simp only [CollatzResearch.WordTrace]
  refine ⟨146476574694620176399022011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195302099592826901865362681 146476574694620176399022011)
  ·
    refine ⟨219714862041930264598533017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146476574694620176399022011 219714862041930264598533017)
    ·
      refine ⟨164786146531447698448899763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219714862041930264598533017 164786146531447698448899763)
      ·
        refine ⟨247179219797171547673349645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164786146531447698448899763 247179219797171547673349645)
        ·
          refine ⟨92692207423939330377506117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247179219797171547673349645 92692207423939330377506117)
          ·
            refine ⟨17379788891988624445782397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92692207423939330377506117 17379788891988624445782397)
            ·
              refine ⟨6517420834495734167168399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17379788891988624445782397 6517420834495734167168399)
              ·
                refine ⟨9776131251743601250752599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517420834495734167168399 9776131251743601250752599)
                ·
                  refine ⟨14664196877615401876128899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776131251743601250752599 14664196877615401876128899)
                  ·
                    refine ⟨21996295316423102814193349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14664196877615401876128899 21996295316423102814193349)
                    ·
                      refine ⟨4124305371829331777661253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21996295316423102814193349 4124305371829331777661253)
                      ·
                        rfl

theorem cell23_8032056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_8032056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032056 prefixEnd_8032056 := by exact prefixLift 8032056
  have htrace : WordTrace (prefixWord ++ tailWord_8032056) baseStart_8032056 baseEnd_8032056 := by
    simpa [prefixWord, tailWord_8032056, baseEnd_8032056] using wordTrace_append hprefix tailTrace_8032056
  have hstable : (prefixWord ++ tailWord_8032056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032056).length < 2 ^ (prefixWord ++ tailWord_8032056).sum := by decide
  have hdescent : baseEnd_8032056 < baseStart_8032056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032062 : List Nat := [4, 2, 1, 2, 2, 12]
def baseStart_8032062 : Nat := 118140960795 + 8032062 * 2 ^ 59
def prefixEnd_8032062 : Nat := 4983230072969 + 3 ^ 40 * 8032062 * 2
def baseEnd_8032062 : Nat := 16972462768367319976075

theorem tailTrace_8032062 : CollatzResearch.WordTrace tailWord_8032062 prefixEnd_8032062 16972462768367319976075 := by
  unfold tailWord_8032062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36619171028402326977845305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195302245484812410548508293 36619171028402326977845305)
  ·
    refine ⟨27464378271301745233383979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36619171028402326977845305 27464378271301745233383979)
    ·
      refine ⟨41196567406952617850075969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27464378271301745233383979 41196567406952617850075969)
      ·
        refine ⟨30897425555214463387556977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41196567406952617850075969 30897425555214463387556977)
        ·
          refine ⟨23173069166410847540667733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30897425555214463387556977 23173069166410847540667733)
          ·
            refine ⟨16972462768367319976075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23173069166410847540667733 16972462768367319976075)
            ·
              rfl

theorem cell23_8032062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 12].length) (baseStart_8032062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032062 prefixEnd_8032062 := by exact prefixLift 8032062
  have htrace : WordTrace (prefixWord ++ tailWord_8032062) baseStart_8032062 baseEnd_8032062 := by
    simpa [prefixWord, tailWord_8032062, baseEnd_8032062] using wordTrace_append hprefix tailTrace_8032062
  have hstable : (prefixWord ++ tailWord_8032062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032062).length < 2 ^ (prefixWord ++ tailWord_8032062).sum := by decide
  have hdescent : baseEnd_8032062 < baseStart_8032062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032073 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 1, 2, 2]
def baseStart_8032073 : Nat := 118140960795 + 8032073 * 2 ^ 59
def prefixEnd_8032073 : Nat := 4983230072969 + 3 ^ 40 * 8032073 * 2
def baseEnd_8032073 : Nat := 4124314101000458211148675

theorem tailTrace_8032073 : CollatzResearch.WordTrace tailWord_8032073 prefixEnd_8032073 4124314101000458211148675 := by
  unfold tailWord_8032073
  simp only [CollatzResearch.WordTrace]
  refine ⟨292953769430178764701412873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195302512953452509800941915 292953769430178764701412873)
  ·
    refine ⟨219715327072634073526059655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292953769430178764701412873 219715327072634073526059655)
    ·
      refine ⟨329572990608951110289089483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219715327072634073526059655 329572990608951110289089483)
      ·
        refine ⟨494359485913426665433634225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329572990608951110289089483 494359485913426665433634225)
        ·
          refine ⟨370769614435069999075225669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494359485913426665433634225 370769614435069999075225669)
          ·
            refine ⟨69519302706575624826604813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370769614435069999075225669 69519302706575624826604813)
            ·
              refine ⟨26069738514965859309976805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69519302706575624826604813 26069738514965859309976805)
              ·
                refine ⟨4888075971556098620620651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26069738514965859309976805 4888075971556098620620651)
                ·
                  refine ⟨7332113957334147930930977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888075971556098620620651 7332113957334147930930977)
                  ·
                    refine ⟨5499085468000610948198233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332113957334147930930977 5499085468000610948198233)
                    ·
                      refine ⟨4124314101000458211148675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499085468000610948198233 4124314101000458211148675)
                      ·
                        rfl

theorem cell23_8032073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 2, 2].length) (baseStart_8032073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032073 prefixEnd_8032073 := by exact prefixLift 8032073
  have htrace : WordTrace (prefixWord ++ tailWord_8032073) baseStart_8032073 baseEnd_8032073 := by
    simpa [prefixWord, tailWord_8032073, baseEnd_8032073] using wordTrace_append hprefix tailTrace_8032073
  have hstable : (prefixWord ++ tailWord_8032073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032073).length < 2 ^ (prefixWord ++ tailWord_8032073).sum := by decide
  have hdescent : baseEnd_8032073 < baseStart_8032073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032089 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_8032089 : Nat := 118140960795 + 8032089 * 2 ^ 59
def prefixEnd_8032089 : Nat := 4983230072969 + 3 ^ 40 * 8032089 * 2
def baseEnd_8032089 : Nat := 4124322316690930148548601

theorem tailTrace_8032089 : CollatzResearch.WordTrace tailWord_8032089 prefixEnd_8032089 4124322316690930148548601 := by
  unfold tailWord_8032089
  simp only [CollatzResearch.WordTrace]
  refine ⟨292954352998120799433995321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195302901998747199622663547 292954352998120799433995321)
  ·
    refine ⟨219715764748590599575496491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292954352998120799433995321 219715764748590599575496491)
    ·
      refine ⟨329573647122885899363244737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219715764748590599575496491 329573647122885899363244737)
      ·
        refine ⟨247180235342164424522433553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329573647122885899363244737 247180235342164424522433553)
        ·
          refine ⟨185385176506623318391825165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247180235342164424522433553 185385176506623318391825165)
          ·
            refine ⟨69519441189983744396934437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185385176506623318391825165 69519441189983744396934437)
            ·
              refine ⟨13034895223121952074425207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69519441189983744396934437 13034895223121952074425207)
              ·
                refine ⟨19552342834682928111637811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13034895223121952074425207 19552342834682928111637811)
                ·
                  refine ⟨29328514252024392167456717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19552342834682928111637811 29328514252024392167456717)
                  ·
                    refine ⟨10998192844509147062796269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29328514252024392167456717 10998192844509147062796269)
                    ·
                      refine ⟨4124322316690930148548601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998192844509147062796269 4124322316690930148548601)
                      ·
                        rfl

theorem cell23_8032089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_8032089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032089 prefixEnd_8032089 := by exact prefixLift 8032089
  have htrace : WordTrace (prefixWord ++ tailWord_8032089) baseStart_8032089 baseEnd_8032089 := by
    simpa [prefixWord, tailWord_8032089, baseEnd_8032089] using wordTrace_append hprefix tailTrace_8032089
  have hstable : (prefixWord ++ tailWord_8032089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032089).length < 2 ^ (prefixWord ++ tailWord_8032089).sum := by decide
  have hdescent : baseEnd_8032089 < baseStart_8032089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032110 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_8032110 : Nat := 118140960795 + 8032110 * 2 ^ 59
def prefixEnd_8032110 : Nat := 4983230072969 + 3 ^ 40 * 8032110 * 2
def baseEnd_8032110 : Nat := 4124333099784674566386005

theorem tailTrace_8032110 : CollatzResearch.WordTrace tailWord_8032110 prefixEnd_8032110 4124333099784674566386005 := by
  unfold tailWord_8032110
  simp only [CollatzResearch.WordTrace]
  refine ⟨36619389866380590002563723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195303412620696480013673189 36619389866380590002563723)
  ·
    refine ⟨54929084799570885003845585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36619389866380590002563723 54929084799570885003845585)
    ·
      refine ⟨41196813599678163752884189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54929084799570885003845585 41196813599678163752884189)
      ·
        refine ⟨15448805099879311407331571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41196813599678163752884189 15448805099879311407331571)
        ·
          refine ⟨23173207649818967110997357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15448805099879311407331571 23173207649818967110997357)
          ·
            refine ⟨8689952868682112666624009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23173207649818967110997357 8689952868682112666624009)
            ·
              refine ⟨6517464651511584499968007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689952868682112666624009 6517464651511584499968007)
              ·
                refine ⟨9776196977267376749952011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517464651511584499968007 9776196977267376749952011)
                ·
                  refine ⟨14664295465901065124928017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776196977267376749952011 14664295465901065124928017)
                  ·
                    refine ⟨10998221599425798843696013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14664295465901065124928017 10998221599425798843696013)
                    ·
                      refine ⟨4124333099784674566386005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998221599425798843696013 4124333099784674566386005)
                      ·
                        rfl

theorem cell23_8032110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_8032110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032110 prefixEnd_8032110 := by exact prefixLift 8032110
  have htrace : WordTrace (prefixWord ++ tailWord_8032110) baseStart_8032110 baseEnd_8032110 := by
    simpa [prefixWord, tailWord_8032110, baseEnd_8032110] using wordTrace_append hprefix tailTrace_8032110
  have hstable : (prefixWord ++ tailWord_8032110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032110).length < 2 ^ (prefixWord ++ tailWord_8032110).sum := by decide
  have hdescent : baseEnd_8032110 < baseStart_8032110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032122 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_8032122 : Nat := 118140960795 + 8032122 * 2 ^ 59
def prefixEnd_8032122 : Nat := 4983230072969 + 3 ^ 40 * 8032122 * 2
def baseEnd_8032122 : Nat := 1374779753850842839811983

theorem tailTrace_8032122 : CollatzResearch.WordTrace tailWord_8032122 prefixEnd_8032122 1374779753850842839811983 := by
  unfold tailWord_8032122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238889151750311517486655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195303704404667497379964413 73238889151750311517486655)
  ·
    refine ⟨109858333727625467276229983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73238889151750311517486655 109858333727625467276229983)
    ·
      refine ⟨164787500591438200914344975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109858333727625467276229983 164787500591438200914344975)
      ·
        refine ⟨247181250887157301371517463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164787500591438200914344975 247181250887157301371517463)
        ·
          refine ⟨370771876330735952057276195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247181250887157301371517463 370771876330735952057276195)
          ·
            refine ⟨556157814496103928085914293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370771876330735952057276195 556157814496103928085914293)
            ·
              refine ⟨52139795109009743258054465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556157814496103928085914293 52139795109009743258054465)
              ·
                refine ⟨39104846331757307443540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52139795109009743258054465 39104846331757307443540849)
                ·
                  refine ⟨29328634748817980582655637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39104846331757307443540849 29328634748817980582655637)
                  ·
                    refine ⟨1374779753850842839811983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29328634748817980582655637 1374779753850842839811983)
                    ·
                      rfl

theorem cell23_8032122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_8032122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032122 prefixEnd_8032122 := by exact prefixLift 8032122
  have htrace : WordTrace (prefixWord ++ tailWord_8032122) baseStart_8032122 baseEnd_8032122 := by
    simpa [prefixWord, tailWord_8032122, baseEnd_8032122] using wordTrace_append hprefix tailTrace_8032122
  have hstable : (prefixWord ++ tailWord_8032122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032122).length < 2 ^ (prefixWord ++ tailWord_8032122).sum := by decide
  have hdescent : baseEnd_8032122 < baseStart_8032122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032169 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 5]
def baseStart_8032169 : Nat := 118140960795 + 8032169 * 2 ^ 59
def prefixEnd_8032169 : Nat := 4983230072969 + 3 ^ 40 * 8032169 * 2
def baseEnd_8032169 : Nat := 458262599460365537283137

theorem tailTrace_8032169 : CollatzResearch.WordTrace tailWord_8032169 prefixEnd_8032169 458262599460365537283137 := by
  unfold tailWord_8032169
  simp only [CollatzResearch.WordTrace]
  refine ⟨292957270837830973096907561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195304847225220648731271707 292957270837830973096907561)
  ·
    refine ⟨219717953128373229822680671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292957270837830973096907561 219717953128373229822680671)
    ·
      refine ⟨329576929692559844734021007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219717953128373229822680671 329576929692559844734021007)
      ·
        refine ⟨494365394538839767101031511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329576929692559844734021007 494365394538839767101031511)
        ·
          refine ⟨741548091808259650651547267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494365394538839767101031511 741548091808259650651547267)
          ·
            refine ⟨1112322137712389475977320901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741548091808259650651547267 1112322137712389475977320901)
            ·
              refine ⟨208560400821073026745747669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1112322137712389475977320901 208560400821073026745747669)
              ·
                refine ⟨4888134394243899064353461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208560400821073026745747669 4888134394243899064353461)
                ·
                  refine ⟨458262599460365537283137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4888134394243899064353461 458262599460365537283137)
                  ·
                    rfl

theorem cell23_8032169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 5].length) (baseStart_8032169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032169 prefixEnd_8032169 := by exact prefixLift 8032169
  have htrace : WordTrace (prefixWord ++ tailWord_8032169) baseStart_8032169 baseEnd_8032169 := by
    simpa [prefixWord, tailWord_8032169, baseEnd_8032169] using wordTrace_append hprefix tailTrace_8032169
  have hstable : (prefixWord ++ tailWord_8032169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032169).length < 2 ^ (prefixWord ++ tailWord_8032169).sum := by decide
  have hdescent : baseEnd_8032169 < baseStart_8032169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032237 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 5]
def baseStart_8032237 : Nat := 118140960795 + 8032237 * 2 ^ 59
def prefixEnd_8032237 : Nat := 4983230072969 + 3 ^ 40 * 8032237 * 2
def baseEnd_8032237 : Nat := 458266479091977285499769

theorem tailTrace_8032237 : CollatzResearch.WordTrace tailWord_8032237 prefixEnd_8032237 458266479091977285499769 := by
  unfold tailWord_8032237
  simp only [CollatzResearch.WordTrace]
  refine ⟨292959751001584620710382965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195306500667723080473588643 292959751001584620710382965)
  ·
    refine ⟨27464976656398558191598403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292959751001584620710382965 27464976656398558191598403)
    ·
      refine ⟨41197464984597837287397605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27464976656398558191598403 41197464984597837287397605)
      ·
        refine ⟨7724524684612094491387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41197464984597837287397605 7724524684612094491387051)
        ·
          refine ⟨11586787026918141737080577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724524684612094491387051 11586787026918141737080577)
          ·
            refine ⟨8690090270188606302810433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11586787026918141737080577 8690090270188606302810433)
            ·
              refine ⟨6517567702641454727107825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690090270188606302810433 6517567702641454727107825)
              ·
                refine ⟨4888175776981091045330869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517567702641454727107825 4888175776981091045330869)
                ·
                  refine ⟨458266479091977285499769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4888175776981091045330869 458266479091977285499769)
                  ·
                    rfl

theorem cell23_8032237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_8032237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032237 prefixEnd_8032237 := by exact prefixLift 8032237
  have htrace : WordTrace (prefixWord ++ tailWord_8032237) baseStart_8032237 baseEnd_8032237 := by
    simpa [prefixWord, tailWord_8032237, baseEnd_8032237] using wordTrace_append hprefix tailTrace_8032237
  have hstable : (prefixWord ++ tailWord_8032237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032237).length < 2 ^ (prefixWord ++ tailWord_8032237).sum := by decide
  have hdescent : baseEnd_8032237 < baseStart_8032237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032329 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_8032329 : Nat := 118140960795 + 8032329 * 2 ^ 59
def prefixEnd_8032329 : Nat := 4983230072969 + 3 ^ 40 * 8032329 * 2
def baseEnd_8032329 : Nat := 4124445552048009209547497

theorem tailTrace_8032329 : CollatzResearch.WordTrace tailWord_8032329 prefixEnd_8032329 4124445552048009209547497 := by
  unfold tailWord_8032329
  simp only [CollatzResearch.WordTrace]
  refine ⟨292963106517251320422732041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195308737678167546948488027 292963106517251320422732041)
  ·
    refine ⟨219722329887938490317049031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292963106517251320422732041 219722329887938490317049031)
    ·
      refine ⟨329583494831907735475573547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219722329887938490317049031 329583494831907735475573547)
      ·
        refine ⟨494375242247861603213360321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329583494831907735475573547 494375242247861603213360321)
        ·
          refine ⟨370781431685896202410020241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494375242247861603213360321 370781431685896202410020241)
          ·
            refine ⟨278086073764422151807515181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370781431685896202410020241 278086073764422151807515181)
            ·
              refine ⟨104282277661658306927818193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278086073764422151807515181 104282277661658306927818193)
              ·
                refine ⟨78211708246243730195863645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104282277661658306927818193 78211708246243730195863645)
                ·
                  refine ⟨29329390592341398823448867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78211708246243730195863645 29329390592341398823448867)
                  ·
                    refine ⟨43994085888512098235173301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29329390592341398823448867 43994085888512098235173301)
                    ·
                      refine ⟨4124445552048009209547497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43994085888512098235173301 4124445552048009209547497)
                      ·
                        rfl

theorem cell23_8032329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_8032329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032329 prefixEnd_8032329 := by exact prefixLift 8032329
  have htrace : WordTrace (prefixWord ++ tailWord_8032329) baseStart_8032329 baseEnd_8032329 := by
    simpa [prefixWord, tailWord_8032329, baseEnd_8032329] using wordTrace_append hprefix tailTrace_8032329
  have hstable : (prefixWord ++ tailWord_8032329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032329).length < 2 ^ (prefixWord ++ tailWord_8032329).sum := by decide
  have hdescent : baseEnd_8032329 < baseStart_8032329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032343 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_8032343 : Nat := 118140960795 + 8032343 * 2 ^ 59
def prefixEnd_8032343 : Nat := 4983230072969 + 3 ^ 40 * 8032343 * 2
def baseEnd_8032343 : Nat := 4124452740777172154772433

theorem tailTrace_8032343 : CollatzResearch.WordTrace tailWord_8032343 prefixEnd_8032343 4124452740777172154772433 := by
  unfold tailWord_8032343
  simp only [CollatzResearch.WordTrace]
  refine ⟨292963617139200600813741683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195309078092800400542494455 292963617139200600813741683)
  ·
    refine ⟨439445425708800901220612525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292963617139200600813741683 439445425708800901220612525)
    ·
      refine ⟨164792034640800337957729697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439445425708800901220612525 164792034640800337957729697)
      ·
        refine ⟨123594025980600253468297273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164792034640800337957729697 123594025980600253468297273)
        ·
          refine ⟨92695519485450190101222955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123594025980600253468297273 92695519485450190101222955)
          ·
            refine ⟨139043279228175285151834433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92695519485450190101222955 139043279228175285151834433)
            ·
              refine ⟨104282459421131463863875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139043279228175285151834433 104282459421131463863875825)
              ·
                refine ⟨78211844565848597897906869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104282459421131463863875825 78211844565848597897906869)
                ·
                  refine ⟨7332360428048306052928769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78211844565848597897906869 7332360428048306052928769)
                  ·
                    refine ⟨5499270321036229539696577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332360428048306052928769 5499270321036229539696577)
                    ·
                      refine ⟨4124452740777172154772433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499270321036229539696577 4124452740777172154772433)
                      ·
                        rfl

theorem cell23_8032343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_8032343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032343 prefixEnd_8032343 := by exact prefixLift 8032343
  have htrace : WordTrace (prefixWord ++ tailWord_8032343) baseStart_8032343 baseEnd_8032343 := by
    simpa [prefixWord, tailWord_8032343, baseEnd_8032343] using wordTrace_append hprefix tailTrace_8032343
  have hstable : (prefixWord ++ tailWord_8032343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032343).length < 2 ^ (prefixWord ++ tailWord_8032343).sum := by decide
  have hdescent : baseEnd_8032343 < baseStart_8032343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032346 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_8032346 : Nat := 118140960795 + 8032346 * 2 ^ 59
def prefixEnd_8032346 : Nat := 4983230072969 + 3 ^ 40 * 8032346 * 2
def baseEnd_8032346 : Nat := 4124454281219135643034919

theorem tailTrace_8032346 : CollatzResearch.WordTrace tailWord_8032346 prefixEnd_8032346 4124454281219135643034919 := by
  unfold tailWord_8032346
  simp only [CollatzResearch.WordTrace]
  refine ⟨73240931639547433081525223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195309151038793154884067261 73240931639547433081525223)
  ·
    refine ⟨109861397459321149622287835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73240931639547433081525223 109861397459321149622287835)
    ·
      refine ⟨164792096188981724433431753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109861397459321149622287835 164792096188981724433431753)
      ·
        refine ⟨123594072141736293325073815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164792096188981724433431753 123594072141736293325073815)
        ·
          refine ⟨185391108212604439987610723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123594072141736293325073815 185391108212604439987610723)
          ·
            refine ⟨278086662318906659981416085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185391108212604439987610723 278086662318906659981416085)
            ·
              refine ⟨13035312296198749686628879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278086662318906659981416085 13035312296198749686628879)
              ·
                refine ⟨19552968444298124529943319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035312296198749686628879 19552968444298124529943319)
                ·
                  refine ⟨29329452666447186794914979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19552968444298124529943319 29329452666447186794914979)
                  ·
                    refine ⟨43994178999670780192372469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29329452666447186794914979 43994178999670780192372469)
                    ·
                      refine ⟨4124454281219135643034919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43994178999670780192372469 4124454281219135643034919)
                      ·
                        rfl

theorem cell23_8032346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_8032346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032346 prefixEnd_8032346 := by exact prefixLift 8032346
  have htrace : WordTrace (prefixWord ++ tailWord_8032346) baseStart_8032346 baseEnd_8032346 := by
    simpa [prefixWord, tailWord_8032346, baseEnd_8032346] using wordTrace_append hprefix tailTrace_8032346
  have hstable : (prefixWord ++ tailWord_8032346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032346).length < 2 ^ (prefixWord ++ tailWord_8032346).sum := by decide
  have hdescent : baseEnd_8032346 < baseStart_8032346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032354 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8032354 : Nat := 118140960795 + 8032354 * 2 ^ 59
def prefixEnd_8032354 : Nat := 4983230072969 + 3 ^ 40 * 8032354 * 2
def baseEnd_8032354 : Nat := 4124458389064371611734883

theorem tailTrace_8032354 : CollatzResearch.WordTrace tailWord_8032354 prefixEnd_8032354 4124458389064371611734883 := by
  unfold tailWord_8032354
  simp only [CollatzResearch.WordTrace]
  refine ⟨73241004585540187423098029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195309345561440499794928077 73241004585540187423098029)
  ·
    refine ⟨27465376719577570283661761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73241004585540187423098029 27465376719577570283661761)
    ·
      refine ⟨20599032539683177712746321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27465376719577570283661761 20599032539683177712746321)
      ·
        refine ⟨15449274404762383284559741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20599032539683177712746321 15449274404762383284559741)
        ·
          refine ⟨5793477901785893731709903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15449274404762383284559741 5793477901785893731709903)
          ·
            refine ⟨8690216852678840597564855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793477901785893731709903 8690216852678840597564855)
            ·
              refine ⟨13035325279018260896347283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690216852678840597564855 13035325279018260896347283)
              ·
                refine ⟨19552987918527391344520925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13035325279018260896347283 19552987918527391344520925)
                ·
                  refine ⟨7332370469447771754195347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19552987918527391344520925 7332370469447771754195347)
                  ·
                    refine ⟨10998555704171657631293021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332370469447771754195347 10998555704171657631293021)
                    ·
                      refine ⟨4124458389064371611734883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998555704171657631293021 4124458389064371611734883)
                      ·
                        rfl

theorem cell23_8032354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8032354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032354 prefixEnd_8032354 := by exact prefixLift 8032354
  have htrace : WordTrace (prefixWord ++ tailWord_8032354) baseStart_8032354 baseEnd_8032354 := by
    simpa [prefixWord, tailWord_8032354, baseEnd_8032354] using wordTrace_append hprefix tailTrace_8032354
  have hstable : (prefixWord ++ tailWord_8032354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032354).length < 2 ^ (prefixWord ++ tailWord_8032354).sum := by decide
  have hdescent : baseEnd_8032354 < baseStart_8032354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032366 : List Nat := [4, 1, 2, 2, 1, 1, 4, 8]
def baseStart_8032366 : Nat := 118140960795 + 8032366 * 2 ^ 59
def prefixEnd_8032366 : Nat := 4983230072969 + 3 ^ 40 * 8032366 * 2
def baseEnd_8032366 : Nat := 152757946327119465362401

theorem tailTrace_8032366 : CollatzResearch.WordTrace tailWord_8032366 prefixEnd_8032366 152757946327119465362401 := by
  unfold tailWord_8032366
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620557002264659467728619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195309637345411517161219301 36620557002264659467728619)
  ·
    refine ⟨54930835503396989201592929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36620557002264659467728619 54930835503396989201592929)
    ·
      refine ⟨41198126627547741901194697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54930835503396989201592929 41198126627547741901194697)
      ·
        refine ⟨30898594970660806425896023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41198126627547741901194697 30898594970660806425896023)
        ·
          refine ⟨46347892455991209638844035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30898594970660806425896023 46347892455991209638844035)
          ·
            refine ⟨69521838683986814458266053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46347892455991209638844035 69521838683986814458266053)
            ·
              refine ⟨13035344753247527710924885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69521838683986814458266053 13035344753247527710924885)
              ·
                refine ⟨152757946327119465362401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13035344753247527710924885 152757946327119465362401)
                ·
                  rfl

theorem cell23_8032366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_8032366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032366 prefixEnd_8032366 := by exact prefixLift 8032366
  have htrace : WordTrace (prefixWord ++ tailWord_8032366) baseStart_8032366 baseEnd_8032366 := by
    simpa [prefixWord, tailWord_8032366, baseEnd_8032366] using wordTrace_append hprefix tailTrace_8032366
  have hstable : (prefixWord ++ tailWord_8032366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032366).length < 2 ^ (prefixWord ++ tailWord_8032366).sum := by decide
  have hdescent : baseEnd_8032366 < baseStart_8032366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032369 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_8032369 : Nat := 118140960795 + 8032369 * 2 ^ 59
def prefixEnd_8032369 : Nat := 4983230072969 + 3 ^ 40 * 8032369 * 2
def baseEnd_8032369 : Nat := 4124466091274189053047313

theorem tailTrace_8032369 : CollatzResearch.WordTrace tailWord_8032369 prefixEnd_8032369 4124466091274189053047313 := by
  unfold tailWord_8032369
  simp only [CollatzResearch.WordTrace]
  refine ⟨292964565437106407254188161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195309710291404271502792107 292964565437106407254188161)
  ·
    refine ⟨219723424077829805440641121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292964565437106407254188161 219723424077829805440641121)
    ·
      refine ⟨164792568058372354080480841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219723424077829805440641121 164792568058372354080480841)
      ·
        refine ⟨123594426043779265560360631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164792568058372354080480841 123594426043779265560360631)
        ·
          refine ⟨185391639065668898340540947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123594426043779265560360631 185391639065668898340540947)
          ·
            refine ⟨278087458598503347510811421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185391639065668898340540947 278087458598503347510811421)
            ·
              refine ⟨104282796974438755316554283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278087458598503347510811421 104282796974438755316554283)
              ·
                refine ⟨156424195461658132974831425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104282796974438755316554283 156424195461658132974831425)
                ·
                  refine ⟨117318146596243599731123569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156424195461658132974831425 117318146596243599731123569)
                  ·
                    refine ⟨87988609947182699798342677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117318146596243599731123569 87988609947182699798342677)
                    ·
                      refine ⟨4124466091274189053047313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87988609947182699798342677 4124466091274189053047313)
                      ·
                        rfl

theorem cell23_8032369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_8032369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032369 prefixEnd_8032369 := by exact prefixLift 8032369
  have htrace : WordTrace (prefixWord ++ tailWord_8032369) baseStart_8032369 baseEnd_8032369 := by
    simpa [prefixWord, tailWord_8032369, baseEnd_8032369] using wordTrace_append hprefix tailTrace_8032369
  have hstable : (prefixWord ++ tailWord_8032369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032369).length < 2 ^ (prefixWord ++ tailWord_8032369).sum := by decide
  have hdescent : baseEnd_8032369 < baseStart_8032369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032370 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_8032370 : Nat := 118140960795 + 8032370 * 2 ^ 59
def prefixEnd_8032370 : Nat := 4983230072969 + 3 ^ 40 * 8032370 * 2
def baseEnd_8032370 : Nat := 1374822201584947849711603

theorem tailTrace_8032370 : CollatzResearch.WordTrace tailWord_8032370 prefixEnd_8032370 1374822201584947849711603 := by
  unfold tailWord_8032370
  simp only [CollatzResearch.WordTrace]
  refine ⟨73241150477525696106243641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195309734606735189616649709 73241150477525696106243641)
  ·
    refine ⟨54930862858144272079682731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73241150477525696106243641 54930862858144272079682731)
    ·
      refine ⟨82396294287216408119524097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54930862858144272079682731 82396294287216408119524097)
      ·
        refine ⟨61797220715412306089643073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82396294287216408119524097 61797220715412306089643073)
        ·
          refine ⟨46347915536559229567232305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61797220715412306089643073 46347915536559229567232305)
          ·
            refine ⟨34760936652419422175424229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46347915536559229567232305 34760936652419422175424229)
            ·
              refine ⟨6517675622328641657892043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34760936652419422175424229 6517675622328641657892043)
              ·
                refine ⟨9776513433492962486838065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517675622328641657892043 9776513433492962486838065)
                ·
                  refine ⟨7332385075119721865128549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9776513433492962486838065 7332385075119721865128549)
                  ·
                    refine ⟨1374822201584947849711603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332385075119721865128549 1374822201584947849711603)
                    ·
                      rfl

theorem cell23_8032370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_8032370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032370 prefixEnd_8032370 := by exact prefixLift 8032370
  have htrace : WordTrace (prefixWord ++ tailWord_8032370) baseStart_8032370 baseEnd_8032370 := by
    simpa [prefixWord, tailWord_8032370, baseEnd_8032370] using wordTrace_append hprefix tailTrace_8032370
  have hstable : (prefixWord ++ tailWord_8032370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032370).length < 2 ^ (prefixWord ++ tailWord_8032370).sum := by decide
  have hdescent : baseEnd_8032370 < baseStart_8032370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032376 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_8032376 : Nat := 118140960795 + 8032376 * 2 ^ 59
def prefixEnd_8032376 : Nat := 4983230072969 + 3 ^ 40 * 8032376 * 2
def baseEnd_8032376 : Nat := 4124469685638770525659781

theorem tailTrace_8032376 : CollatzResearch.WordTrace tailWord_8032376 prefixEnd_8032376 4124469685638770525659781 := by
  unfold tailWord_8032376
  simp only [CollatzResearch.WordTrace]
  refine ⟨146482410374040523724846491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195309880498720698299795321 146482410374040523724846491)
  ·
    refine ⟨219723615561060785587269737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146482410374040523724846491 219723615561060785587269737)
    ·
      refine ⟨164792711670795589190452303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219723615561060785587269737 164792711670795589190452303)
      ·
        refine ⟨247189067506193383785678455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164792711670795589190452303 247189067506193383785678455)
        ·
          refine ⟨370783601259290075678517683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247189067506193383785678455 370783601259290075678517683)
          ·
            refine ⟨556175401888935113517776525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370783601259290075678517683 556175401888935113517776525)
            ·
              refine ⟨208565775708350667569166197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556175401888935113517776525 208565775708350667569166197)
              ·
                refine ⟨19553041472657875084609331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208565775708350667569166197 19553041472657875084609331)
                ·
                  refine ⟨29329562208986812626913997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19553041472657875084609331 29329562208986812626913997)
                  ·
                    refine ⟨10998585828370054735092749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29329562208986812626913997 10998585828370054735092749)
                    ·
                      refine ⟨4124469685638770525659781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998585828370054735092749 4124469685638770525659781)
                      ·
                        rfl

theorem cell23_8032376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_8032376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032376 prefixEnd_8032376 := by exact prefixLift 8032376
  have htrace : WordTrace (prefixWord ++ tailWord_8032376) baseStart_8032376 baseEnd_8032376 := by
    simpa [prefixWord, tailWord_8032376, baseEnd_8032376] using wordTrace_append hprefix tailTrace_8032376
  have hstable : (prefixWord ++ tailWord_8032376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032376).length < 2 ^ (prefixWord ++ tailWord_8032376).sum := by decide
  have hdescent : baseEnd_8032376 < baseStart_8032376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032380 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_8032380 : Nat := 118140960795 + 8032380 * 2 ^ 59
def prefixEnd_8032380 : Nat := 4983230072969 + 3 ^ 40 * 8032380 * 2
def baseEnd_8032380 : Nat := 4124471739561388510009763

theorem tailTrace_8032380 : CollatzResearch.WordTrace tailWord_8032380 prefixEnd_8032380 4124471739561388510009763 := by
  unfold tailWord_8032380
  simp only [CollatzResearch.WordTrace]
  refine ⟨146482483320033278066419297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195309977760044370755225729 146482483320033278066419297)
  ·
    refine ⟨109861862490024958549814473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146482483320033278066419297 109861862490024958549814473)
    ·
      refine ⟨82396396867518718912360855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109861862490024958549814473 82396396867518718912360855)
      ·
        refine ⟨123594595301278078368541283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82396396867518718912360855 123594595301278078368541283)
        ·
          refine ⟨185391892951917117552811925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123594595301278078368541283 185391892951917117552811925)
          ·
            refine ⟨8690244982121114885288059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185391892951917117552811925 8690244982121114885288059)
            ·
              refine ⟨13035367473181672327932089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690244982121114885288059 13035367473181672327932089)
              ·
                refine ⟨9776525604886254245949067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13035367473181672327932089 9776525604886254245949067)
                ·
                  refine ⟨14664788407329381368923601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776525604886254245949067 14664788407329381368923601)
                  ·
                    refine ⟨10998591305497036026692701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14664788407329381368923601 10998591305497036026692701)
                    ·
                      refine ⟨4124471739561388510009763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998591305497036026692701 4124471739561388510009763)
                      ·
                        rfl

theorem cell23_8032380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_8032380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032380 prefixEnd_8032380 := by exact prefixLift 8032380
  have htrace : WordTrace (prefixWord ++ tailWord_8032380) baseStart_8032380 baseEnd_8032380 := by
    simpa [prefixWord, tailWord_8032380, baseEnd_8032380] using wordTrace_append hprefix tailTrace_8032380
  have hstable : (prefixWord ++ tailWord_8032380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032380).length < 2 ^ (prefixWord ++ tailWord_8032380).sum := by decide
  have hdescent : baseEnd_8032380 < baseStart_8032380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032409 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_8032409 : Nat := 118140960795 + 8032409 * 2 ^ 59
def prefixEnd_8032409 : Nat := 4983230072969 + 3 ^ 40 * 8032409 * 2
def baseEnd_8032409 : Nat := 1374828876833456298849043

theorem tailTrace_8032409 : CollatzResearch.WordTrace tailWord_8032409 prefixEnd_8032409 1374828876833456298849043 := by
  unfold tailWord_8032409
  simp only [CollatzResearch.WordTrace]
  refine ⟨292966024356961494085644281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195310682904640996057096187 292966024356961494085644281)
  ·
    refine ⟨219724518267721120564233211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292966024356961494085644281 219724518267721120564233211)
    ·
      refine ⟨329586777401581680846349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219724518267721120564233211 329586777401581680846349817)
      ·
        refine ⟨247190083051186260634762363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329586777401581680846349817 247190083051186260634762363)
        ·
          refine ⟨370785124576779390952143545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247190083051186260634762363 370785124576779390952143545)
          ·
            refine ⟨278088843432584543214107659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370785124576779390952143545 278088843432584543214107659)
            ·
              refine ⟨417133265148876814821161489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278088843432584543214107659 417133265148876814821161489)
              ·
                refine ⟨312849948861657611115871117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417133265148876814821161489 312849948861657611115871117)
                ·
                  refine ⟨117318730823121604168451669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312849948861657611115871117 117318730823121604168451669)
                  ·
                    refine ⟨1374828876833456298849043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117318730823121604168451669 1374828876833456298849043)
                    ·
                      rfl

theorem cell23_8032409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_8032409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032409 prefixEnd_8032409 := by exact prefixLift 8032409
  have htrace : WordTrace (prefixWord ++ tailWord_8032409) baseStart_8032409 baseEnd_8032409 := by
    simpa [prefixWord, tailWord_8032409, baseEnd_8032409] using wordTrace_append hprefix tailTrace_8032409
  have hstable : (prefixWord ++ tailWord_8032409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032409).length < 2 ^ (prefixWord ++ tailWord_8032409).sum := by decide
  have hdescent : baseEnd_8032409 < baseStart_8032409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032416 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_8032416 : Nat := 118140960795 + 8032416 * 2 ^ 59
def prefixEnd_8032416 : Nat := 4983230072969 + 3 ^ 40 * 8032416 * 2
def baseEnd_8032416 : Nat := 4124490224864950369159597

theorem tailTrace_8032416 : CollatzResearch.WordTrace tailWord_8032416 prefixEnd_8032416 4124490224864950369159597 := by
  unfold tailWord_8032416
  simp only [CollatzResearch.WordTrace]
  refine ⟨146483139833968067140574551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195310853111957422854099401 146483139833968067140574551)
  ·
    refine ⟨219724709750952100710861827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146483139833968067140574551 219724709750952100710861827)
    ·
      refine ⟨329587064626428151066292741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219724709750952100710861827 329587064626428151066292741)
      ·
        refine ⟨61797574617455278324929889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329587064626428151066292741 61797574617455278324929889)
        ·
          refine ⟨46348180963091458743697417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61797574617455278324929889 46348180963091458743697417)
          ·
            refine ⟨34761135722318594057773063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46348180963091458743697417 34761135722318594057773063)
            ·
              refine ⟨52141703583477891086659595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34761135722318594057773063 52141703583477891086659595)
              ·
                refine ⟨78212555375216836629989393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52141703583477891086659595 78212555375216836629989393)
                ·
                  refine ⟨58659416531412627472492045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78212555375216836629989393 58659416531412627472492045)
                  ·
                    refine ⟨21997281199279735302184517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58659416531412627472492045 21997281199279735302184517)
                    ·
                      refine ⟨4124490224864950369159597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21997281199279735302184517 4124490224864950369159597)
                      ·
                        rfl

theorem cell23_8032416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_8032416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032416 prefixEnd_8032416 := by exact prefixLift 8032416
  have htrace : WordTrace (prefixWord ++ tailWord_8032416) baseStart_8032416 baseEnd_8032416 := by
    simpa [prefixWord, tailWord_8032416, baseEnd_8032416] using wordTrace_append hprefix tailTrace_8032416
  have hstable : (prefixWord ++ tailWord_8032416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032416).length < 2 ^ (prefixWord ++ tailWord_8032416).sum := by decide
  have hdescent : baseEnd_8032416 < baseStart_8032416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032473 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 5]
def baseStart_8032473 : Nat := 118140960795 + 8032473 * 2 ^ 59
def prefixEnd_8032473 : Nat := 4983230072969 + 3 ^ 40 * 8032473 * 2
def baseEnd_8032473 : Nat := 458279943695806294016315

theorem tailTrace_8032473 : CollatzResearch.WordTrace tailWord_8032473 prefixEnd_8032473 458279943695806294016315 := by
  unfold tailWord_8032473
  simp only [CollatzResearch.WordTrace]
  refine ⟨292968358628729633015974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195312239085819755343982715 292968358628729633015974073)
  ·
    refine ⟨219726268971547224761980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292968358628729633015974073 219726268971547224761980555)
    ·
      refine ⟨329589403457320837142970833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219726268971547224761980555 329589403457320837142970833)
      ·
        refine ⟨247192052592990627857228125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329589403457320837142970833 247192052592990627857228125)
        ·
          refine ⟨92697019722371485446460547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247192052592990627857228125 92697019722371485446460547)
          ·
            refine ⟨139045529583557228169690821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92697019722371485446460547 139045529583557228169690821)
            ·
              refine ⟨26071036796916980281817029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139045529583557228169690821 26071036796916980281817029)
              ·
                refine ⟨4888319399421933802840693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26071036796916980281817029 4888319399421933802840693)
                ·
                  refine ⟨458279943695806294016315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4888319399421933802840693 458279943695806294016315)
                  ·
                    rfl

theorem cell23_8032473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 5].length) (baseStart_8032473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032473 prefixEnd_8032473 := by exact prefixLift 8032473
  have htrace : WordTrace (prefixWord ++ tailWord_8032473) baseStart_8032473 baseEnd_8032473 := by
    simpa [prefixWord, tailWord_8032473, baseEnd_8032473] using wordTrace_append hprefix tailTrace_8032473
  have hstable : (prefixWord ++ tailWord_8032473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032473).length < 2 ^ (prefixWord ++ tailWord_8032473).sum := by decide
  have hdescent : baseEnd_8032473 < baseStart_8032473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032523 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4]
def baseStart_8032523 : Nat := 118140960795 + 8032523 * 2 ^ 59
def prefixEnd_8032523 : Nat := 4983230072969 + 3 ^ 40 * 8032523 * 2
def baseEnd_8032523 : Nat := 4124545167294981450521605

theorem tailTrace_8032523 : CollatzResearch.WordTrace tailWord_8032523 prefixEnd_8032523 4124545167294981450521605 := by
  unfold tailWord_8032523
  simp only [CollatzResearch.WordTrace]
  refine ⟨292970182278548491555294223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195313454852365661036862815 292970182278548491555294223)
  ·
    refine ⟨439455273417822737332941335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292970182278548491555294223 439455273417822737332941335)
    ·
      refine ⟨659182910126734105999412003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439455273417822737332941335 659182910126734105999412003)
      ·
        refine ⟨988774365190101158999118005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659182910126734105999412003 988774365190101158999118005)
        ·
          refine ⟨92697596736571983656167313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 988774365190101158999118005 92697596736571983656167313)
          ·
            refine ⟨69523197552428987742125485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92697596736571983656167313 69523197552428987742125485)
            ·
              refine ⟨26071199082160870403297057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69523197552428987742125485 26071199082160870403297057)
              ·
                refine ⟨19553399311620652802472793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26071199082160870403297057 19553399311620652802472793)
                ·
                  refine ⟨14665049483715489601854595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19553399311620652802472793 14665049483715489601854595)
                  ·
                    refine ⟨21997574225573234402781893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14665049483715489601854595 21997574225573234402781893)
                    ·
                      refine ⟨4124545167294981450521605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21997574225573234402781893 4124545167294981450521605)
                      ·
                        rfl

theorem cell23_8032523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_8032523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032523 prefixEnd_8032523 := by exact prefixLift 8032523
  have htrace : WordTrace (prefixWord ++ tailWord_8032523) baseStart_8032523 baseEnd_8032523 := by
    simpa [prefixWord, tailWord_8032523, baseEnd_8032523] using wordTrace_append hprefix tailTrace_8032523
  have hstable : (prefixWord ++ tailWord_8032523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032523).length < 2 ^ (prefixWord ++ tailWord_8032523).sum := by decide
  have hdescent : baseEnd_8032523 < baseStart_8032523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032593 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_8032593 : Nat := 118140960795 + 8032593 * 2 ^ 59
def prefixEnd_8032593 : Nat := 4983230072969 + 3 ^ 40 * 8032593 * 2
def baseEnd_8032593 : Nat := 1374860370313598725548761

theorem tailTrace_8032593 : CollatzResearch.WordTrace tailWord_8032593 prefixEnd_8032593 1374860370313598725548761 := by
  unfold tailWord_8032593
  simp only [CollatzResearch.WordTrace]
  refine ⟨292972735388294893510342433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195315156925529929006894955 292972735388294893510342433)
  ·
    refine ⟨219729551541221170132756825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292972735388294893510342433 219729551541221170132756825)
    ·
      refine ⟨164797163655915877599567619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219729551541221170132756825 164797163655915877599567619)
      ·
        refine ⟨247195745483873816399351429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164797163655915877599567619 247195745483873816399351429)
        ·
          refine ⟨46349202278226340574878393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247195745483873816399351429 46349202278226340574878393)
          ·
            refine ⟨34761901708669755431158795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46349202278226340574878393 34761901708669755431158795)
            ·
              refine ⟨52142852563004633146738193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34761901708669755431158795 52142852563004633146738193)
              ·
                refine ⟨39107139422253474860053645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52142852563004633146738193 39107139422253474860053645)
                ·
                  refine ⟨14665177283345053072520117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39107139422253474860053645 14665177283345053072520117)
                  ·
                    refine ⟨1374860370313598725548761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14665177283345053072520117 1374860370313598725548761)
                    ·
                      rfl

theorem cell23_8032593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_8032593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032593 prefixEnd_8032593 := by exact prefixLift 8032593
  have htrace : WordTrace (prefixWord ++ tailWord_8032593) baseStart_8032593 baseEnd_8032593 := by
    simpa [prefixWord, tailWord_8032593, baseEnd_8032593] using wordTrace_append hprefix tailTrace_8032593
  have hstable : (prefixWord ++ tailWord_8032593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032593).length < 2 ^ (prefixWord ++ tailWord_8032593).sum := by decide
  have hdescent : baseEnd_8032593 < baseStart_8032593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032610 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8032610 : Nat := 118140960795 + 8032610 * 2 ^ 59
def prefixEnd_8032610 : Nat := 4983230072969 + 3 ^ 40 * 8032610 * 2
def baseEnd_8032610 : Nat := 1374863280037307536711235

theorem tailTrace_8032610 : CollatzResearch.WordTrace tailWord_8032610 prefixEnd_8032610 1374863280037307536711235 := by
  unfold tailWord_8032610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73243338857308326353427821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195315570286155536942474189 73243338857308326353427821)
  ·
    refine ⟨27466252071490622382535433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73243338857308326353427821 27466252071490622382535433)
    ·
      refine ⟨20599689053617966786901575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27466252071490622382535433 20599689053617966786901575)
      ·
        refine ⟨30899533580426950180352363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599689053617966786901575 30899533580426950180352363)
        ·
          refine ⟨46349300370640425270528545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30899533580426950180352363 46349300370640425270528545)
          ·
            refine ⟨34761975277980318952896409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46349300370640425270528545 34761975277980318952896409)
            ·
              refine ⟨26071481458485239214672307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34761975277980318952896409 26071481458485239214672307)
              ·
                refine ⟨39107222187727858822008461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26071481458485239214672307 39107222187727858822008461)
                ·
                  refine ⟨14665208320397947058253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39107222187727858822008461 14665208320397947058253173)
                  ·
                    refine ⟨1374863280037307536711235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14665208320397947058253173 1374863280037307536711235)
                    ·
                      rfl

theorem cell23_8032610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8032610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032610 prefixEnd_8032610 := by exact prefixLift 8032610
  have htrace : WordTrace (prefixWord ++ tailWord_8032610) baseStart_8032610 baseEnd_8032610 := by
    simpa [prefixWord, tailWord_8032610, baseEnd_8032610] using wordTrace_append hprefix tailTrace_8032610
  have hstable : (prefixWord ++ tailWord_8032610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032610).length < 2 ^ (prefixWord ++ tailWord_8032610).sum := by decide
  have hdescent : baseEnd_8032610 < baseStart_8032610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032624 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 1, 1, 3]
def baseStart_8032624 : Nat := 118140960795 + 8032624 * 2 ^ 59
def prefixEnd_8032624 : Nat := 4983230072969 + 3 ^ 40 * 8032624 * 2
def baseEnd_8032624 : Nat := 4124597028841085555358641

theorem tailTrace_8032624 : CollatzResearch.WordTrace tailWord_8032624 prefixEnd_8032624 4124597028841085555358641 := by
  unfold tailWord_8032624
  simp only [CollatzResearch.WordTrace]
  refine ⟨146486933025591292902360463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195315910700788390536480617 146486933025591292902360463)
  ·
    refine ⟨219730399538386939353540695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146486933025591292902360463 219730399538386939353540695)
    ·
      refine ⟨329595599307580409030311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219730399538386939353540695 329595599307580409030311043)
      ·
        refine ⟨494393398961370613545466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329595599307580409030311043 494393398961370613545466565)
        ·
          refine ⟨92698762305256990039774981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494393398961370613545466565 92698762305256990039774981)
          ·
            refine ⟨17381017932235685632457809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92698762305256990039774981 17381017932235685632457809)
            ·
              refine ⟨13035763449176764224343357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17381017932235685632457809 13035763449176764224343357)
              ·
                refine ⟨4888411293441286584128759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13035763449176764224343357 4888411293441286584128759)
                ·
                  refine ⟨7332616940161929876193139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888411293441286584128759 7332616940161929876193139)
                  ·
                    refine ⟨10998925410242894814289709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332616940161929876193139 10998925410242894814289709)
                    ·
                      refine ⟨4124597028841085555358641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10998925410242894814289709 4124597028841085555358641)
                      ·
                        rfl

theorem cell23_8032624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 1, 3].length) (baseStart_8032624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032624 prefixEnd_8032624 := by exact prefixLift 8032624
  have htrace : WordTrace (prefixWord ++ tailWord_8032624) baseStart_8032624 baseEnd_8032624 := by
    simpa [prefixWord, tailWord_8032624, baseEnd_8032624] using wordTrace_append hprefix tailTrace_8032624
  have hstable : (prefixWord ++ tailWord_8032624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032624).length < 2 ^ (prefixWord ++ tailWord_8032624).sum := by decide
  have hdescent : baseEnd_8032624 < baseStart_8032624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032633 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_8032633 : Nat := 118140960795 + 8032633 * 2 ^ 59
def prefixEnd_8032633 : Nat := 4983230072969 + 3 ^ 40 * 8032633 * 2
def baseEnd_8032633 : Nat := 4124601650166976020146099

theorem tailTrace_8032633 : CollatzResearch.WordTrace tailWord_8032633 prefixEnd_8032633 4124601650166976020146099 := by
  unfold tailWord_8032633
  simp only [CollatzResearch.WordTrace]
  refine ⟨292974194308149980341798553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195316129538766653561199035 292974194308149980341798553)
  ·
    refine ⟨219730645731112485256348915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292974194308149980341798553 219730645731112485256348915)
    ·
      refine ⟨329595968596668727884523373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219730645731112485256348915 329595968596668727884523373)
      ·
        refine ⟨123598488223750772956696265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329595968596668727884523373 123598488223750772956696265)
        ·
          refine ⟨92698866167813079717522199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123598488223750772956696265 92698866167813079717522199)
          ·
            refine ⟨139048299251719619576283299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92698866167813079717522199 139048299251719619576283299)
            ·
              refine ⟨208572448877579429364424949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139048299251719619576283299 208572448877579429364424949)
              ·
                refine ⟨19553667082273071502914839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208572448877579429364424949 19553667082273071502914839)
                ·
                  refine ⟨29330500623409607254372259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19553667082273071502914839 29330500623409607254372259)
                  ·
                    refine ⟨43995750935114410881558389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29330500623409607254372259 43995750935114410881558389)
                    ·
                      refine ⟨4124601650166976020146099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43995750935114410881558389 4124601650166976020146099)
                      ·
                        rfl

theorem cell23_8032633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_8032633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032633 prefixEnd_8032633 := by exact prefixLift 8032633
  have htrace : WordTrace (prefixWord ++ tailWord_8032633) baseStart_8032633 baseEnd_8032633 := by
    simpa [prefixWord, tailWord_8032633, baseEnd_8032633] using wordTrace_append hprefix tailTrace_8032633
  have hstable : (prefixWord ++ tailWord_8032633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032633).length < 2 ^ (prefixWord ++ tailWord_8032633).sum := by decide
  have hdescent : baseEnd_8032633 < baseStart_8032633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032664 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_8032664 : Nat := 118140960795 + 8032664 * 2 ^ 59
def prefixEnd_8032664 : Nat := 4983230072969 + 3 ^ 40 * 8032664 * 2
def baseEnd_8032664 : Nat := 4124617568067265398858457

theorem tailTrace_8032664 : CollatzResearch.WordTrace tailWord_8032664 prefixEnd_8032664 4124617568067265398858457 := by
  unfold tailWord_8032664
  simp only [CollatzResearch.WordTrace]
  refine ⟨146487662485518836318088523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195316883314025115090784697 146487662485518836318088523)
  ·
    refine ⟨219731493728278254477132785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146487662485518836318088523 219731493728278254477132785)
    ·
      refine ⟨164798620296208690857849589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219731493728278254477132785 164798620296208690857849589)
      ·
        refine ⟨15449870652769564767923399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164798620296208690857849589 15449870652769564767923399)
        ·
          refine ⟨23174805979154347151885099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449870652769564767923399 23174805979154347151885099)
          ·
            refine ⟨34762208968731520727827649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23174805979154347151885099 34762208968731520727827649)
            ·
              refine ⟨26071656726548640545870737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34762208968731520727827649 26071656726548640545870737)
              ·
                refine ⟨19553742544911480409403053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26071656726548640545870737 19553742544911480409403053)
                ·
                  refine ⟨7332653454341805153526145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19553742544911480409403053 7332653454341805153526145)
                  ·
                    refine ⟨5499490090756353865144609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332653454341805153526145 5499490090756353865144609)
                    ·
                      refine ⟨4124617568067265398858457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499490090756353865144609 4124617568067265398858457)
                      ·
                        rfl

theorem cell23_8032664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_8032664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032664 prefixEnd_8032664 := by exact prefixLift 8032664
  have htrace : WordTrace (prefixWord ++ tailWord_8032664) baseStart_8032664 baseEnd_8032664 := by
    simpa [prefixWord, tailWord_8032664, baseEnd_8032664] using wordTrace_append hprefix tailTrace_8032664
  have hstable : (prefixWord ++ tailWord_8032664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032664).length < 2 ^ (prefixWord ++ tailWord_8032664).sum := by decide
  have hdescent : baseEnd_8032664 < baseStart_8032664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032697 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_8032697 : Nat := 118140960795 + 8032697 * 2 ^ 59
def prefixEnd_8032697 : Nat := 4983230072969 + 3 ^ 40 * 8032697 * 2
def baseEnd_8032697 : Nat := 4124634512928863769745805

theorem tailTrace_8032697 : CollatzResearch.WordTrace tailWord_8032697 prefixEnd_8032697 4124634512928863769745805 := by
  unfold tailWord_8032697
  simp only [CollatzResearch.WordTrace]
  refine ⟨292976528579918119272128345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195317685719945412848085563 292976528579918119272128345)
  ·
    refine ⟨219732396434938589454096259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292976528579918119272128345 219732396434938589454096259)
    ·
      refine ⟨329598594652407884181144389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219732396434938589454096259 329598594652407884181144389)
      ·
        refine ⟨61799736497326478283964573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329598594652407884181144389 61799736497326478283964573)
        ·
          refine ⟨23174901186497429356486715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61799736497326478283964573 23174901186497429356486715)
          ·
            refine ⟨34762351779746144034730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23174901186497429356486715 34762351779746144034730073)
            ·
              refine ⟨26071763834809608026047555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34762351779746144034730073 26071763834809608026047555)
              ·
                refine ⟨39107645752214412039071333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26071763834809608026047555 39107645752214412039071333)
                ·
                  refine ⟨7332683578540202257325875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39107645752214412039071333 7332683578540202257325875)
                  ·
                    refine ⟨10999025367810303385988813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332683578540202257325875 10999025367810303385988813)
                    ·
                      refine ⟨4124634512928863769745805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999025367810303385988813 4124634512928863769745805)
                      ·
                        rfl

theorem cell23_8032697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_8032697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032697 prefixEnd_8032697 := by exact prefixLift 8032697
  have htrace : WordTrace (prefixWord ++ tailWord_8032697) baseStart_8032697 baseEnd_8032697 := by
    simpa [prefixWord, tailWord_8032697, baseEnd_8032697] using wordTrace_append hprefix tailTrace_8032697
  have hstable : (prefixWord ++ tailWord_8032697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032697).length < 2 ^ (prefixWord ++ tailWord_8032697).sum := by decide
  have hdescent : baseEnd_8032697 < baseStart_8032697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032708 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_8032708 : Nat := 118140960795 + 8032708 * 2 ^ 59
def prefixEnd_8032708 : Nat := 4983230072969 + 3 ^ 40 * 8032708 * 2
def baseEnd_8032708 : Nat := 1374880053738687742236085

theorem tailTrace_8032708 : CollatzResearch.WordTrace tailWord_8032708 prefixEnd_8032708 1374880053738687742236085 := by
  unfold tailWord_8032708
  simp only [CollatzResearch.WordTrace]
  refine ⟨146488464891439134075389389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195317953188585512100519185 146488464891439134075389389)
  ·
    refine ⟨54933174334289675278271021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146488464891439134075389389 54933174334289675278271021)
    ·
      refine ⟨20599940375358628229351633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54933174334289675278271021 20599940375358628229351633)
      ·
        refine ⟨15449955281518971172013725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20599940375358628229351633 15449955281518971172013725)
        ·
          refine ⟨5793733230569614189505147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15449955281518971172013725 5793733230569614189505147)
          ·
            refine ⟨8690599845854421284257721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793733230569614189505147 8690599845854421284257721)
            ·
              refine ⟨6517949884390815963193291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690599845854421284257721 6517949884390815963193291)
              ·
                refine ⟨9776924826586223944789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517949884390815963193291 9776924826586223944789937)
                ·
                  refine ⟨7332693619939667958592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9776924826586223944789937 7332693619939667958592453)
                  ·
                    refine ⟨1374880053738687742236085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332693619939667958592453 1374880053738687742236085)
                    ·
                      rfl

theorem cell23_8032708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_8032708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032708 prefixEnd_8032708 := by exact prefixLift 8032708
  have htrace : WordTrace (prefixWord ++ tailWord_8032708) baseStart_8032708 baseEnd_8032708 := by
    simpa [prefixWord, tailWord_8032708, baseEnd_8032708] using wordTrace_append hprefix tailTrace_8032708
  have hstable : (prefixWord ++ tailWord_8032708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032708).length < 2 ^ (prefixWord ++ tailWord_8032708).sum := by decide
  have hdescent : baseEnd_8032708 < baseStart_8032708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032713 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_8032713 : Nat := 118140960795 + 8032713 * 2 ^ 59
def prefixEnd_8032713 : Nat := 4983230072969 + 3 ^ 40 * 8032713 * 2
def baseEnd_8032713 : Nat := 1374880909539778569048577

theorem tailTrace_8032713 : CollatzResearch.WordTrace tailWord_8032713 prefixEnd_8032713 1374880909539778569048577 := by
  unfold tailWord_8032713
  simp only [CollatzResearch.WordTrace]
  refine ⟨292977112147860154004710793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195318074765240102669807195 292977112147860154004710793)
  ·
    refine ⟨219732834110895115503533095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292977112147860154004710793 219732834110895115503533095)
    ·
      refine ⟨329599251166342673255299643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219732834110895115503533095 329599251166342673255299643)
      ·
        refine ⟨494398876749514009882949465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329599251166342673255299643 494398876749514009882949465)
        ·
          refine ⟨370799157562135507412212099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494398876749514009882949465 370799157562135507412212099)
          ·
            refine ⟨556198736343203261118318149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370799157562135507412212099 556198736343203261118318149)
            ·
              refine ⟨104287263064350611459684653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556198736343203261118318149 104287263064350611459684653)
              ·
                refine ⟨39107723649131479297381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104287263064350611459684653 39107723649131479297381745)
                ·
                  refine ⟨29330792736848609473036309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39107723649131479297381745 29330792736848609473036309)
                  ·
                    refine ⟨1374880909539778569048577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29330792736848609473036309 1374880909539778569048577)
                    ·
                      rfl

theorem cell23_8032713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_8032713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032713 prefixEnd_8032713 := by exact prefixLift 8032713
  have htrace : WordTrace (prefixWord ++ tailWord_8032713) baseStart_8032713 baseEnd_8032713 := by
    simpa [prefixWord, tailWord_8032713, baseEnd_8032713] using wordTrace_append hprefix tailTrace_8032713
  have hstable : (prefixWord ++ tailWord_8032713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032713).length < 2 ^ (prefixWord ++ tailWord_8032713).sum := by decide
  have hdescent : baseEnd_8032713 < baseStart_8032713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032724 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_8032724 : Nat := 118140960795 + 8032724 * 2 ^ 59
def prefixEnd_8032724 : Nat := 4983230072969 + 3 ^ 40 * 8032724 * 2
def baseEnd_8032724 : Nat := 4124648376906535164108181

theorem tailTrace_8032724 : CollatzResearch.WordTrace tailWord_8032724 prefixEnd_8032724 4124648376906535164108181 := by
  unfold tailWord_8032724
  simp only [CollatzResearch.WordTrace]
  refine ⟨146488756675410151441680613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195318342233880201922240817 146488756675410151441680613)
  ·
    refine ⟨27466641876639403395315115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146488756675410151441680613 27466641876639403395315115)
    ·
      refine ⟨41199962814959105092972673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27466641876639403395315115 41199962814959105092972673)
      ·
        refine ⟨30899972111219328819729505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41199962814959105092972673 30899972111219328819729505)
        ·
          refine ⟨23174979083414496614797129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30899972111219328819729505 23174979083414496614797129)
          ·
            refine ⟨17381234312560872461097847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23174979083414496614797129 17381234312560872461097847)
            ·
              refine ⟨26071851468841308691646771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17381234312560872461097847 26071851468841308691646771)
              ·
                refine ⟨39107777203261963037470157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26071851468841308691646771 39107777203261963037470157)
                ·
                  refine ⟨14665416451223236139051309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39107777203261963037470157 14665416451223236139051309)
                  ·
                    refine ⟨5499531169208713552144241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14665416451223236139051309 5499531169208713552144241)
                    ·
                      refine ⟨4124648376906535164108181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499531169208713552144241 4124648376906535164108181)
                      ·
                        rfl

theorem cell23_8032724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_8032724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032724 prefixEnd_8032724 := by exact prefixLift 8032724
  have htrace : WordTrace (prefixWord ++ tailWord_8032724) baseStart_8032724 baseEnd_8032724 := by
    simpa [prefixWord, tailWord_8032724, baseEnd_8032724] using wordTrace_append hprefix tailTrace_8032724
  have hstable : (prefixWord ++ tailWord_8032724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032724).length < 2 ^ (prefixWord ++ tailWord_8032724).sum := by decide
  have hdescent : baseEnd_8032724 < baseStart_8032724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032737 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_8032737 : Nat := 118140960795 + 8032737 * 2 ^ 59
def prefixEnd_8032737 : Nat := 4983230072969 + 3 ^ 40 * 8032737 * 2
def baseEnd_8032737 : Nat := 4124655052155043613245621

theorem tailTrace_8032737 : CollatzResearch.WordTrace tailWord_8032737 prefixEnd_8032737 4124655052155043613245621 := by
  unfold tailWord_8032737
  simp only [CollatzResearch.WordTrace]
  refine ⟨292977987499773206103584465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195318658333182137402389643 292977987499773206103584465)
  ·
    refine ⟨219733490624829904577688349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292977987499773206103584465 219733490624829904577688349)
    ·
      refine ⟨82400058984311214216633131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219733490624829904577688349 82400058984311214216633131)
      ·
        refine ⟨123600088476466821324949697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82400058984311214216633131 123600088476466821324949697)
        ·
          refine ⟨92700066357350115993712273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123600088476466821324949697 92700066357350115993712273)
          ·
            refine ⟨69525049768012586995284205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92700066357350115993712273 69525049768012586995284205)
            ·
              refine ⟨26071893663004720123231577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69525049768012586995284205 26071893663004720123231577)
              ·
                refine ⟨19553920247253540092423683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26071893663004720123231577 19553920247253540092423683)
                ·
                  refine ⟨29330880370880310138635525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19553920247253540092423683 29330880370880310138635525)
                  ·
                    refine ⟨5499540069540058150994161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29330880370880310138635525 5499540069540058150994161)
                    ·
                      refine ⟨4124655052155043613245621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499540069540058150994161 4124655052155043613245621)
                      ·
                        rfl

theorem cell23_8032737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_8032737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032737 prefixEnd_8032737 := by exact prefixLift 8032737
  have htrace : WordTrace (prefixWord ++ tailWord_8032737) baseStart_8032737 baseEnd_8032737 := by
    simpa [prefixWord, tailWord_8032737, baseEnd_8032737] using wordTrace_append hprefix tailTrace_8032737
  have hstable : (prefixWord ++ tailWord_8032737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032737).length < 2 ^ (prefixWord ++ tailWord_8032737).sum := by decide
  have hdescent : baseEnd_8032737 < baseStart_8032737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032783 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_8032783 : Nat := 118140960795 + 8032783 * 2 ^ 59
def prefixEnd_8032783 : Nat := 4983230072969 + 3 ^ 40 * 8032783 * 2
def baseEnd_8032783 : Nat := 4124678672265150433270409

theorem tailTrace_8032783 : CollatzResearch.WordTrace tailWord_8032783 prefixEnd_8032783 4124678672265150433270409 := by
  unfold tailWord_8032783
  simp only [CollatzResearch.WordTrace]
  refine ⟨292979665257606555959759003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195319776838404370639839335 292979665257606555959759003)
  ·
    refine ⟨439469497886409833939638505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292979665257606555959759003 439469497886409833939638505)
    ·
      refine ⟨329602123414807375454728879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439469497886409833939638505 329602123414807375454728879)
      ·
        refine ⟨494403185122211063182093319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329602123414807375454728879 494403185122211063182093319)
        ·
          refine ⟨741604777683316594773139979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494403185122211063182093319 741604777683316594773139979)
          ·
            refine ⟨1112407166524974892159709969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741604777683316594773139979 1112407166524974892159709969)
            ·
              refine ⟨834305374893731169119782477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112407166524974892159709969 834305374893731169119782477)
              ·
                refine ⟨312864515585149188419918429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834305374893731169119782477 312864515585149188419918429)
                ·
                  refine ⟨117324193344430945657469411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312864515585149188419918429 117324193344430945657469411)
                  ·
                    refine ⟨175986290016646418486204117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117324193344430945657469411 175986290016646418486204117)
                    ·
                      refine ⟨4124678672265150433270409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175986290016646418486204117 4124678672265150433270409)
                      ·
                        rfl

theorem cell23_8032783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_8032783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032783 prefixEnd_8032783 := by exact prefixLift 8032783
  have htrace : WordTrace (prefixWord ++ tailWord_8032783) baseStart_8032783 baseEnd_8032783 := by
    simpa [prefixWord, tailWord_8032783, baseEnd_8032783] using wordTrace_append hprefix tailTrace_8032783
  have hstable : (prefixWord ++ tailWord_8032783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032783).length < 2 ^ (prefixWord ++ tailWord_8032783).sum := by decide
  have hdescent : baseEnd_8032783 < baseStart_8032783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032837 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_8032837 : Nat := 118140960795 + 8032837 * 2 ^ 59
def prefixEnd_8032837 : Nat := 4983230072969 + 3 ^ 40 * 8032837 * 2
def baseEnd_8032837 : Nat := 1374902133406831073998387

theorem tailTrace_8032837 : CollatzResearch.WordTrace tailWord_8032837 prefixEnd_8032837 1374902133406831073998387 := by
  unfold tailWord_8032837
  simp only [CollatzResearch.WordTrace]
  refine ⟨292981634799410923182224765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195321089866273948788149843 292981634799410923182224765)
  ·
    refine ⟨109868113049779096193334287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292981634799410923182224765 109868113049779096193334287)
    ·
      refine ⟨164802169574668644290001431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109868113049779096193334287 164802169574668644290001431)
      ·
        refine ⟨247203254362002966435002147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164802169574668644290001431 247203254362002966435002147)
        ·
          refine ⟨370804881543004449652503221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247203254362002966435002147 370804881543004449652503221)
          ·
            refine ⟨34762957644656667154922177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370804881543004449652503221 34762957644656667154922177)
            ·
              refine ⟨26072218233492500366191633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34762957644656667154922177 26072218233492500366191633)
              ·
                refine ⟨19554163675119375274643725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26072218233492500366191633 19554163675119375274643725)
                ·
                  refine ⟨7332811378169765727991397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19554163675119375274643725 7332811378169765727991397)
                  ·
                    refine ⟨1374902133406831073998387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332811378169765727991397 1374902133406831073998387)
                    ·
                      rfl

theorem cell23_8032837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_8032837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032837 prefixEnd_8032837 := by exact prefixLift 8032837
  have htrace : WordTrace (prefixWord ++ tailWord_8032837) baseStart_8032837 baseEnd_8032837 := by
    simpa [prefixWord, tailWord_8032837, baseEnd_8032837] using wordTrace_append hprefix tailTrace_8032837
  have hstable : (prefixWord ++ tailWord_8032837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032837).length < 2 ^ (prefixWord ++ tailWord_8032837).sum := by decide
  have hdescent : baseEnd_8032837 < baseStart_8032837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032850 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_8032850 : Nat := 118140960795 + 8032850 * 2 ^ 59
def prefixEnd_8032850 : Nat := 4983230072969 + 3 ^ 40 * 8032850 * 2
def baseEnd_8032850 : Nat := 458301452829889074570289

theorem tailTrace_8032850 : CollatzResearch.WordTrace tailWord_8032850 prefixEnd_8032850 458301452829889074570289 := by
  unfold tailWord_8032850
  simp only [CollatzResearch.WordTrace]
  refine ⟨73245527237090956600612001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195321405965575884268298669 73245527237090956600612001)
  ·
    refine ⟨54934145427818217450459001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73245527237090956600612001 54934145427818217450459001)
    ·
      refine ⟨41200609070863663087844251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54934145427818217450459001 41200609070863663087844251)
      ·
        refine ⟨61800913606295494631766377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41200609070863663087844251 61800913606295494631766377)
        ·
          refine ⟨46350685204721620973824783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61800913606295494631766377 46350685204721620973824783)
          ·
            refine ⟨69526027807082431460737175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46350685204721620973824783 69526027807082431460737175)
            ·
              refine ⟨104289041710623647191105763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69526027807082431460737175 104289041710623647191105763)
              ·
                refine ⟨156433562565935470786658645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104289041710623647191105763 156433562565935470786658645)
                ·
                  refine ⟨458301452829889074570289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156433562565935470786658645 458301452829889074570289)
                  ·
                    rfl

theorem cell23_8032850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_8032850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032850 prefixEnd_8032850 := by exact prefixLift 8032850
  have htrace : WordTrace (prefixWord ++ tailWord_8032850) baseStart_8032850 baseEnd_8032850 := by
    simpa [prefixWord, tailWord_8032850, baseEnd_8032850] using wordTrace_append hprefix tailTrace_8032850
  have hstable : (prefixWord ++ tailWord_8032850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032850).length < 2 ^ (prefixWord ++ tailWord_8032850).sum := by decide
  have hdescent : baseEnd_8032850 < baseStart_8032850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032887 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_8032887 : Nat := 118140960795 + 8032887 * 2 ^ 59
def prefixEnd_8032887 : Nat := 4983230072969 + 3 ^ 40 * 8032887 * 2
def baseEnd_8032887 : Nat := 4124732074253218026369931

theorem tailTrace_8032887 : CollatzResearch.WordTrace tailWord_8032887 prefixEnd_8032887 4124732074253218026369931 := by
  unfold tailWord_8032887
  simp only [CollatzResearch.WordTrace]
  refine ⟨292983458449229781721544915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195322305632819854481029943 292983458449229781721544915)
  ·
    refine ⟨439475187673844672582317373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292983458449229781721544915 439475187673844672582317373)
    ·
      refine ⟨164803195377691752218369015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439475187673844672582317373 164803195377691752218369015)
      ·
        refine ⟨247204793066537628327553523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164803195377691752218369015 247204793066537628327553523)
        ·
          refine ⟨370807189599806442491330285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247204793066537628327553523 370807189599806442491330285)
          ·
            refine ⟨139052696099927415934248857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370807189599806442491330285 139052696099927415934248857)
            ·
              refine ⟨104289522074945561950686643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139052696099927415934248857 104289522074945561950686643)
              ·
                refine ⟨156434283112418342926029965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104289522074945561950686643 156434283112418342926029965)
                ·
                  refine ⟨58662856167156878597261237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156434283112418342926029965 58662856167156878597261237)
                  ·
                    refine ⟨5499642765670957368493241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58662856167156878597261237 5499642765670957368493241)
                    ·
                      refine ⟨4124732074253218026369931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499642765670957368493241 4124732074253218026369931)
                      ·
                        rfl

theorem cell23_8032887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_8032887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032887 prefixEnd_8032887 := by exact prefixLift 8032887
  have htrace : WordTrace (prefixWord ++ tailWord_8032887) baseStart_8032887 baseEnd_8032887 := by
    simpa [prefixWord, tailWord_8032887, baseEnd_8032887] using wordTrace_append hprefix tailTrace_8032887
  have hstable : (prefixWord ++ tailWord_8032887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032887).length < 2 ^ (prefixWord ++ tailWord_8032887).sum := by decide
  have hdescent : baseEnd_8032887 < baseStart_8032887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032897 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_8032897 : Nat := 118140960795 + 8032897 * 2 ^ 59
def prefixEnd_8032897 : Nat := 4983230072969 + 3 ^ 40 * 8032897 * 2
def baseEnd_8032897 : Nat := 1374912403019920995748295

theorem tailTrace_8032897 : CollatzResearch.WordTrace tailWord_8032897 prefixEnd_8032897 1374912403019920995748295 := by
  unfold tailWord_8032897
  simp only [CollatzResearch.WordTrace]
  refine ⟨292983823179193553429408945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195322548786129035619605963 292983823179193553429408945)
  ·
    refine ⟨219737867384395165072056709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292983823179193553429408945 219737867384395165072056709)
    ·
      refine ⟨41200850134574093451010633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219737867384395165072056709 41200850134574093451010633)
      ·
        refine ⟨30900637600930570088257975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41200850134574093451010633 30900637600930570088257975)
        ·
          refine ⟨46350956401395855132386963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30900637600930570088257975 46350956401395855132386963)
          ·
            refine ⟨69526434602093782698580445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46350956401395855132386963 69526434602093782698580445)
            ·
              refine ⟨26072412975785168511967667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69526434602093782698580445 26072412975785168511967667)
              ·
                refine ⟨39108619463677752767951501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26072412975785168511967667 39108619463677752767951501)
                ·
                  refine ⟨14665732298879157287981813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39108619463677752767951501 14665732298879157287981813)
                  ·
                    refine ⟨1374912403019920995748295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14665732298879157287981813 1374912403019920995748295)
                    ·
                      rfl

theorem cell23_8032897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_8032897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032897 prefixEnd_8032897 := by exact prefixLift 8032897
  have htrace : WordTrace (prefixWord ++ tailWord_8032897) baseStart_8032897 baseEnd_8032897 := by
    simpa [prefixWord, tailWord_8032897, baseEnd_8032897] using wordTrace_append hprefix tailTrace_8032897
  have hstable : (prefixWord ++ tailWord_8032897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032897).length < 2 ^ (prefixWord ++ tailWord_8032897).sum := by decide
  have hdescent : baseEnd_8032897 < baseStart_8032897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032922 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_8032922 : Nat := 118140960795 + 8032922 * 2 ^ 59
def prefixEnd_8032922 : Nat := 4983230072969 + 3 ^ 40 * 8032922 * 2
def baseEnd_8032922 : Nat := 1374916682025375129810757

theorem tailTrace_8032922 : CollatzResearch.WordTrace tailWord_8032922 prefixEnd_8032922 1374916682025375129810757 := by
  unfold tailWord_8032922
  simp only [CollatzResearch.WordTrace]
  refine ⟨73246183751025745674767255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195323156669401988466046013 73246183751025745674767255)
  ·
    refine ⟨109869275626538618512150883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73246183751025745674767255 109869275626538618512150883)
    ·
      refine ⟨164803913439807927768226325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109869275626538618512150883 164803913439807927768226325)
      ·
        refine ⟨7725183442490996614135609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164803913439807927768226325 7725183442490996614135609)
        ·
          refine ⟨5793887581868247460601707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7725183442490996614135609 5793887581868247460601707)
          ·
            refine ⟨8690831372802371190902561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793887581868247460601707 8690831372802371190902561)
            ·
              refine ⟨6518123529601778393176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8690831372802371190902561 6518123529601778393176921)
              ·
                refine ⟨4888592647201333794882691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518123529601778393176921 4888592647201333794882691)
                ·
                  refine ⟨7332888970802000692324037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888592647201333794882691 7332888970802000692324037)
                  ·
                    refine ⟨1374916682025375129810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332888970802000692324037 1374916682025375129810757)
                    ·
                      rfl

theorem cell23_8032922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_8032922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032922 prefixEnd_8032922 := by exact prefixLift 8032922
  have htrace : WordTrace (prefixWord ++ tailWord_8032922) baseStart_8032922 baseEnd_8032922 := by
    simpa [prefixWord, tailWord_8032922, baseEnd_8032922] using wordTrace_append hprefix tailTrace_8032922
  have hstable : (prefixWord ++ tailWord_8032922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032922).length < 2 ^ (prefixWord ++ tailWord_8032922).sum := by decide
  have hdescent : baseEnd_8032922 < baseStart_8032922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032928 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 1, 1, 3]
def baseStart_8032928 : Nat := 118140960795 + 8032928 * 2 ^ 59
def prefixEnd_8032928 : Nat := 4983230072969 + 3 ^ 40 * 8032928 * 2
def baseEnd_8032928 : Nat := 4124753126960052365957243

theorem tailTrace_8032928 : CollatzResearch.WordTrace tailWord_8032928 prefixEnd_8032928 4124753126960052365957243 := by
  unfold tailWord_8032928
  simp only [CollatzResearch.WordTrace]
  refine ⟨146492476921040622861893719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195323302561387497149191625 146492476921040622861893719)
  ·
    refine ⟨219738715381560934292840579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146492476921040622861893719 219738715381560934292840579)
    ·
      refine ⟨329608073072341401439260869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219738715381560934292840579 329608073072341401439260869)
      ·
        refine ⟨61801513701064012769861413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329608073072341401439260869 61801513701064012769861413)
        ·
          refine ⟨11587783818949502394349015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61801513701064012769861413 11587783818949502394349015)
          ·
            refine ⟨17381675728424253591523523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587783818949502394349015 17381675728424253591523523)
            ·
              refine ⟨26072513592636380387285285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17381675728424253591523523 26072513592636380387285285)
              ·
                refine ⟨4888596298619321322615991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26072513592636380387285285 4888596298619321322615991)
                ·
                  refine ⟨7332894447928981983923987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888596298619321322615991 7332894447928981983923987)
                  ·
                    refine ⟨10999341671893472975885981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332894447928981983923987 10999341671893472975885981)
                    ·
                      refine ⟨4124753126960052365957243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999341671893472975885981 4124753126960052365957243)
                      ·
                        rfl

theorem cell23_8032928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_8032928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032928 prefixEnd_8032928 := by exact prefixLift 8032928
  have htrace : WordTrace (prefixWord ++ tailWord_8032928) baseStart_8032928 baseEnd_8032928 := by
    simpa [prefixWord, tailWord_8032928, baseEnd_8032928] using wordTrace_append hprefix tailTrace_8032928
  have hstable : (prefixWord ++ tailWord_8032928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032928).length < 2 ^ (prefixWord ++ tailWord_8032928).sum := by decide
  have hdescent : baseEnd_8032928 < baseStart_8032928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032937 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_8032937 : Nat := 118140960795 + 8032937 * 2 ^ 59
def prefixEnd_8032937 : Nat := 4983230072969 + 3 ^ 40 * 8032937 * 2
def baseEnd_8032937 : Nat := 4124757748285942830744701

theorem tailTrace_8032937 : CollatzResearch.WordTrace tailWord_8032937 prefixEnd_8032937 4124757748285942830744701 := by
  unfold tailWord_8032937
  simp only [CollatzResearch.WordTrace]
  refine ⟨292985282099048640260865065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195323521399365760173910043 292985282099048640260865065)
  ·
    refine ⟨219738961574286480195648799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292985282099048640260865065 219738961574286480195648799)
    ·
      refine ⟨329608442361429720293473199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219738961574286480195648799 329608442361429720293473199)
      ·
        refine ⟨494412663542144580440209799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329608442361429720293473199 494412663542144580440209799)
        ·
          refine ⟨741618995313216870660314699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494412663542144580440209799 741618995313216870660314699)
          ·
            refine ⟨1112428492969825305990472049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741618995313216870660314699 1112428492969825305990472049)
            ·
              refine ⟨834321369727368979492854037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112428492969825305990472049 834321369727368979492854037)
              ·
                refine ⟨39108814205970420913727533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834321369727368979492854037 39108814205970420913727533)
                ·
                  refine ⟨14665805327238907842647825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39108814205970420913727533 14665805327238907842647825)
                  ·
                    refine ⟨10999353995429180881985869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14665805327238907842647825 10999353995429180881985869)
                    ·
                      refine ⟨4124757748285942830744701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999353995429180881985869 4124757748285942830744701)
                      ·
                        rfl

theorem cell23_8032937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_8032937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032937 prefixEnd_8032937 := by exact prefixLift 8032937
  have htrace : WordTrace (prefixWord ++ tailWord_8032937) baseStart_8032937 baseEnd_8032937 := by
    simpa [prefixWord, tailWord_8032937, baseEnd_8032937] using wordTrace_append hprefix tailTrace_8032937
  have hstable : (prefixWord ++ tailWord_8032937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032937).length < 2 ^ (prefixWord ++ tailWord_8032937).sum := by decide
  have hdescent : baseEnd_8032937 < baseStart_8032937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032947 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_8032947 : Nat := 118140960795 + 8032947 * 2 ^ 59
def prefixEnd_8032947 : Nat := 4983230072969 + 3 ^ 40 * 8032947 * 2
def baseEnd_8032947 : Nat := 4124762883092487791619655

theorem tailTrace_8032947 : CollatzResearch.WordTrace tailWord_8032947 prefixEnd_8032947 4124762883092487791619655 := by
  unfold tailWord_8032947
  simp only [CollatzResearch.WordTrace]
  refine ⟨292985646829012411968729095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195323764552674941312486063 292985646829012411968729095)
  ·
    refine ⟨439478470243518617953093643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292985646829012411968729095 439478470243518617953093643)
    ·
      refine ⟨659217705365277926929640465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439478470243518617953093643 659217705365277926929640465)
      ·
        refine ⟨494413279023958445197230349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659217705365277926929640465 494413279023958445197230349)
        ·
          refine ⟨185404979633984416948961381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494413279023958445197230349 185404979633984416948961381)
          ·
            refine ⟨34763433681372078177930259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185404979633984416948961381 34763433681372078177930259)
            ·
              refine ⟨52145150522058117266895389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34763433681372078177930259 52145150522058117266895389)
              ·
                refine ⟨19554431445771793975085771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52145150522058117266895389 19554431445771793975085771)
                ·
                  refine ⟨29331647168657690962628657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19554431445771793975085771 29331647168657690962628657)
                  ·
                    refine ⟨21998735376493268221971493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29331647168657690962628657 21998735376493268221971493)
                    ·
                      refine ⟨4124762883092487791619655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21998735376493268221971493 4124762883092487791619655)
                      ·
                        rfl

theorem cell23_8032947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_8032947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032947 prefixEnd_8032947 := by exact prefixLift 8032947
  have htrace : WordTrace (prefixWord ++ tailWord_8032947) baseStart_8032947 baseEnd_8032947 := by
    simpa [prefixWord, tailWord_8032947, baseEnd_8032947] using wordTrace_append hprefix tailTrace_8032947
  have hstable : (prefixWord ++ tailWord_8032947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032947).length < 2 ^ (prefixWord ++ tailWord_8032947).sum := by decide
  have hdescent : baseEnd_8032947 < baseStart_8032947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032954 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_8032954 : Nat := 118140960795 + 8032954 * 2 ^ 59
def prefixEnd_8032954 : Nat := 4983230072969 + 3 ^ 40 * 8032954 * 2
def baseEnd_8032954 : Nat := 4124766477457069264232123

theorem tailTrace_8032954 : CollatzResearch.WordTrace tailWord_8032954 prefixEnd_8032954 4124766477457069264232123 := by
  unfold tailWord_8032954
  simp only [CollatzResearch.WordTrace]
  refine ⟨73246475534996763041058479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195323934759991368109489277 73246475534996763041058479)
  ·
    refine ⟨109869713302495144561587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73246475534996763041058479 109869713302495144561587719)
    ·
      refine ⟨164804569953742716842381579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109869713302495144561587719 164804569953742716842381579)
      ·
        refine ⟨247206854930614075263572369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164804569953742716842381579 247206854930614075263572369)
        ·
          refine ⟨185405141197960556447679277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247206854930614075263572369 185405141197960556447679277)
          ·
            refine ⟨69526927949235208667879729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185405141197960556447679277 69526927949235208667879729)
            ·
              refine ⟨52145195961926406500909797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69526927949235208667879729 52145195961926406500909797)
              ·
                refine ⟨9777224242861201218920587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52145195961926406500909797 9777224242861201218920587)
                ·
                  refine ⟨14665836364291801828380881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777224242861201218920587 14665836364291801828380881)
                  ·
                    refine ⟨10999377273218851371285661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14665836364291801828380881 10999377273218851371285661)
                    ·
                      refine ⟨4124766477457069264232123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999377273218851371285661 4124766477457069264232123)
                      ·
                        rfl

theorem cell23_8032954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_8032954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032954 prefixEnd_8032954 := by exact prefixLift 8032954
  have htrace : WordTrace (prefixWord ++ tailWord_8032954) baseStart_8032954 baseEnd_8032954 := by
    simpa [prefixWord, tailWord_8032954, baseEnd_8032954] using wordTrace_append hprefix tailTrace_8032954
  have hstable : (prefixWord ++ tailWord_8032954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032954).length < 2 ^ (prefixWord ++ tailWord_8032954).sum := by decide
  have hdescent : baseEnd_8032954 < baseStart_8032954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032964 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_8032964 : Nat := 118140960795 + 8032964 * 2 ^ 59
def prefixEnd_8032964 : Nat := 4983230072969 + 3 ^ 40 * 8032964 * 2
def baseEnd_8032964 : Nat := 4124771612263614225107077

theorem tailTrace_8032964 : CollatzResearch.WordTrace tailWord_8032964 prefixEnd_8032964 4124771612263614225107077 := by
  unfold tailWord_8032964
  simp only [CollatzResearch.WordTrace]
  refine ⟨146493133434975411936048973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195324177913300549248065297 146493133434975411936048973)
  ·
    refine ⟨54934925038115779476018365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146493133434975411936048973 54934925038115779476018365)
    ·
      refine ⟨20600596889293417303506887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54934925038115779476018365 20600596889293417303506887)
      ·
        refine ⟨30900895333940125955260331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20600596889293417303506887 30900895333940125955260331)
        ·
          refine ⟨46351343000910188932890497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30900895333940125955260331 46351343000910188932890497)
          ·
            refine ⟨34763507250682641699667873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46351343000910188932890497 34763507250682641699667873)
            ·
              refine ⟨26072630438011981274750905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34763507250682641699667873 26072630438011981274750905)
              ·
                refine ⟨19554472828508985956063179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26072630438011981274750905 19554472828508985956063179)
                ·
                  refine ⟨29331709242763478934094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19554472828508985956063179 29331709242763478934094769)
                  ·
                    refine ⟨21998781932072609200571077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29331709242763478934094769 21998781932072609200571077)
                    ·
                      refine ⟨4124771612263614225107077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21998781932072609200571077 4124771612263614225107077)
                      ·
                        rfl

theorem cell23_8032964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_8032964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032964 prefixEnd_8032964 := by exact prefixLift 8032964
  have htrace : WordTrace (prefixWord ++ tailWord_8032964) baseStart_8032964 baseEnd_8032964 := by
    simpa [prefixWord, tailWord_8032964, baseEnd_8032964] using wordTrace_append hprefix tailTrace_8032964
  have hstable : (prefixWord ++ tailWord_8032964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032964).length < 2 ^ (prefixWord ++ tailWord_8032964).sum := by decide
  have hdescent : baseEnd_8032964 < baseStart_8032964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032967 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_8032967 : Nat := 118140960795 + 8032967 * 2 ^ 59
def prefixEnd_8032967 : Nat := 4983230072969 + 3 ^ 40 * 8032967 * 2
def baseEnd_8032967 : Nat := 4124773152705577713369563

theorem tailTrace_8032967 : CollatzResearch.WordTrace tailWord_8032967 prefixEnd_8032967 4124773152705577713369563 := by
  unfold tailWord_8032967
  simp only [CollatzResearch.WordTrace]
  refine ⟨292986376288939955384457155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195324250859293303589638103 292986376288939955384457155)
  ·
    refine ⟨439479564433409933076685733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292986376288939955384457155 439479564433409933076685733)
    ·
      refine ⟨82402418331264362451878575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439479564433409933076685733 82402418331264362451878575)
      ·
        refine ⟨123603627496896543677817863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82402418331264362451878575 123603627496896543677817863)
        ·
          refine ⟨185405441245344815516726795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123603627496896543677817863 185405441245344815516726795)
          ·
            refine ⟨278108161868017223275090193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185405441245344815516726795 278108161868017223275090193)
            ·
              refine ⟨208581121401012917456317645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278108161868017223275090193 208581121401012917456317645)
              ·
                refine ⟨78217920525379844046119117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208581121401012917456317645 78217920525379844046119117)
                ·
                  refine ⟨29331720197017441517294669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78217920525379844046119117 29331720197017441517294669)
                  ·
                    refine ⟨10999395073881540568985501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29331720197017441517294669 10999395073881540568985501)
                    ·
                      refine ⟨4124773152705577713369563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999395073881540568985501 4124773152705577713369563)
                      ·
                        rfl

theorem cell23_8032967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_8032967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032967 prefixEnd_8032967 := by exact prefixLift 8032967
  have htrace : WordTrace (prefixWord ++ tailWord_8032967) baseStart_8032967 baseEnd_8032967 := by
    simpa [prefixWord, tailWord_8032967, baseEnd_8032967] using wordTrace_append hprefix tailTrace_8032967
  have hstable : (prefixWord ++ tailWord_8032967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032967).length < 2 ^ (prefixWord ++ tailWord_8032967).sum := by decide
  have hdescent : baseEnd_8032967 < baseStart_8032967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032968 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_8032968 : Nat := 118140960795 + 8032968 * 2 ^ 59
def prefixEnd_8032968 : Nat := 4983230072969 + 3 ^ 40 * 8032968 * 2
def baseEnd_8032968 : Nat := 4124773666186232209457059

theorem tailTrace_8032968 : CollatzResearch.WordTrace tailWord_8032968 prefixEnd_8032968 4124773666186232209457059 := by
  unfold tailWord_8032968
  simp only [CollatzResearch.WordTrace]
  refine ⟨146493206380968166277621779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195324275174624221703495705 146493206380968166277621779)
  ·
    refine ⟨219739809571452249416432669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146493206380968166277621779 219739809571452249416432669)
    ·
      refine ⟨82402428589294593531162251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219739809571452249416432669 82402428589294593531162251)
      ·
        refine ⟨123603642883941890296743377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82402428589294593531162251 123603642883941890296743377)
        ·
          refine ⟨92702732162956417722557533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123603642883941890296743377 92702732162956417722557533)
          ·
            refine ⟨34763524561108656645959075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92702732162956417722557533 34763524561108656645959075)
            ·
              refine ⟨52145286841662984968938613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34763524561108656645959075 52145286841662984968938613)
              ·
                refine ⟨4888620641405904840837995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52145286841662984968938613 4888620641405904840837995)
                ·
                  refine ⟨7332930962108857261256993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888620641405904840837995 7332930962108857261256993)
                  ·
                    refine ⟨5499698221581642945942745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332930962108857261256993 5499698221581642945942745)
                    ·
                      refine ⟨4124773666186232209457059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499698221581642945942745 4124773666186232209457059)
                      ·
                        rfl

theorem cell23_8032968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_8032968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032968 prefixEnd_8032968 := by exact prefixLift 8032968
  have htrace : WordTrace (prefixWord ++ tailWord_8032968) baseStart_8032968 baseEnd_8032968 := by
    simpa [prefixWord, tailWord_8032968, baseEnd_8032968] using wordTrace_append hprefix tailTrace_8032968
  have hstable : (prefixWord ++ tailWord_8032968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032968).length < 2 ^ (prefixWord ++ tailWord_8032968).sum := by decide
  have hdescent : baseEnd_8032968 < baseStart_8032968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8032978 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_8032978 : Nat := 118140960795 + 8032978 * 2 ^ 59
def prefixEnd_8032978 : Nat := 4983230072969 + 3 ^ 40 * 8032978 * 2
def baseEnd_8032978 : Nat := 1374926266997592390110671

theorem tailTrace_8032978 : CollatzResearch.WordTrace tailWord_8032978 prefixEnd_8032978 1374926266997592390110671 := by
  unfold tailWord_8032978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73246694372975026065776897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195324518327933402842071725 73246694372975026065776897)
  ·
    refine ⟨54935020779731269549332673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73246694372975026065776897 54935020779731269549332673)
    ·
      refine ⟨41201265584798452161999505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54935020779731269549332673 41201265584798452161999505)
      ·
        refine ⟨30900949188598839121499629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41201265584798452161999505 30900949188598839121499629)
        ·
          refine ⟨11587855945724564670562361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30900949188598839121499629 11587855945724564670562361)
          ·
            refine ⟨8690891959293423502921771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11587855945724564670562361 8690891959293423502921771)
            ·
              refine ⟨13036337938940135254382657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690891959293423502921771 13036337938940135254382657)
              ·
                refine ⟨9777253454205101440786993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13036337938940135254382657 9777253454205101440786993)
                ·
                  refine ⟨7332940090653826080590245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9777253454205101440786993 7332940090653826080590245)
                  ·
                    refine ⟨1374926266997592390110671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332940090653826080590245 1374926266997592390110671)
                    ·
                      rfl

theorem cell23_8032978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_8032978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8032978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8032978 prefixEnd_8032978 := by exact prefixLift 8032978
  have htrace : WordTrace (prefixWord ++ tailWord_8032978) baseStart_8032978 baseEnd_8032978 := by
    simpa [prefixWord, tailWord_8032978, baseEnd_8032978] using wordTrace_append hprefix tailTrace_8032978
  have hstable : (prefixWord ++ tailWord_8032978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8032978).length < 2 ^ (prefixWord ++ tailWord_8032978).sum := by decide
  have hdescent : baseEnd_8032978 < baseStart_8032978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8032978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3]
def baseStart_8033027 : Nat := 118140960795 + 8033027 * 2 ^ 59
def prefixEnd_8033027 : Nat := 4983230072969 + 3 ^ 40 * 8033027 * 2
def baseEnd_8033027 : Nat := 4124803961544847478619287

theorem tailTrace_8033027 : CollatzResearch.WordTrace tailWord_8033027 prefixEnd_8033027 4124803961544847478619287 := by
  unfold tailWord_8033027
  simp only [CollatzResearch.WordTrace]
  refine ⟨292988564668722585631641335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195325709779148390421094223 292988564668722585631641335)
  ·
    refine ⟨439482847003083878447462003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292988564668722585631641335 439482847003083878447462003)
    ·
      refine ⟨659224270504625817671193005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439482847003083878447462003 659224270504625817671193005)
      ·
        refine ⟨247209101439234681626697377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659224270504625817671193005 247209101439234681626697377)
        ·
          refine ⟨185406826079426011220023033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247209101439234681626697377 185406826079426011220023033)
          ·
            refine ⟨139055119559569508415017275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185406826079426011220023033 139055119559569508415017275)
            ·
              refine ⟨208582679339354262622525913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139055119559569508415017275 208582679339354262622525913)
              ·
                refine ⟨156437009504515696966894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208582679339354262622525913 156437009504515696966894435)
                ·
                  refine ⟨234655514256773545450341653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156437009504515696966894435 234655514256773545450341653)
                  ·
                    refine ⟨10999477230786259942984765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234655514256773545450341653 10999477230786259942984765)
                    ·
                      refine ⟨4124803961544847478619287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999477230786259942984765 4124803961544847478619287)
                      ·
                        rfl

theorem cell23_8033027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_8033027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033027 prefixEnd_8033027 := by exact prefixLift 8033027
  have htrace : WordTrace (prefixWord ++ tailWord_8033027) baseStart_8033027 baseEnd_8033027 := by
    simpa [prefixWord, tailWord_8033027, baseEnd_8033027] using wordTrace_append hprefix tailTrace_8033027
  have hstable : (prefixWord ++ tailWord_8033027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033027).length < 2 ^ (prefixWord ++ tailWord_8033027).sum := by decide
  have hdescent : baseEnd_8033027 < baseStart_8033027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033041 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_8033041 : Nat := 118140960795 + 8033041 * 2 ^ 59
def prefixEnd_8033041 : Nat := 4983230072969 + 3 ^ 40 * 8033041 * 2
def baseEnd_8033041 : Nat := 4124811150274010423844223

theorem tailTrace_8033041 : CollatzResearch.WordTrace tailWord_8033041 prefixEnd_8033041 4124811150274010423844223 := by
  unfold tailWord_8033041
  simp only [CollatzResearch.WordTrace]
  refine ⟨292989075290671866022650977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195326050193781244015100651 292989075290671866022650977)
  ·
    refine ⟨219741806468003899516988233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292989075290671866022650977 219741806468003899516988233)
    ·
      refine ⟨164806354851002924637741175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219741806468003899516988233 164806354851002924637741175)
      ·
        refine ⟨247209532276504386956611763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164806354851002924637741175 247209532276504386956611763)
        ·
          refine ⟨370814298414756580434917645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247209532276504386956611763 370814298414756580434917645)
          ·
            refine ⟨139055361905533717663094117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370814298414756580434917645 139055361905533717663094117)
            ·
              refine ⟨26072880357287572061830147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139055361905533717663094117 26072880357287572061830147)
              ·
                refine ⟨39109320535931358092745221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26072880357287572061830147 39109320535931358092745221)
                ·
                  refine ⟨7332997600487129642389729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39109320535931358092745221 7332997600487129642389729)
                  ·
                    refine ⟨5499748200365347231792297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332997600487129642389729 5499748200365347231792297)
                    ·
                      refine ⟨4124811150274010423844223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499748200365347231792297 4124811150274010423844223)
                      ·
                        rfl

theorem cell23_8033041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_8033041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033041 prefixEnd_8033041 := by exact prefixLift 8033041
  have htrace : WordTrace (prefixWord ++ tailWord_8033041) baseStart_8033041 baseEnd_8033041 := by
    simpa [prefixWord, tailWord_8033041, baseEnd_8033041] using wordTrace_append hprefix tailTrace_8033041
  have hstable : (prefixWord ++ tailWord_8033041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033041).length < 2 ^ (prefixWord ++ tailWord_8033041).sum := by decide
  have hdescent : baseEnd_8033041 < baseStart_8033041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033184 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_8033184 : Nat := 118140960795 + 8033184 * 2 ^ 59
def prefixEnd_8033184 : Nat := 4983230072969 + 3 ^ 40 * 8033184 * 2
def baseEnd_8033184 : Nat := 1374961526002534454785355

theorem tailTrace_8033184 : CollatzResearch.WordTrace tailWord_8033184 prefixEnd_8033184 1374961526002534454785355 := by
  unfold tailWord_8033184
  simp only [CollatzResearch.WordTrace]
  refine ⟨146497145464576900722553303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195329527286102534296737737 146497145464576900722553303)
  ·
    refine ⟨219745718196865351083829955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146497145464576900722553303 219745718196865351083829955)
    ·
      refine ⟨329618577295298026625744933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219745718196865351083829955 329618577295298026625744933)
      ·
        refine ⟨61803483242868379992327175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329618577295298026625744933 61803483242868379992327175)
        ·
          refine ⟨92705224864302569988490763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61803483242868379992327175 92705224864302569988490763)
          ·
            refine ⟨139057837296453854982736145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92705224864302569988490763 139057837296453854982736145)
            ·
              refine ⟨104293377972340391237052109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139057837296453854982736145 104293377972340391237052109)
              ·
                refine ⟨39110016739627646713894541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104293377972340391237052109 39110016739627646713894541)
                ·
                  refine ⟨14666256277360367517710453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39110016739627646713894541 14666256277360367517710453)
                  ·
                    refine ⟨1374961526002534454785355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14666256277360367517710453 1374961526002534454785355)
                    ·
                      rfl

theorem cell23_8033184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_8033184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033184 prefixEnd_8033184 := by exact prefixLift 8033184
  have htrace : WordTrace (prefixWord ++ tailWord_8033184) baseStart_8033184 baseEnd_8033184 := by
    simpa [prefixWord, tailWord_8033184, baseEnd_8033184] using wordTrace_append hprefix tailTrace_8033184
  have hstable : (prefixWord ++ tailWord_8033184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033184).length < 2 ^ (prefixWord ++ tailWord_8033184).sum := by decide
  have hdescent : baseEnd_8033184 < baseStart_8033184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033208 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_8033208 : Nat := 118140960795 + 8033208 * 2 ^ 59
def prefixEnd_8033208 : Nat := 4983230072969 + 3 ^ 40 * 8033208 * 2
def baseEnd_8033208 : Nat := 4124896901543311270455955

theorem tailTrace_8033208 : CollatzResearch.WordTrace tailWord_8033208 prefixEnd_8033208 4124896901543311270455955 := by
  unfold tailWord_8033208
  simp only [CollatzResearch.WordTrace]
  refine ⟨146497583140533426771990139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195330110854044569029320185 146497583140533426771990139)
  ·
    refine ⟨219746374710800140157985209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146497583140533426771990139 219746374710800140157985209)
    ·
      refine ⟨164809781033100105118488907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219746374710800140157985209 164809781033100105118488907)
      ·
        refine ⟨247214671549650157677733361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164809781033100105118488907 247214671549650157677733361)
        ·
          refine ⟨185411003662237618258300021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247214671549650157677733361 185411003662237618258300021)
          ·
            refine ⟨17382281593334776711715627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185411003662237618258300021 17382281593334776711715627)
            ·
              refine ⟨26073422390002165067573441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17382281593334776711715627 26073422390002165067573441)
              ·
                refine ⟨19555066792501623800680081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26073422390002165067573441 19555066792501623800680081)
                ·
                  refine ⟨14666300094376217850510061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19555066792501623800680081 14666300094376217850510061)
                  ·
                    refine ⟨5499862535391081693941273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14666300094376217850510061 5499862535391081693941273)
                    ·
                      refine ⟨4124896901543311270455955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499862535391081693941273 4124896901543311270455955)
                      ·
                        rfl

theorem cell23_8033208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_8033208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033208 prefixEnd_8033208 := by exact prefixLift 8033208
  have htrace : WordTrace (prefixWord ++ tailWord_8033208) baseStart_8033208 baseEnd_8033208 := by
    simpa [prefixWord, tailWord_8033208, baseEnd_8033208] using wordTrace_append hprefix tailTrace_8033208
  have hstable : (prefixWord ++ tailWord_8033208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033208).length < 2 ^ (prefixWord ++ tailWord_8033208).sum := by decide
  have hdescent : baseEnd_8033208 < baseStart_8033208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033251 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_8033251 : Nat := 118140960795 + 8033251 * 2 ^ 59
def prefixEnd_8033251 : Nat := 4983230072969 + 3 ^ 40 * 8033251 * 2
def baseEnd_8033251 : Nat := 4124918981211454602218257

theorem tailTrace_8033251 : CollatzResearch.WordTrace tailWord_8033251 prefixEnd_8033251 4124918981211454602218257 := by
  unfold tailWord_8033251
  simp only [CollatzResearch.WordTrace]
  refine ⟨292996734619911071887795607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195331156413274047925197071 292996734619911071887795607)
  ·
    refine ⟨439495101929866607831693411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292996734619911071887795607 439495101929866607831693411)
    ·
      refine ⟨659242652894799911747540117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439495101929866607831693411 659242652894799911747540117)
      ·
        refine ⟨30901999354443745863165943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 659242652894799911747540117 30901999354443745863165943)
        ·
          refine ⟨46352999031665618794748915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30901999354443745863165943 46352999031665618794748915)
          ·
            refine ⟨69529498547498428192123373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46352999031665618794748915 69529498547498428192123373)
            ·
              refine ⟨26073561955311910572046265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69529498547498428192123373 26073561955311910572046265)
              ·
                refine ⟨19555171466483932929034699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26073561955311910572046265 19555171466483932929034699)
                ·
                  refine ⟨29332757199725899393552049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19555171466483932929034699 29332757199725899393552049)
                  ·
                    refine ⟨21999567899794424545164037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29332757199725899393552049 21999567899794424545164037)
                    ·
                      refine ⟨4124918981211454602218257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21999567899794424545164037 4124918981211454602218257)
                      ·
                        rfl

theorem cell23_8033251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_8033251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033251 prefixEnd_8033251 := by exact prefixLift 8033251
  have htrace : WordTrace (prefixWord ++ tailWord_8033251) baseStart_8033251 baseEnd_8033251 := by
    simpa [prefixWord, tailWord_8033251, baseEnd_8033251] using wordTrace_append hprefix tailTrace_8033251
  have hstable : (prefixWord ++ tailWord_8033251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033251).length < 2 ^ (prefixWord ++ tailWord_8033251).sum := by decide
  have hdescent : baseEnd_8033251 < baseStart_8033251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033255 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_8033255 : Nat := 118140960795 + 8033255 * 2 ^ 59
def prefixEnd_8033255 : Nat := 4983230072969 + 3 ^ 40 * 8033255 * 2
def baseEnd_8033255 : Nat := 4124921035134072586568239

theorem tailTrace_8033255 : CollatzResearch.WordTrace tailWord_8033255 prefixEnd_8033255 4124921035134072586568239 := by
  unfold tailWord_8033255
  simp only [CollatzResearch.WordTrace]
  refine ⟨292996880511896580570941219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195331253674597720380627479 292996880511896580570941219)
  ·
    refine ⟨439495320767844870856411829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292996880511896580570941219 439495320767844870856411829)
    ·
      refine ⟨41202686321985456642788609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439495320767844870856411829 41202686321985456642788609)
      ·
        refine ⟨30902014741489092482091457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41202686321985456642788609 30902014741489092482091457)
        ·
          refine ⟨23176511056116819361568593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30902014741489092482091457 23176511056116819361568593)
          ·
            refine ⟨17382383292087614521176445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23176511056116819361568593 17382383292087614521176445)
            ·
              refine ⟨6518393734532855445441167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17382383292087614521176445 6518393734532855445441167)
              ·
                refine ⟨9777590601799283168161751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518393734532855445441167 9777590601799283168161751)
                ·
                  refine ⟨14666385902698924752242627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777590601799283168161751 14666385902698924752242627)
                  ·
                    refine ⟨21999578854048387128363941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14666385902698924752242627 21999578854048387128363941)
                    ·
                      refine ⟨4124921035134072586568239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21999578854048387128363941 4124921035134072586568239)
                      ·
                        rfl

theorem cell23_8033255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_8033255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033255 prefixEnd_8033255 := by exact prefixLift 8033255
  have htrace : WordTrace (prefixWord ++ tailWord_8033255) baseStart_8033255 baseEnd_8033255 := by
    simpa [prefixWord, tailWord_8033255, baseEnd_8033255] using wordTrace_append hprefix tailTrace_8033255
  have hstable : (prefixWord ++ tailWord_8033255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033255).length < 2 ^ (prefixWord ++ tailWord_8033255).sum := by decide
  have hdescent : baseEnd_8033255 < baseStart_8033255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033258 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_8033258 : Nat := 118140960795 + 8033258 * 2 ^ 59
def prefixEnd_8033258 : Nat := 4983230072969 + 3 ^ 40 * 8033258 * 2
def baseEnd_8033258 : Nat := 4124922575576036074830725

theorem tailTrace_8033258 : CollatzResearch.WordTrace tailWord_8033258 prefixEnd_8033258 4124922575576036074830725 := by
  unfold tailWord_8033258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73249247482721428020825107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195331326620590474722200285 73249247482721428020825107)
  ·
    refine ⟨109873871224082142031237661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73249247482721428020825107 109873871224082142031237661)
    ·
      refine ⟨41202701709030803261714123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109873871224082142031237661 41202701709030803261714123)
      ·
        refine ⟨61804052563546204892571185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41202701709030803261714123 61804052563546204892571185)
        ·
          refine ⟨46353039422659653669428389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61804052563546204892571185 46353039422659653669428389)
          ·
            refine ⟨8691194891748685063017823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46353039422659653669428389 8691194891748685063017823)
            ·
              refine ⟨13036792337623027594526735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691194891748685063017823 13036792337623027594526735)
              ·
                refine ⟨19555188506434541391790103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13036792337623027594526735 19555188506434541391790103)
                ·
                  refine ⟨29332782759651812087685155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19555188506434541391790103 29332782759651812087685155)
                  ·
                    refine ⟨43999174139477718131527733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29332782759651812087685155 43999174139477718131527733)
                    ·
                      refine ⟨4124922575576036074830725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43999174139477718131527733 4124922575576036074830725)
                      ·
                        rfl

theorem cell23_8033258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_8033258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033258 prefixEnd_8033258 := by exact prefixLift 8033258
  have htrace : WordTrace (prefixWord ++ tailWord_8033258) baseStart_8033258 baseEnd_8033258 := by
    simpa [prefixWord, tailWord_8033258, baseEnd_8033258] using wordTrace_append hprefix tailTrace_8033258
  have hstable : (prefixWord ++ tailWord_8033258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033258).length < 2 ^ (prefixWord ++ tailWord_8033258).sum := by decide
  have hdescent : baseEnd_8033258 < baseStart_8033258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033266 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8033266 : Nat := 118140960795 + 8033266 * 2 ^ 59
def prefixEnd_8033266 : Nat := 4983230072969 + 3 ^ 40 * 8033266 * 2
def baseEnd_8033266 : Nat := 4124926683421272043530689

theorem tailTrace_8033266 : CollatzResearch.WordTrace tailWord_8033266 prefixEnd_8033266 4124926683421272043530689 := by
  unfold tailWord_8033266
  simp only [CollatzResearch.WordTrace]
  refine ⟨73249320428714182362397913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195331521143237819633061101 73249320428714182362397913)
  ·
    refine ⟨54936990321535636771798435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73249320428714182362397913 54936990321535636771798435)
    ·
      refine ⟨82405485482303455157697653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54936990321535636771798435 82405485482303455157697653)
      ·
        refine ⟨7725514263965948921034155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82405485482303455157697653 7725514263965948921034155)
        ·
          refine ⟨11588271395948923381551233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725514263965948921034155 11588271395948923381551233)
          ·
            refine ⟨8691203546961692536163425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588271395948923381551233 8691203546961692536163425)
            ·
              refine ⟨6518402660221269402122569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691203546961692536163425 6518402660221269402122569)
              ·
                refine ⟨4888801995165952051591927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518402660221269402122569 4888801995165952051591927)
                ·
                  refine ⟨7333202992748928077387891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888801995165952051591927 7333202992748928077387891)
                  ·
                    refine ⟨10999804489123392116081837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333202992748928077387891 10999804489123392116081837)
                    ·
                      refine ⟨4124926683421272043530689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999804489123392116081837 4124926683421272043530689)
                      ·
                        rfl

theorem cell23_8033266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8033266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033266 prefixEnd_8033266 := by exact prefixLift 8033266
  have htrace : WordTrace (prefixWord ++ tailWord_8033266) baseStart_8033266 baseEnd_8033266 := by
    simpa [prefixWord, tailWord_8033266, baseEnd_8033266] using wordTrace_append hprefix tailTrace_8033266
  have hstable : (prefixWord ++ tailWord_8033266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033266).length < 2 ^ (prefixWord ++ tailWord_8033266).sum := by decide
  have hdescent : baseEnd_8033266 < baseStart_8033266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033288 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_8033288 : Nat := 118140960795 + 8033288 * 2 ^ 59
def prefixEnd_8033288 : Nat := 4983230072969 + 3 ^ 40 * 8033288 * 2
def baseEnd_8033288 : Nat := 4124937979995670957455587

theorem tailTrace_8033288 : CollatzResearch.WordTrace tailWord_8033288 prefixEnd_8033288 4124937979995670957455587 := by
  unfold tailWord_8033288
  simp only [CollatzResearch.WordTrace]
  refine ⟨146499042060388513603446259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195332056080518018137928345 146499042060388513603446259)
  ·
    refine ⟨219748563090582770405169389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146499042060388513603446259 219748563090582770405169389)
    ·
      refine ⟨82405711158968538901938521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219748563090582770405169389 82405711158968538901938521)
      ·
        refine ⟨61804283369226404176453891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82405711158968538901938521 61804283369226404176453891)
        ·
          refine ⟨92706425053839606264680837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61804283369226404176453891 92706425053839606264680837)
          ·
            refine ⟨17382454697594926174627657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92706425053839606264680837 17382454697594926174627657)
            ·
              refine ⟨13036841023196194630970743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17382454697594926174627657 13036841023196194630970743)
              ·
                refine ⟨19555261534794291946456115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13036841023196194630970743 19555261534794291946456115)
                ·
                  refine ⟨29332892302191437919684173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19555261534794291946456115 29332892302191437919684173)
                  ·
                    refine ⟨10999834613321789219881565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29332892302191437919684173 10999834613321789219881565)
                    ·
                      refine ⟨4124937979995670957455587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999834613321789219881565 4124937979995670957455587)
                      ·
                        rfl

theorem cell23_8033288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_8033288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033288 prefixEnd_8033288 := by exact prefixLift 8033288
  have htrace : WordTrace (prefixWord ++ tailWord_8033288) baseStart_8033288 baseEnd_8033288 := by
    simpa [prefixWord, tailWord_8033288, baseEnd_8033288] using wordTrace_append hprefix tailTrace_8033288
  have hstable : (prefixWord ++ tailWord_8033288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033288).length < 2 ^ (prefixWord ++ tailWord_8033288).sum := by decide
  have hdescent : baseEnd_8033288 < baseStart_8033288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033309 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_8033309 : Nat := 118140960795 + 8033309 * 2 ^ 59
def prefixEnd_8033309 : Nat := 4983230072969 + 3 ^ 40 * 8033309 * 2
def baseEnd_8033309 : Nat := 4124948763089415375292991

theorem tailTrace_8033309 : CollatzResearch.WordTrace tailWord_8033309 prefixEnd_8033309 4124948763089415375292991 := by
  unfold tailWord_8033309
  simp only [CollatzResearch.WordTrace]
  refine ⟨292998850053700947793406981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195332566702467298528937987 292998850053700947793406981)
  ·
    refine ⟨54937284385068927711263809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292998850053700947793406981 54937284385068927711263809)
    ·
      refine ⟨41202963288801695783447857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54937284385068927711263809 41202963288801695783447857)
      ·
        refine ⟨30902222466601271837585893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41202963288801695783447857 30902222466601271837585893)
        ·
          refine ⟨5794166712487738469547355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30902222466601271837585893 5794166712487738469547355)
          ·
            refine ⟨8691250068731607704321033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794166712487738469547355 8691250068731607704321033)
            ·
              refine ⟨6518437551548705778240775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691250068731607704321033 6518437551548705778240775)
              ·
                refine ⟨9777656327323058667361163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518437551548705778240775 9777656327323058667361163)
                ·
                  refine ⟨14666484490984588001041745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777656327323058667361163 14666484490984588001041745)
                  ·
                    refine ⟨10999863368238441000781309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14666484490984588001041745 10999863368238441000781309)
                    ·
                      refine ⟨4124948763089415375292991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999863368238441000781309 4124948763089415375292991)
                      ·
                        rfl

theorem cell23_8033309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_8033309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033309 prefixEnd_8033309 := by exact prefixLift 8033309
  have htrace : WordTrace (prefixWord ++ tailWord_8033309) baseStart_8033309 baseEnd_8033309 := by
    simpa [prefixWord, tailWord_8033309, baseEnd_8033309] using wordTrace_append hprefix tailTrace_8033309
  have hstable : (prefixWord ++ tailWord_8033309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033309).length < 2 ^ (prefixWord ++ tailWord_8033309).sum := by decide
  have hdescent : baseEnd_8033309 < baseStart_8033309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033315 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 1, 3, 2]
def baseStart_8033315 : Nat := 118140960795 + 8033315 * 2 ^ 59
def prefixEnd_8033315 : Nat := 4983230072969 + 3 ^ 40 * 8033315 * 2
def baseEnd_8033315 : Nat := 4124951843973342351817963

theorem tailTrace_8033315 : CollatzResearch.WordTrace tailWord_8033315 prefixEnd_8033315 4124951843973342351817963 := by
  unfold tailWord_8033315
  simp only [CollatzResearch.WordTrace]
  refine ⟨292999068891679210818125399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195332712594452807212083599 292999068891679210818125399)
  ·
    refine ⟨439498603337518816227188099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292999068891679210818125399 439498603337518816227188099)
    ·
      refine ⟨659247905006278224340782149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439498603337518816227188099 659247905006278224340782149)
      ·
        refine ⟨123608982188677167063896653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659247905006278224340782149 123608982188677167063896653)
        ·
          refine ⟨46353368320753937648961245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123608982188677167063896653 46353368320753937648961245)
          ·
            refine ⟨17382513120282726618360467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46353368320753937648961245 17382513120282726618360467)
            ·
              refine ⟨26073769680424089927540701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17382513120282726618360467 26073769680424089927540701)
              ·
                refine ⟨9777663630159033722827763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26073769680424089927540701 9777663630159033722827763)
                ·
                  refine ⟨14666495445238550584241645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777663630159033722827763 14666495445238550584241645)
                  ·
                    refine ⟨5499935791964456469090617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14666495445238550584241645 5499935791964456469090617)
                    ·
                      refine ⟨4124951843973342351817963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499935791964456469090617 4124951843973342351817963)
                      ·
                        rfl

theorem cell23_8033315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_8033315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033315 prefixEnd_8033315 := by exact prefixLift 8033315
  have htrace : WordTrace (prefixWord ++ tailWord_8033315) baseStart_8033315 baseEnd_8033315 := by
    simpa [prefixWord, tailWord_8033315, baseEnd_8033315] using wordTrace_append hprefix tailTrace_8033315
  have hstable : (prefixWord ++ tailWord_8033315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033315).length < 2 ^ (prefixWord ++ tailWord_8033315).sum := by decide
  have hdescent : baseEnd_8033315 < baseStart_8033315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033351 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 7]
def baseStart_8033351 : Nat := 118140960795 + 8033351 * 2 ^ 59
def prefixEnd_8033351 : Nat := 4983230072969 + 3 ^ 40 * 8033351 * 2
def baseEnd_8033351 : Nat := 458330036586322690107533

theorem tailTrace_8033351 : CollatzResearch.WordTrace tailWord_8033351 prefixEnd_8033351 458330036586322690107533 := by
  unfold tailWord_8033351
  simp only [CollatzResearch.WordTrace]
  refine ⟨293000381919548788966435907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195333587946365859310957271 293000381919548788966435907)
  ·
    refine ⟨439500572879323183449653861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293000381919548788966435907 439500572879323183449653861)
    ·
      refine ⟨82406357414873096896810099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439500572879323183449653861 82406357414873096896810099)
      ·
        refine ⟨123609536122309645345215149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82406357414873096896810099 123609536122309645345215149)
        ·
          refine ⟨46353576045866117004455681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123609536122309645345215149 46353576045866117004455681)
          ·
            refine ⟨34765182034399587753341761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46353576045866117004455681 34765182034399587753341761)
            ·
              refine ⟨26073886525799690815006321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34765182034399587753341761 26073886525799690815006321)
              ·
                refine ⟨19555414894349768111254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26073886525799690815006321 19555414894349768111254741)
                ·
                  refine ⟨458330036586322690107533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19555414894349768111254741 458330036586322690107533)
                  ·
                    rfl

theorem cell23_8033351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 7].length) (baseStart_8033351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033351 prefixEnd_8033351 := by exact prefixLift 8033351
  have htrace : WordTrace (prefixWord ++ tailWord_8033351) baseStart_8033351 baseEnd_8033351 := by
    simpa [prefixWord, tailWord_8033351, baseEnd_8033351] using wordTrace_append hprefix tailTrace_8033351
  have hstable : (prefixWord ++ tailWord_8033351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033351).length < 2 ^ (prefixWord ++ tailWord_8033351).sum := by decide
  have hdescent : baseEnd_8033351 < baseStart_8033351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033361 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_8033361 : Nat := 118140960795 + 8033361 * 2 ^ 59
def prefixEnd_8033361 : Nat := 4983230072969 + 3 ^ 40 * 8033361 * 2
def baseEnd_8033361 : Nat := 4124975464083449171842751

theorem tailTrace_8033361 : CollatzResearch.WordTrace tailWord_8033361 prefixEnd_8033361 4124975464083449171842751 := by
  unfold tailWord_8033361
  simp only [CollatzResearch.WordTrace]
  refine ⟨293000746649512560674299937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195333831099675040449533291 293000746649512560674299937)
  ·
    refine ⟨219750559987134420505724953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293000746649512560674299937 219750559987134420505724953)
    ·
      refine ⟨164812919990350815379293715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219750559987134420505724953 164812919990350815379293715)
      ·
        refine ⟨247219379985526223068940573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164812919990350815379293715 247219379985526223068940573)
        ·
          refine ⟨92707267494572333650852715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247219379985526223068940573 92707267494572333650852715)
          ·
            refine ⟨139060901241858500476279073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92707267494572333650852715 139060901241858500476279073)
            ·
              refine ⟨104295675931393875357209305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139060901241858500476279073 104295675931393875357209305)
              ·
                refine ⟨78221756948545406517906979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104295675931393875357209305 78221756948545406517906979)
                ·
                  refine ⟨117332635422818109776860469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78221756948545406517906979 117332635422818109776860469)
                  ·
                    refine ⟨10999934570889197791580669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117332635422818109776860469 10999934570889197791580669)
                    ·
                      refine ⟨4124975464083449171842751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10999934570889197791580669 4124975464083449171842751)
                      ·
                        rfl

theorem cell23_8033361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_8033361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033361 prefixEnd_8033361 := by exact prefixLift 8033361
  have htrace : WordTrace (prefixWord ++ tailWord_8033361) baseStart_8033361 baseEnd_8033361 := by
    simpa [prefixWord, tailWord_8033361, baseEnd_8033361] using wordTrace_append hprefix tailTrace_8033361
  have hstable : (prefixWord ++ tailWord_8033361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033361).length < 2 ^ (prefixWord ++ tailWord_8033361).sum := by decide
  have hdescent : baseEnd_8033361 < baseStart_8033361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033385 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 5]
def baseStart_8033385 : Nat := 118140960795 + 8033385 * 2 ^ 59
def prefixEnd_8033385 : Nat := 4983230072969 + 3 ^ 40 * 8033385 * 2
def baseEnd_8033385 : Nat := 458331976402128564215849

theorem tailTrace_8033385 : CollatzResearch.WordTrace tailWord_8033385 prefixEnd_8033385 458331976402128564215849 := by
  unfold tailWord_8033385
  simp only [CollatzResearch.WordTrace]
  refine ⟨293001622001425612773173609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195334414667617075182115739 293001622001425612773173609)
  ·
    refine ⟨219751216501069209579880207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293001622001425612773173609 219751216501069209579880207)
    ·
      refine ⟨329626824751603814369820311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219751216501069209579880207 329626824751603814369820311)
      ·
        refine ⟨494440237127405721554730467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329626824751603814369820311 494440237127405721554730467)
        ·
          refine ⟨741660355691108582332095701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494440237127405721554730467 741660355691108582332095701)
          ·
            refine ⟨17382664586510357398408493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 741660355691108582332095701 17382664586510357398408493)
            ·
              refine ⟨6518499219941384024403185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17382664586510357398408493 6518499219941384024403185)
              ·
                refine ⟨4888874414956038018302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518499219941384024403185 4888874414956038018302389)
                ·
                  refine ⟨458331976402128564215849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4888874414956038018302389 458331976402128564215849)
                  ·
                    rfl

theorem cell23_8033385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 5].length) (baseStart_8033385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033385 prefixEnd_8033385 := by exact prefixLift 8033385
  have htrace : WordTrace (prefixWord ++ tailWord_8033385) baseStart_8033385 baseEnd_8033385 := by
    simpa [prefixWord, tailWord_8033385, baseEnd_8033385] using wordTrace_append hprefix tailTrace_8033385
  have hstable : (prefixWord ++ tailWord_8033385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033385).length < 2 ^ (prefixWord ++ tailWord_8033385).sum := by decide
  have hdescent : baseEnd_8033385 < baseStart_8033385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033388 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_8033388 : Nat := 118140960795 + 8033388 * 2 ^ 59
def prefixEnd_8033388 : Nat := 4983230072969 + 3 ^ 40 * 8033388 * 2
def baseEnd_8033388 : Nat := 4124989328061120566205127

theorem tailTrace_8033388 : CollatzResearch.WordTrace tailWord_8033388 prefixEnd_8033388 4124989328061120566205127 := by
  unfold tailWord_8033388
  simp only [CollatzResearch.WordTrace]
  refine ⟨146500865710207372142766409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195334487613609829523688545 146500865710207372142766409)
  ·
    refine ⟨109875649282655529107074807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146500865710207372142766409 109875649282655529107074807)
    ·
      refine ⟨164813473923983293660612211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109875649282655529107074807 164813473923983293660612211)
      ·
        refine ⟨247220210885974940490918317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164813473923983293660612211 247220210885974940490918317)
        ·
          refine ⟨92707579082240602684094369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247220210885974940490918317 92707579082240602684094369)
          ·
            refine ⟨69530684311680452013070777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92707579082240602684094369 69530684311680452013070777)
            ·
              refine ⟨52148013233760339009803083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69530684311680452013070777 52148013233760339009803083)
              ·
                refine ⟨78222019850640508514704625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52148013233760339009803083 78222019850640508514704625)
                ·
                  refine ⟨58666514887980381386028469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78222019850640508514704625 58666514887980381386028469)
                  ·
                    refine ⟨5499985770748160754940169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58666514887980381386028469 5499985770748160754940169)
                    ·
                      refine ⟨4124989328061120566205127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5499985770748160754940169 4124989328061120566205127)
                      ·
                        rfl

theorem cell23_8033388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_8033388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033388 prefixEnd_8033388 := by exact prefixLift 8033388
  have htrace : WordTrace (prefixWord ++ tailWord_8033388) baseStart_8033388 baseEnd_8033388 := by
    simpa [prefixWord, tailWord_8033388, baseEnd_8033388] using wordTrace_append hprefix tailTrace_8033388
  have hstable : (prefixWord ++ tailWord_8033388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033388).length < 2 ^ (prefixWord ++ tailWord_8033388).sum := by decide
  have hdescent : baseEnd_8033388 < baseStart_8033388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033391 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_8033391 : Nat := 118140960795 + 8033391 * 2 ^ 59
def prefixEnd_8033391 : Nat := 4983230072969 + 3 ^ 40 * 8033391 * 2
def baseEnd_8033391 : Nat := 4124990868503084054467613

theorem tailTrace_8033391 : CollatzResearch.WordTrace tailWord_8033391 prefixEnd_8033391 4124990868503084054467613 := by
  unfold tailWord_8033391
  simp only [CollatzResearch.WordTrace]
  refine ⟨293001840839403875797892027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195334560559602583865261351 293001840839403875797892027)
  ·
    refine ⟨439502761259105813696838041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293001840839403875797892027 439502761259105813696838041)
    ·
      refine ⟨329627070944329360272628531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439502761259105813696838041 329627070944329360272628531)
      ·
        refine ⟨494440606416494040408942797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329627070944329360272628531 494440606416494040408942797)
        ·
          refine ⟨185415227406185265153353549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494440606416494040408942797 185415227406185265153353549)
          ·
            refine ⟨69530710277319474432507581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185415227406185265153353549 69530710277319474432507581)
            ·
              refine ⟨26074016353994802912190343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69530710277319474432507581 26074016353994802912190343)
              ·
                refine ⟨39111024530992204368285515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26074016353994802912190343 39111024530992204368285515)
                ·
                  refine ⟨58666536796488306552428273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39111024530992204368285515 58666536796488306552428273)
                  ·
                    refine ⟨43999902597366229914321205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58666536796488306552428273 43999902597366229914321205)
                    ·
                      refine ⟨4124990868503084054467613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43999902597366229914321205 4124990868503084054467613)
                      ·
                        rfl

theorem cell23_8033391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_8033391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033391 prefixEnd_8033391 := by exact prefixLift 8033391
  have htrace : WordTrace (prefixWord ++ tailWord_8033391) baseStart_8033391 baseEnd_8033391 := by
    simpa [prefixWord, tailWord_8033391, baseEnd_8033391] using wordTrace_append hprefix tailTrace_8033391
  have hstable : (prefixWord ++ tailWord_8033391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033391).length < 2 ^ (prefixWord ++ tailWord_8033391).sum := by decide
  have hdescent : baseEnd_8033391 < baseStart_8033391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033398 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_8033398 : Nat := 118140960795 + 8033398 * 2 ^ 59
def prefixEnd_8033398 : Nat := 4983230072969 + 3 ^ 40 * 8033398 * 2
def baseEnd_8033398 : Nat := 1374998154289221842360027

theorem tailTrace_8033398 : CollatzResearch.WordTrace tailWord_8033398 prefixEnd_8033398 1374998154289221842360027 := by
  unfold tailWord_8033398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312631009398657249587303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195334730766919010662264565 18312631009398657249587303)
  ·
    refine ⟨27468946514097985874380955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18312631009398657249587303 27468946514097985874380955)
    ·
      refine ⟨41203419771146978811571433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27468946514097985874380955 41203419771146978811571433)
      ·
        refine ⟨30902564828360234108678575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41203419771146978811571433 30902564828360234108678575)
        ·
          refine ⟨46353847242540351163017863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30902564828360234108678575 46353847242540351163017863)
          ·
            refine ⟨69530770863810526744526795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46353847242540351163017863 69530770863810526744526795)
            ·
              refine ⟨104296156295715790116790193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69530770863810526744526795 104296156295715790116790193)
              ·
                refine ⟨78222117221786842587592645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104296156295715790116790193 78222117221786842587592645)
                ·
                  refine ⟨14666646979085032985173621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78222117221786842587592645 14666646979085032985173621)
                  ·
                    refine ⟨1374998154289221842360027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14666646979085032985173621 1374998154289221842360027)
                    ·
                      rfl

theorem cell23_8033398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_8033398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033398 prefixEnd_8033398 := by exact prefixLift 8033398
  have htrace : WordTrace (prefixWord ++ tailWord_8033398) baseStart_8033398 baseEnd_8033398 := by
    simpa [prefixWord, tailWord_8033398, baseEnd_8033398] using wordTrace_append hprefix tailTrace_8033398
  have hstable : (prefixWord ++ tailWord_8033398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033398).length < 2 ^ (prefixWord ++ tailWord_8033398).sum := by decide
  have hdescent : baseEnd_8033398 < baseStart_8033398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033458 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_8033458 : Nat := 118140960795 + 8033458 * 2 ^ 59
def prefixEnd_8033458 : Nat := 4983230072969 + 3 ^ 40 * 8033458 * 2
def baseEnd_8033458 : Nat := 458336141300770588036645

theorem tailTrace_8033458 : CollatzResearch.WordTrace tailWord_8033458 prefixEnd_8033458 458336141300770588036645 := by
  unfold tailWord_8033458
  simp only [CollatzResearch.WordTrace]
  refine ⟨73251071132540286560145257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195336189686774097493720685 73251071132540286560145257)
  ·
    refine ⟨54938303349405214920108943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73251071132540286560145257 54938303349405214920108943)
    ·
      refine ⟨82407455024107822380163415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54938303349405214920108943 82407455024107822380163415)
      ·
        refine ⟨123611182536161733570245123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82407455024107822380163415 123611182536161733570245123)
        ·
          refine ⟨185416773804242600355367685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123611182536161733570245123 185416773804242600355367685)
          ·
            refine ⟨34765645088295487566631441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185416773804242600355367685 34765645088295487566631441)
            ·
              refine ⟨26074233816221615674973581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34765645088295487566631441 26074233816221615674973581)
              ·
                refine ⟨9777837681083105878115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26074233816221615674973581 9777837681083105878115093)
                ·
                  refine ⟨458336141300770588036645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9777837681083105878115093 458336141300770588036645)
                  ·
                    rfl

theorem cell23_8033458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_8033458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033458 prefixEnd_8033458 := by exact prefixLift 8033458
  have htrace : WordTrace (prefixWord ++ tailWord_8033458) baseStart_8033458 baseEnd_8033458 := by
    simpa [prefixWord, tailWord_8033458, baseEnd_8033458] using wordTrace_append hprefix tailTrace_8033458
  have hstable : (prefixWord ++ tailWord_8033458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033458).length < 2 ^ (prefixWord ++ tailWord_8033458).sum := by decide
  have hdescent : baseEnd_8033458 < baseStart_8033458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033472 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_8033472 : Nat := 118140960795 + 8033472 * 2 ^ 59
def prefixEnd_8033472 : Nat := 4983230072969 + 3 ^ 40 * 8033472 * 2
def baseEnd_8033472 : Nat := 4125032460436098237554741

theorem tailTrace_8033472 : CollatzResearch.WordTrace tailWord_8033472 prefixEnd_8033472 4125032460436098237554741 := by
  unfold tailWord_8033472
  simp only [CollatzResearch.WordTrace]
  refine ⟨146502397576055213315795335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195336530101406951087727113 146502397576055213315795335)
  ·
    refine ⟨219753596364082819973693003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146502397576055213315795335 219753596364082819973693003)
    ·
      refine ⟨329630394546124229960539505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219753596364082819973693003 329630394546124229960539505)
      ·
        refine ⟨247222795909593172470404629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329630394546124229960539505 247222795909593172470404629)
        ·
          refine ⟨11588568558262179959550217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247222795909593172470404629 11588568558262179959550217)
          ·
            refine ⟨8691426418696634969662663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588568558262179959550217 8691426418696634969662663)
            ·
              refine ⟨13037139628044952454493995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691426418696634969662663 13037139628044952454493995)
              ·
                refine ⟨19555709442067428681740993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13037139628044952454493995 19555709442067428681740993)
                ·
                  refine ⟨14666782081550571511305745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19555709442067428681740993 14666782081550571511305745)
                  ·
                    refine ⟨11000086561162928633479309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14666782081550571511305745 11000086561162928633479309)
                    ·
                      refine ⟨4125032460436098237554741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000086561162928633479309 4125032460436098237554741)
                      ·
                        rfl

theorem cell23_8033472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_8033472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033472 prefixEnd_8033472 := by exact prefixLift 8033472
  have htrace : WordTrace (prefixWord ++ tailWord_8033472) baseStart_8033472 baseEnd_8033472 := by
    simpa [prefixWord, tailWord_8033472, baseEnd_8033472] using wordTrace_append hprefix tailTrace_8033472
  have hstable : (prefixWord ++ tailWord_8033472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033472).length < 2 ^ (prefixWord ++ tailWord_8033472).sum := by decide
  have hdescent : baseEnd_8033472 < baseStart_8033472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033495 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_8033495 : Nat := 118140960795 + 8033495 * 2 ^ 59
def prefixEnd_8033495 : Nat := 4983230072969 + 3 ^ 40 * 8033495 * 2
def baseEnd_8033495 : Nat := 4125044270491151647567135

theorem tailTrace_8033495 : CollatzResearch.WordTrace tailWord_8033495 prefixEnd_8033495 4125044270491151647567135 := by
  unfold tailWord_8033495
  simp only [CollatzResearch.WordTrace]
  refine ⟨293005634031027101559677939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195337089354018067706451959 293005634031027101559677939)
  ·
    refine ⟨439508451046540652339516909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293005634031027101559677939 439508451046540652339516909)
    ·
      refine ⟨164815669142452744627318841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439508451046540652339516909 164815669142452744627318841)
      ·
        refine ⟨123611751856839558470489131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164815669142452744627318841 123611751856839558470489131)
        ·
          refine ⟨185417627785259337705733697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123611751856839558470489131 185417627785259337705733697)
          ·
            refine ⟨139063220838944503279300273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185417627785259337705733697 139063220838944503279300273)
            ·
              refine ⟨104297415629208377459475205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139063220838944503279300273 104297415629208377459475205)
              ·
                refine ⟨19555765430476570773651601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104297415629208377459475205 19555765430476570773651601)
                ·
                  refine ⟨14666824072857428080238701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19555765430476570773651601 14666824072857428080238701)
                  ·
                    refine ⟨5500059027321535530089513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14666824072857428080238701 5500059027321535530089513)
                    ·
                      refine ⟨4125044270491151647567135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500059027321535530089513 4125044270491151647567135)
                      ·
                        rfl

theorem cell23_8033495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_8033495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033495 prefixEnd_8033495 := by exact prefixLift 8033495
  have htrace : WordTrace (prefixWord ++ tailWord_8033495) baseStart_8033495 baseEnd_8033495 := by
    simpa [prefixWord, tailWord_8033495, baseEnd_8033495] using wordTrace_append hprefix tailTrace_8033495
  have hstable : (prefixWord ++ tailWord_8033495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033495).length < 2 ^ (prefixWord ++ tailWord_8033495).sum := by decide
  have hdescent : baseEnd_8033495 < baseStart_8033495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033508 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_8033508 : Nat := 118140960795 + 8033508 * 2 ^ 59
def prefixEnd_8033508 : Nat := 4983230072969 + 3 ^ 40 * 8033508 * 2
def baseEnd_8033508 : Nat := 4125050945739660096704575

theorem tailTrace_8033508 : CollatzResearch.WordTrace tailWord_8033508 prefixEnd_8033508 4125050945739660096704575 := by
  unfold tailWord_8033508
  simp only [CollatzResearch.WordTrace]
  refine ⟨146503054089990002389950589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195337405453320003186600785 146503054089990002389950589)
  ·
    refine ⟨54938645283746250896231471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146503054089990002389950589 54938645283746250896231471)
    ·
      refine ⟨82407967925619376344347207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54938645283746250896231471 82407967925619376344347207)
      ·
        refine ⟨123611951888429064516520811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82407967925619376344347207 123611951888429064516520811)
        ·
          refine ⟨185417927832643596774781217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123611951888429064516520811 185417927832643596774781217)
          ·
            refine ⟨139063445874482697581085913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185417927832643596774781217 139063445874482697581085913)
            ·
              refine ⟨104297584405862023185814435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139063445874482697581085913 104297584405862023185814435)
              ·
                refine ⟨156446376608793034778721653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104297584405862023185814435 156446376608793034778721653)
                ·
                  refine ⟨14666847807074347010505155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156446376608793034778721653 14666847807074347010505155)
                  ·
                    refine ⟨22000271710611520515757733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14666847807074347010505155 22000271710611520515757733)
                    ·
                      refine ⟨4125050945739660096704575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22000271710611520515757733 4125050945739660096704575)
                      ·
                        rfl

theorem cell23_8033508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_8033508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033508 prefixEnd_8033508 := by exact prefixLift 8033508
  have htrace : WordTrace (prefixWord ++ tailWord_8033508) baseStart_8033508 baseEnd_8033508 := by
    simpa [prefixWord, tailWord_8033508, baseEnd_8033508] using wordTrace_append hprefix tailTrace_8033508
  have hstable : (prefixWord ++ tailWord_8033508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033508).length < 2 ^ (prefixWord ++ tailWord_8033508).sum := by decide
  have hdescent : baseEnd_8033508 < baseStart_8033508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033522 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_8033522 : Nat := 118140960795 + 8033522 * 2 ^ 59
def prefixEnd_8033522 : Nat := 4983230072969 + 3 ^ 40 * 8033522 * 2
def baseEnd_8033522 : Nat := 1375019378156274347309837

theorem tailTrace_8033522 : CollatzResearch.WordTrace tailWord_8033522 prefixEnd_8033522 1375019378156274347309837 := by
  unfold tailWord_8033522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73251654700482321292727705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195337745867952856780607213 73251654700482321292727705)
  ·
    refine ⟨54938741025361740969545779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73251654700482321292727705 54938741025361740969545779)
    ·
      refine ⟨82408111538042611454318669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54938741025361740969545779 82408111538042611454318669)
      ·
        refine ⟨30903041826765979295369501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82408111538042611454318669 30903041826765979295369501)
        ·
          refine ⟨11588640685037242235763563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30903041826765979295369501 11588640685037242235763563)
          ·
            refine ⟨17382961027555863353645345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11588640685037242235763563 17382961027555863353645345)
            ·
              refine ⟨13037220770666897515234009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17382961027555863353645345 13037220770666897515234009)
              ·
                refine ⟨9777915578000173136425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13037220770666897515234009 9777915578000173136425507)
                ·
                  refine ⟨14666873367000259704638261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777915578000173136425507 14666873367000259704638261)
                  ·
                    refine ⟨1375019378156274347309837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14666873367000259704638261 1375019378156274347309837)
                    ·
                      rfl

theorem cell23_8033522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_8033522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033522 prefixEnd_8033522 := by exact prefixLift 8033522
  have htrace : WordTrace (prefixWord ++ tailWord_8033522) baseStart_8033522 baseEnd_8033522 := by
    simpa [prefixWord, tailWord_8033522, baseEnd_8033522] using wordTrace_append hprefix tailTrace_8033522
  have hstable : (prefixWord ++ tailWord_8033522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033522).length < 2 ^ (prefixWord ++ tailWord_8033522).sum := by decide
  have hdescent : baseEnd_8033522 < baseStart_8033522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033545 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_8033545 : Nat := 118140960795 + 8033545 * 2 ^ 59
def prefixEnd_8033545 : Nat := 4983230072969 + 3 ^ 40 * 8033545 * 2
def baseEnd_8033545 : Nat := 4125069944523876451941905

theorem tailTrace_8033545 : CollatzResearch.WordTrace tailWord_8033545 prefixEnd_8033545 4125069944523876451941905 := by
  unfold tailWord_8033545
  simp only [CollatzResearch.WordTrace]
  refine ⟨293007457680845960098998089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195338305120563973399332059 293007457680845960098998089)
  ·
    refine ⟨219755593260634470074248567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293007457680845960098998089 219755593260634470074248567)
    ·
      refine ⟨329633389890951705111372851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219755593260634470074248567 329633389890951705111372851)
      ·
        refine ⟨494450084836427557667059277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329633389890951705111372851 494450084836427557667059277)
        ·
          refine ⟨185418781813660334125147229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494450084836427557667059277 185418781813660334125147229)
          ·
            refine ⟨69532043180122625296930211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185418781813660334125147229 69532043180122625296930211)
            ·
              refine ⟨104298064770183937945395317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69532043180122625296930211 104298064770183937945395317)
              ·
                refine ⟨9777943572204744182380811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104298064770183937945395317 9777943572204744182380811)
                ·
                  refine ⟨14666915358307116273571217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9777943572204744182380811 14666915358307116273571217)
                  ·
                    refine ⟨11000186518730337205178413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14666915358307116273571217 11000186518730337205178413)
                    ·
                      refine ⟨4125069944523876451941905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000186518730337205178413 4125069944523876451941905)
                      ·
                        rfl

theorem cell23_8033545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_8033545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033545 prefixEnd_8033545 := by exact prefixLift 8033545
  have htrace : WordTrace (prefixWord ++ tailWord_8033545) baseStart_8033545 baseEnd_8033545 := by
    simpa [prefixWord, tailWord_8033545, baseEnd_8033545] using wordTrace_append hprefix tailTrace_8033545
  have hstable : (prefixWord ++ tailWord_8033545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033545).length < 2 ^ (prefixWord ++ tailWord_8033545).sum := by decide
  have hdescent : baseEnd_8033545 < baseStart_8033545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033548 : List Nat := [2, 2, 1, 2, 2, 5, 9]
def baseStart_8033548 : Nat := 118140960795 + 8033548 * 2 ^ 59
def prefixEnd_8033548 : Nat := 4983230072969 + 3 ^ 40 * 8033548 * 2
def baseEnd_8033548 : Nat := 50926808456368394323511

theorem tailTrace_8033548 : CollatzResearch.WordTrace tailWord_8033548 prefixEnd_8033548 50926808456368394323511 := by
  unfold tailWord_8033548
  simp only [CollatzResearch.WordTrace]
  refine ⟨146503783549917545805678649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195338378066556727740904865 146503783549917545805678649)
  ·
    refine ⟨109877837662438159354258987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146503783549917545805678649 109877837662438159354258987)
    ·
      refine ⟨164816756493657239031388481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109877837662438159354258987 164816756493657239031388481)
      ·
        refine ⟨123612567370242929273541361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164816756493657239031388481 123612567370242929273541361)
        ·
          refine ⟨92709425527682196955156021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123612567370242929273541361 92709425527682196955156021)
          ·
            refine ⟨8691508643220205964545877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92709425527682196955156021 8691508643220205964545877)
            ·
              refine ⟨50926808456368394323511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8691508643220205964545877 50926808456368394323511)
              ·
                rfl

theorem cell23_8033548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 9].length) (baseStart_8033548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033548 prefixEnd_8033548 := by exact prefixLift 8033548
  have htrace : WordTrace (prefixWord ++ tailWord_8033548) baseStart_8033548 baseEnd_8033548 := by
    simpa [prefixWord, tailWord_8033548, baseEnd_8033548] using wordTrace_append hprefix tailTrace_8033548
  have hstable : (prefixWord ++ tailWord_8033548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033548).length < 2 ^ (prefixWord ++ tailWord_8033548).sum := by decide
  have hdescent : baseEnd_8033548 < baseStart_8033548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033565 : List Nat := [1, 4, 2, 3, 1, 2, 2, 8]
def baseStart_8033565 : Nat := 118140960795 + 8033565 * 2 ^ 59
def prefixEnd_8033565 : Nat := 4983230072969 + 3 ^ 40 * 8033565 * 2
def baseEnd_8033565 : Nat := 152780748671739495321919

theorem tailTrace_8033565 : CollatzResearch.WordTrace tailWord_8033565 prefixEnd_8033565 152780748671739495321919 := by
  unfold tailWord_8033565
  simp only [CollatzResearch.WordTrace]
  refine ⟨293008187140773503514726149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195338791427182335676484099 293008187140773503514726149)
  ·
    refine ⟨54939035088895031909011153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293008187140773503514726149 54939035088895031909011153)
    ·
      refine ⟨41204276316671273931758365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54939035088895031909011153 41204276316671273931758365)
      ·
        refine ⟨15451603618751727724409387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41204276316671273931758365 15451603618751727724409387)
        ·
          refine ⟨23177405428127591586614081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15451603618751727724409387 23177405428127591586614081)
          ·
            refine ⟨17383054071095693689960561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23177405428127591586614081 17383054071095693689960561)
            ·
              refine ⟨13037290553321770267470421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17383054071095693689960561 13037290553321770267470421)
              ·
                refine ⟨152780748671739495321919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13037290553321770267470421 152780748671739495321919)
                ·
                  rfl

theorem cell23_8033565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 8].length) (baseStart_8033565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033565 prefixEnd_8033565 := by exact prefixLift 8033565
  have htrace : WordTrace (prefixWord ++ tailWord_8033565) baseStart_8033565 baseEnd_8033565 := by
    simpa [prefixWord, tailWord_8033565, baseEnd_8033565] using wordTrace_append hprefix tailTrace_8033565
  have hstable : (prefixWord ++ tailWord_8033565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033565).length < 2 ^ (prefixWord ++ tailWord_8033565).sum := by decide
  have hdescent : baseEnd_8033565 < baseStart_8033565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033608 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_8033608 : Nat := 118140960795 + 8033608 * 2 ^ 59
def prefixEnd_8033608 : Nat := 4983230072969 + 3 ^ 40 * 8033608 * 2
def baseEnd_8033608 : Nat := 1375034097935036568484705

theorem tailTrace_8033608 : CollatzResearch.WordTrace tailWord_8033608 prefixEnd_8033608 1375034097935036568484705 := by
  unfold tailWord_8033608
  simp only [CollatzResearch.WordTrace]
  refine ⟨146504877739808860929270739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195339836986411814572360985 146504877739808860929270739)
  ·
    refine ⟨219757316609713291393906109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146504877739808860929270739 219757316609713291393906109)
    ·
      refine ⟨82408993728642484272714791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219757316609713291393906109 82408993728642484272714791)
      ·
        refine ⟨123613490592963726409072187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82408993728642484272714791 123613490592963726409072187)
        ·
          refine ⟨185420235889445589613608281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123613490592963726409072187 185420235889445589613608281)
          ·
            refine ⟨139065176917084192210206211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185420235889445589613608281 139065176917084192210206211)
            ·
              refine ⟨208597765375626288315309317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139065176917084192210206211 208597765375626288315309317)
              ·
                refine ⟨39112081007929929059120497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208597765375626288315309317 39112081007929929059120497)
                ·
                  refine ⟨29334060755947446794340373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39112081007929929059120497 29334060755947446794340373)
                  ·
                    refine ⟨1375034097935036568484705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29334060755947446794340373 1375034097935036568484705)
                    ·
                      rfl

theorem cell23_8033608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_8033608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033608 prefixEnd_8033608 := by exact prefixLift 8033608
  have htrace : WordTrace (prefixWord ++ tailWord_8033608) baseStart_8033608 baseEnd_8033608 := by
    simpa [prefixWord, tailWord_8033608, baseEnd_8033608] using wordTrace_append hprefix tailTrace_8033608
  have hstable : (prefixWord ++ tailWord_8033608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033608).length < 2 ^ (prefixWord ++ tailWord_8033608).sum := by decide
  have hdescent : baseEnd_8033608 < baseStart_8033608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033632 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2]
def baseStart_8033632 : Nat := 118140960795 + 8033632 * 2 ^ 59
def prefixEnd_8033632 : Nat := 4983230072969 + 3 ^ 40 * 8033632 * 2
def baseEnd_8033632 : Nat := 4125114617340817611554005

theorem tailTrace_8033632 : CollatzResearch.WordTrace tailWord_8033632 prefixEnd_8033632 4125114617340817611554005 := by
  unfold tailWord_8033632
  simp only [CollatzResearch.WordTrace]
  refine ⟨146505315415765386978707575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195340420554353849304943433 146505315415765386978707575)
  ·
    refine ⟨219757973123648080468061363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146505315415765386978707575 219757973123648080468061363)
    ·
      refine ⟨329636959685472120702092045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219757973123648080468061363 329636959685472120702092045)
      ·
        refine ⟨123613859882052045263284517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329636959685472120702092045 123613859882052045263284517)
        ·
          refine ⟨23177598727884758486865847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123613859882052045263284517 23177598727884758486865847)
          ·
            refine ⟨34766398091827137730298771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23177598727884758486865847 34766398091827137730298771)
            ·
              refine ⟨52149597137740706595448157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34766398091827137730298771 52149597137740706595448157)
              ·
                refine ⟨19556098926652764973293059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52149597137740706595448157 19556098926652764973293059)
                ·
                  refine ⟨29334148389979147459939589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19556098926652764973293059 29334148389979147459939589)
                  ·
                    refine ⟨5500152823121090148738673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29334148389979147459939589 5500152823121090148738673)
                    ·
                      refine ⟨4125114617340817611554005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500152823121090148738673 4125114617340817611554005)
                      ·
                        rfl

theorem cell23_8033632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_8033632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033632 prefixEnd_8033632 := by exact prefixLift 8033632
  have htrace : WordTrace (prefixWord ++ tailWord_8033632) baseStart_8033632 baseEnd_8033632 := by
    simpa [prefixWord, tailWord_8033632, baseEnd_8033632] using wordTrace_append hprefix tailTrace_8033632
  have hstable : (prefixWord ++ tailWord_8033632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033632).length < 2 ^ (prefixWord ++ tailWord_8033632).sum := by decide
  have hdescent : baseEnd_8033632 < baseStart_8033632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033653 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_8033653 : Nat := 118140960795 + 8033653 * 2 ^ 59
def prefixEnd_8033653 : Nat := 4983230072969 + 3 ^ 40 * 8033653 * 2
def baseEnd_8033653 : Nat := 4125125400434562029391409

theorem tailTrace_8033653 : CollatzResearch.WordTrace tailWord_8033653 prefixEnd_8033653 4125125400434562029391409 := by
  unfold tailWord_8033653
  simp only [CollatzResearch.WordTrace]
  refine ⟨293011396764454694543929613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195340931176303129695953075 293011396764454694543929613)
  ·
    refine ⟨109879273786670510453973605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293011396764454694543929613 109879273786670510453973605)
    ·
      refine ⟨20602363835000720710120051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109879273786670510453973605 20602363835000720710120051)
      ·
        refine ⟨30903545752501081065180077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602363835000720710120051 30903545752501081065180077)
        ·
          refine ⟨11588829657187905399442529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30903545752501081065180077 11588829657187905399442529)
          ·
            refine ⟨8691622242890929049581897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588829657187905399442529 8691622242890929049581897)
            ·
              refine ⟨6518716682168196787186423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691622242890929049581897 6518716682168196787186423)
              ·
                refine ⟨9778075023252295180779635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518716682168196787186423 9778075023252295180779635)
                ·
                  refine ⟨14667112534878442771169453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9778075023252295180779635 14667112534878442771169453)
                  ·
                    refine ⟨5500167200579416039188545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14667112534878442771169453 5500167200579416039188545)
                    ·
                      refine ⟨4125125400434562029391409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500167200579416039188545 4125125400434562029391409)
                      ·
                        rfl

theorem cell23_8033653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_8033653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033653 prefixEnd_8033653 := by exact prefixLift 8033653
  have htrace : WordTrace (prefixWord ++ tailWord_8033653) baseStart_8033653 baseEnd_8033653 := by
    simpa [prefixWord, tailWord_8033653, baseEnd_8033653] using wordTrace_append hprefix tailTrace_8033653
  have hstable : (prefixWord ++ tailWord_8033653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033653).length < 2 ^ (prefixWord ++ tailWord_8033653).sum := by decide
  have hdescent : baseEnd_8033653 < baseStart_8033653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033672 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 5]
def baseStart_8033672 : Nat := 118140960795 + 8033672 * 2 ^ 59
def prefixEnd_8033672 : Nat := 4983230072969 + 3 ^ 40 * 8033672 * 2
def baseEnd_8033672 : Nat := 458348350729666383894869

theorem tailTrace_8033672 : CollatzResearch.WordTrace tailWord_8033672 prefixEnd_8033672 458348350729666383894869 := by
  unfold tailWord_8033672
  simp only [CollatzResearch.WordTrace]
  refine ⟨146506044875692930394435635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195341393167590573859247513 146506044875692930394435635)
  ·
    refine ⟨219759067313539395591653453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146506044875692930394435635 219759067313539395591653453)
    ·
      refine ⟨82409650242577273346870045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219759067313539395591653453 82409650242577273346870045)
      ·
        refine ⟨30903618840966477505076267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82409650242577273346870045 30903618840966477505076267)
        ·
          refine ⟨46355428261449716257614401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30903618840966477505076267 46355428261449716257614401)
          ·
            refine ⟨34766571196087287193210801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46355428261449716257614401 34766571196087287193210801)
            ·
              refine ⟨26074928397065465394908101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34766571196087287193210801 26074928397065465394908101)
              ·
                refine ⟨4889049074449774761545269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26074928397065465394908101 4889049074449774761545269)
                ·
                  refine ⟨458348350729666383894869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4889049074449774761545269 458348350729666383894869)
                  ·
                    rfl

theorem cell23_8033672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 5].length) (baseStart_8033672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033672 prefixEnd_8033672 := by exact prefixLift 8033672
  have htrace : WordTrace (prefixWord ++ tailWord_8033672) baseStart_8033672 baseEnd_8033672 := by
    simpa [prefixWord, tailWord_8033672, baseEnd_8033672] using wordTrace_append hprefix tailTrace_8033672
  have hstable : (prefixWord ++ tailWord_8033672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033672).length < 2 ^ (prefixWord ++ tailWord_8033672).sum := by decide
  have hdescent : baseEnd_8033672 < baseStart_8033672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033715 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 5, 4]
def baseStart_8033715 : Nat := 118140960795 + 8033715 * 2 ^ 59
def prefixEnd_8033715 : Nat := 4983230072969 + 3 ^ 40 * 8033715 * 2
def baseEnd_8033715 : Nat := 1375052412078380262272041

theorem tailTrace_8033715 : CollatzResearch.WordTrace tailWord_8033715 prefixEnd_8033715 1375052412078380262272041 := by
  unfold tailWord_8033715
  simp only [CollatzResearch.WordTrace]
  refine ⟨293013658090230079132686599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195342438726820052755124399 293013658090230079132686599)
  ·
    refine ⟨439520487135345118699029899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293013658090230079132686599 439520487135345118699029899)
    ·
      refine ⟨659280730703017678048544849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439520487135345118699029899 659280730703017678048544849)
      ·
        refine ⟨494460548027263258536408637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659280730703017678048544849 494460548027263258536408637)
        ·
          refine ⟨185422705510223721951153239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494460548027263258536408637 185422705510223721951153239)
          ·
            refine ⟨278134058265335582926729859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185422705510223721951153239 278134058265335582926729859)
            ·
              refine ⟨417201087398003374390094789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278134058265335582926729859 417201087398003374390094789)
              ·
                refine ⟨78225203887125632698142773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417201087398003374390094789 78225203887125632698142773)
                ·
                  refine ⟨7333612864418028065450885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78225203887125632698142773 7333612864418028065450885)
                  ·
                    refine ⟨1375052412078380262272041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333612864418028065450885 1375052412078380262272041)
                    ·
                      rfl

theorem cell23_8033715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 4].length) (baseStart_8033715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033715 prefixEnd_8033715 := by exact prefixLift 8033715
  have htrace : WordTrace (prefixWord ++ tailWord_8033715) baseStart_8033715 baseEnd_8033715 := by
    simpa [prefixWord, tailWord_8033715, baseEnd_8033715] using wordTrace_append hprefix tailTrace_8033715
  have hstable : (prefixWord ++ tailWord_8033715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033715).length < 2 ^ (prefixWord ++ tailWord_8033715).sum := by decide
  have hdescent : baseEnd_8033715 < baseStart_8033715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033772 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_8033772 : Nat := 118140960795 + 8033772 * 2 ^ 59
def prefixEnd_8033772 : Nat := 4983230072969 + 3 ^ 40 * 8033772 * 2
def baseEnd_8033772 : Nat := 4125186504632447063803361

theorem tailTrace_8033772 : CollatzResearch.WordTrace tailWord_8033772 prefixEnd_8033772 4125186504632447063803361 := by
  unfold tailWord_8033772
  simp only [CollatzResearch.WordTrace]
  refine ⟨146507868525511788933755785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195343824700682385245007713 146507868525511788933755785)
  ·
    refine ⟨109880901394133841700316839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146507868525511788933755785 109880901394133841700316839)
    ·
      refine ⟨164821352091200762550475259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109880901394133841700316839 164821352091200762550475259)
      ·
        refine ⟨247232028136801143825712889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164821352091200762550475259 247232028136801143825712889)
        ·
          refine ⟨185424021102600857869284667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247232028136801143825712889 185424021102600857869284667)
          ·
            refine ⟨278136031653901286803927001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185424021102600857869284667 278136031653901286803927001)
            ·
              refine ⟨208602023740425965102945251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278136031653901286803927001 208602023740425965102945251)
              ·
                refine ⟨312903035610638947654417877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208602023740425965102945251 312903035610638947654417877)
                ·
                  refine ⟨7333664897124350335650419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312903035610638947654417877 7333664897124350335650419)
                  ·
                    refine ⟨11000497345686525503475629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333664897124350335650419 11000497345686525503475629)
                    ·
                      refine ⟨4125186504632447063803361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000497345686525503475629 4125186504632447063803361)
                      ·
                        rfl

theorem cell23_8033772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_8033772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033772 prefixEnd_8033772 := by exact prefixLift 8033772
  have htrace : WordTrace (prefixWord ++ tailWord_8033772) baseStart_8033772 baseEnd_8033772 := by
    simpa [prefixWord, tailWord_8033772, baseEnd_8033772] using wordTrace_append hprefix tailTrace_8033772
  have hstable : (prefixWord ++ tailWord_8033772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033772).length < 2 ^ (prefixWord ++ tailWord_8033772).sum := by decide
  have hdescent : baseEnd_8033772 < baseStart_8033772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033806 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_8033806 : Nat := 118140960795 + 8033806 * 2 ^ 59
def prefixEnd_8033806 : Nat := 4983230072969 + 3 ^ 40 * 8033806 * 2
def baseEnd_8033806 : Nat := 4125203962974699930778205

theorem tailTrace_8033806 : CollatzResearch.WordTrace tailWord_8033806 prefixEnd_8033806 4125203962974699930778205 := by
  unfold tailWord_8033806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627122141612550209281159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195344651421933601116166181 36627122141612550209281159)
  ·
    refine ⟨54940683212418825313921739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36627122141612550209281159 54940683212418825313921739)
    ·
      refine ⟨82411024818628237970882609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54940683212418825313921739 82411024818628237970882609)
      ·
        refine ⟨61808268613971178478161957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82411024818628237970882609 61808268613971178478161957)
        ·
          refine ⟨11589050365119595964655367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61808268613971178478161957 11589050365119595964655367)
          ·
            refine ⟨17383575547679393946983051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589050365119595964655367 17383575547679393946983051)
            ·
              refine ⟨26075363321519090920474577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17383575547679393946983051 26075363321519090920474577)
              ·
                refine ⟨19556522491139318190355933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26075363321519090920474577 19556522491139318190355933)
                ·
                  refine ⟨7333695934177244321383475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19556522491139318190355933 7333695934177244321383475)
                  ·
                    refine ⟨11000543901265866482075213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333695934177244321383475 11000543901265866482075213)
                    ·
                      refine ⟨4125203962974699930778205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000543901265866482075213 4125203962974699930778205)
                      ·
                        rfl

theorem cell23_8033806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_8033806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033806 prefixEnd_8033806 := by exact prefixLift 8033806
  have htrace : WordTrace (prefixWord ++ tailWord_8033806) baseStart_8033806 baseEnd_8033806 := by
    simpa [prefixWord, tailWord_8033806, baseEnd_8033806] using wordTrace_append hprefix tailTrace_8033806
  have hstable : (prefixWord ++ tailWord_8033806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033806).length < 2 ^ (prefixWord ++ tailWord_8033806).sum := by decide
  have hdescent : baseEnd_8033806 < baseStart_8033806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033829 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_8033829 : Nat := 118140960795 + 8033829 * 2 ^ 59
def prefixEnd_8033829 : Nat := 4983230072969 + 3 ^ 40 * 8033829 * 2
def baseEnd_8033829 : Nat := 4125215773029753340790599

theorem tailTrace_8033829 : CollatzResearch.WordTrace tailWord_8033829 prefixEnd_8033829 4125215773029753340790599 := by
  unfold tailWord_8033829
  simp only [CollatzResearch.WordTrace]
  refine ⟨293017816011817076602336541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195345210674544717734891027 293017816011817076602336541)
  ·
    refine ⟨109881681004431403725876203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293017816011817076602336541 109881681004431403725876203)
    ·
      refine ⟨164822521506647105588814305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109881681004431403725876203 164822521506647105588814305)
      ·
        refine ⟨123616891129985329191610729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164822521506647105588814305 123616891129985329191610729)
        ·
          refine ⟨92712668347488996893708047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123616891129985329191610729 92712668347488996893708047)
          ·
            refine ⟨139069002521233495340562071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92712668347488996893708047 139069002521233495340562071)
            ·
              refine ⟨208603503781850243010843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139069002521233495340562071 208603503781850243010843107)
              ·
                refine ⟨312905255672775364516264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208603503781850243010843107 312905255672775364516264661)
                ·
                  refine ⟨7333716929830672605849953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312905255672775364516264661 7333716929830672605849953)
                  ·
                    refine ⟨5500287697373004454387465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7333716929830672605849953 5500287697373004454387465)
                    ·
                      refine ⟨4125215773029753340790599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500287697373004454387465 4125215773029753340790599)
                      ·
                        rfl

theorem cell23_8033829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_8033829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033829 prefixEnd_8033829 := by exact prefixLift 8033829
  have htrace : WordTrace (prefixWord ++ tailWord_8033829) baseStart_8033829 baseEnd_8033829 := by
    simpa [prefixWord, tailWord_8033829, baseEnd_8033829] using wordTrace_append hprefix tailTrace_8033829
  have hstable : (prefixWord ++ tailWord_8033829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033829).length < 2 ^ (prefixWord ++ tailWord_8033829).sum := by decide
  have hdescent : baseEnd_8033829 < baseStart_8033829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033865 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_8033865 : Nat := 118140960795 + 8033865 * 2 ^ 59
def prefixEnd_8033865 : Nat := 4983230072969 + 3 ^ 40 * 8033865 * 2
def baseEnd_8033865 : Nat := 1375078086111105066646811

theorem tailTrace_8033865 : CollatzResearch.WordTrace tailWord_8033865 prefixEnd_8033865 1375078086111105066646811 := by
  unfold tailWord_8033865
  simp only [CollatzResearch.WordTrace]
  refine ⟨293019129039686654750647049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195346086026457769833764699 293019129039686654750647049)
  ·
    refine ⟨219764346779764991062985287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293019129039686654750647049 219764346779764991062985287)
    ·
      refine ⟨329646520169647486594477931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219764346779764991062985287 329646520169647486594477931)
      ·
        refine ⟨494469780254471229891716897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329646520169647486594477931 494469780254471229891716897)
        ·
          refine ⟨370852335190853422418787673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494469780254471229891716897 370852335190853422418787673)
          ·
            refine ⟨278139251393140066814090755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370852335190853422418787673 278139251393140066814090755)
            ·
              refine ⟨417208877089710100221136133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278139251393140066814090755 417208877089710100221136133)
              ·
                refine ⟨78226664454320643791463025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417208877089710100221136133 78226664454320643791463025)
                ·
                  refine ⟨58669998340740482843597269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78226664454320643791463025 58669998340740482843597269)
                  ·
                    refine ⟨1375078086111105066646811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58669998340740482843597269 1375078086111105066646811)
                    ·
                      rfl

theorem cell23_8033865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_8033865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033865 prefixEnd_8033865 := by exact prefixLift 8033865
  have htrace : WordTrace (prefixWord ++ tailWord_8033865) baseStart_8033865 baseEnd_8033865 := by
    simpa [prefixWord, tailWord_8033865, baseEnd_8033865] using wordTrace_append hprefix tailTrace_8033865
  have hstable : (prefixWord ++ tailWord_8033865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033865).length < 2 ^ (prefixWord ++ tailWord_8033865).sum := by decide
  have hdescent : baseEnd_8033865 < baseStart_8033865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033869 : List Nat := [1, 6, 1, 1, 3, 1, 1, 9]
def baseStart_8033869 : Nat := 118140960795 + 8033869 * 2 ^ 59
def prefixEnd_8033869 : Nat := 4983230072969 + 3 ^ 40 * 8033869 * 2
def baseEnd_8033869 : Nat := 152786530083553080899645

theorem tailTrace_8033869 : CollatzResearch.WordTrace tailWord_8033869 prefixEnd_8033869 152786530083553080899645 := by
  unfold tailWord_8033869
  simp only [CollatzResearch.WordTrace]
  refine ⟨293019274931672163433792661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195346183287781442289195107 293019274931672163433792661)
  ·
    refine ⟨13735278512422132660959031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293019274931672163433792661 13735278512422132660959031)
    ·
      refine ⟨20602917768633198991438547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735278512422132660959031 20602917768633198991438547)
      ·
        refine ⟨30904376652949798487157821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602917768633198991438547 30904376652949798487157821)
        ·
          refine ⟨11589141244856174432684183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30904376652949798487157821 11589141244856174432684183)
          ·
            refine ⟨17383711867284261649026275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589141244856174432684183 17383711867284261649026275)
            ·
              refine ⟨26075567800926392473539413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17383711867284261649026275 26075567800926392473539413)
              ·
                refine ⟨152786530083553080899645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26075567800926392473539413 152786530083553080899645)
                ·
                  rfl

theorem cell23_8033869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 9].length) (baseStart_8033869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033869 prefixEnd_8033869 := by exact prefixLift 8033869
  have htrace : WordTrace (prefixWord ++ tailWord_8033869) baseStart_8033869 baseEnd_8033869 := by
    simpa [prefixWord, tailWord_8033869, baseEnd_8033869] using wordTrace_append hprefix tailTrace_8033869
  have hstable : (prefixWord ++ tailWord_8033869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033869).length < 2 ^ (prefixWord ++ tailWord_8033869).sum := by decide
  have hdescent : baseEnd_8033869 < baseStart_8033869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033879 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_8033879 : Nat := 118140960795 + 8033879 * 2 ^ 59
def prefixEnd_8033879 : Nat := 4983230072969 + 3 ^ 40 * 8033879 * 2
def baseEnd_8033879 : Nat := 4125241447062478145165369

theorem tailTrace_8033879 : CollatzResearch.WordTrace tailWord_8033879 prefixEnd_8033879 4125241447062478145165369 := by
  unfold tailWord_8033879
  simp only [CollatzResearch.WordTrace]
  refine ⟨293019639661635935141656691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195346426441090623427771127 293019639661635935141656691)
  ·
    refine ⟨439529459492453902712485037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293019639661635935141656691 439529459492453902712485037)
    ·
      refine ⟨164823547309670213517181889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439529459492453902712485037 164823547309670213517181889)
      ·
        refine ⟨123617660482252660137886417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164823547309670213517181889 123617660482252660137886417)
        ·
          refine ⟨92713245361689495103414813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123617660482252660137886417 92713245361689495103414813)
          ·
            refine ⟨34767467010633560663780555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92713245361689495103414813 34767467010633560663780555)
            ·
              refine ⟨52151200515950340995670833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34767467010633560663780555 52151200515950340995670833)
              ·
                refine ⟨39113400386962755746753125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52151200515950340995670833 39113400386962755746753125)
                ·
                  refine ⟨7333762572555516702516211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39113400386962755746753125 7333762572555516702516211)
                  ·
                    refine ⟨11000643858833275053774317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333762572555516702516211 11000643858833275053774317)
                    ·
                      refine ⟨4125241447062478145165369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000643858833275053774317 4125241447062478145165369)
                      ·
                        rfl

theorem cell23_8033879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_8033879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033879 prefixEnd_8033879 := by exact prefixLift 8033879
  have htrace : WordTrace (prefixWord ++ tailWord_8033879) baseStart_8033879 baseEnd_8033879 := by
    simpa [prefixWord, tailWord_8033879, baseEnd_8033879] using wordTrace_append hprefix tailTrace_8033879
  have hstable : (prefixWord ++ tailWord_8033879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033879).length < 2 ^ (prefixWord ++ tailWord_8033879).sum := by decide
  have hdescent : baseEnd_8033879 < baseStart_8033879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033896 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_8033896 : Nat := 118140960795 + 8033896 * 2 ^ 59
def prefixEnd_8033896 : Nat := 4983230072969 + 3 ^ 40 * 8033896 * 2
def baseEnd_8033896 : Nat := 4125250176233604578652791

theorem tailTrace_8033896 : CollatzResearch.WordTrace tailWord_8033896 prefixEnd_8033896 4125250176233604578652791 := by
  unfold tailWord_8033896
  simp only [CollatzResearch.WordTrace]
  refine ⟨146510129851287173522512771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195346839801716231363350361 146510129851287173522512771)
  ·
    refine ⟨219765194776930760283769157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146510129851287173522512771 219765194776930760283769157)
    ·
      refine ⟨41205974020674517553206717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219765194776930760283769157 41205974020674517553206717)
      ·
        refine ⟨15452240257752944082452519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41205974020674517553206717 15452240257752944082452519)
        ·
          refine ⟨23178360386629416123678779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452240257752944082452519 23178360386629416123678779)
          ·
            refine ⟨34767540579944124185518169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23178360386629416123678779 34767540579944124185518169)
            ·
              refine ⟨26075655434958093139138627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34767540579944124185518169 26075655434958093139138627)
              ·
                refine ⟨39113483152437139708707941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26075655434958093139138627 39113483152437139708707941)
                ·
                  refine ⟨7333778091081963695382739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39113483152437139708707941 7333778091081963695382739)
                  ·
                    refine ⟨11000667136622945543074109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7333778091081963695382739 11000667136622945543074109)
                    ·
                      refine ⟨4125250176233604578652791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11000667136622945543074109 4125250176233604578652791)
                      ·
                        rfl

theorem cell23_8033896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_8033896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033896 prefixEnd_8033896 := by exact prefixLift 8033896
  have htrace : WordTrace (prefixWord ++ tailWord_8033896) baseStart_8033896 baseEnd_8033896 := by
    simpa [prefixWord, tailWord_8033896, baseEnd_8033896] using wordTrace_append hprefix tailTrace_8033896
  have hstable : (prefixWord ++ tailWord_8033896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033896).length < 2 ^ (prefixWord ++ tailWord_8033896).sum := by decide
  have hdescent : baseEnd_8033896 < baseStart_8033896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033953 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_8033953 : Nat := 118140960795 + 8033953 * 2 ^ 59
def prefixEnd_8033953 : Nat := 4983230072969 + 3 ^ 40 * 8033953 * 2
def baseEnd_8033953 : Nat := 4125279444630910855640029

theorem tailTrace_8033953 : CollatzResearch.WordTrace tailWord_8033953 prefixEnd_8033953 4125279444630910855640029 := by
  unfold tailWord_8033953
  simp only [CollatzResearch.WordTrace]
  refine ⟨293022338663367845779850513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195348225775578563853233675 293022338663367845779850513)
  ·
    refine ⟨219766753997525884334887885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293022338663367845779850513 219766753997525884334887885)
    ·
      refine ⟨82412532749072206625582957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219766753997525884334887885 82412532749072206625582957)
      ·
        refine ⟨30904699780902077484593609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82412532749072206625582957 30904699780902077484593609)
        ·
          refine ⟨23178524835676558113445207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30904699780902077484593609 23178524835676558113445207)
          ·
            refine ⟨34767787253514837170167811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23178524835676558113445207 34767787253514837170167811)
            ·
              refine ⟨52151680880272255755251717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34767787253514837170167811 52151680880272255755251717)
              ·
                refine ⟨9778440165051047954109697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52151680880272255755251717 9778440165051047954109697)
                ·
                  refine ⟨7333830123788285965582273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778440165051047954109697 7333830123788285965582273)
                  ·
                    refine ⟨5500372592841214474186705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7333830123788285965582273 5500372592841214474186705)
                    ·
                      refine ⟨4125279444630910855640029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500372592841214474186705 4125279444630910855640029)
                      ·
                        rfl

theorem cell23_8033953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_8033953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8033953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8033953 prefixEnd_8033953 := by exact prefixLift 8033953
  have htrace : WordTrace (prefixWord ++ tailWord_8033953) baseStart_8033953 baseEnd_8033953 := by
    simpa [prefixWord, tailWord_8033953, baseEnd_8033953] using wordTrace_append hprefix tailTrace_8033953
  have hstable : (prefixWord ++ tailWord_8033953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033953).length < 2 ^ (prefixWord ++ tailWord_8033953).sum := by decide
  have hdescent : baseEnd_8033953 < baseStart_8033953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034026 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_8034026 : Nat := 118140960795 + 8034026 * 2 ^ 59
def prefixEnd_8034026 : Nat := 4983230072969 + 3 ^ 40 * 8034026 * 2
def baseEnd_8034026 : Nat := 4125316928718689070027193

theorem tailTrace_8034026 : CollatzResearch.WordTrace tailWord_8034026 prefixEnd_8034026 4125316928718689070027193 := by
  unfold tailWord_8034026
  simp only [CollatzResearch.WordTrace]
  refine ⟨73256250298025844811814483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195350000794735586164838621 73256250298025844811814483)
  ·
    refine ⟨109884375447038767217721725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73256250298025844811814483 109884375447038767217721725)
    ·
      refine ⟨41206640792639537706645647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109884375447038767217721725 41206640792639537706645647)
      ·
        refine ⟨61809961188959306559968471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41206640792639537706645647 61809961188959306559968471)
        ·
          refine ⟨92714941783438959839952707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61809961188959306559968471 92714941783438959839952707)
          ·
            refine ⟨139072412675158439759929061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92714941783438959839952707 139072412675158439759929061)
            ·
              refine ⟨26076077376592207454986699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139072412675158439759929061 26076077376592207454986699)
              ·
                refine ⟨39114116064888311182480049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26076077376592207454986699 39114116064888311182480049)
                ·
                  refine ⟨29335587048666233386860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39114116064888311182480049 29335587048666233386860037)
                  ·
                    refine ⟨5500422571624918760036257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29335587048666233386860037 5500422571624918760036257)
                    ·
                      refine ⟨4125316928718689070027193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500422571624918760036257 4125316928718689070027193)
                      ·
                        rfl

theorem cell23_8034026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_8034026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034026 prefixEnd_8034026 := by exact prefixLift 8034026
  have htrace : WordTrace (prefixWord ++ tailWord_8034026) baseStart_8034026 baseEnd_8034026 := by
    simpa [prefixWord, tailWord_8034026, baseEnd_8034026] using wordTrace_append hprefix tailTrace_8034026
  have hstable : (prefixWord ++ tailWord_8034026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034026).length < 2 ^ (prefixWord ++ tailWord_8034026).sum := by decide
  have hdescent : baseEnd_8034026 < baseStart_8034026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034066 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_8034066 : Nat := 118140960795 + 8034066 * 2 ^ 59
def prefixEnd_8034066 : Nat := 4983230072969 + 3 ^ 40 * 8034066 * 2
def baseEnd_8034066 : Nat := 458370829771652101503001

theorem tailTrace_8034066 : CollatzResearch.WordTrace tailWord_8034066 prefixEnd_8034066 458370829771652101503001 := by
  unfold tailWord_8034066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73256615027989616519678513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195350973407972310719142701 73256615027989616519678513)
  ·
    refine ⟨54942461270992212389758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73256615027989616519678513 54942461270992212389758885)
    ·
      refine ⟨10301711488311039823079791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54942461270992212389758885 10301711488311039823079791)
      ·
        refine ⟨15452567232466559734619687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301711488311039823079791 15452567232466559734619687)
        ·
          refine ⟨23178850848699839601929531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452567232466559734619687 23178850848699839601929531)
          ·
            refine ⟨34768276273049759402894297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23178850848699839601929531 34768276273049759402894297)
            ·
              refine ⟨26076207204787319552170723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34768276273049759402894297 26076207204787319552170723)
              ·
                refine ⟨39114310807180979328256085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26076207204787319552170723 39114310807180979328256085)
                ·
                  refine ⟨458370829771652101503001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39114310807180979328256085 458370829771652101503001)
                  ·
                    rfl

theorem cell23_8034066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_8034066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034066 prefixEnd_8034066 := by exact prefixLift 8034066
  have htrace : WordTrace (prefixWord ++ tailWord_8034066) baseStart_8034066 baseEnd_8034066 := by
    simpa [prefixWord, tailWord_8034066, baseEnd_8034066] using wordTrace_append hprefix tailTrace_8034066
  have hstable : (prefixWord ++ tailWord_8034066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034066).length < 2 ^ (prefixWord ++ tailWord_8034066).sum := by decide
  have hdescent : baseEnd_8034066 < baseStart_8034066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034079 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 3, 5]
def baseStart_8034079 : Nat := 118140960795 + 8034079 * 2 ^ 59
def prefixEnd_8034079 : Nat := 4983230072969 + 3 ^ 40 * 8034079 * 2
def baseEnd_8034079 : Nat := 1375114714397792454221483

theorem tailTrace_8034079 : CollatzResearch.WordTrace tailWord_8034079 prefixEnd_8034079 1375114714397792454221483 := by
  unfold tailWord_8034079
  simp only [CollatzResearch.WordTrace]
  refine ⟨293026934260911369298937291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195351289507274246199291527 293026934260911369298937291)
  ·
    refine ⟨439540401391367053948405937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293026934260911369298937291 439540401391367053948405937)
    ·
      refine ⟨329655301043525290461304453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439540401391367053948405937 329655301043525290461304453)
      ·
        refine ⟨61810368945660991961494585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329655301043525290461304453 61810368945660991961494585)
        ·
          refine ⟨46357776709245743971120939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61810368945660991961494585 46357776709245743971120939)
          ·
            refine ⟨69536665063868615956681409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46357776709245743971120939 69536665063868615956681409)
            ·
              refine ⟨52152498797901461967511057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69536665063868615956681409 52152498797901461967511057)
              ·
                refine ⟨39114374098426096475633293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52152498797901461967511057 39114374098426096475633293)
                ·
                  refine ⟨14667890286909786178362485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39114374098426096475633293 14667890286909786178362485)
                  ·
                    refine ⟨1375114714397792454221483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14667890286909786178362485 1375114714397792454221483)
                    ·
                      rfl

theorem cell23_8034079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_8034079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034079 prefixEnd_8034079 := by exact prefixLift 8034079
  have htrace : WordTrace (prefixWord ++ tailWord_8034079) baseStart_8034079 baseEnd_8034079 := by
    simpa [prefixWord, tailWord_8034079, baseEnd_8034079] using wordTrace_append hprefix tailTrace_8034079
  have hstable : (prefixWord ++ tailWord_8034079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034079).length < 2 ^ (prefixWord ++ tailWord_8034079).sum := by decide
  have hdescent : baseEnd_8034079 < baseStart_8034079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034154 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_8034154 : Nat := 118140960795 + 8034154 * 2 ^ 59
def prefixEnd_8034154 : Nat := 4983230072969 + 3 ^ 40 * 8034154 * 2
def baseEnd_8034154 : Nat := 4125382654242464569226605

theorem tailTrace_8034154 : CollatzResearch.WordTrace tailWord_8034154 prefixEnd_8034154 4125382654242464569226605 := by
  unfold tailWord_8034154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73257417433909914276979379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195353113157093104738611677 73257417433909914276979379)
  ·
    refine ⟨109886126150864871415469069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73257417433909914276979379 109886126150864871415469069)
    ·
      refine ⟨41207297306574326780800901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109886126150864871415469069 41207297306574326780800901)
      ·
        refine ⟨7726368244982686271400169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41207297306574326780800901 7726368244982686271400169)
        ·
          refine ⟨5794776183737014703550127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7726368244982686271400169 5794776183737014703550127)
          ·
            refine ⟨8692164275605522055325191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794776183737014703550127 8692164275605522055325191)
            ·
              refine ⟨13038246413408283082987787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692164275605522055325191 13038246413408283082987787)
              ·
                refine ⟨19557369620112424624481681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038246413408283082987787 19557369620112424624481681)
                ·
                  refine ⟨14668027215084318468361261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19557369620112424624481681 14668027215084318468361261)
                  ·
                    refine ⟨5500510205656619425635473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14668027215084318468361261 5500510205656619425635473)
                    ·
                      refine ⟨4125382654242464569226605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500510205656619425635473 4125382654242464569226605)
                      ·
                        rfl

theorem cell23_8034154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_8034154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034154 prefixEnd_8034154 := by exact prefixLift 8034154
  have htrace : WordTrace (prefixWord ++ tailWord_8034154) baseStart_8034154 baseEnd_8034154 := by
    simpa [prefixWord, tailWord_8034154, baseEnd_8034154] using wordTrace_append hprefix tailTrace_8034154
  have hstable : (prefixWord ++ tailWord_8034154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034154).length < 2 ^ (prefixWord ++ tailWord_8034154).sum := by decide
  have hdescent : baseEnd_8034154 < baseStart_8034154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034156 : List Nat := [2, 2, 1, 1, 4, 3, 3, 7]
def baseStart_8034156 : Nat := 118140960795 + 8034156 * 2 ^ 59
def prefixEnd_8034156 : Nat := 4983230072969 + 3 ^ 40 * 8034156 * 2
def baseEnd_8034156 : Nat := 152791988192732354125985

theorem tailTrace_8034156 : CollatzResearch.WordTrace tailWord_8034156 prefixEnd_8034156 152791988192732354125985 := by
  unfold tailWord_8034156
  simp only [CollatzResearch.WordTrace]
  refine ⟨146514871340816205724745161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195353161787754940966326881 146514871340816205724745161)
  ·
    refine ⟨109886153505612154293558871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146514871340816205724745161 109886153505612154293558871)
    ·
      refine ⟨164829230258418231440338307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109886153505612154293558871 164829230258418231440338307)
      ·
        refine ⟨247243845387627347160507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164829230258418231440338307 247243845387627347160507461)
        ·
          refine ⟨46358221010180127592595149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247243845387627347160507461 46358221010180127592595149)
          ·
            refine ⟨17384332878817547847223181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46358221010180127592595149 17384332878817547847223181)
            ·
              refine ⟨6519124829556580442708693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17384332878817547847223181 6519124829556580442708693)
              ·
                refine ⟨152791988192732354125985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6519124829556580442708693 152791988192732354125985)
                ·
                  rfl

theorem cell23_8034156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 7].length) (baseStart_8034156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034156 prefixEnd_8034156 := by exact prefixLift 8034156
  have htrace : WordTrace (prefixWord ++ tailWord_8034156) baseStart_8034156 baseEnd_8034156 := by
    simpa [prefixWord, tailWord_8034156, baseEnd_8034156] using wordTrace_append hprefix tailTrace_8034156
  have hstable : (prefixWord ++ tailWord_8034156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034156).length < 2 ^ (prefixWord ++ tailWord_8034156).sum := by decide
  have hdescent : baseEnd_8034156 < baseStart_8034156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034177 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_8034177 : Nat := 118140960795 + 8034177 * 2 ^ 59
def prefixEnd_8034177 : Nat := 4983230072969 + 3 ^ 40 * 8034177 * 2
def baseEnd_8034177 : Nat := 1375131488099172659746333

theorem tailTrace_8034177 : CollatzResearch.WordTrace tailWord_8034177 prefixEnd_8034177 1375131488099172659746333 := by
  unfold tailWord_8034177
  simp only [CollatzResearch.WordTrace]
  refine ⟨293030508614556332036004785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195353672409704221357336523 293030508614556332036004785)
  ·
    refine ⟨219772881460917249027003589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293030508614556332036004785 219772881460917249027003589)
    ·
      refine ⟨41207415273921984192563173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219772881460917249027003589 41207415273921984192563173)
      ·
        refine ⟨7726390363860372036105595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41207415273921984192563173 7726390363860372036105595)
        ·
          refine ⟨11589585545790558054158393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726390363860372036105595 11589585545790558054158393)
          ·
            refine ⟨8692189159342918540618795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589585545790558054158393 8692189159342918540618795)
            ·
              refine ⟨13038283739014377810928193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692189159342918540618795 13038283739014377810928193)
              ·
                refine ⟨9778712804260783358196145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13038283739014377810928193 9778712804260783358196145)
                ·
                  refine ⟨7334034603195587518647109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778712804260783358196145 7334034603195587518647109)
                  ·
                    refine ⟨1375131488099172659746333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7334034603195587518647109 1375131488099172659746333)
                    ·
                      rfl

theorem cell23_8034177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_8034177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034177 prefixEnd_8034177 := by exact prefixLift 8034177
  have htrace : WordTrace (prefixWord ++ tailWord_8034177) baseStart_8034177 baseEnd_8034177 := by
    simpa [prefixWord, tailWord_8034177, baseEnd_8034177] using wordTrace_append hprefix tailTrace_8034177
  have hstable : (prefixWord ++ tailWord_8034177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034177).length < 2 ^ (prefixWord ++ tailWord_8034177).sum := by decide
  have hdescent : baseEnd_8034177 < baseStart_8034177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034223 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 6, 2, 2]
def baseStart_8034223 : Nat := 118140960795 + 8034223 * 2 ^ 59
def prefixEnd_8034223 : Nat := 4983230072969 + 3 ^ 40 * 8034223 * 2
def baseEnd_8034223 : Nat := 4125418084407624799263787

theorem tailTrace_8034223 : CollatzResearch.WordTrace tailWord_8034223 prefixEnd_8034223 4125418084407624799263787 := by
  unfold tailWord_8034223
  simp only [CollatzResearch.WordTrace]
  refine ⟨293032186372389681892179323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195354790914926454594786215 293032186372389681892179323)
  ·
    refine ⟨439548279558584522838268985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293032186372389681892179323 439548279558584522838268985)
    ·
      refine ⟨329661209668938392128701739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439548279558584522838268985 329661209668938392128701739)
      ·
        refine ⟨494491814503407588193052609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329661209668938392128701739 494491814503407588193052609)
        ·
          refine ⟨370868860877555691144789457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494491814503407588193052609 370868860877555691144789457)
          ·
            refine ⟨278151645658166768358592093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370868860877555691144789457 278151645658166768358592093)
            ·
              refine ⟨104306867121812538134472035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278151645658166768358592093 104306867121812538134472035)
              ·
                refine ⟨156460300682718807201708053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104306867121812538134472035 156460300682718807201708053)
                ·
                  refine ⟨7334076594502444087580065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156460300682718807201708053 7334076594502444087580065)
                  ·
                    refine ⟨5500557445876833065685049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7334076594502444087580065 5500557445876833065685049)
                    ·
                      refine ⟨4125418084407624799263787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500557445876833065685049 4125418084407624799263787)
                      ·
                        rfl

theorem cell23_8034223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2, 2].length) (baseStart_8034223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034223 prefixEnd_8034223 := by exact prefixLift 8034223
  have htrace : WordTrace (prefixWord ++ tailWord_8034223) baseStart_8034223 baseEnd_8034223 := by
    simpa [prefixWord, tailWord_8034223, baseEnd_8034223] using wordTrace_append hprefix tailTrace_8034223
  have hstable : (prefixWord ++ tailWord_8034223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034223).length < 2 ^ (prefixWord ++ tailWord_8034223).sum := by decide
  have hdescent : baseEnd_8034223 < baseStart_8034223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034239 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_8034239 : Nat := 118140960795 + 8034239 * 2 ^ 59
def prefixEnd_8034239 : Nat := 4983230072969 + 3 ^ 40 * 8034239 * 2
def baseEnd_8034239 : Nat := 4125426300098096736663713

theorem tailTrace_8034239 : CollatzResearch.WordTrace tailWord_8034239 prefixEnd_8034239 4125426300098096736663713 := by
  unfold tailWord_8034239
  simp only [CollatzResearch.WordTrace]
  refine ⟨293032769940331716624761771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195355179960221144416507847 293032769940331716624761771)
  ·
    refine ⟨439549154910497574937142657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293032769940331716624761771 439549154910497574937142657)
    ·
      refine ⟨329661866182873181202856993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439549154910497574937142657 329661866182873181202856993)
      ·
        refine ⟨247246399637154885902142745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329661866182873181202856993 247246399637154885902142745)
        ·
          refine ⟨185434799727866164426607059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247246399637154885902142745 185434799727866164426607059)
          ·
            refine ⟨278152199591799246639910589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185434799727866164426607059 278152199591799246639910589)
            ·
              refine ⟨104307074846924717489966471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278152199591799246639910589 104307074846924717489966471)
              ·
                refine ⟨156460612270387076234949707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104307074846924717489966471 156460612270387076234949707)
                ·
                  refine ⟨234690918405580614352424561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156460612270387076234949707 234690918405580614352424561)
                  ·
                    refine ⟨176018188804185460764318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234690918405580614352424561 176018188804185460764318421)
                    ·
                      refine ⟨4125426300098096736663713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176018188804185460764318421 4125426300098096736663713)
                      ·
                        rfl

theorem cell23_8034239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_8034239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034239 prefixEnd_8034239 := by exact prefixLift 8034239
  have htrace : WordTrace (prefixWord ++ tailWord_8034239) baseStart_8034239 baseEnd_8034239 := by
    simpa [prefixWord, tailWord_8034239, baseEnd_8034239] using wordTrace_append hprefix tailTrace_8034239
  have hstable : (prefixWord ++ tailWord_8034239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034239).length < 2 ^ (prefixWord ++ tailWord_8034239).sum := by decide
  have hdescent : baseEnd_8034239 < baseStart_8034239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034240 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2]
def baseStart_8034240 : Nat := 118140960795 + 8034240 * 2 ^ 59
def prefixEnd_8034240 : Nat := 4983230072969 + 3 ^ 40 * 8034240 * 2
def baseEnd_8034240 : Nat := 4125426813578751232751209

theorem tailTrace_8034240 : CollatzResearch.WordTrace tailWord_8034240 prefixEnd_8034240 4125426813578751232751209 := by
  unfold tailWord_8034240
  simp only [CollatzResearch.WordTrace]
  refine ⟨146516403206664046897774087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195355204275552062530365449 146516403206664046897774087)
  ·
    refine ⟨219774604809996070346661131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146516403206664046897774087 219774604809996070346661131)
    ·
      refine ⟨329661907214994105519991697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219774604809996070346661131 329661907214994105519991697)
      ·
        refine ⟨247246430411245579139993773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329661907214994105519991697 247246430411245579139993773)
        ·
          refine ⟨92717411404217092177497665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247246430411245579139993773 92717411404217092177497665)
          ·
            refine ⟨69538058553162819133123249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92717411404217092177497665 69538058553162819133123249)
            ·
              refine ⟨52153543914872114349842437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69538058553162819133123249 52153543914872114349842437)
              ·
                refine ⟨9778789484038521440595457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52153543914872114349842437 9778789484038521440595457)
                ·
                  refine ⟨7334092113028891080446593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778789484038521440595457 7334092113028891080446593)
                  ·
                    refine ⟨5500569084771668310334945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7334092113028891080446593 5500569084771668310334945)
                    ·
                      refine ⟨4125426813578751232751209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500569084771668310334945 4125426813578751232751209)
                      ·
                        rfl

theorem cell23_8034240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_8034240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034240 prefixEnd_8034240 := by exact prefixLift 8034240
  have htrace : WordTrace (prefixWord ++ tailWord_8034240) baseStart_8034240 baseEnd_8034240 := by
    simpa [prefixWord, tailWord_8034240, baseEnd_8034240] using wordTrace_append hprefix tailTrace_8034240
  have hstable : (prefixWord ++ tailWord_8034240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034240).length < 2 ^ (prefixWord ++ tailWord_8034240).sum := by decide
  have hdescent : baseEnd_8034240 < baseStart_8034240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034256 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_8034256 : Nat := 118140960795 + 8034256 * 2 ^ 59
def prefixEnd_8034256 : Nat := 4983230072969 + 3 ^ 40 * 8034256 * 2
def baseEnd_8034256 : Nat := 4125435029269223170151135

theorem tailTrace_8034256 : CollatzResearch.WordTrace tailWord_8034256 prefixEnd_8034256 4125435029269223170151135 := by
  unfold tailWord_8034256
  simp only [CollatzResearch.WordTrace]
  refine ⟨146516694990635064264065311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195355593320846752352087081 146516694990635064264065311)
  ·
    refine ⟨219775042485952596396097967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146516694990635064264065311 219775042485952596396097967)
    ·
      refine ⟨329662563728928894594146951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219775042485952596396097967 329662563728928894594146951)
      ·
        refine ⟨494493845593393341891220427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329662563728928894594146951 494493845593393341891220427)
        ·
          refine ⟨741740768390090012836830641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494493845593393341891220427 741740768390090012836830641)
          ·
            refine ⟨556305576292567509627622981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741740768390090012836830641 556305576292567509627622981)
            ·
              refine ⟨104307295554856408055179309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556305576292567509627622981 104307295554856408055179309)
              ·
                refine ⟨39115235833071153020692241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104307295554856408055179309 39115235833071153020692241)
                ·
                  refine ⟨29336426874803364765519181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39115235833071153020692241 29336426874803364765519181)
                  ·
                    refine ⟨11001160078051261787069693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29336426874803364765519181 11001160078051261787069693)
                    ·
                      refine ⟨4125435029269223170151135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001160078051261787069693 4125435029269223170151135)
                      ·
                        rfl

theorem cell23_8034256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_8034256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034256 prefixEnd_8034256 := by exact prefixLift 8034256
  have htrace : WordTrace (prefixWord ++ tailWord_8034256) baseStart_8034256 baseEnd_8034256 := by
    simpa [prefixWord, tailWord_8034256, baseEnd_8034256] using wordTrace_append hprefix tailTrace_8034256
  have hstable : (prefixWord ++ tailWord_8034256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034256).length < 2 ^ (prefixWord ++ tailWord_8034256).sum := by decide
  have hdescent : baseEnd_8034256 < baseStart_8034256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034327 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 2, 5]
def baseStart_8034327 : Nat := 118140960795 + 8034327 * 2 ^ 59
def prefixEnd_8034327 : Nat := 4983230072969 + 3 ^ 40 * 8034327 * 2
def baseEnd_8034327 : Nat := 1375157162131897464121103

theorem tailTrace_8034327 : CollatzResearch.WordTrace tailWord_8034327 prefixEnd_8034327 1375157162131897464121103 := by
  unfold tailWord_8034327
  simp only [CollatzResearch.WordTrace]
  refine ⟨293035979564012907653965235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195357319709341938435976823 293035979564012907653965235)
  ·
    refine ⟨439553969346019361480947853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293035979564012907653965235 439553969346019361480947853)
    ·
      refine ⟨164832738504757260555355445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439553969346019361480947853 164832738504757260555355445)
      ·
        refine ⟨15453069234820993177064573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164832738504757260555355445 15453069234820993177064573)
        ·
          refine ⟨5794900963057872441399215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15453069234820993177064573 5794900963057872441399215)
          ·
            refine ⟨8692351444586808662098823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794900963057872441399215 8692351444586808662098823)
            ·
              refine ⟨13038527166880212993148235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692351444586808662098823 13038527166880212993148235)
              ·
                refine ⟨19557790750320319489722353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038527166880212993148235 19557790750320319489722353)
                ·
                  refine ⟨14668343062740239617291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19557790750320319489722353 14668343062740239617291765)
                  ·
                    refine ⟨1375157162131897464121103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14668343062740239617291765 1375157162131897464121103)
                    ·
                      rfl

theorem cell23_8034327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_8034327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034327 prefixEnd_8034327 := by exact prefixLift 8034327
  have htrace : WordTrace (prefixWord ++ tailWord_8034327) baseStart_8034327 baseEnd_8034327 := by
    simpa [prefixWord, tailWord_8034327, baseEnd_8034327] using wordTrace_append hprefix tailTrace_8034327
  have hstable : (prefixWord ++ tailWord_8034327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034327).length < 2 ^ (prefixWord ++ tailWord_8034327).sum := by decide
  have hdescent : baseEnd_8034327 < baseStart_8034327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034330 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_8034330 : Nat := 118140960795 + 8034330 * 2 ^ 59
def prefixEnd_8034330 : Nat := 4983230072969 + 3 ^ 40 * 8034330 * 2
def baseEnd_8034330 : Nat := 4125473026837655880625795

theorem tailTrace_8034330 : CollatzResearch.WordTrace tailWord_8034330 prefixEnd_8034330 4125473026837655880625795 := by
  unfold tailWord_8034330
  simp only [CollatzResearch.WordTrace]
  refine ⟨73259022245750509791581111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195357392655334692777549629 73259022245750509791581111)
  ·
    refine ⟨109888533368625764687371667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73259022245750509791581111 109888533368625764687371667)
    ·
      refine ⟨164832800052938647031057501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109888533368625764687371667 164832800052938647031057501)
      ·
        refine ⟨61812300019851992636646563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164832800052938647031057501 61812300019851992636646563)
        ·
          refine ⟨92718450029777988954969845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61812300019851992636646563 92718450029777988954969845)
          ·
            refine ⟨8692354690291686464528423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92718450029777988954969845 8692354690291686464528423)
            ·
              refine ⟨13038532035437529696792635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692354690291686464528423 13038532035437529696792635)
              ·
                refine ⟨19557798053156294545188953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038532035437529696792635 19557798053156294545188953)
                ·
                  refine ⟨14668348539867220908891715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19557798053156294545188953 14668348539867220908891715)
                  ·
                    refine ⟨22002522809800831363337573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14668348539867220908891715 22002522809800831363337573)
                    ·
                      refine ⟨4125473026837655880625795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22002522809800831363337573 4125473026837655880625795)
                      ·
                        rfl

theorem cell23_8034330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_8034330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034330 prefixEnd_8034330 := by exact prefixLift 8034330
  have htrace : WordTrace (prefixWord ++ tailWord_8034330) baseStart_8034330 baseEnd_8034330 := by
    simpa [prefixWord, tailWord_8034330, baseEnd_8034330] using wordTrace_append hprefix tailTrace_8034330
  have hstable : (prefixWord ++ tailWord_8034330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034330).length < 2 ^ (prefixWord ++ tailWord_8034330).sum := by decide
  have hdescent : baseEnd_8034330 < baseStart_8034330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034353 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 6]
def baseStart_8034353 : Nat := 118140960795 + 8034353 * 2 ^ 59
def prefixEnd_8034353 : Nat := 4983230072969 + 3 ^ 40 * 8034353 * 2
def baseEnd_8034353 : Nat := 458387204099189921182021

theorem tailTrace_8034353 : CollatzResearch.WordTrace tailWord_8034353 prefixEnd_8034353 458387204099189921182021 := by
  unfold tailWord_8034353
  simp only [CollatzResearch.WordTrace]
  refine ⟨293036927861918714094411713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195357951907945809396274475 293036927861918714094411713)
  ·
    refine ⟨219777695896439035570808785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293036927861918714094411713 219777695896439035570808785)
    ·
      refine ⟨164833271922329276678106589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219777695896439035570808785 164833271922329276678106589)
      ·
        refine ⟨61812476970873478754289971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164833271922329276678106589 61812476970873478754289971)
        ·
          refine ⟨92718715456310218131434957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61812476970873478754289971 92718715456310218131434957)
          ·
            refine ⟨34769518296116331799288109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92718715456310218131434957 34769518296116331799288109)
            ·
              refine ⟨13038569361043624424733041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34769518296116331799288109 13038569361043624424733041)
              ·
                refine ⟨9778927020782718318549781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13038569361043624424733041 9778927020782718318549781)
                ·
                  refine ⟨458387204099189921182021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9778927020782718318549781 458387204099189921182021)
                  ·
                    rfl

theorem cell23_8034353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_8034353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034353 prefixEnd_8034353 := by exact prefixLift 8034353
  have htrace : WordTrace (prefixWord ++ tailWord_8034353) baseStart_8034353 baseEnd_8034353 := by
    simpa [prefixWord, tailWord_8034353, baseEnd_8034353] using wordTrace_append hprefix tailTrace_8034353
  have hstable : (prefixWord ++ tailWord_8034353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034353).length < 2 ^ (prefixWord ++ tailWord_8034353).sum := by decide
  have hdescent : baseEnd_8034353 < baseStart_8034353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034363 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 3]
def baseStart_8034363 : Nat := 118140960795 + 8034363 * 2 ^ 59
def prefixEnd_8034363 : Nat := 4983230072969 + 3 ^ 40 * 8034363 * 2
def baseEnd_8034363 : Nat := 4125489971699254251513143

theorem tailTrace_8034363 : CollatzResearch.WordTrace tailWord_8034363 prefixEnd_8034363 4125489971699254251513143 := by
  unfold tailWord_8034363
  simp only [CollatzResearch.WordTrace]
  refine ⟨293037292591882485802275743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195358195061254990534850495 293037292591882485802275743)
  ·
    refine ⟨439555938887823728703413615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293037292591882485802275743 439555938887823728703413615)
    ·
      refine ⟨659333908331735593055120423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439555938887823728703413615 659333908331735593055120423)
      ·
        refine ⟨989000862497603389582680635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659333908331735593055120423 989000862497603389582680635)
        ·
          refine ⟨1483501293746405084374020953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989000862497603389582680635 1483501293746405084374020953)
          ·
            refine ⟨1112625970309803813280515715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483501293746405084374020953 1112625970309803813280515715)
            ·
              refine ⟨1668938955464705719920773573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112625970309803813280515715 1668938955464705719920773573)
              ·
                refine ⟨312926054149632322485145045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1668938955464705719920773573 312926054149632322485145045)
                ·
                  refine ⟨7334204394132007558245587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312926054149632322485145045 7334204394132007558245587)
                  ·
                    refine ⟨11001306591198011337368381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7334204394132007558245587 11001306591198011337368381)
                    ·
                      refine ⟨4125489971699254251513143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001306591198011337368381 4125489971699254251513143)
                      ·
                        rfl

theorem cell23_8034363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 3].length) (baseStart_8034363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034363 prefixEnd_8034363 := by exact prefixLift 8034363
  have htrace : WordTrace (prefixWord ++ tailWord_8034363) baseStart_8034363 baseEnd_8034363 := by
    simpa [prefixWord, tailWord_8034363, baseEnd_8034363] using wordTrace_append hprefix tailTrace_8034363
  have hstable : (prefixWord ++ tailWord_8034363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034363).length < 2 ^ (prefixWord ++ tailWord_8034363).sum := by decide
  have hdescent : baseEnd_8034363 < baseStart_8034363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034380 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_8034380 : Nat := 118140960795 + 8034380 * 2 ^ 59
def prefixEnd_8034380 : Nat := 4983230072969 + 3 ^ 40 * 8034380 * 2
def baseEnd_8034380 : Nat := 4125498700870380685000565

theorem tailTrace_8034380 : CollatzResearch.WordTrace tailWord_8034380 prefixEnd_8034380 4125498700870380685000565 := by
  unfold tailWord_8034380
  simp only [CollatzResearch.WordTrace]
  refine ⟨146518956316410448852822297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195358608421880598470429729 146518956316410448852822297)
  ·
    refine ⟨109889217237307836639616723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146518956316410448852822297 109889217237307836639616723)
    ·
      refine ⟨164833825855961754959425085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109889217237307836639616723 164833825855961754959425085)
      ·
        refine ⟨61812684695985658109784407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164833825855961754959425085 61812684695985658109784407)
        ·
          refine ⟨92719027043978487164676611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61812684695985658109784407 92719027043978487164676611)
          ·
            refine ⟨139078540565967730747014917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92719027043978487164676611 139078540565967730747014917)
            ·
              refine ⟨26077226356118949515065297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139078540565967730747014917 26077226356118949515065297)
              ·
                refine ⟨19557919767089212136298973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26077226356118949515065297 19557919767089212136298973)
                ·
                  refine ⟨7334219912658454551112115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19557919767089212136298973 7334219912658454551112115)
                  ·
                    refine ⟨11001329868987681826668173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7334219912658454551112115 11001329868987681826668173)
                    ·
                      refine ⟨4125498700870380685000565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001329868987681826668173 4125498700870380685000565)
                      ·
                        rfl

theorem cell23_8034380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_8034380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034380 prefixEnd_8034380 := by exact prefixLift 8034380
  have htrace : WordTrace (prefixWord ++ tailWord_8034380) baseStart_8034380 baseEnd_8034380 := by
    simpa [prefixWord, tailWord_8034380, baseEnd_8034380] using wordTrace_append hprefix tailTrace_8034380
  have hstable : (prefixWord ++ tailWord_8034380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034380).length < 2 ^ (prefixWord ++ tailWord_8034380).sum := by decide
  have hdescent : baseEnd_8034380 < baseStart_8034380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034423 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_8034423 : Nat := 118140960795 + 8034423 * 2 ^ 59
def prefixEnd_8034423 : Nat := 4983230072969 + 3 ^ 40 * 8034423 * 2
def baseEnd_8034423 : Nat := 4125520780538524016762867

theorem tailTrace_8034423 : CollatzResearch.WordTrace tailWord_8034423 prefixEnd_8034423 4125520780538524016762867 := by
  unfold tailWord_8034423
  simp only [CollatzResearch.WordTrace]
  refine ⟨293039480971665116049459923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195359653981110077366306615 293039480971665116049459923)
  ·
    refine ⟨439559221457497674074189885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293039480971665116049459923 439559221457497674074189885)
    ·
      refine ⟨164834708046561627777821207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439559221457497674074189885 164834708046561627777821207)
      ·
        refine ⟨247252062069842441666731811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164834708046561627777821207 247252062069842441666731811)
        ·
          refine ⟨370878093104763662500097717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247252062069842441666731811 370878093104763662500097717)
          ·
            refine ⟨34769821228571593359384161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370878093104763662500097717 34769821228571593359384161)
            ·
              refine ⟨26077365921428695019538121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34769821228571593359384161 26077365921428695019538121)
              ·
                refine ⟨19558024441071521264653591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26077365921428695019538121 19558024441071521264653591)
                ·
                  refine ⟨29337036661607281896980387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19558024441071521264653591 29337036661607281896980387)
                  ·
                    refine ⟨44005554992410922845470581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29337036661607281896980387 44005554992410922845470581)
                    ·
                      refine ⟨4125520780538524016762867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44005554992410922845470581 4125520780538524016762867)
                      ·
                        rfl

theorem cell23_8034423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_8034423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034423 prefixEnd_8034423 := by exact prefixLift 8034423
  have htrace : WordTrace (prefixWord ++ tailWord_8034423) baseStart_8034423 baseEnd_8034423 := by
    simpa [prefixWord, tailWord_8034423, baseEnd_8034423] using wordTrace_append hprefix tailTrace_8034423
  have hstable : (prefixWord ++ tailWord_8034423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034423).length < 2 ^ (prefixWord ++ tailWord_8034423).sum := by decide
  have hdescent : baseEnd_8034423 < baseStart_8034423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034437 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_8034437 : Nat := 118140960795 + 8034437 * 2 ^ 59
def prefixEnd_8034437 : Nat := 4983230072969 + 3 ^ 40 * 8034437 * 2
def baseEnd_8034437 : Nat := 4125527969267686961987803

theorem tailTrace_8034437 : CollatzResearch.WordTrace tailWord_8034437 prefixEnd_8034437 4125527969267686961987803 := by
  unfold tailWord_8034437
  simp only [CollatzResearch.WordTrace]
  refine ⟨293039991593614396440469565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195359994395742930960313043 293039991593614396440469565)
  ·
    refine ⟨109889996847605398665176087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293039991593614396440469565 109889996847605398665176087)
    ·
      refine ⟨164834995271408097997764131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109889996847605398665176087 164834995271408097997764131)
      ·
        refine ⟨247252492907112146996646197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164834995271408097997764131 247252492907112146996646197)
        ·
          refine ⟨23179921210041763780935581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247252492907112146996646197 23179921210041763780935581)
          ·
            refine ⟨8692470453765661417850843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23179921210041763780935581 8692470453765661417850843)
            ·
              refine ⟨13038705680648492126776265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692470453765661417850843 13038705680648492126776265)
              ·
                refine ⟨9779029260486369095082199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13038705680648492126776265 9779029260486369095082199)
                ·
                  refine ⟨14668543890729553642623299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779029260486369095082199 14668543890729553642623299)
                  ·
                    refine ⟨22002815836094330463934949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14668543890729553642623299 22002815836094330463934949)
                    ·
                      refine ⟨4125527969267686961987803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22002815836094330463934949 4125527969267686961987803)
                      ·
                        rfl

theorem cell23_8034437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_8034437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034437 prefixEnd_8034437 := by exact prefixLift 8034437
  have htrace : WordTrace (prefixWord ++ tailWord_8034437) baseStart_8034437 baseEnd_8034437 := by
    simpa [prefixWord, tailWord_8034437, baseEnd_8034437] using wordTrace_append hprefix tailTrace_8034437
  have hstable : (prefixWord ++ tailWord_8034437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034437).length < 2 ^ (prefixWord ++ tailWord_8034437).sum := by decide
  have hdescent : baseEnd_8034437 < baseStart_8034437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034450 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_8034450 : Nat := 118140960795 + 8034450 * 2 ^ 59
def prefixEnd_8034450 : Nat := 4983230072969 + 3 ^ 40 * 8034450 * 2
def baseEnd_8034450 : Nat := 4125534644516195411125243

theorem tailTrace_8034450 : CollatzResearch.WordTrace tailWord_8034450 prefixEnd_8034450 4125534644516195411125243 := by
  unfold tailWord_8034450
  simp only [CollatzResearch.WordTrace]
  refine ⟨73260116435641824915173201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195360310495044866440461869 73260116435641824915173201)
  ·
    refine ⟨54945087326731368686379901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73260116435641824915173201 54945087326731368686379901)
    ·
      refine ⟨20604407747524263257392463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54945087326731368686379901 20604407747524263257392463)
      ·
        refine ⟨30906611621286394886088695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20604407747524263257392463 30906611621286394886088695)
        ·
          refine ⟨46359917431929592329133043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30906611621286394886088695 46359917431929592329133043)
          ·
            refine ⟨69539876147894388493699565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46359917431929592329133043 69539876147894388493699565)
            ·
              refine ⟨26077453555460395685137337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69539876147894388493699565 26077453555460395685137337)
              ·
                refine ⟨19558090166595296763853003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26077453555460395685137337 19558090166595296763853003)
                ·
                  refine ⟨29337135249892945145779505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19558090166595296763853003 29337135249892945145779505)
                  ·
                    refine ⟨22002851437419708859334629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29337135249892945145779505 22002851437419708859334629)
                    ·
                      refine ⟨4125534644516195411125243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22002851437419708859334629 4125534644516195411125243)
                      ·
                        rfl

theorem cell23_8034450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_8034450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034450 prefixEnd_8034450 := by exact prefixLift 8034450
  have htrace : WordTrace (prefixWord ++ tailWord_8034450) baseStart_8034450 baseEnd_8034450 := by
    simpa [prefixWord, tailWord_8034450, baseEnd_8034450] using wordTrace_append hprefix tailTrace_8034450
  have hstable : (prefixWord ++ tailWord_8034450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034450).length < 2 ^ (prefixWord ++ tailWord_8034450).sum := by decide
  have hdescent : baseEnd_8034450 < baseStart_8034450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034487 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_8034487 : Nat := 118140960795 + 8034487 * 2 ^ 59
def prefixEnd_8034487 : Nat := 4983230072969 + 3 ^ 40 * 8034487 * 2
def baseEnd_8034487 : Nat := 4125553643300411766362573

theorem tailTrace_8034487 : CollatzResearch.WordTrace tailWord_8034487 prefixEnd_8034487 4125553643300411766362573 := by
  unfold tailWord_8034487
  simp only [CollatzResearch.WordTrace]
  refine ⟨293041815243433254979789715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195361210162288836653193143 293041815243433254979789715)
  ·
    refine ⟨439562722865149882469684573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293041815243433254979789715 439562722865149882469684573)
    ·
      refine ⟨164836021074431205926131715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439562722865149882469684573 164836021074431205926131715)
      ·
        refine ⟨247254031611646808889197573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164836021074431205926131715 247254031611646808889197573)
        ·
          refine ⟨46360130927183776666724545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247254031611646808889197573 46360130927183776666724545)
          ·
            refine ⟨34770098195387832500043409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46360130927183776666724545 34770098195387832500043409)
            ·
              refine ⟨26077573646540874375032557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34770098195387832500043409 26077573646540874375032557)
              ·
                refine ⟨9779090117452827890637209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26077573646540874375032557 9779090117452827890637209)
                ·
                  refine ⟨7334317588089620917977907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9779090117452827890637209 7334317588089620917977907)
                  ·
                    refine ⟨11001476382134431376966861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7334317588089620917977907 11001476382134431376966861)
                    ·
                      refine ⟨4125553643300411766362573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001476382134431376966861 4125553643300411766362573)
                      ·
                        rfl

theorem cell23_8034487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_8034487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034487 prefixEnd_8034487 := by exact prefixLift 8034487
  have htrace : WordTrace (prefixWord ++ tailWord_8034487) baseStart_8034487 baseEnd_8034487 := by
    simpa [prefixWord, tailWord_8034487, baseEnd_8034487] using wordTrace_append hprefix tailTrace_8034487
  have hstable : (prefixWord ++ tailWord_8034487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034487).length < 2 ^ (prefixWord ++ tailWord_8034487).sum := by decide
  have hdescent : baseEnd_8034487 < baseStart_8034487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034493 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_8034493 : Nat := 118140960795 + 8034493 * 2 ^ 59
def prefixEnd_8034493 : Nat := 4983230072969 + 3 ^ 40 * 8034493 * 2
def baseEnd_8034493 : Nat := 4125556724184338742887545

theorem tailTrace_8034493 : CollatzResearch.WordTrace tailWord_8034493 prefixEnd_8034493 4125556724184338742887545 := by
  unfold tailWord_8034493
  simp only [CollatzResearch.WordTrace]
  refine ⟨293042034081411518004508133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195361356054274345336338755 293042034081411518004508133)
  ·
    refine ⟨54945381390264659625845275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293042034081411518004508133 54945381390264659625845275)
    ·
      refine ⟨82418072085396989438767913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54945381390264659625845275 82418072085396989438767913)
      ·
        refine ⟨61813554064047742079075935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82418072085396989438767913 61813554064047742079075935)
        ·
          refine ⟨92720331096071613118613903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61813554064047742079075935 92720331096071613118613903)
          ·
            refine ⟨139080496644107419677920855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92720331096071613118613903 139080496644107419677920855)
            ·
              refine ⟨208620744966161129516881283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139080496644107419677920855 208620744966161129516881283)
              ·
                refine ⟨312931117449241694275321925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208620744966161129516881283 312931117449241694275321925)
                ·
                  refine ⟨58674584521732817676622861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312931117449241694275321925 58674584521732817676622861)
                  ·
                    refine ⟨22002969195649806628733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58674584521732817676622861 22002969195649806628733573)
                    ·
                      refine ⟨4125556724184338742887545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22002969195649806628733573 4125556724184338742887545)
                      ·
                        rfl

theorem cell23_8034493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_8034493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034493 prefixEnd_8034493 := by exact prefixLift 8034493
  have htrace : WordTrace (prefixWord ++ tailWord_8034493) baseStart_8034493 baseEnd_8034493 := by
    simpa [prefixWord, tailWord_8034493, baseEnd_8034493] using wordTrace_append hprefix tailTrace_8034493
  have hstable : (prefixWord ++ tailWord_8034493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034493).length < 2 ^ (prefixWord ++ tailWord_8034493).sum := by decide
  have hdescent : baseEnd_8034493 < baseStart_8034493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034508 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8034508 : Nat := 118140960795 + 8034508 * 2 ^ 59
def prefixEnd_8034508 : Nat := 4983230072969 + 3 ^ 40 * 8034508 * 2
def baseEnd_8034508 : Nat := 4125564426394156184199977

theorem tailTrace_8034508 : CollatzResearch.WordTrace tailWord_8034508 prefixEnd_8034508 4125564426394156184199977 := by
  unfold tailWord_8034508
  simp only [CollatzResearch.WordTrace]
  refine ⟨146521290588178587783152089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195361720784238117044202785 146521290588178587783152089)
  ·
    refine ⟨109890967941133940837364067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146521290588178587783152089 109890967941133940837364067)
    ·
      refine ⟨164836451911700911256046101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109890967941133940837364067 164836451911700911256046101)
      ·
        refine ⟨7726708683360980215127161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164836451911700911256046101 7726708683360980215127161)
        ·
          refine ⟨5795031512520735161345371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7726708683360980215127161 5795031512520735161345371)
          ·
            refine ⟨8692547268781102742018057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795031512520735161345371 8692547268781102742018057)
            ·
              refine ⟨6519410451585827056513543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8692547268781102742018057 6519410451585827056513543)
              ·
                refine ⟨9779115677378740584770315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519410451585827056513543 9779115677378740584770315)
                ·
                  refine ⟨14668673516068110877155473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779115677378740584770315 14668673516068110877155473)
                  ·
                    refine ⟨11001505137051083157866605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14668673516068110877155473 11001505137051083157866605)
                    ·
                      refine ⟨4125564426394156184199977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001505137051083157866605 4125564426394156184199977)
                      ·
                        rfl

theorem cell23_8034508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8034508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034508 prefixEnd_8034508 := by exact prefixLift 8034508
  have htrace : WordTrace (prefixWord ++ tailWord_8034508) baseStart_8034508 baseEnd_8034508 := by
    simpa [prefixWord, tailWord_8034508, baseEnd_8034508] using wordTrace_append hprefix tailTrace_8034508
  have hstable : (prefixWord ++ tailWord_8034508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034508).length < 2 ^ (prefixWord ++ tailWord_8034508).sum := by decide
  have hdescent : baseEnd_8034508 < baseStart_8034508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034513 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_8034513 : Nat := 118140960795 + 8034513 * 2 ^ 59
def prefixEnd_8034513 : Nat := 4983230072969 + 3 ^ 40 * 8034513 * 2
def baseEnd_8034513 : Nat := 4125566993797428664637453

theorem tailTrace_8034513 : CollatzResearch.WordTrace tailWord_8034513 prefixEnd_8034513 4125566993797428664637453 := by
  unfold tailWord_8034513
  simp only [CollatzResearch.WordTrace]
  refine ⟨293042763541339061420236193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195361842360892707613490795 293042763541339061420236193)
  ·
    refine ⟨219782072656004296065177145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293042763541339061420236193 219782072656004296065177145)
    ·
      refine ⟨164836554492003222048882859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219782072656004296065177145 164836554492003222048882859)
      ·
        refine ⟨247254831738004833073324289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164836554492003222048882859 247254831738004833073324289)
        ·
          refine ⟨185441123803503624804993217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247254831738004833073324289 185441123803503624804993217)
          ·
            refine ⟨139080842852627718603744913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185441123803503624804993217 139080842852627718603744913)
            ·
              refine ⟨104310632139470788952808685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139080842852627718603744913 104310632139470788952808685)
              ·
                refine ⟨39116487052301545857303257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104310632139470788952808685 39116487052301545857303257)
                ·
                  refine ⟨29337365289226159392977443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39116487052301545857303257 29337365289226159392977443)
                  ·
                    refine ⟨44006047933839239089466165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29337365289226159392977443 44006047933839239089466165)
                    ·
                      refine ⟨4125566993797428664637453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44006047933839239089466165 4125566993797428664637453)
                      ·
                        rfl

theorem cell23_8034513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_8034513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034513 prefixEnd_8034513 := by exact prefixLift 8034513
  have htrace : WordTrace (prefixWord ++ tailWord_8034513) baseStart_8034513 baseEnd_8034513 := by
    simpa [prefixWord, tailWord_8034513, baseEnd_8034513] using wordTrace_append hprefix tailTrace_8034513
  have hstable : (prefixWord ++ tailWord_8034513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034513).length < 2 ^ (prefixWord ++ tailWord_8034513).sum := by decide
  have hdescent : baseEnd_8034513 < baseStart_8034513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034514 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_8034514 : Nat := 118140960795 + 8034514 * 2 ^ 59
def prefixEnd_8034514 : Nat := 4983230072969 + 3 ^ 40 * 8034514 * 2
def baseEnd_8034514 : Nat := 4125567507278083160724949

theorem tailTrace_8034514 : CollatzResearch.WordTrace tailWord_8034514 prefixEnd_8034514 4125567507278083160724949 := by
  unfold tailWord_8034514
  simp only [CollatzResearch.WordTrace]
  refine ⟨73260700003583859647755649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195361866676223625727348397 73260700003583859647755649)
  ·
    refine ⟨54945525002687894735816737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73260700003583859647755649 54945525002687894735816737)
    ·
      refine ⟨41209143752015921051862553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54945525002687894735816737 41209143752015921051862553)
      ·
        refine ⟨30906857814011940788896915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41209143752015921051862553 30906857814011940788896915)
        ·
          refine ⟨46360286721017911183345373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30906857814011940788896915 46360286721017911183345373)
          ·
            refine ⟨17385107520381716693754515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46360286721017911183345373 17385107520381716693754515)
            ·
              refine ⟨26077661280572575040631773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17385107520381716693754515 26077661280572575040631773)
              ·
                refine ⟨9779122980214715640236915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26077661280572575040631773 9779122980214715640236915)
                ·
                  refine ⟨14668684470322073460355373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779122980214715640236915 14668684470322073460355373)
                  ·
                    refine ⟨5500756676370777547633265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14668684470322073460355373 5500756676370777547633265)
                    ·
                      refine ⟨4125567507278083160724949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500756676370777547633265 4125567507278083160724949)
                      ·
                        rfl

theorem cell23_8034514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_8034514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034514 prefixEnd_8034514 := by exact prefixLift 8034514
  have htrace : WordTrace (prefixWord ++ tailWord_8034514) baseStart_8034514 baseEnd_8034514 := by
    simpa [prefixWord, tailWord_8034514, baseEnd_8034514] using wordTrace_append hprefix tailTrace_8034514
  have hstable : (prefixWord ++ tailWord_8034514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034514).length < 2 ^ (prefixWord ++ tailWord_8034514).sum := by decide
  have hdescent : baseEnd_8034514 < baseStart_8034514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034523 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_8034523 : Nat := 118140960795 + 8034523 * 2 ^ 59
def prefixEnd_8034523 : Nat := 4983230072969 + 3 ^ 40 * 8034523 * 2
def baseEnd_8034523 : Nat := 4125572128603973625512407

theorem tailTrace_8034523 : CollatzResearch.WordTrace tailWord_8034523 prefixEnd_8034523 4125572128603973625512407 := by
  unfold tailWord_8034523
  simp only [CollatzResearch.WordTrace]
  refine ⟨293043128271302833128100223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195362085514201888752066815 293043128271302833128100223)
  ·
    refine ⟨439564692406954249692150335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293043128271302833128100223 439564692406954249692150335)
    ·
      refine ⟨659347038610431374538225503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439564692406954249692150335 659347038610431374538225503)
      ·
        refine ⟨989020557915647061807338255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659347038610431374538225503 989020557915647061807338255)
        ·
          refine ⟨1483530836873470592711007383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989020557915647061807338255 1483530836873470592711007383)
          ·
            refine ⟨2225296255310205889066511075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483530836873470592711007383 2225296255310205889066511075)
            ·
              refine ⟨3337944382965308833599766613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225296255310205889066511075 3337944382965308833599766613)
              ·
                refine ⟨39116535737874712893747265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3337944382965308833599766613 39116535737874712893747265)
                ·
                  refine ⟨29337401803406034670310449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39116535737874712893747265 29337401803406034670310449)
                  ·
                    refine ⟨22003051352554526002732837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29337401803406034670310449 22003051352554526002732837)
                    ·
                      refine ⟨4125572128603973625512407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22003051352554526002732837 4125572128603973625512407)
                      ·
                        rfl

theorem cell23_8034523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_8034523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034523 prefixEnd_8034523 := by exact prefixLift 8034523
  have htrace : WordTrace (prefixWord ++ tailWord_8034523) baseStart_8034523 baseEnd_8034523 := by
    simpa [prefixWord, tailWord_8034523, baseEnd_8034523] using wordTrace_append hprefix tailTrace_8034523
  have hstable : (prefixWord ++ tailWord_8034523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034523).length < 2 ^ (prefixWord ++ tailWord_8034523).sum := by decide
  have hdescent : baseEnd_8034523 < baseStart_8034523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034550 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_8034550 : Nat := 118140960795 + 8034550 * 2 ^ 59
def prefixEnd_8034550 : Nat := 4983230072969 + 3 ^ 40 * 8034550 * 2
def baseEnd_8034550 : Nat := 458398443620182779986087

theorem tailTrace_8034550 : CollatzResearch.WordTrace tailWord_8034550 prefixEnd_8034550 458398443620182779986087 := by
  unfold tailWord_8034550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315257065137813546208319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195362742028136677826222069 18315257065137813546208319)
  ·
    refine ⟨27472885597706720319312479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18315257065137813546208319 27472885597706720319312479)
    ·
      refine ⟨41209328396560080478968719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27472885597706720319312479 41209328396560080478968719)
      ·
        refine ⟨61813992594840120718453079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41209328396560080478968719 61813992594840120718453079)
        ·
          refine ⟨92720988892260181077679619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61813992594840120718453079 92720988892260181077679619)
          ·
            refine ⟨139081483338390271616519429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92720988892260181077679619 139081483338390271616519429)
            ·
              refine ⟨26077778125948175928097393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139081483338390271616519429 26077778125948175928097393)
              ·
                refine ⟨19558333594461131946073045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26077778125948175928097393 19558333594461131946073045)
                ·
                  refine ⟨458398443620182779986087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19558333594461131946073045 458398443620182779986087)
                  ·
                    rfl

theorem cell23_8034550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_8034550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034550 prefixEnd_8034550 := by exact prefixLift 8034550
  have htrace : WordTrace (prefixWord ++ tailWord_8034550) baseStart_8034550 baseEnd_8034550 := by
    simpa [prefixWord, tailWord_8034550, baseEnd_8034550] using wordTrace_append hprefix tailTrace_8034550
  have hstable : (prefixWord ++ tailWord_8034550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034550).length < 2 ^ (prefixWord ++ tailWord_8034550).sum := by decide
  have hdescent : baseEnd_8034550 < baseStart_8034550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034563 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 7]
def baseStart_8034563 : Nat := 118140960795 + 8034563 * 2 ^ 59
def prefixEnd_8034563 : Nat := 4983230072969 + 3 ^ 40 * 8034563 * 2
def baseEnd_8034563 : Nat := 1375197555943384489670741

theorem tailTrace_8034563 : CollatzResearch.WordTrace tailWord_8034563 prefixEnd_8034563 1375197555943384489670741 := by
  unfold tailWord_8034563
  simp only [CollatzResearch.WordTrace]
  refine ⟨293044587191157919959556343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195363058127438613306370895 293044587191157919959556343)
  ·
    refine ⟨439566880786736879939334515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293044587191157919959556343 439566880786736879939334515)
    ·
      refine ⟨659350321180105319909001773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439566880786736879939334515 659350321180105319909001773)
      ·
        refine ⟨247256370442539494965875665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659350321180105319909001773 247256370442539494965875665)
        ·
          refine ⟨185442277831904621224406749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247256370442539494965875665 185442277831904621224406749)
          ·
            refine ⟨69540854186964232959152531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185442277831904621224406749 69540854186964232959152531)
            ·
              refine ⟨104311281280446349438728797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69540854186964232959152531 104311281280446349438728797)
              ·
                refine ⟨39116730480167381039523299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104311281280446349438728797 39116730480167381039523299)
                ·
                  refine ⟨58675095720251071559284949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39116730480167381039523299 58675095720251071559284949)
                  ·
                    refine ⟨1375197555943384489670741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58675095720251071559284949 1375197555943384489670741)
                    ·
                      rfl

theorem cell23_8034563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_8034563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034563 prefixEnd_8034563 := by exact prefixLift 8034563
  have htrace : WordTrace (prefixWord ++ tailWord_8034563) baseStart_8034563 baseEnd_8034563 := by
    simpa [prefixWord, tailWord_8034563, baseEnd_8034563] using wordTrace_append hprefix tailTrace_8034563
  have hstable : (prefixWord ++ tailWord_8034563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034563).length < 2 ^ (prefixWord ++ tailWord_8034563).sum := by decide
  have hdescent : baseEnd_8034563 < baseStart_8034563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034617 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8034617 : Nat := 118140960795 + 8034617 * 2 ^ 59
def prefixEnd_8034617 : Nat := 4983230072969 + 3 ^ 40 * 8034617 * 2
def baseEnd_8034617 : Nat := 4125620395785496257736975

theorem tailTrace_8034617 : CollatzResearch.WordTrace tailWord_8034617 prefixEnd_8034617 4125620395785496257736975 := by
  unfold tailWord_8034617
  simp only [CollatzResearch.WordTrace]
  refine ⟨293046556732962287182022105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195364371155308191454681403 293046556732962287182022105)
  ·
    refine ⟨219784917549721715386516579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293046556732962287182022105 219784917549721715386516579)
    ·
      refine ⟨329677376324582573079774869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219784917549721715386516579 329677376324582573079774869)
      ·
        refine ⟨15453627015214808113114447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 329677376324582573079774869 15453627015214808113114447)
        ·
          refine ⟨23180440522822212169671671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15453627015214808113114447 23180440522822212169671671)
          ·
            refine ⟨34770660784233318254507507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23180440522822212169671671 34770660784233318254507507)
            ·
              refine ⟨52155991176349977381761261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34770660784233318254507507 52155991176349977381761261)
              ·
                refine ⟨19558496691131241518160473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52155991176349977381761261 19558496691131241518160473)
                ·
                  refine ⟨14668872518348431138620355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19558496691131241518160473 14668872518348431138620355)
                  ·
                    refine ⟨22003308777522646707930533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14668872518348431138620355 22003308777522646707930533)
                    ·
                      refine ⟨4125620395785496257736975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22003308777522646707930533 4125620395785496257736975)
                      ·
                        rfl

theorem cell23_8034617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8034617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034617 prefixEnd_8034617 := by exact prefixLift 8034617
  have htrace : WordTrace (prefixWord ++ tailWord_8034617) baseStart_8034617 baseEnd_8034617 := by
    simpa [prefixWord, tailWord_8034617, baseEnd_8034617] using wordTrace_append hprefix tailTrace_8034617
  have hstable : (prefixWord ++ tailWord_8034617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034617).length < 2 ^ (prefixWord ++ tailWord_8034617).sum := by decide
  have hdescent : baseEnd_8034617 < baseStart_8034617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034640 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 6]
def baseStart_8034640 : Nat := 118140960795 + 8034640 * 2 ^ 59
def prefixEnd_8034640 : Nat := 4983230072969 + 3 ^ 40 * 8034640 * 2
def baseEnd_8034640 : Nat := 458403578426727740861041

theorem tailTrace_8034640 : CollatzResearch.WordTrace tailWord_8034640 prefixEnd_8034640 458403578426727740861041 := by
  unfold tailWord_8034640
  simp only [CollatzResearch.WordTrace]
  refine ⟨146523697805939481055054687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195364930407919308073406249 146523697805939481055054687)
  ·
    refine ⟨219785546708909221582582031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146523697805939481055054687 219785546708909221582582031)
    ·
      refine ⟨329678320063363832373873047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219785546708909221582582031 329678320063363832373873047)
      ·
        refine ⟨494517480095045748560809571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329678320063363832373873047 494517480095045748560809571)
        ·
          refine ⟨741776220142568622841214357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494517480095045748560809571 741776220142568622841214357)
          ·
            refine ⟨34770760319182904195681923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 741776220142568622841214357 34770760319182904195681923)
            ·
              refine ⟨52156140478774356293522885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34770760319182904195681923 52156140478774356293522885)
              ·
                refine ⟨9779276339770191805035541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52156140478774356293522885 9779276339770191805035541)
                ·
                  refine ⟨458403578426727740861041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9779276339770191805035541 458403578426727740861041)
                  ·
                    rfl

theorem cell23_8034640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_8034640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034640 prefixEnd_8034640 := by exact prefixLift 8034640
  have htrace : WordTrace (prefixWord ++ tailWord_8034640) baseStart_8034640 baseEnd_8034640 := by
    simpa [prefixWord, tailWord_8034640, baseEnd_8034640] using wordTrace_append hprefix tailTrace_8034640
  have hstable : (prefixWord ++ tailWord_8034640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034640).length < 2 ^ (prefixWord ++ tailWord_8034640).sum := by decide
  have hdescent : baseEnd_8034640 < baseStart_8034640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034650 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_8034650 : Nat := 118140960795 + 8034650 * 2 ^ 59
def prefixEnd_8034650 : Nat := 4983230072969 + 3 ^ 40 * 8034650 * 2
def baseEnd_8034650 : Nat := 4125637340647094628624323

theorem tailTrace_8034650 : CollatzResearch.WordTrace tailWord_8034650 prefixEnd_8034650 4125637340647094628624323 := by
  unfold tailWord_8034650
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261940085460683454493351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195365173561228489211982269 73261940085460683454493351)
  ·
    refine ⟨109892910128191025181740027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73261940085460683454493351 109892910128191025181740027)
    ·
      refine ⟨164839365192286537772610041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109892910128191025181740027 164839365192286537772610041)
      ·
        refine ⟨123629523894214903329457531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164839365192286537772610041 123629523894214903329457531)
        ·
          refine ⟨185444285841322354994186297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123629523894214903329457531 185444285841322354994186297)
          ·
            refine ⟨139083214380991766245639723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185444285841322354994186297 139083214380991766245639723)
            ·
              refine ⟨208624821571487649368459585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139083214380991766245639723 208624821571487649368459585)
              ·
                refine ⟨156468616178615737026344689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208624821571487649368459585 156468616178615737026344689)
                ·
                  refine ⟨117351462133961802769758517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156468616178615737026344689 117351462133961802769758517)
                  ·
                    refine ⟨11001699575058919009664861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117351462133961802769758517 11001699575058919009664861)
                    ·
                      refine ⟨4125637340647094628624323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001699575058919009664861 4125637340647094628624323)
                      ·
                        rfl

theorem cell23_8034650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_8034650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034650 prefixEnd_8034650 := by exact prefixLift 8034650
  have htrace : WordTrace (prefixWord ++ tailWord_8034650) baseStart_8034650 baseEnd_8034650 := by
    simpa [prefixWord, tailWord_8034650, baseEnd_8034650] using wordTrace_append hprefix tailTrace_8034650
  have hstable : (prefixWord ++ tailWord_8034650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034650).length < 2 ^ (prefixWord ++ tailWord_8034650).sum := by decide
  have hdescent : baseEnd_8034650 < baseStart_8034650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034667 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 3]
def baseStart_8034667 : Nat := 118140960795 + 8034667 * 2 ^ 59
def prefixEnd_8034667 : Nat := 4983230072969 + 3 ^ 40 * 8034667 * 2
def baseEnd_8034667 : Nat := 4125646069818221062111745

theorem tailTrace_8034667 : CollatzResearch.WordTrace tailWord_8034667 prefixEnd_8034667 4125646069818221062111745 := by
  unfold tailWord_8034667
  simp only [CollatzResearch.WordTrace]
  refine ⟨293048380382781145721342255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195365586921854097147561503 293048380382781145721342255)
  ·
    refine ⟨439572570574171718582013383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293048380382781145721342255 439572570574171718582013383)
    ·
      refine ⟨659358855861257577873020075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439572570574171718582013383 659358855861257577873020075)
      ·
        refine ⟨989038283791886366809530113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659358855861257577873020075 989038283791886366809530113)
        ·
          refine ⟨741778712843914775107147585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989038283791886366809530113 741778712843914775107147585)
          ·
            refine ⟨556334034632936081330360689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741778712843914775107147585 556334034632936081330360689)
            ·
              refine ⟨417250525974702060997770517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556334034632936081330360689 417250525974702060997770517)
              ·
                refine ⟨19558618405064159109270493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 417250525974702060997770517 19558618405064159109270493)
                ·
                  refine ⟨7334481901899059665976435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19558618405064159109270493 7334481901899059665976435)
                  ·
                    refine ⟨11001722852848589498964653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7334481901899059665976435 11001722852848589498964653)
                    ·
                      refine ⟨4125646069818221062111745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001722852848589498964653 4125646069818221062111745)
                      ·
                        rfl

theorem cell23_8034667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 3].length) (baseStart_8034667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034667 prefixEnd_8034667 := by exact prefixLift 8034667
  have htrace : WordTrace (prefixWord ++ tailWord_8034667) baseStart_8034667 baseEnd_8034667 := by
    simpa [prefixWord, tailWord_8034667, baseEnd_8034667] using wordTrace_append hprefix tailTrace_8034667
  have hstable : (prefixWord ++ tailWord_8034667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034667).length < 2 ^ (prefixWord ++ tailWord_8034667).sum := by decide
  have hdescent : baseEnd_8034667 < baseStart_8034667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034721 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_8034721 : Nat := 118140960795 + 8034721 * 2 ^ 59
def prefixEnd_8034721 : Nat := 4983230072969 + 3 ^ 40 * 8034721 * 2
def baseEnd_8034721 : Nat := 1375224599257854616945499

theorem tailTrace_8034721 : CollatzResearch.WordTrace tailWord_8034721 prefixEnd_8034721 1375224599257854616945499 := by
  unfold tailWord_8034721
  simp only [CollatzResearch.WordTrace]
  refine ⟨293050349924585512943808017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195366899949723675295872011 293050349924585512943808017)
  ·
    refine ⟨219787762443439134707856013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293050349924585512943808017 219787762443439134707856013)
    ·
      refine ⟨82420410916289675515446005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219787762443439134707856013 82420410916289675515446005)
      ·
        refine ⟨7726913523402157079573063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82420410916289675515446005 7726913523402157079573063)
        ·
          refine ⟨11590370285103235619359595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726913523402157079573063 11590370285103235619359595)
          ·
            refine ⟨17385555427654853429039393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11590370285103235619359595 17385555427654853429039393)
            ·
              refine ⟨13039166570741140071779545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17385555427654853429039393 13039166570741140071779545)
              ·
                refine ⟨9779374928055855053834659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13039166570741140071779545 9779374928055855053834659)
                ·
                  refine ⟨14669062392083782580751989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779374928055855053834659 14669062392083782580751989)
                  ·
                    refine ⟨1375224599257854616945499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14669062392083782580751989 1375224599257854616945499)
                    ·
                      rfl

theorem cell23_8034721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_8034721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034721 prefixEnd_8034721 := by exact prefixLift 8034721
  have htrace : WordTrace (prefixWord ++ tailWord_8034721) baseStart_8034721 baseEnd_8034721 := by
    simpa [prefixWord, tailWord_8034721, baseEnd_8034721] using wordTrace_append hprefix tailTrace_8034721
  have hstable : (prefixWord ++ tailWord_8034721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034721).length < 2 ^ (prefixWord ++ tailWord_8034721).sum := by decide
  have hdescent : baseEnd_8034721 < baseStart_8034721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034767 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 7, 2]
def baseStart_8034767 : Nat := 118140960795 + 8034767 * 2 ^ 59
def prefixEnd_8034767 : Nat := 4983230072969 + 3 ^ 40 * 8034767 * 2
def baseEnd_8034767 : Nat := 4125697417883670670861285

theorem tailTrace_8034767 : CollatzResearch.WordTrace tailWord_8034767 prefixEnd_8034767 4125697417883670670861285 := by
  unfold tailWord_8034767
  simp only [CollatzResearch.WordTrace]
  refine ⟨293052027682418862799982555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195368018454945908533321703 293052027682418862799982555)
  ·
    refine ⟨439578041523628294199973833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293052027682418862799982555 439578041523628294199973833)
    ·
      refine ⟨329683531142721220649980375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439578041523628294199973833 329683531142721220649980375)
      ·
        refine ⟨494525296714081830974970563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329683531142721220649980375 494525296714081830974970563)
        ·
          refine ⟨741787945071122746462455845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494525296714081830974970563 741787945071122746462455845)
          ·
            refine ⟨139085239700835514961710471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741787945071122746462455845 139085239700835514961710471)
            ·
              refine ⟨208627859551253272442565707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139085239700835514961710471 208627859551253272442565707)
              ·
                refine ⟨312941789326879908663848561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208627859551253272442565707 312941789326879908663848561)
                ·
                  refine ⟨234706341995159931497886421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312941789326879908663848561 234706341995159931497886421)
                  ·
                    refine ⟨5500929890511560894481713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234706341995159931497886421 5500929890511560894481713)
                    ·
                      refine ⟨4125697417883670670861285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500929890511560894481713 4125697417883670670861285)
                      ·
                        rfl

theorem cell23_8034767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7, 2].length) (baseStart_8034767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034767 prefixEnd_8034767 := by exact prefixLift 8034767
  have htrace : WordTrace (prefixWord ++ tailWord_8034767) baseStart_8034767 baseEnd_8034767 := by
    simpa [prefixWord, tailWord_8034767, baseEnd_8034767] using wordTrace_append hprefix tailTrace_8034767
  have hstable : (prefixWord ++ tailWord_8034767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034767).length < 2 ^ (prefixWord ++ tailWord_8034767).sum := by decide
  have hdescent : baseEnd_8034767 < baseStart_8034767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034784 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2]
def baseStart_8034784 : Nat := 118140960795 + 8034784 * 2 ^ 59
def prefixEnd_8034784 : Nat := 4983230072969 + 3 ^ 40 * 8034784 * 2
def baseEnd_8034784 : Nat := 4125706147054797104348707

theorem tailTrace_8034784 : CollatzResearch.WordTrace tailWord_8034784 prefixEnd_8034784 4125706147054797104348707 := by
  unfold tailWord_8034784
  simp only [CollatzResearch.WordTrace]
  refine ⟨146526323861678637351675703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195368431815571516468900937 146526323861678637351675703)
  ·
    refine ⟨219789485792517956027513555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146526323861678637351675703 219789485792517956027513555)
    ·
      refine ⟨329684228688776934041270333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219789485792517956027513555 329684228688776934041270333)
      ·
        refine ⟨123631585758291350265476375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329684228688776934041270333 123631585758291350265476375)
        ·
          refine ⟨185447378637437025398214563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123631585758291350265476375 185447378637437025398214563)
          ·
            refine ⟨278171067956155538097321845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185447378637437025398214563 278171067956155538097321845)
            ·
              refine ⟨26078537620889581696623923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278171067956155538097321845 26078537620889581696623923)
              ·
                refine ⟨39117806431334372544935885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26078537620889581696623923 39117806431334372544935885)
                ·
                  refine ⟨14669177411750389704350957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39117806431334372544935885 14669177411750389704350957)
                  ·
                    refine ⟨5500941529406396139131609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14669177411750389704350957 5500941529406396139131609)
                    ·
                      refine ⟨4125706147054797104348707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500941529406396139131609 4125706147054797104348707)
                      ·
                        rfl

theorem cell23_8034784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_8034784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034784 prefixEnd_8034784 := by exact prefixLift 8034784
  have htrace : WordTrace (prefixWord ++ tailWord_8034784) baseStart_8034784 baseEnd_8034784 := by
    simpa [prefixWord, tailWord_8034784, baseEnd_8034784] using wordTrace_append hprefix tailTrace_8034784
  have hstable : (prefixWord ++ tailWord_8034784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034784).length < 2 ^ (prefixWord ++ tailWord_8034784).sum := by decide
  have hdescent : baseEnd_8034784 < baseStart_8034784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034827 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_8034827 : Nat := 118140960795 + 8034827 * 2 ^ 59
def prefixEnd_8034827 : Nat := 4983230072969 + 3 ^ 40 * 8034827 * 2
def baseEnd_8034827 : Nat := 4125728226722940436111009

theorem tailTrace_8034827 : CollatzResearch.WordTrace tailWord_8034827 prefixEnd_8034827 4125728226722940436111009 := by
  unfold tailWord_8034827
  simp only [CollatzResearch.WordTrace]
  refine ⟨293054216062201493047166735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195369477374800995364777823 293054216062201493047166735)
  ·
    refine ⟨439581324093302239570750103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293054216062201493047166735 439581324093302239570750103)
    ·
      refine ⟨659371986139953359356125155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439581324093302239570750103 659371986139953359356125155)
      ·
        refine ⟨989057979209930039034187733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659371986139953359356125155 989057979209930039034187733)
        ·
          refine ⟨23181046387732735289863775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 989057979209930039034187733 23181046387732735289863775)
          ·
            refine ⟨34771569581599102934795663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23181046387732735289863775 34771569581599102934795663)
            ·
              refine ⟨52157354372398654402193495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34771569581599102934795663 52157354372398654402193495)
              ·
                refine ⟨78236031558597981603290243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52157354372398654402193495 78236031558597981603290243)
                ·
                  refine ⟨117354047337896972404935365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78236031558597981603290243 117354047337896972404935365)
                  ·
                    refine ⟨22003883875855682325925381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117354047337896972404935365 22003883875855682325925381)
                    ·
                      refine ⟨4125728226722940436111009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22003883875855682325925381 4125728226722940436111009)
                      ·
                        rfl

theorem cell23_8034827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_8034827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034827 prefixEnd_8034827 := by exact prefixLift 8034827
  have htrace : WordTrace (prefixWord ++ tailWord_8034827) baseStart_8034827 baseEnd_8034827 := by
    simpa [prefixWord, tailWord_8034827, baseEnd_8034827] using wordTrace_append hprefix tailTrace_8034827
  have hstable : (prefixWord ++ tailWord_8034827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034827).length < 2 ^ (prefixWord ++ tailWord_8034827).sum := by decide
  have hdescent : baseEnd_8034827 < baseStart_8034827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034837 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 7]
def baseStart_8034837 : Nat := 118140960795 + 8034837 * 2 ^ 59
def prefixEnd_8034837 : Nat := 4983230072969 + 3 ^ 40 * 8034837 * 2
def baseEnd_8034837 : Nat := 458414817947720599665107

theorem tailTrace_8034837 : CollatzResearch.WordTrace tailWord_8034837 prefixEnd_8034837 458414817947720599665107 := by
  unfold tailWord_8034837
  simp only [CollatzResearch.WordTrace]
  refine ⟨293054580792165264755030765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195369720528110176503353843 293054580792165264755030765)
  ·
    refine ⟨109895467797061974283136537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293054580792165264755030765 109895467797061974283136537)
    ·
      refine ⟨82421600847796480712352403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109895467797061974283136537 82421600847796480712352403)
      ·
        refine ⟨123632401271694721068528605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82421600847796480712352403 123632401271694721068528605)
        ·
          refine ⟨46362150476885520400698227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123632401271694721068528605 46362150476885520400698227)
          ·
            refine ⟨69543225715328280601047341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46362150476885520400698227 69543225715328280601047341)
            ·
              refine ⟨26078709643248105225392753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69543225715328280601047341 26078709643248105225392753)
              ·
                refine ⟨19559032232436078919044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26078709643248105225392753 19559032232436078919044565)
                ·
                  refine ⟨458414817947720599665107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19559032232436078919044565 458414817947720599665107)
                  ·
                    rfl

theorem cell23_8034837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_8034837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034837 prefixEnd_8034837 := by exact prefixLift 8034837
  have htrace : WordTrace (prefixWord ++ tailWord_8034837) baseStart_8034837 baseEnd_8034837 := by
    simpa [prefixWord, tailWord_8034837, baseEnd_8034837] using wordTrace_append hprefix tailTrace_8034837
  have hstable : (prefixWord ++ tailWord_8034837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034837).length < 2 ^ (prefixWord ++ tailWord_8034837).sum := by decide
  have hdescent : baseEnd_8034837 < baseStart_8034837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034847 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_8034847 : Nat := 118140960795 + 8034847 * 2 ^ 59
def prefixEnd_8034847 : Nat := 4983230072969 + 3 ^ 40 * 8034847 * 2
def baseEnd_8034847 : Nat := 4125738496336030357860917

theorem tailTrace_8034847 : CollatzResearch.WordTrace tailWord_8034847 prefixEnd_8034847 4125738496336030357860917 := by
  unfold tailWord_8034847
  simp only [CollatzResearch.WordTrace]
  refine ⟨293054945522129036462894795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195369963681419357641929863 293054945522129036462894795)
  ·
    refine ⟨439582418283193554694342193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293054945522129036462894795 439582418283193554694342193)
    ·
      refine ⟨329686813712395166020756645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439582418283193554694342193 329686813712395166020756645)
      ·
        refine ⟨61816277571074093628891871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329686813712395166020756645 61816277571074093628891871)
        ·
          refine ⟨92724416356611140443337807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61816277571074093628891871 92724416356611140443337807)
          ·
            refine ⟨139086624534916710665006711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92724416356611140443337807 139086624534916710665006711)
            ·
              refine ⟨208629936802375065997510067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139086624534916710665006711 208629936802375065997510067)
              ·
                refine ⟨312944905203562598996265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208629936802375065997510067 312944905203562598996265101)
                ·
                  refine ⟨117354339451335974623599413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312944905203562598996265101 117354339451335974623599413)
                  ·
                    refine ⟨11001969323562747620962445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117354339451335974623599413 11001969323562747620962445)
                    ·
                      refine ⟨4125738496336030357860917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11001969323562747620962445 4125738496336030357860917)
                      ·
                        rfl

theorem cell23_8034847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_8034847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034847 prefixEnd_8034847 := by exact prefixLift 8034847
  have htrace : WordTrace (prefixWord ++ tailWord_8034847) baseStart_8034847 baseEnd_8034847 := by
    simpa [prefixWord, tailWord_8034847, baseEnd_8034847] using wordTrace_append hprefix tailTrace_8034847
  have hstable : (prefixWord ++ tailWord_8034847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034847).length < 2 ^ (prefixWord ++ tailWord_8034847).sum := by decide
  have hdescent : baseEnd_8034847 < baseStart_8034847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034852 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_8034852 : Nat := 118140960795 + 8034852 * 2 ^ 59
def prefixEnd_8034852 : Nat := 4983230072969 + 3 ^ 40 * 8034852 * 2
def baseEnd_8034852 : Nat := 4125741063739302838298395

theorem tailTrace_8034852 : CollatzResearch.WordTrace tailWord_8034852 prefixEnd_8034852 4125741063739302838298395 := by
  unfold tailWord_8034852
  simp only [CollatzResearch.WordTrace]
  refine ⟨146527563943555461158413405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195370085258073948211217873 146527563943555461158413405)
  ·
    refine ⟨54947836478833297934405027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146527563943555461158413405 54947836478833297934405027)
    ·
      refine ⟨82421754718249946901607541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54947836478833297934405027 82421754718249946901607541)
      ·
        refine ⟨7727039504835932522025707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82421754718249946901607541 7727039504835932522025707)
        ·
          refine ⟨11590559257253898783038561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727039504835932522025707 11590559257253898783038561)
          ·
            refine ⟨8692919442940424087278921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590559257253898783038561 8692919442940424087278921)
            ·
              refine ⟨6519689582205318065459191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8692919442940424087278921 6519689582205318065459191)
              ·
                refine ⟨9779534373307977098188787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519689582205318065459191 9779534373307977098188787)
                ·
                  refine ⟨14669301559961965647283181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779534373307977098188787 14669301559961965647283181)
                  ·
                    refine ⟨5500988084985737117731193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14669301559961965647283181 5500988084985737117731193)
                    ·
                      refine ⟨4125741063739302838298395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5500988084985737117731193 4125741063739302838298395)
                      ·
                        rfl

theorem cell23_8034852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_8034852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034852 prefixEnd_8034852 := by exact prefixLift 8034852
  have htrace : WordTrace (prefixWord ++ tailWord_8034852) baseStart_8034852 baseEnd_8034852 := by
    simpa [prefixWord, tailWord_8034852, baseEnd_8034852] using wordTrace_append hprefix tailTrace_8034852
  have hstable : (prefixWord ++ tailWord_8034852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034852).length < 2 ^ (prefixWord ++ tailWord_8034852).sum := by decide
  have hdescent : baseEnd_8034852 < baseStart_8034852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034867 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 4, 5]
def baseStart_8034867 : Nat := 118140960795 + 8034867 * 2 ^ 59
def prefixEnd_8034867 : Nat := 4983230072969 + 3 ^ 40 * 8034867 * 2
def baseEnd_8034867 : Nat := 1375249588649706759870275

theorem tailTrace_8034867 : CollatzResearch.WordTrace tailWord_8034867 prefixEnd_8034867 1375249588649706759870275 := by
  unfold tailWord_8034867
  simp only [CollatzResearch.WordTrace]
  refine ⟨293055674982056579878622855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195370449988037719919081903 293055674982056579878622855)
  ·
    refine ⟨439583512473084869817934283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293055674982056579878622855 439583512473084869817934283)
    ·
      refine ⟨659375268709627304726901425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439583512473084869817934283 659375268709627304726901425)
      ·
        refine ⟨494531451532220478545176069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659375268709627304726901425 494531451532220478545176069)
        ·
          refine ⟨92724647162291339727220513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494531451532220478545176069 92724647162291339727220513)
          ·
            refine ⟨69543485371718504795415385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92724647162291339727220513 69543485371718504795415385)
            ·
              refine ⟨52157614028788878596561539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69543485371718504795415385 52157614028788878596561539)
              ·
                refine ⟨78236421043183317894842309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52157614028788878596561539 78236421043183317894842309)
                ·
                  refine ⟨14669328945596872105282933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78236421043183317894842309 14669328945596872105282933)
                  ·
                    refine ⟨1375249588649706759870275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14669328945596872105282933 1375249588649706759870275)
                    ·
                      rfl

theorem cell23_8034867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].length) (baseStart_8034867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034867 prefixEnd_8034867 := by exact prefixLift 8034867
  have htrace : WordTrace (prefixWord ++ tailWord_8034867) baseStart_8034867 baseEnd_8034867 := by
    simpa [prefixWord, tailWord_8034867, baseEnd_8034867] using wordTrace_append hprefix tailTrace_8034867
  have hstable : (prefixWord ++ tailWord_8034867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034867).length < 2 ^ (prefixWord ++ tailWord_8034867).sum := by decide
  have hdescent : baseEnd_8034867 < baseStart_8034867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034904 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_8034904 : Nat := 118140960795 + 8034904 * 2 ^ 59
def prefixEnd_8034904 : Nat := 4983230072969 + 3 ^ 40 * 8034904 * 2
def baseEnd_8034904 : Nat := 4125767764733336634848155

theorem tailTrace_8034904 : CollatzResearch.WordTrace tailWord_8034904 prefixEnd_8034904 4125767764733336634848155 := by
  unfold tailWord_8034904
  simp only [CollatzResearch.WordTrace]
  refine ⟨146528512241461267598859883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195371349655281690131813177 146528512241461267598859883)
  ·
    refine ⟨219792768362191901398289825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146528512241461267598859883 219792768362191901398289825)
    ·
      refine ⟨164844576271643926048717369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219792768362191901398289825 164844576271643926048717369)
      ·
        refine ⟨123633432203732944536538027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164844576271643926048717369 123633432203732944536538027)
        ·
          refine ⟨185450148305599416804807041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123633432203732944536538027 185450148305599416804807041)
          ·
            refine ⟨139087611229199562603605281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185450148305599416804807041 139087611229199562603605281)
            ·
              refine ⟨104315708421899671952703961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139087611229199562603605281 104315708421899671952703961)
              ·
                refine ⟨78236781316424753964527971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104315708421899671952703961 78236781316424753964527971)
                ·
                  refine ⟨117355171974637130946791957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78236781316424753964527971 117355171974637130946791957)
                  ·
                    refine ⟨5501023686311115513130873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117355171974637130946791957 5501023686311115513130873)
                    ·
                      refine ⟨4125767764733336634848155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501023686311115513130873 4125767764733336634848155)
                      ·
                        rfl

theorem cell23_8034904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_8034904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034904 prefixEnd_8034904 := by exact prefixLift 8034904
  have htrace : WordTrace (prefixWord ++ tailWord_8034904) baseStart_8034904 baseEnd_8034904 := by
    simpa [prefixWord, tailWord_8034904, baseEnd_8034904] using wordTrace_append hprefix tailTrace_8034904
  have hstable : (prefixWord ++ tailWord_8034904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034904).length < 2 ^ (prefixWord ++ tailWord_8034904).sum := by decide
  have hdescent : baseEnd_8034904 < baseStart_8034904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034924 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_8034924 : Nat := 118140960795 + 8034924 * 2 ^ 59
def prefixEnd_8034924 : Nat := 4983230072969 + 3 ^ 40 * 8034924 * 2
def baseEnd_8034924 : Nat := 4125778034346426556598063

theorem tailTrace_8034924 : CollatzResearch.WordTrace tailWord_8034924 prefixEnd_8034924 4125778034346426556598063 := by
  unfold tailWord_8034924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146528876971425039306723913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195371835961900052408965217 146528876971425039306723913)
  ·
    refine ⟨109896657728568779480042935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146528876971425039306723913 109896657728568779480042935)
    ·
      refine ⟨164844986592853169220064403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109896657728568779480042935 164844986592853169220064403)
      ·
        refine ⟨247267479889279753830096605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164844986592853169220064403 247267479889279753830096605)
        ·
          refine ⟨92725304958479907686286227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247267479889279753830096605 92725304958479907686286227)
          ·
            refine ⟨139087957437719861529429341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92725304958479907686286227 139087957437719861529429341)
            ·
              refine ⟨52157984039144948073536003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139087957437719861529429341 52157984039144948073536003)
              ·
                refine ⟨78236976058717422110304005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52157984039144948073536003 78236976058717422110304005)
                ·
                  refine ⟨14669433011009516645682001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78236976058717422110304005 14669433011009516645682001)
                  ·
                    refine ⟨11002074758257137484261501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14669433011009516645682001 11002074758257137484261501)
                    ·
                      refine ⟨4125778034346426556598063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002074758257137484261501 4125778034346426556598063)
                      ·
                        rfl

theorem cell23_8034924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_8034924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034924 prefixEnd_8034924 := by exact prefixLift 8034924
  have htrace : WordTrace (prefixWord ++ tailWord_8034924) baseStart_8034924 baseEnd_8034924 := by
    simpa [prefixWord, tailWord_8034924, baseEnd_8034924] using wordTrace_append hprefix tailTrace_8034924
  have hstable : (prefixWord ++ tailWord_8034924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034924).length < 2 ^ (prefixWord ++ tailWord_8034924).sum := by decide
  have hdescent : baseEnd_8034924 < baseStart_8034924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034927 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 8]
def baseStart_8034927 : Nat := 118140960795 + 8034927 * 2 ^ 59
def prefixEnd_8034927 : Nat := 4983230072969 + 3 ^ 40 * 8034927 * 2
def baseEnd_8034927 : Nat := 458419952754265560540061

theorem tailTrace_8034927 : CollatzResearch.WordTrace tailWord_8034927 prefixEnd_8034927 458419952754265560540061 := by
  unfold tailWord_8034927
  simp only [CollatzResearch.WordTrace]
  refine ⟨293057863361839210125807035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195371908907892806750538023 293057863361839210125807035)
  ·
    refine ⟨439586795042758815188710553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293057863361839210125807035 439586795042758815188710553)
    ·
      refine ⟨329690096282069111391532915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439586795042758815188710553 329690096282069111391532915)
      ·
        refine ⟨494535144423103667087299373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329690096282069111391532915 494535144423103667087299373)
        ·
          refine ⟨185450679158663875157737265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494535144423103667087299373 185450679158663875157737265)
          ·
            refine ⟨139088009368997906368302949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185450679158663875157737265 139088009368997906368302949)
            ·
              refine ⟨26079001756687107444056803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139088009368997906368302949 26079001756687107444056803)
              ·
                refine ⟨39118502635030661166085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26079001756687107444056803 39118502635030661166085205)
                ·
                  refine ⟨458419952754265560540061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39118502635030661166085205 458419952754265560540061)
                  ·
                    rfl

theorem cell23_8034927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 8].length) (baseStart_8034927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034927 prefixEnd_8034927 := by exact prefixLift 8034927
  have htrace : WordTrace (prefixWord ++ tailWord_8034927) baseStart_8034927 baseEnd_8034927 := by
    simpa [prefixWord, tailWord_8034927, baseEnd_8034927] using wordTrace_append hprefix tailTrace_8034927
  have hstable : (prefixWord ++ tailWord_8034927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034927).length < 2 ^ (prefixWord ++ tailWord_8034927).sum := by decide
  have hdescent : baseEnd_8034927 < baseStart_8034927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034944 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 6]
def baseStart_8034944 : Nat := 118140960795 + 8034944 * 2 ^ 59
def prefixEnd_8034944 : Nat := 4983230072969 + 3 ^ 40 * 8034944 * 2
def baseEnd_8034944 : Nat := 458420922662168497594219

theorem tailTrace_8034944 : CollatzResearch.WordTrace tailWord_8034944 prefixEnd_8034944 458420922662168497594219 := by
  unfold tailWord_8034944
  simp only [CollatzResearch.WordTrace]
  refine ⟨146529241701388811014587943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195372322268518414686117257 146529241701388811014587943)
  ·
    refine ⟨219793862552083216521881915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146529241701388811014587943 219793862552083216521881915)
    ·
      refine ⟨329690793828124824782822873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219793862552083216521881915 329690793828124824782822873)
      ·
        refine ⟨247268095371093618587117155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329690793828124824782822873 247268095371093618587117155)
        ·
          refine ⟨370902143056640427880675733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247268095371093618587117155 370902143056640427880675733)
          ·
            refine ⟨17386037955780020056906675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 370902143056640427880675733 17386037955780020056906675)
            ·
              refine ⟨26079056933670030085360013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386037955780020056906675 26079056933670030085360013)
              ·
                refine ⟨9779646350126261282010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26079056933670030085360013 9779646350126261282010005)
                ·
                  refine ⟨458420922662168497594219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9779646350126261282010005 458420922662168497594219)
                  ·
                    rfl

theorem cell23_8034944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_8034944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034944 prefixEnd_8034944 := by exact prefixLift 8034944
  have htrace : WordTrace (prefixWord ++ tailWord_8034944) baseStart_8034944 baseEnd_8034944 := by
    simpa [prefixWord, tailWord_8034944, baseEnd_8034944] using wordTrace_append hprefix tailTrace_8034944
  have hstable : (prefixWord ++ tailWord_8034944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034944).length < 2 ^ (prefixWord ++ tailWord_8034944).sum := by decide
  have hdescent : baseEnd_8034944 < baseStart_8034944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8034947 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_8034947 : Nat := 118140960795 + 8034947 * 2 ^ 59
def prefixEnd_8034947 : Nat := 4983230072969 + 3 ^ 40 * 8034947 * 2
def baseEnd_8034947 : Nat := 4125789844401479966610457

theorem tailTrace_8034947 : CollatzResearch.WordTrace tailWord_8034947 prefixEnd_8034947 4125789844401479966610457 := by
  unfold tailWord_8034947
  simp only [CollatzResearch.WordTrace]
  refine ⟨293058592821766753541535095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195372395214511169027690063 293058592821766753541535095)
  ·
    refine ⟨439587889232650130312302643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293058592821766753541535095 439587889232650130312302643)
    ·
      refine ⟨659381833848975195468453965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439587889232650130312302643 659381833848975195468453965)
      ·
        refine ⟨247268187693365698300670237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659381833848975195468453965 247268187693365698300670237)
        ·
          refine ⟨92725570385012136862751339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247268187693365698300670237 92725570385012136862751339)
          ·
            refine ⟨139088355577518205294127009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92725570385012136862751339 139088355577518205294127009)
            ·
              refine ⟨104316266683138653970595257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139088355577518205294127009 104316266683138653970595257)
              ·
                refine ⟨78237200012353990477946443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104316266683138653970595257 78237200012353990477946443)
                ·
                  refine ⟨117355800018530985716919665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78237200012353990477946443 117355800018530985716919665)
                  ·
                    refine ⟨88016850013898239287689749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117355800018530985716919665 88016850013898239287689749)
                    ·
                      refine ⟨4125789844401479966610457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88016850013898239287689749 4125789844401479966610457)
                      ·
                        rfl

theorem cell23_8034947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_8034947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8034947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8034947 prefixEnd_8034947 := by exact prefixLift 8034947
  have htrace : WordTrace (prefixWord ++ tailWord_8034947) baseStart_8034947 baseEnd_8034947 := by
    simpa [prefixWord, tailWord_8034947, baseEnd_8034947] using wordTrace_append hprefix tailTrace_8034947
  have hstable : (prefixWord ++ tailWord_8034947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8034947).length < 2 ^ (prefixWord ++ tailWord_8034947).sum := by decide
  have hdescent : baseEnd_8034947 < baseStart_8034947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8034947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035045 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_8035045 : Nat := 118140960795 + 8035045 * 2 ^ 59
def prefixEnd_8035045 : Nat := 4983230072969 + 3 ^ 40 * 8035045 * 2
def baseEnd_8035045 : Nat := 4125840165505620583185007

theorem tailTrace_8035045 : CollatzResearch.WordTrace tailWord_8035045 prefixEnd_8035045 4125840165505620583185007 := by
  unfold tailWord_8035045
  simp only [CollatzResearch.WordTrace]
  refine ⟨293062167175411716278602589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195374778116941144185735059 293062167175411716278602589)
  ·
    refine ⟨109898312690779393604475971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293062167175411716278602589 109898312690779393604475971)
    ·
      refine ⟨164847469036169090406713957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109898312690779393604475971 164847469036169090406713957)
      ·
        refine ⟨30908900444281704451258867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164847469036169090406713957 30908900444281704451258867)
        ·
          refine ⟨46363350666422556676888301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30908900444281704451258867 46363350666422556676888301)
          ·
            refine ⟨17386256499908458753833113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46363350666422556676888301 17386256499908458753833113)
            ·
              refine ⟨13039692374931344065374835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17386256499908458753833113 13039692374931344065374835)
              ·
                refine ⟨19559538562397016098062253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039692374931344065374835 19559538562397016098062253)
                ·
                  refine ⟨7334826960898881036773345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19559538562397016098062253 7334826960898881036773345)
                  ·
                    refine ⟨5501120220674160777580009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7334826960898881036773345 5501120220674160777580009)
                    ·
                      refine ⟨4125840165505620583185007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501120220674160777580009 4125840165505620583185007)
                      ·
                        rfl

theorem cell23_8035045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_8035045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035045 prefixEnd_8035045 := by exact prefixLift 8035045
  have htrace : WordTrace (prefixWord ++ tailWord_8035045) baseStart_8035045 baseEnd_8035045 := by
    simpa [prefixWord, tailWord_8035045, baseEnd_8035045] using wordTrace_append hprefix tailTrace_8035045
  have hstable : (prefixWord ++ tailWord_8035045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035045).length < 2 ^ (prefixWord ++ tailWord_8035045).sum := by decide
  have hdescent : baseEnd_8035045 < baseStart_8035045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035058 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_8035058 : Nat := 118140960795 + 8035058 * 2 ^ 59
def prefixEnd_8035058 : Nat := 4983230072969 + 3 ^ 40 * 8035058 * 2
def baseEnd_8035058 : Nat := 4125846840754129032322447

theorem tailTrace_8035058 : CollatzResearch.WordTrace tailWord_8035058 prefixEnd_8035058 4125846840754129032322447 := by
  unfold tailWord_8035058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73265660331091154874706457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195375094216243079665883885 73265660331091154874706457)
  ·
    refine ⟨54949245248318366156029843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73265660331091154874706457 54949245248318366156029843)
    ·
      refine ⟨82423867872477549234044765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54949245248318366156029843 82423867872477549234044765)
      ·
        refine ⟨30908950452179080962766787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82423867872477549234044765 30908950452179080962766787)
        ·
          refine ⟨46363425678268621444150181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30908950452179080962766787 46363425678268621444150181)
          ·
            refine ⟨8693142314675366520778159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46363425678268621444150181 8693142314675366520778159)
            ·
              refine ⟨13039713472013049781167239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693142314675366520778159 13039713472013049781167239)
              ·
                refine ⟨19559570208019574671750859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039713472013049781167239 19559570208019574671750859)
                ·
                  refine ⟨29339355312029362007626289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19559570208019574671750859 29339355312029362007626289)
                  ·
                    refine ⟨22004516484022021505719717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29339355312029362007626289 22004516484022021505719717)
                    ·
                      refine ⟨4125846840754129032322447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22004516484022021505719717 4125846840754129032322447)
                      ·
                        rfl

theorem cell23_8035058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_8035058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035058 prefixEnd_8035058 := by exact prefixLift 8035058
  have htrace : WordTrace (prefixWord ++ tailWord_8035058) baseStart_8035058 baseEnd_8035058 := by
    simpa [prefixWord, tailWord_8035058, baseEnd_8035058] using wordTrace_append hprefix tailTrace_8035058
  have hstable : (prefixWord ++ tailWord_8035058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035058).length < 2 ^ (prefixWord ++ tailWord_8035058).sum := by decide
  have hdescent : baseEnd_8035058 < baseStart_8035058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035079 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_8035079 : Nat := 118140960795 + 8035079 * 2 ^ 59
def prefixEnd_8035079 : Nat := 4983230072969 + 3 ^ 40 * 8035079 * 2
def baseEnd_8035079 : Nat := 4125857623847873450159851

theorem tailTrace_8035079 : CollatzResearch.WordTrace tailWord_8035079 prefixEnd_8035079 4125857623847873450159851 := by
  unfold tailWord_8035079
  simp only [CollatzResearch.WordTrace]
  refine ⟨293063407257288540085340291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195375604838192360056893527 293063407257288540085340291)
  ·
    refine ⟨439595110885932810128010437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293063407257288540085340291 439595110885932810128010437)
    ·
      refine ⟨82424083291112401899001957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439595110885932810128010437 82424083291112401899001957)
      ·
        refine ⟨15454515617083575356062867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82424083291112401899001957 15454515617083575356062867)
        ·
          refine ⟨23181773425625363034094301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454515617083575356062867 23181773425625363034094301)
          ·
            refine ⟨8693165034609511137785363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23181773425625363034094301 8693165034609511137785363)
            ·
              refine ⟨13039747551914266706678045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693165034609511137785363 13039747551914266706678045)
              ·
                refine ⟨4889905331967850015004267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13039747551914266706678045 4889905331967850015004267)
                ·
                  refine ⟨7334857997951775022506401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889905331967850015004267 7334857997951775022506401)
                  ·
                    refine ⟨5501143498463831266879801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7334857997951775022506401 5501143498463831266879801)
                    ·
                      refine ⟨4125857623847873450159851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501143498463831266879801 4125857623847873450159851)
                      ·
                        rfl

theorem cell23_8035079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_8035079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035079 prefixEnd_8035079 := by exact prefixLift 8035079
  have htrace : WordTrace (prefixWord ++ tailWord_8035079) baseStart_8035079 baseEnd_8035079 := by
    simpa [prefixWord, tailWord_8035079, baseEnd_8035079] using wordTrace_append hprefix tailTrace_8035079
  have hstable : (prefixWord ++ tailWord_8035079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035079).length < 2 ^ (prefixWord ++ tailWord_8035079).sum := by decide
  have hdescent : baseEnd_8035079 < baseStart_8035079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035084 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_8035084 : Nat := 118140960795 + 8035084 * 2 ^ 59
def prefixEnd_8035084 : Nat := 4983230072969 + 3 ^ 40 * 8035084 * 2
def baseEnd_8035084 : Nat := 4125860191251145930597327

theorem tailTrace_8035084 : CollatzResearch.WordTrace tailWord_8035084 prefixEnd_8035084 4125860191251145930597327 := by
  unfold tailWord_8035084
  simp only [CollatzResearch.WordTrace]
  refine ⟨146531794811135212969636153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195375726414846950626181537 146531794811135212969636153)
  ·
    refine ⟨109898846108351409727227115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146531794811135212969636153 109898846108351409727227115)
    ·
      refine ⟨164848269162527114590840673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109898846108351409727227115 164848269162527114590840673)
      ·
        refine ⟨123636201871895335943130505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164848269162527114590840673 123636201871895335943130505)
        ·
          refine ⟨92727151403921501957347879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123636201871895335943130505 92727151403921501957347879)
          ·
            refine ⟨139090727105882252936021819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92727151403921501957347879 139090727105882252936021819)
            ·
              refine ⟨208636090658823379404032729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139090727105882252936021819 208636090658823379404032729)
              ·
                refine ⟨156477067994117534553024547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208636090658823379404032729 156477067994117534553024547)
                ·
                  refine ⟨234715601991176301829536821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156477067994117534553024547 234715601991176301829536821)
                  ·
                    refine ⟨22004587686672778296519077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234715601991176301829536821 22004587686672778296519077)
                    ·
                      refine ⟨4125860191251145930597327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22004587686672778296519077 4125860191251145930597327)
                      ·
                        rfl

theorem cell23_8035084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_8035084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035084 prefixEnd_8035084 := by exact prefixLift 8035084
  have htrace : WordTrace (prefixWord ++ tailWord_8035084) baseStart_8035084 baseEnd_8035084 := by
    simpa [prefixWord, tailWord_8035084, baseEnd_8035084] using wordTrace_append hprefix tailTrace_8035084
  have hstable : (prefixWord ++ tailWord_8035084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035084).length < 2 ^ (prefixWord ++ tailWord_8035084).sum := by decide
  have hdescent : baseEnd_8035084 < baseStart_8035084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035241 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_8035241 : Nat := 118140960795 + 8035241 * 2 ^ 59
def prefixEnd_8035241 : Nat := 4983230072969 + 3 ^ 40 * 8035241 * 2
def baseEnd_8035241 : Nat := 4125940807713901816334105

theorem tailTrace_8035241 : CollatzResearch.WordTrace tailWord_8035241 prefixEnd_8035241 4125940807713901816334105 := by
  unfold tailWord_8035241
  simp only [CollatzResearch.WordTrace]
  refine ⟨293069315882701641752737577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195379543921801094501825051 293069315882701641752737577)
  ·
    refine ⟨219801986912026231314553183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293069315882701641752737577 219801986912026231314553183)
    ·
      refine ⟨329702980368039346971829775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219801986912026231314553183 329702980368039346971829775)
      ·
        refine ⟨494554470552059020457744663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329702980368039346971829775 494554470552059020457744663)
        ·
          refine ⟨741831705828088530686616995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494554470552059020457744663 741831705828088530686616995)
          ·
            refine ⟨1112747558742132796029925493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741831705828088530686616995 1112747558742132796029925493)
            ·
              refine ⟨104320083632074949627805515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1112747558742132796029925493 104320083632074949627805515)
              ·
                refine ⟨156480125448112424441708273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104320083632074949627805515 156480125448112424441708273)
                ·
                  refine ⟨117360094086084318331281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156480125448112424441708273 117360094086084318331281205)
                  ·
                    refine ⟨11002508820570404843557613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117360094086084318331281205 11002508820570404843557613)
                    ·
                      refine ⟨4125940807713901816334105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002508820570404843557613 4125940807713901816334105)
                      ·
                        rfl

theorem cell23_8035241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_8035241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035241 prefixEnd_8035241 := by exact prefixLift 8035241
  have htrace : WordTrace (prefixWord ++ tailWord_8035241) baseStart_8035241 baseEnd_8035241 := by
    simpa [prefixWord, tailWord_8035241, baseEnd_8035241] using wordTrace_append hprefix tailTrace_8035241
  have hstable : (prefixWord ++ tailWord_8035241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035241).length < 2 ^ (prefixWord ++ tailWord_8035241).sum := by decide
  have hdescent : baseEnd_8035241 < baseStart_8035241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035275 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 3]
def baseStart_8035275 : Nat := 118140960795 + 8035275 * 2 ^ 59
def prefixEnd_8035275 : Nat := 4983230072969 + 3 ^ 40 * 8035275 * 2
def baseEnd_8035275 : Nat := 4125958266056154683308949

theorem tailTrace_8035275 : CollatzResearch.WordTrace tailWord_8035275 prefixEnd_8035275 4125958266056154683308949 := by
  unfold tailWord_8035275
  simp only [CollatzResearch.WordTrace]
  refine ⟨293070555964578465559475279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195380370643052310372983519 293070555964578465559475279)
  ·
    refine ⟨439605833946867698339212919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293070555964578465559475279 439605833946867698339212919)
    ·
      refine ⟨659408750920301547508819379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439605833946867698339212919 659408750920301547508819379)
      ·
        refine ⟨989113126380452321263229069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659408750920301547508819379 989113126380452321263229069)
        ·
          refine ⟨370917422392669620473710901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 989113126380452321263229069 370917422392669620473710901)
          ·
            refine ⟨34773508349312776919410397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370917422392669620473710901 34773508349312776919410397)
            ·
              refine ⟨13040065630992291344778899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34773508349312776919410397 13040065630992291344778899)
              ·
                refine ⟨19560098446488437017168349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13040065630992291344778899 19560098446488437017168349)
                ·
                  refine ⟨7335036917433163881438131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19560098446488437017168349 7335036917433163881438131)
                  ·
                    refine ⟨11002555376149745822157197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335036917433163881438131 11002555376149745822157197)
                    ·
                      refine ⟨4125958266056154683308949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002555376149745822157197 4125958266056154683308949)
                      ·
                        rfl

theorem cell23_8035275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 3].length) (baseStart_8035275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035275 prefixEnd_8035275 := by exact prefixLift 8035275
  have htrace : WordTrace (prefixWord ++ tailWord_8035275) baseStart_8035275 baseEnd_8035275 := by
    simpa [prefixWord, tailWord_8035275, baseEnd_8035275] using wordTrace_append hprefix tailTrace_8035275
  have hstable : (prefixWord ++ tailWord_8035275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035275).length < 2 ^ (prefixWord ++ tailWord_8035275).sum := by decide
  have hdescent : baseEnd_8035275 < baseStart_8035275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035282 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_8035282 : Nat := 118140960795 + 8035282 * 2 ^ 59
def prefixEnd_8035282 : Nat := 4983230072969 + 3 ^ 40 * 8035282 * 2
def baseEnd_8035282 : Nat := 458440206713415128435713

theorem tailTrace_8035282 : CollatzResearch.WordTrace tailWord_8035282 prefixEnd_8035282 458440206713415128435713 := by
  unfold tailWord_8035282
  simp only [CollatzResearch.WordTrace]
  refine ⟨73267702818888276438745025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195380540850368737169986733 73267702818888276438745025)
  ·
    refine ⟨54950777114166207329058769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73267702818888276438745025 54950777114166207329058769)
    ·
      refine ⟨41213082835624655496794077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54950777114166207329058769 41213082835624655496794077)
      ·
        refine ⟨15454906063359245811297779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41213082835624655496794077 15454906063359245811297779)
        ·
          refine ⟨23182359095038868716946669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454906063359245811297779 23182359095038868716946669)
          ·
            refine ⟨8693384660639575768855001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23182359095038868716946669 8693384660639575768855001)
            ·
              refine ⟨6520038495479681826641251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693384660639575768855001 6520038495479681826641251)
              ·
                refine ⟨9780057743219522739961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6520038495479681826641251 9780057743219522739961877)
                ·
                  refine ⟨458440206713415128435713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9780057743219522739961877 458440206713415128435713)
                  ·
                    rfl

theorem cell23_8035282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_8035282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035282 prefixEnd_8035282 := by exact prefixLift 8035282
  have htrace : WordTrace (prefixWord ++ tailWord_8035282) baseStart_8035282 baseEnd_8035282 := by
    simpa [prefixWord, tailWord_8035282, baseEnd_8035282] using wordTrace_append hprefix tailTrace_8035282
  have hstable : (prefixWord ++ tailWord_8035282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035282).length < 2 ^ (prefixWord ++ tailWord_8035282).sum := by decide
  have hdescent : baseEnd_8035282 < baseStart_8035282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035316 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 6]
def baseStart_8035316 : Nat := 118140960795 + 8035316 * 2 ^ 59
def prefixEnd_8035316 : Nat := 4983230072969 + 3 ^ 40 * 8035316 * 2
def baseEnd_8035316 : Nat := 458442146529221002544029

theorem tailTrace_8035316 : CollatzResearch.WordTrace tailWord_8035316 prefixEnd_8035316 458442146529221002544029 := by
  unfold tailWord_8035316
  simp only [CollatzResearch.WordTrace]
  refine ⟨146536025678714964780858901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195381367571619953041145201 146536025678714964780858901)
  ·
    refine ⟨6868876203689763974102761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146536025678714964780858901 6868876203689763974102761)
    ·
      refine ⟨5151657152767322980577071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6868876203689763974102761 5151657152767322980577071)
      ·
        refine ⟨7727485729150984470865607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151657152767322980577071 7727485729150984470865607)
        ·
          refine ⟨11591228593726476706298411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727485729150984470865607 11591228593726476706298411)
          ·
            refine ⟨17386842890589715059447617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591228593726476706298411 17386842890589715059447617)
            ·
              refine ⟨13040132167942286294585713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17386842890589715059447617 13040132167942286294585713)
              ·
                refine ⟨9780099125956714720939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13040132167942286294585713 9780099125956714720939285)
                ·
                  refine ⟨458442146529221002544029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9780099125956714720939285 458442146529221002544029)
                  ·
                    rfl

theorem cell23_8035316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_8035316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035316 prefixEnd_8035316 := by exact prefixLift 8035316
  have htrace : WordTrace (prefixWord ++ tailWord_8035316) baseStart_8035316 baseEnd_8035316 := by
    simpa [prefixWord, tailWord_8035316, baseEnd_8035316] using wordTrace_append hprefix tailTrace_8035316
  have hstable : (prefixWord ++ tailWord_8035316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035316).length < 2 ^ (prefixWord ++ tailWord_8035316).sum := by decide
  have hdescent : baseEnd_8035316 < baseStart_8035316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035326 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_8035326 : Nat := 118140960795 + 8035326 * 2 ^ 59
def prefixEnd_8035326 : Nat := 4983230072969 + 3 ^ 40 * 8035326 * 2
def baseEnd_8035326 : Nat := 4125984453569533983771215

theorem tailTrace_8035326 : CollatzResearch.WordTrace tailWord_8035326 prefixEnd_8035326 4125984453569533983771215 := by
  unfold tailWord_8035326
  simp only [CollatzResearch.WordTrace]
  refine ⟨36634052010924212658697729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195381610724929134179721221 36634052010924212658697729)
  ·
    refine ⟨27475539008193159494023297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36634052010924212658697729 27475539008193159494023297)
    ·
      refine ⟨20606654256144869620517473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27475539008193159494023297 20606654256144869620517473)
      ·
        refine ⟨15454990692108652215388105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20606654256144869620517473 15454990692108652215388105)
        ·
          refine ⟨11591243019081489161541079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15454990692108652215388105 11591243019081489161541079)
          ·
            refine ⟨17386864528622233742311619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591243019081489161541079 17386864528622233742311619)
            ·
              refine ⟨26080296792933350613467429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386864528622233742311619 26080296792933350613467429)
              ·
                refine ⟨4890055648675003240025143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26080296792933350613467429 4890055648675003240025143)
                ·
                  refine ⟨7335083473012504860037715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890055648675003240025143 7335083473012504860037715)
                  ·
                    refine ⟨11002625209518757290056573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335083473012504860037715 11002625209518757290056573)
                    ·
                      refine ⟨4125984453569533983771215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002625209518757290056573 4125984453569533983771215)
                      ·
                        rfl

theorem cell23_8035326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_8035326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035326 prefixEnd_8035326 := by exact prefixLift 8035326
  have htrace : WordTrace (prefixWord ++ tailWord_8035326) baseStart_8035326 baseEnd_8035326 := by
    simpa [prefixWord, tailWord_8035326, baseEnd_8035326] using wordTrace_append hprefix tailTrace_8035326
  have hstable : (prefixWord ++ tailWord_8035326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035326).length < 2 ^ (prefixWord ++ tailWord_8035326).sum := by decide
  have hdescent : baseEnd_8035326 < baseStart_8035326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035338 : List Nat := [3, 1, 2, 2, 3, 1, 3, 8]
def baseStart_8035338 : Nat := 118140960795 + 8035338 * 2 ^ 59
def prefixEnd_8035338 : Nat := 4983230072969 + 3 ^ 40 * 8035338 * 2
def baseEnd_8035338 : Nat := 152814467234718071734117

theorem tailTrace_8035338 : CollatzResearch.WordTrace tailWord_8035338 prefixEnd_8035338 152814467234718071734117 := by
  unfold tailWord_8035338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73268213440837556829754667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195381902508900151546012445 73268213440837556829754667)
  ·
    refine ⟨109902320161256335244632001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73268213440837556829754667 109902320161256335244632001)
    ·
      refine ⟨82426740120942251433474001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109902320161256335244632001 82426740120942251433474001)
      ·
        refine ⟨61820055090706688575105501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82426740120942251433474001 61820055090706688575105501)
        ·
          refine ⟨23182520659015008215664563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61820055090706688575105501 23182520659015008215664563)
          ·
            refine ⟨34773780988522512323496845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23182520659015008215664563 34773780988522512323496845)
            ·
              refine ⟨13040167870695942121311317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34773780988522512323496845 13040167870695942121311317)
              ·
                refine ⟨152814467234718071734117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13040167870695942121311317 152814467234718071734117)
                ·
                  rfl

theorem cell23_8035338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_8035338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035338 prefixEnd_8035338 := by exact prefixLift 8035338
  have htrace : WordTrace (prefixWord ++ tailWord_8035338) baseStart_8035338 baseEnd_8035338 := by
    simpa [prefixWord, tailWord_8035338, baseEnd_8035338] using wordTrace_append hprefix tailTrace_8035338
  have hstable : (prefixWord ++ tailWord_8035338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035338).length < 2 ^ (prefixWord ++ tailWord_8035338).sum := by decide
  have hdescent : baseEnd_8035338 < baseStart_8035338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035365 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_8035365 : Nat := 118140960795 + 8035365 * 2 ^ 59
def prefixEnd_8035365 : Nat := 4983230072969 + 3 ^ 40 * 8035365 * 2
def baseEnd_8035365 : Nat := 4126004479315059331183535

theorem tailTrace_8035365 : CollatzResearch.WordTrace tailWord_8035365 prefixEnd_8035365 4126004479315059331183535 := by
  unfold tailWord_8035365
  simp only [CollatzResearch.WordTrace]
  refine ⟨293073838534252410930251549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195382559022834940620167699 293073838534252410930251549)
  ·
    refine ⟨109902689450344654098844331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293073838534252410930251549 109902689450344654098844331)
    ·
      refine ⟨164854034175516981148266497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109902689450344654098844331 164854034175516981148266497)
      ·
        refine ⟨123640525631637735861199873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164854034175516981148266497 123640525631637735861199873)
        ·
          refine ⟨92730394223728301895899905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123640525631637735861199873 92730394223728301895899905)
          ·
            refine ⟨69547795667796226421924929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92730394223728301895899905 69547795667796226421924929)
            ·
              refine ⟨52160846750847169816443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69547795667796226421924929 52160846750847169816443697)
              ·
                refine ⟨39120635063135377362332773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52160846750847169816443697 39120635063135377362332773)
                ·
                  refine ⟨7335119074337883255437395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39120635063135377362332773 7335119074337883255437395)
                  ·
                    refine ⟨11002678611506824883156093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335119074337883255437395 11002678611506824883156093)
                    ·
                      refine ⟨4126004479315059331183535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002678611506824883156093 4126004479315059331183535)
                      ·
                        rfl

theorem cell23_8035365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_8035365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035365 prefixEnd_8035365 := by exact prefixLift 8035365
  have htrace : WordTrace (prefixWord ++ tailWord_8035365) baseStart_8035365 baseEnd_8035365 := by
    simpa [prefixWord, tailWord_8035365, baseEnd_8035365] using wordTrace_append hprefix tailTrace_8035365
  have hstable : (prefixWord ++ tailWord_8035365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035365).length < 2 ^ (prefixWord ++ tailWord_8035365).sum := by decide
  have hdescent : baseEnd_8035365 < baseStart_8035365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035399 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_8035399 : Nat := 118140960795 + 8035399 * 2 ^ 59
def prefixEnd_8035399 : Nat := 4983230072969 + 3 ^ 40 * 8035399 * 2
def baseEnd_8035399 : Nat := 4126021937657312198158379

theorem tailTrace_8035399 : CollatzResearch.WordTrace tailWord_8035399 prefixEnd_8035399 4126021937657312198158379 := by
  unfold tailWord_8035399
  simp only [CollatzResearch.WordTrace]
  refine ⟨293075078616129234736989251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195383385744086156491326167 293075078616129234736989251)
  ·
    refine ⟨439612617924193852105483877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293075078616129234736989251 439612617924193852105483877)
    ·
      refine ⟨82427365860786347269778227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439612617924193852105483877 82427365860786347269778227)
      ·
        refine ⟨123641048791179520904667341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82427365860786347269778227 123641048791179520904667341)
        ·
          refine ⟨46365393296692320339250253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123641048791179520904667341 46365393296692320339250253)
          ·
            refine ⟨17387022486259620127218845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46365393296692320339250253 17387022486259620127218845)
            ·
              refine ⟨6520133432347357547707067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17387022486259620127218845 6520133432347357547707067)
              ·
                refine ⟨9780200148521036321560601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6520133432347357547707067 9780200148521036321560601)
                ·
                  refine ⟨7335150111390777241170451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9780200148521036321560601 7335150111390777241170451)
                  ·
                    refine ⟨11002725167086165861755677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335150111390777241170451 11002725167086165861755677)
                    ·
                      refine ⟨4126021937657312198158379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002725167086165861755677 4126021937657312198158379)
                      ·
                        rfl

theorem cell23_8035399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_8035399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035399 prefixEnd_8035399 := by exact prefixLift 8035399
  have htrace : WordTrace (prefixWord ++ tailWord_8035399) baseStart_8035399 baseEnd_8035399 := by
    simpa [prefixWord, tailWord_8035399, baseEnd_8035399] using wordTrace_append hprefix tailTrace_8035399
  have hstable : (prefixWord ++ tailWord_8035399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035399).length < 2 ^ (prefixWord ++ tailWord_8035399).sum := by decide
  have hdescent : baseEnd_8035399 < baseStart_8035399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035408 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_8035408 : Nat := 118140960795 + 8035408 * 2 ^ 59
def prefixEnd_8035408 : Nat := 4983230072969 + 3 ^ 40 * 8035408 * 2
def baseEnd_8035408 : Nat := 4126026558983202662945837

theorem tailTrace_8035408 : CollatzResearch.WordTrace tailWord_8035408 prefixEnd_8035408 4126026558983202662945837 := by
  unfold tailWord_8035408
  simp only [CollatzResearch.WordTrace]
  refine ⟨146537703436548314637033439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195383604582064419516044585 146537703436548314637033439)
  ·
    refine ⟨219806555154822471955550159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146537703436548314637033439 219806555154822471955550159)
    ·
      refine ⟨329709832732233707933325239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219806555154822471955550159 329709832732233707933325239)
      ·
        refine ⟨494564749098350561899987859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329709832732233707933325239 494564749098350561899987859)
        ·
          refine ⟨741847123647525842849981789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494564749098350561899987859 741847123647525842849981789)
          ·
            refine ⟨278192671367822191068743171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741847123647525842849981789 278192671367822191068743171)
            ·
              refine ⟨417289007051733286603114757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278192671367822191068743171 417289007051733286603114757)
              ·
                refine ⟨78241688822199991238084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417289007051733286603114757 78241688822199991238084017)
                ·
                  refine ⟨58681266616649993428563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78241688822199991238084017 58681266616649993428563013)
                  ·
                    refine ⟨11002737490621873767855565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58681266616649993428563013 11002737490621873767855565)
                    ·
                      refine ⟨4126026558983202662945837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002737490621873767855565 4126026558983202662945837)
                      ·
                        rfl

theorem cell23_8035408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_8035408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035408 prefixEnd_8035408 := by exact prefixLift 8035408
  have htrace : WordTrace (prefixWord ++ tailWord_8035408) baseStart_8035408 baseEnd_8035408 := by
    simpa [prefixWord, tailWord_8035408, baseEnd_8035408] using wordTrace_append hprefix tailTrace_8035408
  have hstable : (prefixWord ++ tailWord_8035408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035408).length < 2 ^ (prefixWord ++ tailWord_8035408).sum := by decide
  have hdescent : baseEnd_8035408 < baseStart_8035408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035418 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_8035418 : Nat := 118140960795 + 8035418 * 2 ^ 59
def prefixEnd_8035418 : Nat := 4983230072969 + 3 ^ 40 * 8035418 * 2
def baseEnd_8035418 : Nat := 4126031693789747623820791

theorem tailTrace_8035418 : CollatzResearch.WordTrace tailWord_8035418 prefixEnd_8035418 4126031693789747623820791 := by
  unfold tailWord_8035418
  simp only [CollatzResearch.WordTrace]
  refine ⟨73268942900765100245482727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195383847735373600654620605 73268942900765100245482727)
  ·
    refine ⟨109903414351147650368224091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73268942900765100245482727 109903414351147650368224091)
    ·
      refine ⟨164855121526721475552336137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109903414351147650368224091 164855121526721475552336137)
      ·
        refine ⟨123641341145041106664252103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164855121526721475552336137 123641341145041106664252103)
        ·
          refine ⟨185462011717561659996378155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123641341145041106664252103 185462011717561659996378155)
          ·
            refine ⟨278193017576342489994567233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185462011717561659996378155 278193017576342489994567233)
            ·
              refine ⟨208644763182256867495925425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278193017576342489994567233 208644763182256867495925425)
              ·
                refine ⟨156483572386692650621944069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208644763182256867495925425 156483572386692650621944069)
                ·
                  refine ⟨29340669822504871991614513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156483572386692650621944069 29340669822504871991614513)
                  ·
                    refine ⟨22005502366878653993710885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29340669822504871991614513 22005502366878653993710885)
                    ·
                      refine ⟨4126031693789747623820791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22005502366878653993710885 4126031693789747623820791)
                      ·
                        rfl

theorem cell23_8035418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_8035418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035418 prefixEnd_8035418 := by exact prefixLift 8035418
  have htrace : WordTrace (prefixWord ++ tailWord_8035418) baseStart_8035418 baseEnd_8035418 := by
    simpa [prefixWord, tailWord_8035418, baseEnd_8035418] using wordTrace_append hprefix tailTrace_8035418
  have hstable : (prefixWord ++ tailWord_8035418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035418).length < 2 ^ (prefixWord ++ tailWord_8035418).sum := by decide
  have hdescent : baseEnd_8035418 < baseStart_8035418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035526 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8035526 : Nat := 118140960795 + 8035526 * 2 ^ 59
def prefixEnd_8035526 : Nat := 4983230072969 + 3 ^ 40 * 8035526 * 2
def baseEnd_8035526 : Nat := 1375362383233477733756765

theorem tailTrace_8035526 : CollatzResearch.WordTrace tailWord_8035526 prefixEnd_8035526 1375362383233477733756765 := by
  unfold tailWord_8035526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158740958958410482089451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195386473791112756951241621 9158740958958410482089451)
  ·
    refine ⟨13738111438437615723134177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9158740958958410482089451 13738111438437615723134177)
    ·
      refine ⟨10303583578828211792350633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13738111438437615723134177 10303583578828211792350633)
      ·
        refine ⟨7727687684121158844262975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10303583578828211792350633 7727687684121158844262975)
        ·
          refine ⟨11591531526181738266394463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727687684121158844262975 11591531526181738266394463)
          ·
            refine ⟨17387297289272607399591695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591531526181738266394463 17387297289272607399591695)
            ·
              refine ⟨26080945933908911099387543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387297289272607399591695 26080945933908911099387543)
              ·
                refine ⟨39121418900863366649081315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26080945933908911099387543 39121418900863366649081315)
                ·
                  refine ⟨58682128351295049973621973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39121418900863366649081315 58682128351295049973621973)
                  ·
                    refine ⟨1375362383233477733756765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58682128351295049973621973 1375362383233477733756765)
                    ·
                      rfl

theorem cell23_8035526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8035526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035526 prefixEnd_8035526 := by exact prefixLift 8035526
  have htrace : WordTrace (prefixWord ++ tailWord_8035526) baseStart_8035526 baseEnd_8035526 := by
    simpa [prefixWord, tailWord_8035526, baseEnd_8035526] using wordTrace_append hprefix tailTrace_8035526
  have hstable : (prefixWord ++ tailWord_8035526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035526).length < 2 ^ (prefixWord ++ tailWord_8035526).sum := by decide
  have hdescent : baseEnd_8035526 < baseStart_8035526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035552 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 6]
def baseStart_8035552 : Nat := 118140960795 + 8035552 * 2 ^ 59
def prefixEnd_8035552 : Nat := 4983230072969 + 3 ^ 40 * 8035552 * 2
def baseEnd_8035552 : Nat := 458455611133050011060575

theorem tailTrace_8035552 : CollatzResearch.WordTrace tailWord_8035552 prefixEnd_8035552 458455611133050011060575 := by
  unfold tailWord_8035552
  simp only [CollatzResearch.WordTrace]
  refine ⟨146540329492287470933654455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195387105989716627911539273 146540329492287470933654455)
  ·
    refine ⟨219810494238431206400481683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146540329492287470933654455 219810494238431206400481683)
    ·
      refine ⟨329715741357646809600722525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219810494238431206400481683 329715741357646809600722525)
      ·
        refine ⟨123643403009117553600270947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329715741357646809600722525 123643403009117553600270947)
        ·
          refine ⟨185465104513676330400406421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123643403009117553600270947 185465104513676330400406421)
          ·
            refine ⟨8693676774078577987519051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185465104513676330400406421 8693676774078577987519051)
            ·
              refine ⟨13040515161117866981278577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693676774078577987519051 13040515161117866981278577)
              ·
                refine ⟨9780386370838400235958933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13040515161117866981278577 9780386370838400235958933)
                ·
                  refine ⟨458455611133050011060575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9780386370838400235958933 458455611133050011060575)
                  ·
                    rfl

theorem cell23_8035552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_8035552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035552 prefixEnd_8035552 := by exact prefixLift 8035552
  have htrace : WordTrace (prefixWord ++ tailWord_8035552) baseStart_8035552 baseEnd_8035552 := by
    simpa [prefixWord, tailWord_8035552, baseEnd_8035552] using wordTrace_append hprefix tailTrace_8035552
  have hstable : (prefixWord ++ tailWord_8035552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035552).length < 2 ^ (prefixWord ++ tailWord_8035552).sum := by decide
  have hdescent : baseEnd_8035552 < baseStart_8035552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035596 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_8035596 : Nat := 118140960795 + 8035596 * 2 ^ 59
def prefixEnd_8035596 : Nat := 4983230072969 + 3 ^ 40 * 8035596 * 2
def baseEnd_8035596 : Nat := 4126123093346247927394973

theorem tailTrace_8035596 : CollatzResearch.WordTrace tailWord_8035596 prefixEnd_8035596 4126123093346247927394973 := by
  unfold tailWord_8035596
  simp only [CollatzResearch.WordTrace]
  refine ⟨146541131898207768690955321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195388175864277024921273761 146541131898207768690955321)
  ·
    refine ⟨109905848923655826518216491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146541131898207768690955321 109905848923655826518216491)
    ·
      refine ⟨164858773385483739777324737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109905848923655826518216491 164858773385483739777324737)
      ·
        refine ⟨123644080039112804832993553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164858773385483739777324737 123644080039112804832993553)
        ·
          refine ⟨92733060029334603624745165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123644080039112804832993553 92733060029334603624745165)
          ·
            refine ⟨34774897511000476359279437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92733060029334603624745165 34774897511000476359279437)
            ·
              refine ⟨13040586566625178634729789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34774897511000476359279437 13040586566625178634729789)
              ·
                refine ⟨4890219962484441988023671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13040586566625178634729789 4890219962484441988023671)
                ·
                  refine ⟨7335329943726662982035507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890219962484441988023671 7335329943726662982035507)
                  ·
                    refine ⟨11002994915589994473053261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335329943726662982035507 11002994915589994473053261)
                    ·
                      refine ⟨4126123093346247927394973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11002994915589994473053261 4126123093346247927394973)
                      ·
                        rfl

theorem cell23_8035596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_8035596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035596 prefixEnd_8035596 := by exact prefixLift 8035596
  have htrace : WordTrace (prefixWord ++ tailWord_8035596) baseStart_8035596 baseEnd_8035596 := by
    simpa [prefixWord, tailWord_8035596, baseEnd_8035596] using wordTrace_append hprefix tailTrace_8035596
  have hstable : (prefixWord ++ tailWord_8035596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035596).length < 2 ^ (prefixWord ++ tailWord_8035596).sum := by decide
  have hdescent : baseEnd_8035596 < baseStart_8035596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035612 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_8035612 : Nat := 118140960795 + 8035612 * 2 ^ 59
def prefixEnd_8035612 : Nat := 4983230072969 + 3 ^ 40 * 8035612 * 2
def baseEnd_8035612 : Nat := 1375377103012239954931633

theorem tailTrace_8035612 : CollatzResearch.WordTrace tailWord_8035612 prefixEnd_8035612 1375377103012239954931633 := by
  unfold tailWord_8035612
  simp only [CollatzResearch.WordTrace]
  refine ⟨146541423682178786057246545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195388564909571714742995393 146541423682178786057246545)
  ·
    refine ⟨109906067761634089542934909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146541423682178786057246545 109906067761634089542934909)
    ·
      refine ⟨41214775410612783578600591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109906067761634089542934909 41214775410612783578600591)
      ·
        refine ⟨61822163115919175367900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41214775410612783578600591 61822163115919175367900887)
        ·
          refine ⟨92733244673878763051851331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61822163115919175367900887 92733244673878763051851331)
          ·
            refine ⟨139099867010818144577776997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92733244673878763051851331 139099867010818144577776997)
            ·
              refine ⟨26081225064528402108333187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139099867010818144577776997 26081225064528402108333187)
              ·
                refine ⟨39121837596792603162499781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26081225064528402108333187 39121837596792603162499781)
                ·
                  refine ⟨7335344549398613092968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39121837596792603162499781 7335344549398613092968709)
                  ·
                    refine ⟨1375377103012239954931633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7335344549398613092968709 1375377103012239954931633)
                    ·
                      rfl

theorem cell23_8035612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_8035612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035612 prefixEnd_8035612 := by exact prefixLift 8035612
  have htrace : WordTrace (prefixWord ++ tailWord_8035612) baseStart_8035612 baseEnd_8035612 := by
    simpa [prefixWord, tailWord_8035612, baseEnd_8035612] using wordTrace_append hprefix tailTrace_8035612
  have hstable : (prefixWord ++ tailWord_8035612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035612).length < 2 ^ (prefixWord ++ tailWord_8035612).sum := by decide
  have hdescent : baseEnd_8035612 < baseStart_8035612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035636 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_8035636 : Nat := 118140960795 + 8035636 * 2 ^ 59
def prefixEnd_8035636 : Nat := 4983230072969 + 3 ^ 40 * 8035636 * 2
def baseEnd_8035636 : Nat := 4126143632572427770894789

theorem tailTrace_8035636 : CollatzResearch.WordTrace tailWord_8035636 prefixEnd_8035636 4126143632572427770894789 := by
  unfold tailWord_8035636
  simp only [CollatzResearch.WordTrace]
  refine ⟨146541861358135312106683381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195389148477513749475577841 146541861358135312106683381)
  ·
    refine ⟨13738299502325185510001567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146541861358135312106683381 13738299502325185510001567)
    ·
      refine ⟨20607449253487778265002351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13738299502325185510001567 20607449253487778265002351)
      ·
        refine ⟨30911173880231667397503527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20607449253487778265002351 30911173880231667397503527)
        ·
          refine ⟨46366760820347501096255291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30911173880231667397503527 46366760820347501096255291)
          ·
            refine ⟨69550141230521251644382937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46366760820347501096255291 69550141230521251644382937)
            ·
              refine ⟨52162605922890938733287203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69550141230521251644382937 52162605922890938733287203)
              ·
                refine ⟨78243908884336408099930805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52162605922890938733287203 78243908884336408099930805)
                ·
                  refine ⟨7335366457906538259368513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78243908884336408099930805 7335366457906538259368513)
                  ·
                    refine ⟨5501524843429903694526385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7335366457906538259368513 5501524843429903694526385)
                    ·
                      refine ⟨4126143632572427770894789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501524843429903694526385 4126143632572427770894789)
                      ·
                        rfl

theorem cell23_8035636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_8035636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035636 prefixEnd_8035636 := by exact prefixLift 8035636
  have htrace : WordTrace (prefixWord ++ tailWord_8035636) baseStart_8035636 baseEnd_8035636 := by
    simpa [prefixWord, tailWord_8035636, baseEnd_8035636] using wordTrace_append hprefix tailTrace_8035636
  have hstable : (prefixWord ++ tailWord_8035636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035636).length < 2 ^ (prefixWord ++ tailWord_8035636).sum := by decide
  have hdescent : baseEnd_8035636 < baseStart_8035636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035649 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8035649 : Nat := 118140960795 + 8035649 * 2 ^ 59
def prefixEnd_8035649 : Nat := 4983230072969 + 3 ^ 40 * 8035649 * 2
def baseEnd_8035649 : Nat := 4126150307820936220032229

theorem tailTrace_8035649 : CollatzResearch.WordTrace tailWord_8035649 prefixEnd_8035649 4126150307820936220032229 := by
  unfold tailWord_8035649
  simp only [CollatzResearch.WordTrace]
  refine ⟨293084196865223527433590001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195389464576815684955726667 293084196865223527433590001)
  ·
    refine ⟨219813147648917645575192501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293084196865223527433590001 219813147648917645575192501)
    ·
      refine ⟨20607482592086029272674297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219813147648917645575192501 20607482592086029272674297)
      ·
        refine ⟨15455611944064521954505723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20607482592086029272674297 15455611944064521954505723)
        ·
          refine ⟨23183417916096782931758585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15455611944064521954505723 23183417916096782931758585)
          ·
            refine ⟨17387563437072587198818939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23183417916096782931758585 17387563437072587198818939)
            ·
              refine ⟨26081345155608880798228409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387563437072587198818939 26081345155608880798228409)
              ·
                refine ⟨19561008866706660598671307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26081345155608880798228409 19561008866706660598671307)
                ·
                  refine ⟨29341513300059990898006961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561008866706660598671307 29341513300059990898006961)
                  ·
                    refine ⟨22006134975044993173505221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29341513300059990898006961 22006134975044993173505221)
                    ·
                      refine ⟨4126150307820936220032229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22006134975044993173505221 4126150307820936220032229)
                      ·
                        rfl

theorem cell23_8035649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8035649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035649 prefixEnd_8035649 := by exact prefixLift 8035649
  have htrace : WordTrace (prefixWord ++ tailWord_8035649) baseStart_8035649 baseEnd_8035649 := by
    simpa [prefixWord, tailWord_8035649, baseEnd_8035649] using wordTrace_append hprefix tailTrace_8035649
  have hstable : (prefixWord ++ tailWord_8035649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035649).length < 2 ^ (prefixWord ++ tailWord_8035649).sum := by decide
  have hdescent : baseEnd_8035649 < baseStart_8035649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035709 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_8035709 : Nat := 118140960795 + 8035709 * 2 ^ 59
def prefixEnd_8035709 : Nat := 4983230072969 + 3 ^ 40 * 8035709 * 2
def baseEnd_8035709 : Nat := 4126181116660205985281953

theorem tailTrace_8035709 : CollatzResearch.WordTrace tailWord_8035709 prefixEnd_8035709 4126181116660205985281953 := by
  unfold tailWord_8035709
  simp only [CollatzResearch.WordTrace]
  refine ⟨293086385245006157680774181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195390923496670771787182787 293086385245006157680774181)
  ·
    refine ⟨54953697233438654565145159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293086385245006157680774181 54953697233438654565145159)
    ·
      refine ⟨82430545850157981847717739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54953697233438654565145159 82430545850157981847717739)
      ·
        refine ⟨123645818775236972771576609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82430545850157981847717739 123645818775236972771576609)
        ·
          refine ⟨92734364081427729578682457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123645818775236972771576609 92734364081427729578682457)
          ·
            refine ⟨69550773061070797184011843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92734364081427729578682457 69550773061070797184011843)
            ·
              refine ⟨104326159591606195776017765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69550773061070797184011843 104326159591606195776017765)
              ·
                refine ⟨19561154923426161708003331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104326159591606195776017765 19561154923426161708003331)
                ·
                  refine ⟨29341732385139242562004997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561154923426161708003331 29341732385139242562004997)
                  ·
                    refine ⟨5501574822213607980375937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29341732385139242562004997 5501574822213607980375937)
                    ·
                      refine ⟨4126181116660205985281953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501574822213607980375937 4126181116660205985281953)
                      ·
                        rfl

theorem cell23_8035709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_8035709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035709 prefixEnd_8035709 := by exact prefixLift 8035709
  have htrace : WordTrace (prefixWord ++ tailWord_8035709) baseStart_8035709 baseEnd_8035709 := by
    simpa [prefixWord, tailWord_8035709, baseEnd_8035709] using wordTrace_append hprefix tailTrace_8035709
  have hstable : (prefixWord ++ tailWord_8035709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035709).length < 2 ^ (prefixWord ++ tailWord_8035709).sum := by decide
  have hdescent : baseEnd_8035709 < baseStart_8035709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035713 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_8035713 : Nat := 118140960795 + 8035713 * 2 ^ 59
def prefixEnd_8035713 : Nat := 4983230072969 + 3 ^ 40 * 8035713 * 2
def baseEnd_8035713 : Nat := 4126183170582823969631935

theorem tailTrace_8035713 : CollatzResearch.WordTrace tailWord_8035713 prefixEnd_8035713 4126183170582823969631935 := by
  unfold tailWord_8035713
  simp only [CollatzResearch.WordTrace]
  refine ⟨293086531136991666363919793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195391020757994444242613195 293086531136991666363919793)
  ·
    refine ⟨219814898352743749772939845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293086531136991666363919793 219814898352743749772939845)
    ·
      refine ⟨41215293441139453082426221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219814898352743749772939845 41215293441139453082426221)
      ·
        refine ⟨15455735040427294905909833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41215293441139453082426221 15455735040427294905909833)
        ·
          refine ⟨11591801280320471179432375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15455735040427294905909833 11591801280320471179432375)
          ·
            refine ⟨17387701920480706769148563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591801280320471179432375 17387701920480706769148563)
            ·
              refine ⟨26081552880721060153722845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387701920480706769148563 26081552880721060153722845)
              ·
                refine ⟨9780582330270397557646067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26081552880721060153722845 9780582330270397557646067)
                ·
                  refine ⟨14670873495405596336469101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9780582330270397557646067 14670873495405596336469101)
                  ·
                    refine ⟨5501577560777098626175913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14670873495405596336469101 5501577560777098626175913)
                    ·
                      refine ⟨4126183170582823969631935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501577560777098626175913 4126183170582823969631935)
                      ·
                        rfl

theorem cell23_8035713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_8035713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035713 prefixEnd_8035713 := by exact prefixLift 8035713
  have htrace : WordTrace (prefixWord ++ tailWord_8035713) baseStart_8035713 baseEnd_8035713 := by
    simpa [prefixWord, tailWord_8035713, baseEnd_8035713] using wordTrace_append hprefix tailTrace_8035713
  have hstable : (prefixWord ++ tailWord_8035713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035713).length < 2 ^ (prefixWord ++ tailWord_8035713).sum := by decide
  have hdescent : baseEnd_8035713 < baseStart_8035713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035799 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_8035799 : Nat := 118140960795 + 8035799 * 2 ^ 59
def prefixEnd_8035799 : Nat := 4983230072969 + 3 ^ 40 * 8035799 * 2
def baseEnd_8035799 : Nat := 4126227329919110633156539

theorem tailTrace_8035799 : CollatzResearch.WordTrace tailWord_8035799 prefixEnd_8035799 4126227329919110633156539 := by
  unfold tailWord_8035799
  simp only [CollatzResearch.WordTrace]
  refine ⟨293089667814680103051550451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195393111876453402034366967 293089667814680103051550451)
  ·
    refine ⟨439634501722020154577325677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293089667814680103051550451 439634501722020154577325677)
    ·
      refine ⟨164862938145757557966497129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439634501722020154577325677 164862938145757557966497129)
      ·
        refine ⟨123647203609318168474872847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164862938145757557966497129 123647203609318168474872847)
        ·
          refine ⟨185470805413977252712309271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123647203609318168474872847 185470805413977252712309271)
          ·
            refine ⟨278206208120965879068463907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185470805413977252712309271 278206208120965879068463907)
            ·
              refine ⟨417309312181448818602695861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278206208120965879068463907 417309312181448818602695861)
              ·
                refine ⟨39122748017010826744002737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417309312181448818602695861 39122748017010826744002737)
                ·
                  refine ⟨29342061012758120058002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39122748017010826744002737 29342061012758120058002053)
                  ·
                    refine ⟨5501636439892147510875385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29342061012758120058002053 5501636439892147510875385)
                    ·
                      refine ⟨4126227329919110633156539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501636439892147510875385 4126227329919110633156539)
                      ·
                        rfl

theorem cell23_8035799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_8035799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035799 prefixEnd_8035799 := by exact prefixLift 8035799
  have htrace : WordTrace (prefixWord ++ tailWord_8035799) baseStart_8035799 baseEnd_8035799 := by
    simpa [prefixWord, tailWord_8035799, baseEnd_8035799] using wordTrace_append hprefix tailTrace_8035799
  have hstable : (prefixWord ++ tailWord_8035799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035799).length < 2 ^ (prefixWord ++ tailWord_8035799).sum := by decide
  have hdescent : baseEnd_8035799 < baseStart_8035799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035812 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_8035812 : Nat := 118140960795 + 8035812 * 2 ^ 59
def prefixEnd_8035812 : Nat := 4983230072969 + 3 ^ 40 * 8035812 * 2
def baseEnd_8035812 : Nat := 4126234005167619082293979

theorem tailTrace_8035812 : CollatzResearch.WordTrace tailWord_8035812 prefixEnd_8035812 4126234005167619082293979 := by
  unfold tailWord_8035812
  simp only [CollatzResearch.WordTrace]
  refine ⟨146545070981816503135886845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195393427975755337514515793 146545070981816503135886845)
  ·
    refine ⟨54954401618181188675957567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146545070981816503135886845 54954401618181188675957567)
    ·
      refine ⟨82431602427271783013936351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54954401618181188675957567 82431602427271783013936351)
      ·
        refine ⟨123647403640907674520904527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82431602427271783013936351 123647403640907674520904527)
        ·
          refine ⟨185471105461361511781356791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123647403640907674520904527 185471105461361511781356791)
          ·
            refine ⟨278206658192042267672035187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185471105461361511781356791 278206658192042267672035187)
            ·
              refine ⟨417309987288063401508052781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278206658192042267672035187 417309987288063401508052781)
              ·
                refine ⟨156491245233023775565519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417309987288063401508052781 156491245233023775565519793)
                ·
                  refine ⟨117368433924767831674139845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156491245233023775565519793 117368433924767831674139845)
                  ·
                    refine ⟨22006581360893968438901221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117368433924767831674139845 22006581360893968438901221)
                    ·
                      refine ⟨4126234005167619082293979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22006581360893968438901221 4126234005167619082293979)
                      ·
                        rfl

theorem cell23_8035812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_8035812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035812 prefixEnd_8035812 := by exact prefixLift 8035812
  have htrace : WordTrace (prefixWord ++ tailWord_8035812) baseStart_8035812 baseEnd_8035812 := by
    simpa [prefixWord, tailWord_8035812, baseEnd_8035812] using wordTrace_append hprefix tailTrace_8035812
  have hstable : (prefixWord ++ tailWord_8035812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035812).length < 2 ^ (prefixWord ++ tailWord_8035812).sum := by decide
  have hdescent : baseEnd_8035812 < baseStart_8035812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035869 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_8035869 : Nat := 118140960795 + 8035869 * 2 ^ 59
def prefixEnd_8035869 : Nat := 4983230072969 + 3 ^ 40 * 8035869 * 2
def baseEnd_8035869 : Nat := 1375421091188308453093739

theorem tailTrace_8035869 : CollatzResearch.WordTrace tailWord_8035869 prefixEnd_8035869 1375421091188308453093739 := by
  unfold tailWord_8035869
  simp only [CollatzResearch.WordTrace]
  refine ⟨293092220924426505006598661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195394813949617670004399107 293092220924426505006598661)
  ·
    refine ⟨54954791423329969688737249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293092220924426505006598661 54954791423329969688737249)
    ·
      refine ⟨41216093567497477266552937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54954791423329969688737249 41216093567497477266552937)
      ·
        refine ⟨30912070175623107949914703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41216093567497477266552937 30912070175623107949914703)
        ·
          refine ⟨46368105263434661924872055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30912070175623107949914703 46368105263434661924872055)
          ·
            refine ⟨69552157895151992887308083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46368105263434661924872055 69552157895151992887308083)
            ·
              refine ⟨104328236842727989330962125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69552157895151992887308083 104328236842727989330962125)
              ·
                refine ⟨39123088816022995999110797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104328236842727989330962125 39123088816022995999110797)
                ·
                  refine ⟨14671158306008623499666549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39123088816022995999110797 14671158306008623499666549)
                  ·
                    refine ⟨1375421091188308453093739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14671158306008623499666549 1375421091188308453093739)
                    ·
                      rfl

theorem cell23_8035869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_8035869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035869 prefixEnd_8035869 := by exact prefixLift 8035869
  have htrace : WordTrace (prefixWord ++ tailWord_8035869) baseStart_8035869 baseEnd_8035869 := by
    simpa [prefixWord, tailWord_8035869, baseEnd_8035869] using wordTrace_append hprefix tailTrace_8035869
  have hstable : (prefixWord ++ tailWord_8035869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035869).length < 2 ^ (prefixWord ++ tailWord_8035869).sum := by decide
  have hdescent : baseEnd_8035869 < baseStart_8035869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035909 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_8035909 : Nat := 118140960795 + 8035909 * 2 ^ 59
def prefixEnd_8035909 : Nat := 4983230072969 + 3 ^ 40 * 8035909 * 2
def baseEnd_8035909 : Nat := 4126283812791105202781033

theorem tailTrace_8035909 : CollatzResearch.WordTrace tailWord_8035909 prefixEnd_8035909 4126283812791105202781033 := by
  unfold tailWord_8035909
  simp only [CollatzResearch.WordTrace]
  refine ⟨293093679844281591838054781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195395786562854394558703187 293093679844281591838054781)
  ·
    refine ⟨109910129941605596939270543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293093679844281591838054781 109910129941605596939270543)
    ·
      refine ⟨164865194912408395408905815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109910129941605596939270543 164865194912408395408905815)
      ·
        refine ⟨247297792368612593113358723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164865194912408395408905815 247297792368612593113358723)
        ·
          refine ⟨370946688552918889670038085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247297792368612593113358723 370946688552918889670038085)
          ·
            refine ⟨69552504103672291813132141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370946688552918889670038085 69552504103672291813132141)
            ·
              refine ⟨26082189038877109429924553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69552504103672291813132141 26082189038877109429924553)
              ·
                refine ⟨19561641779157832072443415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26082189038877109429924553 19561641779157832072443415)
                ·
                  refine ⟨29342462668736748108665123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561641779157832072443415 29342462668736748108665123)
                  ·
                    refine ⟨44013694003105122162997685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29342462668736748108665123 44013694003105122162997685)
                    ·
                      refine ⟨4126283812791105202781033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44013694003105122162997685 4126283812791105202781033)
                      ·
                        rfl

theorem cell23_8035909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_8035909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035909 prefixEnd_8035909 := by exact prefixLift 8035909
  have htrace : WordTrace (prefixWord ++ tailWord_8035909) baseStart_8035909 baseEnd_8035909 := by
    simpa [prefixWord, tailWord_8035909, baseEnd_8035909] using wordTrace_append hprefix tailTrace_8035909
  have hstable : (prefixWord ++ tailWord_8035909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035909).length < 2 ^ (prefixWord ++ tailWord_8035909).sum := by decide
  have hdescent : baseEnd_8035909 < baseStart_8035909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035916 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_8035916 : Nat := 118140960795 + 8035916 * 2 ^ 59
def prefixEnd_8035916 : Nat := 4983230072969 + 3 ^ 40 * 8035916 * 2
def baseEnd_8035916 : Nat := 1375429135718562225131167

theorem tailTrace_8035916 : CollatzResearch.WordTrace tailWord_8035916 prefixEnd_8035916 1375429135718562225131167 := by
  unfold tailWord_8035916
  simp only [CollatzResearch.WordTrace]
  refine ⟨146546967577628116016779801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195395956770170821355706401 146546967577628116016779801)
  ·
    refine ⟨109910225683221087012584851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146546967577628116016779801 109910225683221087012584851)
    ·
      refine ⟨164865338524831630518877277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109910225683221087012584851 164865338524831630518877277)
      ·
        refine ⟨61824501946811861444578979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164865338524831630518877277 61824501946811861444578979)
        ·
          refine ⟨92736752920217792166868469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61824501946811861444578979 92736752920217792166868469)
          ·
            refine ⟨8694070586270418015643919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92736752920217792166868469 8694070586270418015643919)
            ·
              refine ⟨13041105879405627023465879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694070586270418015643919 13041105879405627023465879)
              ·
                refine ⟨19561658819108440535198819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041105879405627023465879 19561658819108440535198819)
                ·
                  refine ⟨29342488228662660802798229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561658819108440535198819 29342488228662660802798229)
                  ·
                    refine ⟨1375429135718562225131167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29342488228662660802798229 1375429135718562225131167)
                    ·
                      rfl

theorem cell23_8035916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_8035916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035916 prefixEnd_8035916 := by exact prefixLift 8035916
  have htrace : WordTrace (prefixWord ++ tailWord_8035916) baseStart_8035916 baseEnd_8035916 := by
    simpa [prefixWord, tailWord_8035916, baseEnd_8035916] using wordTrace_append hprefix tailTrace_8035916
  have hstable : (prefixWord ++ tailWord_8035916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035916).length < 2 ^ (prefixWord ++ tailWord_8035916).sum := by decide
  have hdescent : baseEnd_8035916 < baseStart_8035916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035957 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_8035957 : Nat := 118140960795 + 8035957 * 2 ^ 59
def prefixEnd_8035957 : Nat := 4983230072969 + 3 ^ 40 * 8035957 * 2
def baseEnd_8035957 : Nat := 4126308459862521014980813

theorem tailTrace_8035957 : CollatzResearch.WordTrace tailWord_8035957 prefixEnd_8035957 4126308459862521014980813 := by
  unfold tailWord_8035957
  simp only [CollatzResearch.WordTrace]
  refine ⟨293095430548107696035802125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195396953698738464023868083 293095430548107696035802125)
  ·
    refine ⟨109910786455540386013425797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293095430548107696035802125 109910786455540386013425797)
    ·
      refine ⟨20608272460413822377517337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109910786455540386013425797 20608272460413822377517337)
      ·
        refine ⟨15456204345310366783138003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20608272460413822377517337 15456204345310366783138003)
        ·
          refine ⟨23184306517965550174707005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15456204345310366783138003 23184306517965550174707005)
          ·
            refine ⟨8694114944237081315515127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23184306517965550174707005 8694114944237081315515127)
            ·
              refine ⟨13041172416355621973272691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694114944237081315515127 13041172416355621973272691)
              ·
                refine ⟨19561758624533432959909037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041172416355621973272691 19561758624533432959909037)
                ·
                  refine ⟨7335659484200037359965889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19561758624533432959909037 7335659484200037359965889)
                  ·
                    refine ⟨5501744613150028019974417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7335659484200037359965889 5501744613150028019974417)
                    ·
                      refine ⟨4126308459862521014980813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501744613150028019974417 4126308459862521014980813)
                      ·
                        rfl

theorem cell23_8035957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_8035957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035957 prefixEnd_8035957 := by exact prefixLift 8035957
  have htrace : WordTrace (prefixWord ++ tailWord_8035957) baseStart_8035957 baseEnd_8035957 := by
    simpa [prefixWord, tailWord_8035957, baseEnd_8035957] using wordTrace_append hprefix tailTrace_8035957
  have hstable : (prefixWord ++ tailWord_8035957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035957).length < 2 ^ (prefixWord ++ tailWord_8035957).sum := by decide
  have hdescent : baseEnd_8035957 < baseStart_8035957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8035973 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_8035973 : Nat := 118140960795 + 8035973 * 2 ^ 59
def prefixEnd_8035973 : Nat := 4983230072969 + 3 ^ 40 * 8035973 * 2
def baseEnd_8035973 : Nat := 4126316675552992952380739

theorem tailTrace_8035973 : CollatzResearch.WordTrace tailWord_8035973 prefixEnd_8035973 4126316675552992952380739 := by
  unfold tailWord_8035973
  simp only [CollatzResearch.WordTrace]
  refine ⟨293096014116049730768384573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195397342744033153845589715 293096014116049730768384573)
  ·
    refine ⟨109911005293518649038144215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293096014116049730768384573 109911005293518649038144215)
    ·
      refine ⟨164866507940277973557216323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109911005293518649038144215 164866507940277973557216323)
      ·
        refine ⟨247299761910416960335824485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164866507940277973557216323 247299761910416960335824485)
        ·
          refine ⟨46368705358203180062967091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247299761910416960335824485 46368705358203180062967091)
          ·
            refine ⟨69553058037304770094450637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46368705358203180062967091 69553058037304770094450637)
            ·
              refine ⟨26082396763989288785418989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69553058037304770094450637 26082396763989288785418989)
              ·
                refine ⟨9780898786495983294532121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26082396763989288785418989 9780898786495983294532121)
                ·
                  refine ⟨7335674089871987470899091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9780898786495983294532121 7335674089871987470899091)
                  ·
                    refine ⟨11003511134807981206348637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335674089871987470899091 11003511134807981206348637)
                    ·
                      refine ⟨4126316675552992952380739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11003511134807981206348637 4126316675552992952380739)
                      ·
                        rfl

theorem cell23_8035973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_8035973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8035973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8035973 prefixEnd_8035973 := by exact prefixLift 8035973
  have htrace : WordTrace (prefixWord ++ tailWord_8035973) baseStart_8035973 baseEnd_8035973 := by
    simpa [prefixWord, tailWord_8035973, baseEnd_8035973] using wordTrace_append hprefix tailTrace_8035973
  have hstable : (prefixWord ++ tailWord_8035973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8035973).length < 2 ^ (prefixWord ++ tailWord_8035973).sum := by decide
  have hdescent : baseEnd_8035973 < baseStart_8035973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8035973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036013 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_8036013 : Nat := 118140960795 + 8036013 * 2 ^ 59
def prefixEnd_8036013 : Nat := 4983230072969 + 3 ^ 40 * 8036013 * 2
def baseEnd_8036013 : Nat := 4126337214779172795880555

theorem tailTrace_8036013 : CollatzResearch.WordTrace tailWord_8036013 prefixEnd_8036013 4126337214779172795880555 := by
  unfold tailWord_8036013
  simp only [CollatzResearch.WordTrace]
  refine ⟨293097473035904817599840693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195398315357269878399893795 293097473035904817599840693)
  ·
    refine ⟨27477888097116076649985065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293097473035904817599840693 27477888097116076649985065)
    ·
      refine ⟨20608416072837057487488799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27477888097116076649985065 20608416072837057487488799)
      ·
        refine ⟨30912624109255586231233199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20608416072837057487488799 30912624109255586231233199)
        ·
          refine ⟨46368936163883379346849799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30912624109255586231233199 46368936163883379346849799)
          ·
            refine ⟨69553404245825069020274699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46368936163883379346849799 69553404245825069020274699)
            ·
              refine ⟨104330106368737603530412049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69553404245825069020274699 104330106368737603530412049)
              ·
                refine ⟨78247579776553202647809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104330106368737603530412049 78247579776553202647809037)
                ·
                  refine ⟨29342842416207450992928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78247579776553202647809037 29342842416207450992928389)
                  ·
                    refine ⟨5501782953038897061174073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29342842416207450992928389 5501782953038897061174073)
                    ·
                      refine ⟨4126337214779172795880555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501782953038897061174073 4126337214779172795880555)
                      ·
                        rfl

theorem cell23_8036013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_8036013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036013 prefixEnd_8036013 := by exact prefixLift 8036013
  have htrace : WordTrace (prefixWord ++ tailWord_8036013) baseStart_8036013 baseEnd_8036013 := by
    simpa [prefixWord, tailWord_8036013, baseEnd_8036013] using wordTrace_append hprefix tailTrace_8036013
  have hstable : (prefixWord ++ tailWord_8036013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036013).length < 2 ^ (prefixWord ++ tailWord_8036013).sum := by decide
  have hdescent : baseEnd_8036013 < baseStart_8036013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
