import V185TrunkScan23Chunk1021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6050190 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6050190 : Nat := 118140960795 + 6050190 * 2 ^ 59
def prefixEnd_6050190 : Nat := 4983230072969 + 3 ^ 40 * 6050190 * 2
def baseEnd_6050190 : Nat := 3106655521025788837500689

theorem tailTrace_6050190 : CollatzResearch.WordTrace tailWord_6050190 prefixEnd_6050190 3106655521025788837500689 := by
  unfold tailWord_6050190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583569743900299379084503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147112371967468263355117349 27583569743900299379084503)
  ·
    refine ⟨41375354615850449068626755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27583569743900299379084503 41375354615850449068626755)
    ·
      refine ⟨62063031923775673602940133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41375354615850449068626755 62063031923775673602940133)
      ·
        refine ⟨11636818485707938800551275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62063031923775673602940133 11636818485707938800551275)
        ·
          refine ⟨17455227728561908200826913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636818485707938800551275 17455227728561908200826913)
          ·
            refine ⟨13091420796421431150620185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17455227728561908200826913 13091420796421431150620185)
            ·
              refine ⟨9818565597316073362965139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13091420796421431150620185 9818565597316073362965139)
              ·
                refine ⟨14727848395974110044447709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818565597316073362965139 14727848395974110044447709)
                ·
                  refine ⟨5522943148490291266667891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14727848395974110044447709 5522943148490291266667891)
                  ·
                    refine ⟨8284414722735436900001837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522943148490291266667891 8284414722735436900001837)
                    ·
                      refine ⟨3106655521025788837500689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284414722735436900001837 3106655521025788837500689)
                      ·
                        rfl

theorem cell23_6050190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6050190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050190 prefixEnd_6050190 := by exact prefixLift 6050190
  have htrace : WordTrace (prefixWord ++ tailWord_6050190) baseStart_6050190 baseEnd_6050190 := by
    simpa [prefixWord, tailWord_6050190, baseEnd_6050190] using wordTrace_append hprefix tailTrace_6050190
  have hstable : (prefixWord ++ tailWord_6050190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050190).length < 2 ^ (prefixWord ++ tailWord_6050190).sum := by decide
  have hdescent : baseEnd_6050190 < baseStart_6050190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050199 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6050199 : Nat := 118140960795 + 6050199 * 2 ^ 59
def prefixEnd_6050199 : Nat := 4983230072969 + 3 ^ 40 * 6050199 * 2
def baseEnd_6050199 : Nat := 3106660142351679302288147

theorem tailTrace_6050199 : CollatzResearch.WordTrace tailWord_6050199 prefixEnd_6050199 3106660142351679302288147 := by
  unfold tailWord_6050199
  simp only [CollatzResearch.WordTrace]
  refine ⟨220668886208169789569753651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147112590805446526379835767 220668886208169789569753651)
  ·
    refine ⟨331003329312254684354630477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220668886208169789569753651 331003329312254684354630477)
    ·
      refine ⟨124126248492095506632986429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331003329312254684354630477 124126248492095506632986429)
      ·
        refine ⟨46547343184535814987369911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124126248492095506632986429 46547343184535814987369911)
        ·
          refine ⟨69821014776803722481054867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46547343184535814987369911 69821014776803722481054867)
          ·
            refine ⟨104731522165205583721582301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69821014776803722481054867 104731522165205583721582301)
            ·
              refine ⟨39274320811952093895593363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104731522165205583721582301 39274320811952093895593363)
              ·
                refine ⟨58911481217928140843390045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39274320811952093895593363 58911481217928140843390045)
                ·
                  refine ⟨22091805456723052816271267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58911481217928140843390045 22091805456723052816271267)
                  ·
                    refine ⟨33137708185084579224406901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22091805456723052816271267 33137708185084579224406901)
                    ·
                      refine ⟨3106660142351679302288147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33137708185084579224406901 3106660142351679302288147)
                      ·
                        rfl

theorem cell23_6050199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6050199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050199 prefixEnd_6050199 := by exact prefixLift 6050199
  have htrace : WordTrace (prefixWord ++ tailWord_6050199) baseStart_6050199 baseEnd_6050199 := by
    simpa [prefixWord, tailWord_6050199, baseEnd_6050199] using wordTrace_append hprefix tailTrace_6050199
  have hstable : (prefixWord ++ tailWord_6050199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050199).length < 2 ^ (prefixWord ++ tailWord_6050199).sum := by decide
  have hdescent : baseEnd_6050199 < baseStart_6050199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050213 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_6050213 : Nat := 118140960795 + 6050213 * 2 ^ 59
def prefixEnd_6050213 : Nat := 4983230072969 + 3 ^ 40 * 6050213 * 2
def baseEnd_6050213 : Nat := 3106667331080842247513083

theorem tailTrace_6050213 : CollatzResearch.WordTrace tailWord_6050213 prefixEnd_6050213 3106667331080842247513083 := by
  unfold tailWord_6050213
  simp only [CollatzResearch.WordTrace]
  refine ⟨220669396830119069960763293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147112931220079379973842195 220669396830119069960763293)
  ·
    refine ⟨82751023811294651235286235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220669396830119069960763293 82751023811294651235286235)
    ·
      refine ⟨124126535716941976852929353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82751023811294651235286235 124126535716941976852929353)
      ·
        refine ⟨93094901787706482639697015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124126535716941976852929353 93094901787706482639697015)
        ·
          refine ⟨139642352681559723959545523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93094901787706482639697015 139642352681559723959545523)
          ·
            refine ⟨209463529022339585939318285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139642352681559723959545523 209463529022339585939318285)
            ·
              refine ⟨78548823383377344727244357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209463529022339585939318285 78548823383377344727244357)
              ·
                refine ⟨14727904384383252136358317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78548823383377344727244357 14727904384383252136358317)
                ·
                  refine ⟨5522964144143719551134369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14727904384383252136358317 5522964144143719551134369)
                  ·
                    refine ⟨4142223108107789663350777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5522964144143719551134369 4142223108107789663350777)
                    ·
                      refine ⟨3106667331080842247513083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142223108107789663350777 3106667331080842247513083)
                      ·
                        rfl

theorem cell23_6050213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_6050213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050213 prefixEnd_6050213 := by exact prefixLift 6050213
  have htrace : WordTrace (prefixWord ++ tailWord_6050213) baseStart_6050213 baseEnd_6050213 := by
    simpa [prefixWord, tailWord_6050213, baseEnd_6050213] using wordTrace_append hprefix tailTrace_6050213
  have hstable : (prefixWord ++ tailWord_6050213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050213).length < 2 ^ (prefixWord ++ tailWord_6050213).sum := by decide
  have hdescent : baseEnd_6050213 < baseStart_6050213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050233 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6050233 : Nat := 118140960795 + 6050233 * 2 ^ 59
def prefixEnd_6050233 : Nat := 4983230072969 + 3 ^ 40 * 6050233 * 2
def baseEnd_6050233 : Nat := 3106677600693932169262991

theorem tailTrace_6050233 : CollatzResearch.WordTrace tailWord_6050233 prefixEnd_6050233 3106677600693932169262991 := by
  unfold tailWord_6050233
  simp only [CollatzResearch.WordTrace]
  refine ⟨220670126290046613376491353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147113417526697742250994235 220670126290046613376491353)
  ·
    refine ⟨165502594717534960032368515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220670126290046613376491353 165502594717534960032368515)
    ·
      refine ⟨248253892076302440048552773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165502594717534960032368515 248253892076302440048552773)
      ·
        refine ⟨46547604764306707509103645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248253892076302440048552773 46547604764306707509103645)
        ·
          refine ⟨17455351786615015315913867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46547604764306707509103645 17455351786615015315913867)
          ·
            refine ⟨26183027679922522973870801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17455351786615015315913867 26183027679922522973870801)
            ·
              refine ⟨19637270759941892230403101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26183027679922522973870801 19637270759941892230403101)
              ·
                refine ⟨7363976534978209586401163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19637270759941892230403101 7363976534978209586401163)
                ·
                  refine ⟨11045964802467314379601745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363976534978209586401163 11045964802467314379601745)
                  ·
                    refine ⟨8284473601850485784701309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11045964802467314379601745 8284473601850485784701309)
                    ·
                      refine ⟨3106677600693932169262991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284473601850485784701309 3106677600693932169262991)
                      ·
                        rfl

theorem cell23_6050233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6050233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050233 prefixEnd_6050233 := by exact prefixLift 6050233
  have htrace : WordTrace (prefixWord ++ tailWord_6050233) baseStart_6050233 baseEnd_6050233 := by
    simpa [prefixWord, tailWord_6050233, baseEnd_6050233] using wordTrace_append hprefix tailTrace_6050233
  have hstable : (prefixWord ++ tailWord_6050233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050233).length < 2 ^ (prefixWord ++ tailWord_6050233).sum := by decide
  have hdescent : baseEnd_6050233 < baseStart_6050233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050236 : List Nat := [2, 2, 2, 4, 1, 3, 9]
def baseStart_6050236 : Nat := 118140960795 + 6050236 * 2 ^ 59
def prefixEnd_6050236 : Nat := 4983230072969 + 3 ^ 40 * 6050236 * 2
def baseEnd_6050236 : Nat := 38354063470813526636117

theorem tailTrace_6050236 : CollatzResearch.WordTrace tailWord_6050236 prefixEnd_6050236 38354063470813526636117 := by
  unfold tailWord_6050236
  simp only [CollatzResearch.WordTrace]
  refine ⟨110335117854517872444425281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147113490472690496592567041 110335117854517872444425281)
  ·
    refine ⟨82751338390888404333318961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110335117854517872444425281 82751338390888404333318961)
    ·
      refine ⟨62063503793166303249989221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82751338390888404333318961 62063503793166303249989221)
      ·
        refine ⟨11636906961218681859372979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62063503793166303249989221 11636906961218681859372979)
        ·
          refine ⟨17455360441828022789059469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636906961218681859372979 17455360441828022789059469)
          ·
            refine ⟨6545760165685508545897301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17455360441828022789059469 6545760165685508545897301)
            ·
              refine ⟨38354063470813526636117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6545760165685508545897301 38354063470813526636117)
              ·
                rfl

theorem cell23_6050236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 9].length) (baseStart_6050236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050236 prefixEnd_6050236 := by exact prefixLift 6050236
  have htrace : WordTrace (prefixWord ++ tailWord_6050236) baseStart_6050236 baseEnd_6050236 := by
    simpa [prefixWord, tailWord_6050236, baseEnd_6050236] using wordTrace_append hprefix tailTrace_6050236
  have hstable : (prefixWord ++ tailWord_6050236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050236).length < 2 ^ (prefixWord ++ tailWord_6050236).sum := by decide
  have hdescent : baseEnd_6050236 < baseStart_6050236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050241 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6050241 : Nat := 118140960795 + 6050241 * 2 ^ 59
def prefixEnd_6050241 : Nat := 4983230072969 + 3 ^ 40 * 6050241 * 2
def baseEnd_6050241 : Nat := 3106681708539168137962955

theorem tailTrace_6050241 : CollatzResearch.WordTrace tailWord_6050241 prefixEnd_6050241 3106681708539168137962955 := by
  unfold tailWord_6050241
  simp only [CollatzResearch.WordTrace]
  refine ⟨220670418074017630742782577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147113612049345087161855051 220670418074017630742782577)
  ·
    refine ⟨165502813555513223057086933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220670418074017630742782577 165502813555513223057086933)
    ·
      refine ⟨3878972192707341165400475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 165502813555513223057086933 3878972192707341165400475)
      ·
        refine ⟨5818458289061011748100713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878972192707341165400475 5818458289061011748100713)
        ·
          refine ⟨4363843716795758811075535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5818458289061011748100713 4363843716795758811075535)
          ·
            refine ⟨6545765575193638216613303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363843716795758811075535 6545765575193638216613303)
            ·
              refine ⟨9818648362790457324919955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545765575193638216613303 9818648362790457324919955)
              ·
                refine ⟨14727972544185685987379933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818648362790457324919955 14727972544185685987379933)
                ·
                  refine ⟨5522989704069632245267475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14727972544185685987379933 5522989704069632245267475)
                  ·
                    refine ⟨8284484556104448367901213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5522989704069632245267475 8284484556104448367901213)
                    ·
                      refine ⟨3106681708539168137962955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284484556104448367901213 3106681708539168137962955)
                      ·
                        rfl

theorem cell23_6050241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6050241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050241 prefixEnd_6050241 := by exact prefixLift 6050241
  have htrace : WordTrace (prefixWord ++ tailWord_6050241) baseStart_6050241 baseEnd_6050241 := by
    simpa [prefixWord, tailWord_6050241, baseEnd_6050241] using wordTrace_append hprefix tailTrace_6050241
  have hstable : (prefixWord ++ tailWord_6050241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050241).length < 2 ^ (prefixWord ++ tailWord_6050241).sum := by decide
  have hdescent : baseEnd_6050241 < baseStart_6050241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050273 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_6050273 : Nat := 118140960795 + 6050273 * 2 ^ 59
def prefixEnd_6050273 : Nat := 4983230072969 + 3 ^ 40 * 6050273 * 2
def baseEnd_6050273 : Nat := 3106698139920112012762807

theorem tailTrace_6050273 : CollatzResearch.WordTrace tailWord_6050273 prefixEnd_6050273 3106698139920112012762807 := by
  unfold tailWord_6050273
  simp only [CollatzResearch.WordTrace]
  refine ⟨220671585209901700207947473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147114390139934466805298315 220671585209901700207947473)
  ·
    refine ⟨165503688907426275155960605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220671585209901700207947473 165503688907426275155960605)
    ·
      refine ⟨62063883340284853183485227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165503688907426275155960605 62063883340284853183485227)
      ·
        refine ⟨93095825010427279775227841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62063883340284853183485227 93095825010427279775227841)
        ·
          refine ⟨69821868757820459831420881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93095825010427279775227841 69821868757820459831420881)
          ·
            refine ⟨52366401568365344873565661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69821868757820459831420881 52366401568365344873565661)
            ·
              refine ⟨19637400588137004327587123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52366401568365344873565661 19637400588137004327587123)
              ·
                refine ⟨29456100882205506491380685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19637400588137004327587123 29456100882205506491380685)
                ·
                  refine ⟨11046037830827064934267757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29456100882205506491380685 11046037830827064934267757)
                  ·
                    refine ⟨4142264186560149350350409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11046037830827064934267757 4142264186560149350350409)
                    ·
                      refine ⟨3106698139920112012762807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142264186560149350350409 3106698139920112012762807)
                      ·
                        rfl

theorem cell23_6050273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_6050273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050273 prefixEnd_6050273 := by exact prefixLift 6050273
  have htrace : WordTrace (prefixWord ++ tailWord_6050273) baseStart_6050273 baseEnd_6050273 := by
    simpa [prefixWord, tailWord_6050273, baseEnd_6050273] using wordTrace_append hprefix tailTrace_6050273
  have hstable : (prefixWord ++ tailWord_6050273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050273).length < 2 ^ (prefixWord ++ tailWord_6050273).sum := by decide
  have hdescent : baseEnd_6050273 < baseStart_6050273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050316 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6050316 : Nat := 118140960795 + 6050316 * 2 ^ 59
def prefixEnd_6050316 : Nat := 4983230072969 + 3 ^ 40 * 6050316 * 2
def baseEnd_6050316 : Nat := 3106720219588255344525109

theorem tailTrace_6050316 : CollatzResearch.WordTrace tailWord_6050316 prefixEnd_6050316 3106720219588255344525109 := by
  unfold tailWord_6050316
  simp only [CollatzResearch.WordTrace]
  refine ⟨110336576774372959275881401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147115435699163945701175201 110336576774372959275881401)
  ·
    refine ⟨82752432580779719456911051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110336576774372959275881401 82752432580779719456911051)
    ·
      refine ⟨124128648871169579185366577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82752432580779719456911051 124128648871169579185366577)
      ·
        refine ⟨93096486653377184389024933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124128648871169579185366577 93096486653377184389024933)
        ·
          refine ⟨17455591247508222072942175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93096486653377184389024933 17455591247508222072942175)
          ·
            refine ⟨26183386871262333109413263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17455591247508222072942175 26183386871262333109413263)
            ·
              refine ⟨39275080306893499664119895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26183386871262333109413263 39275080306893499664119895)
              ·
                refine ⟨58912620460340249496179843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39275080306893499664119895 58912620460340249496179843)
                ·
                  refine ⟨88368930690510374244269765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58912620460340249496179843 88368930690510374244269765)
                  ·
                    refine ⟨16569174504470695170800581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88368930690510374244269765 16569174504470695170800581)
                    ·
                      refine ⟨3106720219588255344525109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16569174504470695170800581 3106720219588255344525109)
                      ·
                        rfl

theorem cell23_6050316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6050316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050316 prefixEnd_6050316 := by exact prefixLift 6050316
  have htrace : WordTrace (prefixWord ++ tailWord_6050316) baseStart_6050316 baseEnd_6050316 := by
    simpa [prefixWord, tailWord_6050316, baseEnd_6050316] using wordTrace_append hprefix tailTrace_6050316
  have hstable : (prefixWord ++ tailWord_6050316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050316).length < 2 ^ (prefixWord ++ tailWord_6050316).sum := by decide
  have hdescent : baseEnd_6050316 < baseStart_6050316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_6050329 : Nat := 118140960795 + 6050329 * 2 ^ 59
def prefixEnd_6050329 : Nat := 4983230072969 + 3 ^ 40 * 6050329 * 2
def baseEnd_6050329 : Nat := 3106726894836763793662549

theorem tailTrace_6050329 : CollatzResearch.WordTrace tailWord_6050329 prefixEnd_6050329 3106726894836763793662549 := by
  unfold tailWord_6050329
  simp only [CollatzResearch.WordTrace]
  refine ⟨220673627697698821771986041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147115751798465881181324027 220673627697698821771986041)
  ·
    refine ⟨165505220773274116328989531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220673627697698821771986041 165505220773274116328989531)
    ·
      refine ⟨248257831159911174493484297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165505220773274116328989531 248257831159911174493484297)
      ·
        refine ⟨186193373369933380870113223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248257831159911174493484297 186193373369933380870113223)
        ·
          refine ⟨279290060054900071305169835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186193373369933380870113223 279290060054900071305169835)
          ·
            refine ⟨418935090082350106957754753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279290060054900071305169835 418935090082350106957754753)
            ·
              refine ⟨314201317561762580218316065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418935090082350106957754753 314201317561762580218316065)
              ·
                refine ⟨235650988171321935163737049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314201317561762580218316065 235650988171321935163737049)
                ·
                  refine ⟨176738241128491451372802787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235650988171321935163737049 176738241128491451372802787)
                  ·
                    refine ⟨265107361692737177059204181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176738241128491451372802787 265107361692737177059204181)
                    ·
                      refine ⟨3106726894836763793662549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265107361692737177059204181 3106726894836763793662549)
                      ·
                        rfl

theorem cell23_6050329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_6050329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050329 prefixEnd_6050329 := by exact prefixLift 6050329
  have htrace : WordTrace (prefixWord ++ tailWord_6050329) baseStart_6050329 baseEnd_6050329 := by
    simpa [prefixWord, tailWord_6050329, baseEnd_6050329] using wordTrace_append hprefix tailTrace_6050329
  have hstable : (prefixWord ++ tailWord_6050329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050329).length < 2 ^ (prefixWord ++ tailWord_6050329).sum := by decide
  have hdescent : baseEnd_6050329 < baseStart_6050329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050386 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6050386 : Nat := 118140960795 + 6050386 * 2 ^ 59
def prefixEnd_6050386 : Nat := 4983230072969 + 3 ^ 40 * 6050386 * 2
def baseEnd_6050386 : Nat := 1035585387744690023549929

theorem tailTrace_6050386 : CollatzResearch.WordTrace tailWord_6050386 prefixEnd_6050386 1035585387744690023549929 := by
  unfold tailWord_6050386
  simp only [CollatzResearch.WordTrace]
  refine ⟨55168926664623080126702753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147117137772328213671207341 55168926664623080126702753)
  ·
    refine ⟨41376694998467310095027065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55168926664623080126702753 41376694998467310095027065)
    ·
      refine ⟨31032521248850482571270299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41376694998467310095027065 31032521248850482571270299)
      ·
        refine ⟨46548781873275723856905449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31032521248850482571270299 46548781873275723856905449)
        ·
          refine ⟨34911586404956792892679087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46548781873275723856905449 34911586404956792892679087)
          ·
            refine ⟨52367379607435189339018631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34911586404956792892679087 52367379607435189339018631)
            ·
              refine ⟨78551069411152784008527947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52367379607435189339018631 78551069411152784008527947)
              ·
                refine ⟨117826604116729176012791921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78551069411152784008527947 117826604116729176012791921)
                ·
                  refine ⟨88369953087546882009593941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117826604116729176012791921 88369953087546882009593941)
                  ·
                    refine ⟨1035585387744690023549929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88369953087546882009593941 1035585387744690023549929)
                    ·
                      rfl

theorem cell23_6050386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6050386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050386 prefixEnd_6050386 := by exact prefixLift 6050386
  have htrace : WordTrace (prefixWord ++ tailWord_6050386) baseStart_6050386 baseEnd_6050386 := by
    simpa [prefixWord, tailWord_6050386, baseEnd_6050386] using wordTrace_append hprefix tailTrace_6050386
  have hstable : (prefixWord ++ tailWord_6050386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050386).length < 2 ^ (prefixWord ++ tailWord_6050386).sum := by decide
  have hdescent : baseEnd_6050386 < baseStart_6050386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050433 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 6]
def baseStart_6050433 : Nat := 118140960795 + 6050433 * 2 ^ 59
def prefixEnd_6050433 : Nat := 4983230072969 + 3 ^ 40 * 6050433 * 2
def baseEnd_6050433 : Nat := 345197810758314598529119

theorem tailTrace_6050433 : CollatzResearch.WordTrace tailWord_6050433 prefixEnd_6050433 345197810758314598529119 := by
  unfold tailWord_6050433
  simp only [CollatzResearch.WordTrace]
  refine ⟨220677420889322047533771953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147118280592881365022514635 220677420889322047533771953)
  ·
    refine ⟨165508065666991535650328965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220677420889322047533771953 165508065666991535650328965)
    ·
      refine ⟨31032762312560912934436681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165508065666991535650328965 31032762312560912934436681)
      ·
        refine ⟨23274571734420684700827511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31032762312560912934436681 23274571734420684700827511)
        ·
          refine ⟨34911857601631027051241267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23274571734420684700827511 34911857601631027051241267)
          ·
            refine ⟨52367786402446540576861901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34911857601631027051241267 52367786402446540576861901)
            ·
              refine ⟨19637919900917452716323213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52367786402446540576861901 19637919900917452716323213)
              ·
                refine ⟨7364219962844044768621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19637919900917452716323213 7364219962844044768621205)
                ·
                  refine ⟨345197810758314598529119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7364219962844044768621205 345197810758314598529119)
                  ·
                    rfl

theorem cell23_6050433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_6050433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050433 prefixEnd_6050433 := by exact prefixLift 6050433
  have htrace : WordTrace (prefixWord ++ tailWord_6050433) baseStart_6050433 baseEnd_6050433 := by
    simpa [prefixWord, tailWord_6050433, baseEnd_6050433] using wordTrace_append hprefix tailTrace_6050433
  have hstable : (prefixWord ++ tailWord_6050433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050433).length < 2 ^ (prefixWord ++ tailWord_6050433).sum := by decide
  have hdescent : baseEnd_6050433 < baseStart_6050433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050483 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4]
def baseStart_6050483 : Nat := 118140960795 + 6050483 * 2 ^ 59
def prefixEnd_6050483 : Nat := 4983230072969 + 3 ^ 40 * 6050483 * 2
def baseEnd_6050483 : Nat := 3106805970857556191136841

theorem tailTrace_6050483 : CollatzResearch.WordTrace tailWord_6050483 prefixEnd_6050483 3106805970857556191136841 := by
  unfold tailWord_6050483
  simp only [CollatzResearch.WordTrace]
  refine ⟨220679244539140906073092103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147119496359427270715394735 220679244539140906073092103)
  ·
    refine ⟨331018866808711359109638155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220679244539140906073092103 331018866808711359109638155)
    ·
      refine ⟨496528300213067038664457233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331018866808711359109638155 496528300213067038664457233)
      ·
        refine ⟨372396225159800278998342925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496528300213067038664457233 372396225159800278998342925)
        ·
          refine ⟨139648584434925104624378597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372396225159800278998342925 139648584434925104624378597)
          ·
            refine ⟨26184109581548457117070987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139648584434925104624378597 26184109581548457117070987)
            ·
              refine ⟨39276164372322685675606481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26184109581548457117070987 39276164372322685675606481)
              ·
                refine ⟨29457123279242014256704861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39276164372322685675606481 29457123279242014256704861)
                ·
                  refine ⟨11046421229715755346264323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29457123279242014256704861 11046421229715755346264323)
                  ·
                    refine ⟨16569631844573633019396485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11046421229715755346264323 16569631844573633019396485)
                    ·
                      refine ⟨3106805970857556191136841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16569631844573633019396485 3106805970857556191136841)
                      ·
                        rfl

theorem cell23_6050483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_6050483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050483 prefixEnd_6050483 := by exact prefixLift 6050483
  have htrace : WordTrace (prefixWord ++ tailWord_6050483) baseStart_6050483 baseEnd_6050483 := by
    simpa [prefixWord, tailWord_6050483, baseEnd_6050483] using wordTrace_append hprefix tailTrace_6050483
  have hstable : (prefixWord ++ tailWord_6050483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050483).length < 2 ^ (prefixWord ++ tailWord_6050483).sum := by decide
  have hdescent : baseEnd_6050483 < baseStart_6050483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050493 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_6050493 : Nat := 118140960795 + 6050493 * 2 ^ 59
def prefixEnd_6050493 : Nat := 4983230072969 + 3 ^ 40 * 6050493 * 2
def baseEnd_6050493 : Nat := 1035603701888033717337265

theorem tailTrace_6050493 : CollatzResearch.WordTrace tailWord_6050493 prefixEnd_6050493 1035603701888033717337265 := by
  unfold tailWord_6050493
  simp only [CollatzResearch.WordTrace]
  refine ⟨220679609269104677780956133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147119739512736451853970755 220679609269104677780956133)
  ·
    refine ⟨41377426737957127083929275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220679609269104677780956133 41377426737957127083929275)
    ·
      refine ⟨62066140106935690625893913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41377426737957127083929275 62066140106935690625893913)
      ·
        refine ⟨46549605080201767969420435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62066140106935690625893913 46549605080201767969420435)
        ·
          refine ⟨69824407620302651954130653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46549605080201767969420435 69824407620302651954130653)
          ·
            refine ⟨26184152857613494482798995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69824407620302651954130653 26184152857613494482798995)
            ·
              refine ⟨39276229286420241724198493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26184152857613494482798995 39276229286420241724198493)
              ·
                refine ⟨14728585982407590646574435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39276229286420241724198493 14728585982407590646574435)
                ·
                  refine ⟨22092878973611385969861653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14728585982407590646574435 22092878973611385969861653)
                  ·
                    refine ⟨1035603701888033717337265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22092878973611385969861653 1035603701888033717337265)
                    ·
                      rfl

theorem cell23_6050493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_6050493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050493 prefixEnd_6050493 := by exact prefixLift 6050493
  have htrace : WordTrace (prefixWord ++ tailWord_6050493) baseStart_6050493 baseEnd_6050493 := by
    simpa [prefixWord, tailWord_6050493, baseEnd_6050493] using wordTrace_append hprefix tailTrace_6050493
  have hstable : (prefixWord ++ tailWord_6050493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050493).length < 2 ^ (prefixWord ++ tailWord_6050493).sum := by decide
  have hdescent : baseEnd_6050493 < baseStart_6050493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050500 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6050500 : Nat := 118140960795 + 6050500 * 2 ^ 59
def prefixEnd_6050500 : Nat := 4983230072969 + 3 ^ 40 * 6050500 * 2
def baseEnd_6050500 : Nat := 3106814700028682624624263

theorem tailTrace_6050500 : CollatzResearch.WordTrace tailWord_6050500 prefixEnd_6050500 3106814700028682624624263 := by
  unfold tailWord_6050500
  simp only [CollatzResearch.WordTrace]
  refine ⟨110339932290039658988230477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147119909720052878650973969 110339932290039658988230477)
  ·
    refine ⟨41377474608764872120586429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110339932290039658988230477 41377474608764872120586429)
    ·
      refine ⟨15516552978286827045219911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41377474608764872120586429 15516552978286827045219911)
      ·
        refine ⟨23274829467430240567829867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15516552978286827045219911 23274829467430240567829867)
        ·
          refine ⟨34912244201145360851744801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23274829467430240567829867 34912244201145360851744801)
          ·
            refine ⟨26184183150859020638808601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34912244201145360851744801 26184183150859020638808601)
            ·
              refine ⟨19638137363144265479106451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26184183150859020638808601 19638137363144265479106451)
              ·
                refine ⟨29457206044716398218659677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19638137363144265479106451 29457206044716398218659677)
                ·
                  refine ⟨11046452266768649331997379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29457206044716398218659677 11046452266768649331997379)
                  ·
                    refine ⟨16569678400152973997996069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11046452266768649331997379 16569678400152973997996069)
                    ·
                      refine ⟨3106814700028682624624263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16569678400152973997996069 3106814700028682624624263)
                      ·
                        rfl

theorem cell23_6050500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6050500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050500 prefixEnd_6050500 := by exact prefixLift 6050500
  have htrace : WordTrace (prefixWord ++ tailWord_6050500) baseStart_6050500 baseEnd_6050500 := by
    simpa [prefixWord, tailWord_6050500, baseEnd_6050500] using wordTrace_append hprefix tailTrace_6050500
  have hstable : (prefixWord ++ tailWord_6050500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050500).length < 2 ^ (prefixWord ++ tailWord_6050500).sum := by decide
  have hdescent : baseEnd_6050500 < baseStart_6050500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050513 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_6050513 : Nat := 118140960795 + 6050513 * 2 ^ 59
def prefixEnd_6050513 : Nat := 4983230072969 + 3 ^ 40 * 6050513 * 2
def baseEnd_6050513 : Nat := 3106821375277191073761703

theorem tailTrace_6050513 : CollatzResearch.WordTrace tailWord_6050513 prefixEnd_6050513 3106821375277191073761703 := by
  unfold tailWord_6050513
  simp only [CollatzResearch.WordTrace]
  refine ⟨220680338729032221196684193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147120225819354814131122795 220680338729032221196684193)
  ·
    refine ⟨165510254046774165897513145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220680338729032221196684193 165510254046774165897513145)
    ·
      refine ⟨124132690535080624423134859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165510254046774165897513145 124132690535080624423134859)
      ·
        refine ⟨186199035802620936634702289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124132690535080624423134859 186199035802620936634702289)
        ·
          refine ⟨139649276851965702476026717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186199035802620936634702289 139649276851965702476026717)
          ·
            refine ⟨52368478819487138428510019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139649276851965702476026717 52368478819487138428510019)
            ·
              refine ⟨78552718229230707642765029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52368478819487138428510019 78552718229230707642765029)
              ·
                refine ⟨14728634667980757683018443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78552718229230707642765029 14728634667980757683018443)
                ·
                  refine ⟨22092952001971136524527665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14728634667980757683018443 22092952001971136524527665)
                  ·
                    refine ⟨16569714001478352393395749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22092952001971136524527665 16569714001478352393395749)
                    ·
                      refine ⟨3106821375277191073761703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16569714001478352393395749 3106821375277191073761703)
                      ·
                        rfl

theorem cell23_6050513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_6050513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050513 prefixEnd_6050513 := by exact prefixLift 6050513
  have htrace : WordTrace (prefixWord ++ tailWord_6050513) baseStart_6050513 baseEnd_6050513 := by
    simpa [prefixWord, tailWord_6050513, baseEnd_6050513] using wordTrace_append hprefix tailTrace_6050513
  have hstable : (prefixWord ++ tailWord_6050513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050513).length < 2 ^ (prefixWord ++ tailWord_6050513).sum := by decide
  have hdescent : baseEnd_6050513 < baseStart_6050513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050514 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_6050514 : Nat := 118140960795 + 6050514 * 2 ^ 59
def prefixEnd_6050514 : Nat := 4983230072969 + 3 ^ 40 * 6050514 * 2
def baseEnd_6050514 : Nat := 1035607296252615189949733

theorem tailTrace_6050514 : CollatzResearch.WordTrace tailWord_6050514 prefixEnd_6050514 1035607296252615189949733 := by
  unfold tailWord_6050514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55170093800507149591867649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147120250134685732244980397 55170093800507149591867649)
  ·
    refine ⟨41377570350380362193900737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55170093800507149591867649 41377570350380362193900737)
    ·
      refine ⟨31033177762785271645425553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41377570350380362193900737 31033177762785271645425553)
      ·
        refine ⟨23274883322088953734069165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31033177762785271645425553 23274883322088953734069165)
        ·
          refine ⟨8728081245783357650275937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23274883322088953734069165 8728081245783357650275937)
          ·
            refine ⟨6546060934337518237706953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8728081245783357650275937 6546060934337518237706953)
            ·
              refine ⟨4909545700753138678280215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546060934337518237706953 4909545700753138678280215)
              ·
                refine ⟨7364318551129708017420323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909545700753138678280215 7364318551129708017420323)
                ·
                  refine ⟨11046477826694562026130485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364318551129708017420323 11046477826694562026130485)
                  ·
                    refine ⟨1035607296252615189949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11046477826694562026130485 1035607296252615189949733)
                    ·
                      rfl

theorem cell23_6050514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_6050514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050514 prefixEnd_6050514 := by exact prefixLift 6050514
  have htrace : WordTrace (prefixWord ++ tailWord_6050514) baseStart_6050514 baseEnd_6050514 := by
    simpa [prefixWord, tailWord_6050514, baseEnd_6050514] using wordTrace_append hprefix tailTrace_6050514
  have hstable : (prefixWord ++ tailWord_6050514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050514).length < 2 ^ (prefixWord ++ tailWord_6050514).sum := by decide
  have hdescent : baseEnd_6050514 < baseStart_6050514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050527 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 2, 4]
def baseStart_6050527 : Nat := 118140960795 + 6050527 * 2 ^ 59
def prefixEnd_6050527 : Nat := 4983230072969 + 3 ^ 40 * 6050527 * 2
def baseEnd_6050527 : Nat := 1035609521335451339662213

theorem tailTrace_6050527 : CollatzResearch.WordTrace tailWord_6050527 prefixEnd_6050527 1035609521335451339662213 := by
  unfold tailWord_6050527
  simp only [CollatzResearch.WordTrace]
  refine ⟨220680849350981501587693835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147120566233987667725129223 220680849350981501587693835)
  ·
    refine ⟨331021274026472252381540753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220680849350981501587693835 331021274026472252381540753)
    ·
      refine ⟨248265955519854189286155565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331021274026472252381540753 248265955519854189286155565)
      ·
        refine ⟨93099733319945320982308337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248265955519854189286155565 93099733319945320982308337)
        ·
          refine ⟨69824799989958990736731253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93099733319945320982308337 69824799989958990736731253)
          ·
            refine ⟨6546074999058655381568555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69824799989958990736731253 6546074999058655381568555)
            ·
              refine ⟨9819112498587983072352833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546074999058655381568555 9819112498587983072352833)
              ·
                refine ⟨7364334373940987304264625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819112498587983072352833 7364334373940987304264625)
                ·
                  refine ⟨5523250780455740478198469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7364334373940987304264625 5523250780455740478198469)
                  ·
                    refine ⟨1035609521335451339662213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5523250780455740478198469 1035609521335451339662213)
                    ·
                      rfl

theorem cell23_6050527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_6050527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050527 prefixEnd_6050527 := by exact prefixLift 6050527
  have htrace : WordTrace (prefixWord ++ tailWord_6050527) baseStart_6050527 baseEnd_6050527 := by
    simpa [prefixWord, tailWord_6050527, baseEnd_6050527] using wordTrace_append hprefix tailTrace_6050527
  have hstable : (prefixWord ++ tailWord_6050527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050527).length < 2 ^ (prefixWord ++ tailWord_6050527).sum := by decide
  have hdescent : baseEnd_6050527 < baseStart_6050527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050567 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6050567 : Nat := 118140960795 + 6050567 * 2 ^ 59
def prefixEnd_6050567 : Nat := 4983230072969 + 3 ^ 40 * 6050567 * 2
def baseEnd_6050567 : Nat := 3106849103232533862486455

theorem tailTrace_6050567 : CollatzResearch.WordTrace tailWord_6050567 prefixEnd_6050567 3106849103232533862486455 := by
  unfold tailWord_6050567
  simp only [CollatzResearch.WordTrace]
  refine ⟨220682308270836588419149955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147121538847224392279433303 220682308270836588419149955)
  ·
    refine ⟨331023462406254882628724933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220682308270836588419149955 331023462406254882628724933)
    ·
      refine ⟨62066899201172790492885925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331023462406254882628724933 62066899201172790492885925)
      ·
        refine ⟨11637543600219898217416111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62066899201172790492885925 11637543600219898217416111)
        ·
          refine ⟨17456315400329847326124167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637543600219898217416111 17456315400329847326124167)
          ·
            refine ⟨26184473100494770989186251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17456315400329847326124167 26184473100494770989186251)
            ·
              refine ⟨39276709650742156483779377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26184473100494770989186251 39276709650742156483779377)
              ·
                refine ⟨29457532238056617362834533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39276709650742156483779377 29457532238056617362834533)
                ·
                  refine ⟨5523287294635615755531475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29457532238056617362834533 5523287294635615755531475)
                  ·
                    refine ⟨8284930941953423633297213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5523287294635615755531475 8284930941953423633297213)
                    ·
                      refine ⟨3106849103232533862486455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8284930941953423633297213 3106849103232533862486455)
                      ·
                        rfl

theorem cell23_6050567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6050567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050567 prefixEnd_6050567 := by exact prefixLift 6050567
  have htrace : WordTrace (prefixWord ++ tailWord_6050567) baseStart_6050567 baseEnd_6050567 := by
    simpa [prefixWord, tailWord_6050567, baseEnd_6050567] using wordTrace_append hprefix tailTrace_6050567
  have hstable : (prefixWord ++ tailWord_6050567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050567).length < 2 ^ (prefixWord ++ tailWord_6050567).sum := by decide
  have hdescent : baseEnd_6050567 < baseStart_6050567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050577 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_6050577 : Nat := 118140960795 + 6050577 * 2 ^ 59
def prefixEnd_6050577 : Nat := 4983230072969 + 3 ^ 40 * 6050577 * 2
def baseEnd_6050577 : Nat := 3106854238039078823361409

theorem tailTrace_6050577 : CollatzResearch.WordTrace tailWord_6050577 prefixEnd_6050577 3106854238039078823361409 := by
  unfold tailWord_6050577
  simp only [CollatzResearch.WordTrace]
  refine ⟨220682673000800360127013985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147121782000533573418009323 220682673000800360127013985)
  ·
    refine ⟨165512004750600270095260489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220682673000800360127013985 165512004750600270095260489)
    ·
      refine ⟨124134003562950202571445367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165512004750600270095260489 124134003562950202571445367)
      ·
        refine ⟨186201005344425303857168051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124134003562950202571445367 186201005344425303857168051)
        ·
          refine ⟨279301508016637955785752077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186201005344425303857168051 279301508016637955785752077)
          ·
            refine ⟨104738065506239233419657029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279301508016637955785752077 104738065506239233419657029)
            ·
              refine ⟨19638387282419856266185693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104738065506239233419657029 19638387282419856266185693)
              ·
                refine ⟨7364395230907446099819635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19638387282419856266185693 7364395230907446099819635)
                ·
                  refine ⟨11046592846361169149729453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364395230907446099819635 11046592846361169149729453)
                  ·
                    refine ⟨4142472317385438431148545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11046592846361169149729453 4142472317385438431148545)
                    ·
                      refine ⟨3106854238039078823361409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142472317385438431148545 3106854238039078823361409)
                      ·
                        rfl

theorem cell23_6050577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_6050577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050577 prefixEnd_6050577 := by exact prefixLift 6050577
  have htrace : WordTrace (prefixWord ++ tailWord_6050577) baseStart_6050577 baseEnd_6050577 := by
    simpa [prefixWord, tailWord_6050577, baseEnd_6050577] using wordTrace_append hprefix tailTrace_6050577
  have hstable : (prefixWord ++ tailWord_6050577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050577).length < 2 ^ (prefixWord ++ tailWord_6050577).sum := by decide
  have hdescent : baseEnd_6050577 < baseStart_6050577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050593 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6050593 : Nat := 118140960795 + 6050593 * 2 ^ 59
def prefixEnd_6050593 : Nat := 4983230072969 + 3 ^ 40 * 6050593 * 2
def baseEnd_6050593 : Nat := 3106862453729550760761335

theorem tailTrace_6050593 : CollatzResearch.WordTrace tailWord_6050593 prefixEnd_6050593 3106862453729550760761335 := by
  unfold tailWord_6050593
  simp only [CollatzResearch.WordTrace]
  refine ⟨220683256568742394859596433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147122171045828263239730955 220683256568742394859596433)
  ·
    refine ⟨165512442426556796144697325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220683256568742394859596433 165512442426556796144697325)
    ·
      refine ⟨62067165909958798554261497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165512442426556796144697325 62067165909958798554261497)
      ·
        refine ⟨46550374432469098915696123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62067165909958798554261497 46550374432469098915696123)
        ·
          refine ⟨69825561648703648373544185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46550374432469098915696123 69825561648703648373544185)
          ·
            refine ⟨52369171236527736280158139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69825561648703648373544185 52369171236527736280158139)
            ·
              refine ⟨78553756854791604420237209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52369171236527736280158139 78553756854791604420237209)
              ·
                refine ⟨58915317641093703315177907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78553756854791604420237209 58915317641093703315177907)
                ·
                  refine ⟨88372976461640554972766861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58915317641093703315177907 88372976461640554972766861)
                  ·
                    refine ⟨33139866173115208114787573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88372976461640554972766861 33139866173115208114787573)
                    ·
                      refine ⟨3106862453729550760761335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33139866173115208114787573 3106862453729550760761335)
                      ·
                        rfl

theorem cell23_6050593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6050593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050593 prefixEnd_6050593 := by exact prefixLift 6050593
  have htrace : WordTrace (prefixWord ++ tailWord_6050593) baseStart_6050593 baseEnd_6050593 := by
    simpa [prefixWord, tailWord_6050593, baseEnd_6050593] using wordTrace_append hprefix tailTrace_6050593
  have hstable : (prefixWord ++ tailWord_6050593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050593).length < 2 ^ (prefixWord ++ tailWord_6050593).sum := by decide
  have hdescent : baseEnd_6050593 < baseStart_6050593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050641 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_6050641 : Nat := 118140960795 + 6050641 * 2 ^ 59
def prefixEnd_6050641 : Nat := 4983230072969 + 3 ^ 40 * 6050641 * 2
def baseEnd_6050641 : Nat := 3106887100800966572961115

theorem tailTrace_6050641 : CollatzResearch.WordTrace tailWord_6050641 prefixEnd_6050641 3106887100800966572961115 := by
  unfold tailWord_6050641
  simp only [CollatzResearch.WordTrace]
  refine ⟨220685007272568499057343777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147123338181712332704895851 220685007272568499057343777)
  ·
    refine ⟨165513755454426374293007833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220685007272568499057343777 165513755454426374293007833)
    ·
      refine ⟨124135316590819780719755875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165513755454426374293007833 124135316590819780719755875)
      ·
        refine ⟨186202974886229671079633813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124135316590819780719755875 186202974886229671079633813)
        ·
          refine ⟨8728264447792015831857835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186202974886229671079633813 8728264447792015831857835)
          ·
            refine ⟨13092396671688023747786753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728264447792015831857835 13092396671688023747786753)
            ·
              refine ⟨9819297503766017810840065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13092396671688023747786753 9819297503766017810840065)
              ·
                refine ⟨7364473127824513358130049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819297503766017810840065 7364473127824513358130049)
                ·
                  refine ⟨5523354845868385018597537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7364473127824513358130049 5523354845868385018597537)
                  ·
                    refine ⟨4142516134401288763948153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523354845868385018597537 4142516134401288763948153)
                    ·
                      refine ⟨3106887100800966572961115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142516134401288763948153 3106887100800966572961115)
                      ·
                        rfl

theorem cell23_6050641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_6050641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050641 prefixEnd_6050641 := by exact prefixLift 6050641
  have htrace : WordTrace (prefixWord ++ tailWord_6050641) baseStart_6050641 baseEnd_6050641 := by
    simpa [prefixWord, tailWord_6050641, baseEnd_6050641] using wordTrace_append hprefix tailTrace_6050641
  have hstable : (prefixWord ++ tailWord_6050641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050641).length < 2 ^ (prefixWord ++ tailWord_6050641).sum := by decide
  have hdescent : baseEnd_6050641 < baseStart_6050641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050647 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 5]
def baseStart_6050647 : Nat := 118140960795 + 6050647 * 2 ^ 59
def prefixEnd_6050647 : Nat := 4983230072969 + 3 ^ 40 * 6050647 * 2
def baseEnd_6050647 : Nat := 345210020187210394387343

theorem tailTrace_6050647 : CollatzResearch.WordTrace tailWord_6050647 prefixEnd_6050647 345210020187210394387343 := by
  unfold tailWord_6050647
  simp only [CollatzResearch.WordTrace]
  refine ⟨220685226110546762082062195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147123484073697841388041463 220685226110546762082062195)
  ·
    refine ⟨331027839165820143123093293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220685226110546762082062195 331027839165820143123093293)
    ·
      refine ⟨124135439687182553671159985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331027839165820143123093293 124135439687182553671159985)
      ·
        refine ⟨93101579765386915253369989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124135439687182553671159985 93101579765386915253369989)
        ·
          refine ⟨17456546206010046610006873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93101579765386915253369989 17456546206010046610006873)
          ·
            refine ⟨13092409654507534957505155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17456546206010046610006873 13092409654507534957505155)
            ·
              refine ⟨19638614481761302436257733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13092409654507534957505155 19638614481761302436257733)
              ·
                refine ⟨3682240215330244206798325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19638614481761302436257733 3682240215330244206798325)
                ·
                  refine ⟨345210020187210394387343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3682240215330244206798325 345210020187210394387343)
                  ·
                    rfl

theorem cell23_6050647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 5].length) (baseStart_6050647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050647 prefixEnd_6050647 := by exact prefixLift 6050647
  have htrace : WordTrace (prefixWord ++ tailWord_6050647) baseStart_6050647 baseEnd_6050647 := by
    simpa [prefixWord, tailWord_6050647, baseEnd_6050647] using wordTrace_append hprefix tailTrace_6050647
  have hstable : (prefixWord ++ tailWord_6050647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050647).length < 2 ^ (prefixWord ++ tailWord_6050647).sum := by decide
  have hdescent : baseEnd_6050647 < baseStart_6050647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050677 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6050677 : Nat := 118140960795 + 6050677 * 2 ^ 59
def prefixEnd_6050677 : Nat := 4983230072969 + 3 ^ 40 * 6050677 * 2
def baseEnd_6050677 : Nat := 1035635195368176144036983

theorem tailTrace_6050677 : CollatzResearch.WordTrace tailWord_6050677 prefixEnd_6050677 1035635195368176144036983 := by
  unfold tailWord_6050677
  simp only [CollatzResearch.WordTrace]
  refine ⟨220686320300438077205654285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147124213533625384803769523 220686320300438077205654285)
  ·
    refine ⟨82757370112664278952120357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220686320300438077205654285 82757370112664278952120357)
    ·
      refine ⟨15517006896124552303522567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82757370112664278952120357 15517006896124552303522567)
      ·
        refine ⟨23275510344186828455283851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15517006896124552303522567 23275510344186828455283851)
        ·
          refine ⟨34913265516280242682925777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23275510344186828455283851 34913265516280242682925777)
          ·
            refine ⟨26184949137210182012194333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34913265516280242682925777 26184949137210182012194333)
            ·
              refine ⟨9819355926453818254572875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26184949137210182012194333 9819355926453818254572875)
              ·
                refine ⟨14729033889680727381859313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9819355926453818254572875 14729033889680727381859313)
                ·
                  refine ⟨11046775417260545536394485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14729033889680727381859313 11046775417260545536394485)
                  ·
                    refine ⟨1035635195368176144036983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11046775417260545536394485 1035635195368176144036983)
                    ·
                      rfl

theorem cell23_6050677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6050677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050677 prefixEnd_6050677 := by exact prefixLift 6050677
  have htrace : WordTrace (prefixWord ++ tailWord_6050677) baseStart_6050677 baseEnd_6050677 := by
    simpa [prefixWord, tailWord_6050677, baseEnd_6050677] using wordTrace_append hprefix tailTrace_6050677
  have hstable : (prefixWord ++ tailWord_6050677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050677).length < 2 ^ (prefixWord ++ tailWord_6050677).sum := by decide
  have hdescent : baseEnd_6050677 < baseStart_6050677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050680 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_6050680 : Nat := 118140960795 + 6050680 * 2 ^ 59
def prefixEnd_6050680 : Nat := 4983230072969 + 3 ^ 40 * 6050680 * 2
def baseEnd_6050680 : Nat := 3106907126546491920373435

theorem tailTrace_6050680 : CollatzResearch.WordTrace tailWord_6050680 prefixEnd_6050680 3106907126546491920373435 := by
  unfold tailWord_6050680
  simp only [CollatzResearch.WordTrace]
  refine ⟨110343214859713604359006747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147124286479618139145342329 110343214859713604359006747)
  ·
    refine ⟨165514822289570406538510121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110343214859713604359006747 165514822289570406538510121)
    ·
      refine ⟨124136116717177804903882591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165514822289570406538510121 124136116717177804903882591)
      ·
        refine ⟨186204175075766707355823887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124136116717177804903882591 186204175075766707355823887)
        ·
          refine ⟨279306262613650061033735831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186204175075766707355823887 279306262613650061033735831)
          ·
            refine ⟨418959393920475091550603747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279306262613650061033735831 418959393920475091550603747)
            ·
              refine ⟨628439090880712637325905621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418959393920475091550603747 628439090880712637325905621)
              ·
                refine ⟨14729041192516702437325913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 628439090880712637325905621 14729041192516702437325913)
                ·
                  refine ⟨11046780894387526827994435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14729041192516702437325913 11046780894387526827994435)
                  ·
                    refine ⟨16570171341581290241991653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11046780894387526827994435 16570171341581290241991653)
                    ·
                      refine ⟨3106907126546491920373435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16570171341581290241991653 3106907126546491920373435)
                      ·
                        rfl

theorem cell23_6050680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_6050680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050680 prefixEnd_6050680 := by exact prefixLift 6050680
  have htrace : WordTrace (prefixWord ++ tailWord_6050680) baseStart_6050680 baseEnd_6050680 := by
    simpa [prefixWord, tailWord_6050680, baseEnd_6050680] using wordTrace_append hprefix tailTrace_6050680
  have hstable : (prefixWord ++ tailWord_6050680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050680).length < 2 ^ (prefixWord ++ tailWord_6050680).sum := by decide
  have hdescent : baseEnd_6050680 < baseStart_6050680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050697 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 4, 2]
def baseStart_6050697 : Nat := 118140960795 + 6050697 * 2 ^ 59
def prefixEnd_6050697 : Nat := 4983230072969 + 3 ^ 40 * 6050697 * 2
def baseEnd_6050697 : Nat := 3106915855717618353860857

theorem tailTrace_6050697 : CollatzResearch.WordTrace tailWord_6050697 prefixEnd_6050697 3106915855717618353860857 := by
  unfold tailWord_6050697
  simp only [CollatzResearch.WordTrace]
  refine ⟨220687049760365620621382345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147124699840243747080921563 220687049760365620621382345)
  ·
    refine ⟨165515287320274215466036759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220687049760365620621382345 165515287320274215466036759)
    ·
      refine ⟨248272930980411323199055139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165515287320274215466036759 248272930980411323199055139)
      ·
        refine ⟨372409396470616984798582709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248272930980411323199055139 372409396470616984798582709)
        ·
          refine ⟨34913380919120342324867129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372409396470616984798582709 34913380919120342324867129)
          ·
            refine ⟨26185035689340256743650347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34913380919120342324867129 26185035689340256743650347)
            ·
              refine ⟨39277553534010385115475521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26185035689340256743650347 39277553534010385115475521)
              ·
                refine ⟨29458165150507788836606641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39277553534010385115475521 29458165150507788836606641)
                ·
                  refine ⟨22093623862880841627454981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29458165150507788836606641 22093623862880841627454981)
                  ·
                    refine ⟨4142554474290157805147809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22093623862880841627454981 4142554474290157805147809)
                    ·
                      refine ⟨3106915855717618353860857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142554474290157805147809 3106915855717618353860857)
                      ·
                        rfl

theorem cell23_6050697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4, 2].length) (baseStart_6050697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050697 prefixEnd_6050697 := by exact prefixLift 6050697
  have htrace : WordTrace (prefixWord ++ tailWord_6050697) baseStart_6050697 baseEnd_6050697 := by
    simpa [prefixWord, tailWord_6050697, baseEnd_6050697] using wordTrace_append hprefix tailTrace_6050697
  have hstable : (prefixWord ++ tailWord_6050697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050697).length < 2 ^ (prefixWord ++ tailWord_6050697).sum := by decide
  have hdescent : baseEnd_6050697 < baseStart_6050697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050720 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 6]
def baseStart_6050720 : Nat := 118140960795 + 6050720 * 2 ^ 59
def prefixEnd_6050720 : Nat := 4983230072969 + 3 ^ 40 * 6050720 * 2
def baseEnd_6050720 : Nat := 345214185085852418208139

theorem tailTrace_6050720 : CollatzResearch.WordTrace tailWord_6050720 prefixEnd_6050720 345214185085852418208139 := by
  unfold tailWord_6050720
  simp only [CollatzResearch.WordTrace]
  refine ⟨110343944319641147774734807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147125259092854863699646409 110343944319641147774734807)
  ·
    refine ⟨165515916479461721662102211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110343944319641147774734807 165515916479461721662102211)
    ·
      refine ⟨248273874719192582493153317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165515916479461721662102211 248273874719192582493153317)
      ·
        refine ⟨46551351509848609217466247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248273874719192582493153317 46551351509848609217466247)
        ·
          refine ⟨69827027264772913826199371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46551351509848609217466247 69827027264772913826199371)
          ·
            refine ⟨104740540897159370739299057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69827027264772913826199371 104740540897159370739299057)
            ·
              refine ⟨78555405672869528054474293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104740540897159370739299057 78555405672869528054474293)
              ·
                refine ⟨7364569281831518255106965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78555405672869528054474293 7364569281831518255106965)
                ·
                  refine ⟨345214185085852418208139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7364569281831518255106965 345214185085852418208139)
                  ·
                    rfl

theorem cell23_6050720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_6050720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050720 prefixEnd_6050720 := by exact prefixLift 6050720
  have htrace : WordTrace (prefixWord ++ tailWord_6050720) baseStart_6050720 baseEnd_6050720 := by
    simpa [prefixWord, tailWord_6050720, baseEnd_6050720] using wordTrace_append hprefix tailTrace_6050720
  have hstable : (prefixWord ++ tailWord_6050720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050720).length < 2 ^ (prefixWord ++ tailWord_6050720).sum := by decide
  have hdescent : baseEnd_6050720 < baseStart_6050720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050787 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6050787 : Nat := 118140960795 + 6050787 * 2 ^ 59
def prefixEnd_6050787 : Nat := 4983230072969 + 3 ^ 40 * 6050787 * 2
def baseEnd_6050787 : Nat := 3106962068976523001735443

theorem tailTrace_6050787 : CollatzResearch.WordTrace tailWord_6050787 prefixEnd_6050787 3106962068976523001735443 := by
  unfold tailWord_6050787
  simp only [CollatzResearch.WordTrace]
  refine ⟨220690332330039565992158615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147126888220026377328105743 220690332330039565992158615)
  ·
    refine ⟨331035498495059348988237923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220690332330039565992158615 331035498495059348988237923)
    ·
      refine ⟨496553247742589023482356885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331035498495059348988237923 496553247742589023482356885)
      ·
        refine ⟨23275933487933860475735479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 496553247742589023482356885 23275933487933860475735479)
        ·
          refine ⟨34913900231900790713603219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23275933487933860475735479 34913900231900790713603219)
          ·
            refine ⟨52370850347851186070404829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34913900231900790713603219 52370850347851186070404829)
            ·
              refine ⟨19639068880444194776401811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52370850347851186070404829 19639068880444194776401811)
              ·
                refine ⟨29458603320666292164602717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19639068880444194776401811 29458603320666292164602717)
                ·
                  refine ⟨11046976245249859561726019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29458603320666292164602717 11046976245249859561726019)
                  ·
                    refine ⟨16570464367874789342589029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11046976245249859561726019 16570464367874789342589029)
                    ·
                      refine ⟨3106962068976523001735443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16570464367874789342589029 3106962068976523001735443)
                      ·
                        rfl

theorem cell23_6050787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6050787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050787 prefixEnd_6050787 := by exact prefixLift 6050787
  have htrace : WordTrace (prefixWord ++ tailWord_6050787) baseStart_6050787 baseEnd_6050787 := by
    simpa [prefixWord, tailWord_6050787, baseEnd_6050787] using wordTrace_append hprefix tailTrace_6050787
  have hstable : (prefixWord ++ tailWord_6050787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050787).length < 2 ^ (prefixWord ++ tailWord_6050787).sum := by decide
  have hdescent : baseEnd_6050787 < baseStart_6050787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050791 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6050791 : Nat := 118140960795 + 6050791 * 2 ^ 59
def prefixEnd_6050791 : Nat := 4983230072969 + 3 ^ 40 * 6050791 * 2
def baseEnd_6050791 : Nat := 3106964122899140986085425

theorem tailTrace_6050791 : CollatzResearch.WordTrace tailWord_6050791 prefixEnd_6050791 3106964122899140986085425 := by
  unfold tailWord_6050791
  simp only [CollatzResearch.WordTrace]
  refine ⟨220690478222025074675304227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147126985481350049783536151 220690478222025074675304227)
  ·
    refine ⟨331035717333037612012956341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220690478222025074675304227 331035717333037612012956341)
    ·
      refine ⟨31034598499972276126214657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331035717333037612012956341 31034598499972276126214657)
      ·
        refine ⟨23275948874979207094660993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31034598499972276126214657 23275948874979207094660993)
        ·
          refine ⟨17456961656234405320995745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23275948874979207094660993 17456961656234405320995745)
          ·
            refine ⟨13092721242175803990746809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17456961656234405320995745 13092721242175803990746809)
            ·
              refine ⟨9819540931631852993060107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13092721242175803990746809 9819540931631852993060107)
              ·
                refine ⟨14729311397447779489590161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9819540931631852993060107 14729311397447779489590161)
                ·
                  refine ⟨11046983548085834617192621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14729311397447779489590161 11046983548085834617192621)
                  ·
                    refine ⟨4142618830532187981447233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11046983548085834617192621 4142618830532187981447233)
                    ·
                      refine ⟨3106964122899140986085425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142618830532187981447233 3106964122899140986085425)
                      ·
                        rfl

theorem cell23_6050791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6050791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050791 prefixEnd_6050791 := by exact prefixLift 6050791
  have htrace : WordTrace (prefixWord ++ tailWord_6050791) baseStart_6050791 baseEnd_6050791 := by
    simpa [prefixWord, tailWord_6050791, baseEnd_6050791] using wordTrace_append hprefix tailTrace_6050791
  have hstable : (prefixWord ++ tailWord_6050791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050791).length < 2 ^ (prefixWord ++ tailWord_6050791).sum := by decide
  have hdescent : baseEnd_6050791 < baseStart_6050791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050827 : List Nat := [1, 1, 1, 1, 6, 4, 1, 8]
def baseStart_6050827 : Nat := 118140960795 + 6050827 * 2 ^ 59
def prefixEnd_6050827 : Nat := 4983230072969 + 3 ^ 40 * 6050827 * 2
def baseEnd_6050827 : Nat := 115073429933433438712417

theorem tailTrace_6050827 : CollatzResearch.WordTrace tailWord_6050827 prefixEnd_6050827 115073429933433438712417 := by
  unfold tailWord_6050827
  simp only [CollatzResearch.WordTrace]
  refine ⟨220691791249894652823614735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147127860833263101882409823 220691791249894652823614735)
  ·
    refine ⟨331037686874841979235422103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220691791249894652823614735 331037686874841979235422103)
    ·
      refine ⟨496556530312262968853133155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331037686874841979235422103 496556530312262968853133155)
      ·
        refine ⟨744834795468394453279699733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496556530312262968853133155 744834795468394453279699733)
        ·
          refine ⟨34914131037580989997485925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 744834795468394453279699733 34914131037580989997485925)
          ·
            refine ⟨6546399569546435624528611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34914131037580989997485925 6546399569546435624528611)
            ·
              refine ⟨9819599354319653436792917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546399569546435624528611 9819599354319653436792917)
              ·
                refine ⟨115073429933433438712417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9819599354319653436792917 115073429933433438712417)
                ·
                  rfl

theorem cell23_6050827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 8].length) (baseStart_6050827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050827 prefixEnd_6050827 := by exact prefixLift 6050827
  have htrace : WordTrace (prefixWord ++ tailWord_6050827) baseStart_6050827 baseEnd_6050827 := by
    simpa [prefixWord, tailWord_6050827, baseEnd_6050827] using wordTrace_append hprefix tailTrace_6050827
  have hstable : (prefixWord ++ tailWord_6050827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050827).length < 2 ^ (prefixWord ++ tailWord_6050827).sum := by decide
  have hdescent : baseEnd_6050827 < baseStart_6050827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050844 : List Nat := [2, 2, 3, 1, 4, 1, 3, 7]
def baseStart_6050844 : Nat := 118140960795 + 6050844 * 2 ^ 59
def prefixEnd_6050844 : Nat := 4983230072969 + 3 ^ 40 * 6050844 * 2
def baseEnd_6050844 : Nat := 115073753236067751063803

theorem tailTrace_6050844 : CollatzResearch.WordTrace tailWord_6050844 prefixEnd_6050844 115073753236067751063803 := by
  unfold tailWord_6050844
  simp only [CollatzResearch.WordTrace]
  refine ⟨110346205645416532363491793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147128274193888709817989057 110346205645416532363491793)
  ·
    refine ⟨82759654234062399272618845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110346205645416532363491793 82759654234062399272618845)
    ·
      refine ⟨31034870337773399727232067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82759654234062399272618845 31034870337773399727232067)
      ·
        refine ⟨46552305506660099590848101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31034870337773399727232067 46552305506660099590848101)
        ·
          refine ⟨8728557282498768673284019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46552305506660099590848101 8728557282498768673284019)
          ·
            refine ⟨13092835923748153009926029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728557282498768673284019 13092835923748153009926029)
            ·
              refine ⟨4909813471405557378722261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13092835923748153009926029 4909813471405557378722261)
              ·
                refine ⟨115073753236067751063803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4909813471405557378722261 115073753236067751063803)
                ·
                  rfl

theorem cell23_6050844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 7].length) (baseStart_6050844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050844 prefixEnd_6050844 := by exact prefixLift 6050844
  have htrace : WordTrace (prefixWord ++ tailWord_6050844) baseStart_6050844 baseEnd_6050844 := by
    simpa [prefixWord, tailWord_6050844, baseEnd_6050844] using wordTrace_append hprefix tailTrace_6050844
  have hstable : (prefixWord ++ tailWord_6050844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050844).length < 2 ^ (prefixWord ++ tailWord_6050844).sum := by decide
  have hdescent : baseEnd_6050844 < baseStart_6050844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050855 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6050855 : Nat := 118140960795 + 6050855 * 2 ^ 59
def prefixEnd_6050855 : Nat := 4983230072969 + 3 ^ 40 * 6050855 * 2
def baseEnd_6050855 : Nat := 3106996985661028735685131

theorem tailTrace_6050855 : CollatzResearch.WordTrace tailWord_6050855 prefixEnd_6050855 3106996985661028735685131 := by
  unfold tailWord_6050855
  simp only [CollatzResearch.WordTrace]
  refine ⟨220692812493793213605634019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147128541662528809070422679 220692812493793213605634019)
  ·
    refine ⟨331039218740689820408451029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220692812493793213605634019 331039218740689820408451029)
    ·
      refine ⟨7758731689234917665823071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 331039218740689820408451029 7758731689234917665823071)
      ·
        refine ⟨11638097533852376498734607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758731689234917665823071 11638097533852376498734607)
        ·
          refine ⟨17457146300778564748101911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638097533852376498734607 17457146300778564748101911)
          ·
            refine ⟨26185719451167847122152867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457146300778564748101911 26185719451167847122152867)
            ·
              refine ⟨39278579176751770683229301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26185719451167847122152867 39278579176751770683229301)
              ·
                refine ⟨3682366797820478501552747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39278579176751770683229301 3682366797820478501552747)
                ·
                  refine ⟨5523550196730717752329121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682366797820478501552747 5523550196730717752329121)
                  ·
                    refine ⟨4142662647548038314246841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523550196730717752329121 4142662647548038314246841)
                    ·
                      refine ⟨3106996985661028735685131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142662647548038314246841 3106996985661028735685131)
                      ·
                        rfl

theorem cell23_6050855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6050855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050855 prefixEnd_6050855 := by exact prefixLift 6050855
  have htrace : WordTrace (prefixWord ++ tailWord_6050855) baseStart_6050855 baseEnd_6050855 := by
    simpa [prefixWord, tailWord_6050855, baseEnd_6050855] using wordTrace_append hprefix tailTrace_6050855
  have hstable : (prefixWord ++ tailWord_6050855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050855).length < 2 ^ (prefixWord ++ tailWord_6050855).sum := by decide
  have hdescent : baseEnd_6050855 < baseStart_6050855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050887 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 6]
def baseStart_6050887 : Nat := 118140960795 + 6050887 * 2 ^ 59
def prefixEnd_6050887 : Nat := 4983230072969 + 3 ^ 40 * 6050887 * 2
def baseEnd_6050887 : Nat := 1035671139013990870161661

theorem tailTrace_6050887 : CollatzResearch.WordTrace tailWord_6050887 prefixEnd_6050887 1035671139013990870161661 := by
  unfold tailWord_6050887
  simp only [CollatzResearch.WordTrace]
  refine ⟨220693979629677283070798915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147129319753118188713865943 220693979629677283070798915)
  ·
    refine ⟨331040969444515924606198373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220693979629677283070798915 331040969444515924606198373)
    ·
      refine ⟨62070181770846735863662195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331040969444515924606198373 62070181770846735863662195)
      ·
        refine ⟨93105272656270103795493293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62070181770846735863662195 93105272656270103795493293)
        ·
          refine ⟨34914477246101288923309985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93105272656270103795493293 34914477246101288923309985)
          ·
            refine ⟨26185857934575966692482489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34914477246101288923309985 26185857934575966692482489)
            ·
              refine ⟨19639393450931975019361867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26185857934575966692482489 19639393450931975019361867)
              ·
                refine ⟨29459090176397962529042801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19639393450931975019361867 29459090176397962529042801)
                ·
                  refine ⟨22094317632298471896782101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29459090176397962529042801 22094317632298471896782101)
                  ·
                    refine ⟨1035671139013990870161661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22094317632298471896782101 1035671139013990870161661)
                    ·
                      rfl

theorem cell23_6050887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_6050887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050887 prefixEnd_6050887 := by exact prefixLift 6050887
  have htrace : WordTrace (prefixWord ++ tailWord_6050887) baseStart_6050887 baseEnd_6050887 := by
    simpa [prefixWord, tailWord_6050887, baseEnd_6050887] using wordTrace_append hprefix tailTrace_6050887
  have hstable : (prefixWord ++ tailWord_6050887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050887).length < 2 ^ (prefixWord ++ tailWord_6050887).sum := by decide
  have hdescent : baseEnd_6050887 < baseStart_6050887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050897 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_6050897 : Nat := 118140960795 + 6050897 * 2 ^ 59
def prefixEnd_6050897 : Nat := 4983230072969 + 3 ^ 40 * 6050897 * 2
def baseEnd_6050897 : Nat := 3107018551848517571359937

theorem tailTrace_6050897 : CollatzResearch.WordTrace tailWord_6050897 prefixEnd_6050897 3107018551848517571359937 := by
  unfold tailWord_6050897
  simp only [CollatzResearch.WordTrace]
  refine ⟨220694344359641054778662945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147129562906427369852441963 220694344359641054778662945)
  ·
    refine ⟨165520758269730791083997209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220694344359641054778662945 165520758269730791083997209)
    ·
      refine ⟨124140568702298093312997907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165520758269730791083997209 124140568702298093312997907)
      ·
        refine ⟨186210853053447139969496861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124140568702298093312997907 186210853053447139969496861)
        ·
          refine ⟨69829069895042677488561323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186210853053447139969496861 69829069895042677488561323)
          ·
            refine ⟨104743604842564016232841985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69829069895042677488561323 104743604842564016232841985)
            ·
              refine ⟨78557703631923012174631489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104743604842564016232841985 78557703631923012174631489)
              ·
                refine ⟨58918277723942259130973617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78557703631923012174631489 58918277723942259130973617)
                ·
                  refine ⟨44188708292956694348230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58918277723942259130973617 44188708292956694348230213)
                  ·
                    refine ⟨8285382804929380190293165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44188708292956694348230213 8285382804929380190293165)
                    ·
                      refine ⟨3107018551848517571359937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8285382804929380190293165 3107018551848517571359937)
                      ·
                        rfl

theorem cell23_6050897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_6050897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050897 prefixEnd_6050897 := by exact prefixLift 6050897
  have htrace : WordTrace (prefixWord ++ tailWord_6050897) baseStart_6050897 baseEnd_6050897 := by
    simpa [prefixWord, tailWord_6050897, baseEnd_6050897] using wordTrace_append hprefix tailTrace_6050897
  have hstable : (prefixWord ++ tailWord_6050897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050897).length < 2 ^ (prefixWord ++ tailWord_6050897).sum := by decide
  have hdescent : baseEnd_6050897 < baseStart_6050897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050898 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_6050898 : Nat := 118140960795 + 6050898 * 2 ^ 59
def prefixEnd_6050898 : Nat := 4983230072969 + 3 ^ 40 * 6050898 * 2
def baseEnd_6050898 : Nat := 3107019065329172067447433

theorem tailTrace_6050898 : CollatzResearch.WordTrace tailWord_6050898 prefixEnd_6050898 3107019065329172067447433 := by
  unfold tailWord_6050898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55173595208159357987362337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147129587221758287966299565 55173595208159357987362337)
  ·
    refine ⟨41380196406119518490521753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55173595208159357987362337 41380196406119518490521753)
    ·
      refine ⟨31035147304589638867891315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41380196406119518490521753 31035147304589638867891315)
      ·
        refine ⟨46552720956884458301836973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31035147304589638867891315 46552720956884458301836973)
        ·
          refine ⟨17457270358831671863188865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46552720956884458301836973 17457270358831671863188865)
          ·
            refine ⟨13092952769123753897391649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17457270358831671863188865 13092952769123753897391649)
            ·
              refine ⟨9819714576842815423043737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13092952769123753897391649 9819714576842815423043737)
              ·
                refine ⟨7364785932632111567282803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819714576842815423043737 7364785932632111567282803)
                ·
                  refine ⟨11047178898948167350924205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364785932632111567282803 11047178898948167350924205)
                  ·
                    refine ⟨4142692087105562756596577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11047178898948167350924205 4142692087105562756596577)
                    ·
                      refine ⟨3107019065329172067447433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142692087105562756596577 3107019065329172067447433)
                      ·
                        rfl

theorem cell23_6050898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_6050898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050898 prefixEnd_6050898 := by exact prefixLift 6050898
  have htrace : WordTrace (prefixWord ++ tailWord_6050898) baseStart_6050898 baseEnd_6050898 := by
    simpa [prefixWord, tailWord_6050898, baseEnd_6050898] using wordTrace_append hprefix tailTrace_6050898
  have hstable : (prefixWord ++ tailWord_6050898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050898).length < 2 ^ (prefixWord ++ tailWord_6050898).sum := by decide
  have hdescent : baseEnd_6050898 < baseStart_6050898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050914 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6050914 : Nat := 118140960795 + 6050914 * 2 ^ 59
def prefixEnd_6050914 : Nat := 4983230072969 + 3 ^ 40 * 6050914 * 2
def baseEnd_6050914 : Nat := 3107027281019644004847359

theorem tailTrace_6050914 : CollatzResearch.WordTrace tailWord_6050914 prefixEnd_6050914 3107027281019644004847359 := by
  unfold tailWord_6050914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55173741100144866670507949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147129976267052977788021197 55173741100144866670507949)
  ·
    refine ⟨20690152912554325001440481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55173741100144866670507949 20690152912554325001440481)
    ·
      refine ⟨15517614684415743751080361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20690152912554325001440481 15517614684415743751080361)
      ·
        refine ⟨11638211013311807813310271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15517614684415743751080361 11638211013311807813310271)
        ·
          refine ⟨17457316519967711719965407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638211013311807813310271 17457316519967711719965407)
          ·
            refine ⟨26185974779951567579948111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457316519967711719965407 26185974779951567579948111)
            ·
              refine ⟨39278962169927351369922167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26185974779951567579948111 39278962169927351369922167)
              ·
                refine ⟨58918443254891027054883251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39278962169927351369922167 58918443254891027054883251)
                ·
                  refine ⟨88377664882336540582324877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58918443254891027054883251 88377664882336540582324877)
                  ·
                    refine ⟨33141624330876202718371829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88377664882336540582324877 33141624330876202718371829)
                    ·
                      refine ⟨3107027281019644004847359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33141624330876202718371829 3107027281019644004847359)
                      ·
                        rfl

theorem cell23_6050914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6050914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050914 prefixEnd_6050914 := by exact prefixLift 6050914
  have htrace : WordTrace (prefixWord ++ tailWord_6050914) baseStart_6050914 baseEnd_6050914 := by
    simpa [prefixWord, tailWord_6050914, baseEnd_6050914] using wordTrace_append hprefix tailTrace_6050914
  have hstable : (prefixWord ++ tailWord_6050914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050914).length < 2 ^ (prefixWord ++ tailWord_6050914).sum := by decide
  have hdescent : baseEnd_6050914 < baseStart_6050914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050945 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_6050945 : Nat := 118140960795 + 6050945 * 2 ^ 59
def prefixEnd_6050945 : Nat := 4983230072969 + 3 ^ 40 * 6050945 * 2
def baseEnd_6050945 : Nat := 3107043198919933383559717

theorem tailTrace_6050945 : CollatzResearch.WordTrace tailWord_6050945 prefixEnd_6050945 3107043198919933383559717 := by
  unfold tailWord_6050945
  simp only [CollatzResearch.WordTrace]
  refine ⟨220696095063467158976410289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147130730042311439317606859 220696095063467158976410289)
  ·
    refine ⟨165522071297600369232307717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220696095063467158976410289 165522071297600369232307717)
    ·
      refine ⟨31035388368300069231057697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165522071297600369232307717 31035388368300069231057697)
      ·
        refine ⟨23276541276225051923293273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31035388368300069231057697 23276541276225051923293273)
        ·
          refine ⟨17457405957168788942469955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23276541276225051923293273 17457405957168788942469955)
          ·
            refine ⟨26186108935753183413704933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17457405957168788942469955 26186108935753183413704933)
            ·
              refine ⟨4909895425453721890069675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26186108935753183413704933 4909895425453721890069675)
              ·
                refine ⟨7364843138180582835104513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909895425453721890069675 7364843138180582835104513)
                ·
                  refine ⟨5523632353635437126328385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7364843138180582835104513 5523632353635437126328385)
                  ·
                    refine ⟨4142724265226577844746289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523632353635437126328385 4142724265226577844746289)
                    ·
                      refine ⟨3107043198919933383559717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142724265226577844746289 3107043198919933383559717)
                      ·
                        rfl

theorem cell23_6050945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_6050945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050945 prefixEnd_6050945 := by exact prefixLift 6050945
  have htrace : WordTrace (prefixWord ++ tailWord_6050945) baseStart_6050945 baseEnd_6050945 := by
    simpa [prefixWord, tailWord_6050945, baseEnd_6050945] using wordTrace_append hprefix tailTrace_6050945
  have hstable : (prefixWord ++ tailWord_6050945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050945).length < 2 ^ (prefixWord ++ tailWord_6050945).sum := by decide
  have hdescent : baseEnd_6050945 < baseStart_6050945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6050947 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 4, 5]
def baseStart_6050947 : Nat := 118140960795 + 6050947 * 2 ^ 59
def prefixEnd_6050947 : Nat := 4983230072969 + 3 ^ 40 * 6050947 * 2
def baseEnd_6050947 : Nat := 1035681408627080791911569

theorem tailTrace_6050947 : CollatzResearch.WordTrace tailWord_6050947 prefixEnd_6050947 1035681408627080791911569 := by
  unfold tailWord_6050947
  simp only [CollatzResearch.WordTrace]
  refine ⟨220696168009459913317983095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147130778672973275545322063 220696168009459913317983095)
  ·
    refine ⟨331044252014189869976974643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220696168009459913317983095 331044252014189869976974643)
    ·
      refine ⟨496566378021284804965461965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331044252014189869976974643 496566378021284804965461965)
      ·
        refine ⟨186212391757981801862048237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496566378021284804965461965 186212391757981801862048237)
        ·
          refine ⟨69829646909243175698268089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186212391757981801862048237 69829646909243175698268089)
          ·
            refine ⟨52372235181932381773701067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69829646909243175698268089 52372235181932381773701067)
            ·
              refine ⟨78558352772898572660551601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52372235181932381773701067 78558352772898572660551601)
              ·
                refine ⟨58918764579673929495413701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78558352772898572660551601 58918764579673929495413701)
                ·
                  refine ⟨11047268358688861780390069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58918764579673929495413701 11047268358688861780390069)
                  ·
                    refine ⟨1035681408627080791911569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11047268358688861780390069 1035681408627080791911569)
                    ·
                      rfl

theorem cell23_6050947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].length) (baseStart_6050947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6050947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6050947 prefixEnd_6050947 := by exact prefixLift 6050947
  have htrace : WordTrace (prefixWord ++ tailWord_6050947) baseStart_6050947 baseEnd_6050947 := by
    simpa [prefixWord, tailWord_6050947, baseEnd_6050947] using wordTrace_append hprefix tailTrace_6050947
  have hstable : (prefixWord ++ tailWord_6050947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6050947).length < 2 ^ (prefixWord ++ tailWord_6050947).sum := by decide
  have hdescent : baseEnd_6050947 < baseStart_6050947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6050947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051001 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6051001 : Nat := 118140960795 + 6051001 * 2 ^ 59
def prefixEnd_6051001 : Nat := 4983230072969 + 3 ^ 40 * 6051001 * 2
def baseEnd_6051001 : Nat := 3107071953836585164459459

theorem tailTrace_6051001 : CollatzResearch.WordTrace tailWord_6051001 prefixEnd_6051001 3107071953836585164459459 := by
  unfold tailWord_6051001
  simp only [CollatzResearch.WordTrace]
  refine ⟨220698137551264280540448857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147132091700842853693632571 220698137551264280540448857)
  ·
    refine ⟨165523603163448210405336643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220698137551264280540448857 165523603163448210405336643)
    ·
      refine ⟨248285404745172315608004965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165523603163448210405336643 248285404745172315608004965)
      ·
        refine ⟨46553513389719809176500931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248285404745172315608004965 46553513389719809176500931)
        ·
          refine ⟨69830270084579713764751397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46553513389719809176500931 69830270084579713764751397)
          ·
            refine ⟨13093175640858696330890887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69830270084579713764751397 13093175640858696330890887)
            ·
              refine ⟨19639763461288044496336331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13093175640858696330890887 19639763461288044496336331)
              ·
                refine ⟨29459645191932066744504497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19639763461288044496336331 29459645191932066744504497)
                ·
                  refine ⟨22094733893949050058378373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29459645191932066744504497 22094733893949050058378373)
                  ·
                    refine ⟨4142762605115446885945945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22094733893949050058378373 4142762605115446885945945)
                    ·
                      refine ⟨3107071953836585164459459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142762605115446885945945 3107071953836585164459459)
                      ·
                        rfl

theorem cell23_6051001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6051001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051001 prefixEnd_6051001 := by exact prefixLift 6051001
  have htrace : WordTrace (prefixWord ++ tailWord_6051001) baseStart_6051001 baseEnd_6051001 := by
    simpa [prefixWord, tailWord_6051001, baseEnd_6051001] using wordTrace_append hprefix tailTrace_6051001
  have hstable : (prefixWord ++ tailWord_6051001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051001).length < 2 ^ (prefixWord ++ tailWord_6051001).sum := by decide
  have hdescent : baseEnd_6051001 < baseStart_6051001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051041 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 6]
def baseStart_6051041 : Nat := 118140960795 + 6051041 * 2 ^ 59
def prefixEnd_6051041 : Nat := 4983230072969 + 3 ^ 40 * 6051041 * 2
def baseEnd_6051041 : Nat := 345232499229196111995475

theorem tailTrace_6051041 : CollatzResearch.WordTrace tailWord_6051041 prefixEnd_6051041 345232499229196111995475 := by
  unfold tailWord_6051041
  simp only [CollatzResearch.WordTrace]
  refine ⟨220699596471119367371904977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147133064314079578247936651 220699596471119367371904977)
  ·
    refine ⟨165524697353339525528928733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220699596471119367371904977 165524697353339525528928733)
    ·
      refine ⟨62071761507502322073348275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165524697353339525528928733 62071761507502322073348275)
      ·
        refine ⟨93107642261253483110022413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62071761507502322073348275 93107642261253483110022413)
        ·
          refine ⟨34915365847970056166258405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93107642261253483110022413 34915365847970056166258405)
          ·
            refine ⟨6546631096494385531173451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34915365847970056166258405 6546631096494385531173451)
            ·
              refine ⟨9819946644741578296760177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546631096494385531173451 9819946644741578296760177)
              ·
                refine ⟨7364959983556183722570133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819946644741578296760177 7364959983556183722570133)
                ·
                  refine ⟨345232499229196111995475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7364959983556183722570133 345232499229196111995475)
                  ·
                    rfl

theorem cell23_6051041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_6051041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051041 prefixEnd_6051041 := by exact prefixLift 6051041
  have htrace : WordTrace (prefixWord ++ tailWord_6051041) baseStart_6051041 baseEnd_6051041 := by
    simpa [prefixWord, tailWord_6051041, baseEnd_6051041] using wordTrace_append hprefix tailTrace_6051041
  have hstable : (prefixWord ++ tailWord_6051041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051041).length < 2 ^ (prefixWord ++ tailWord_6051041).sum := by decide
  have hdescent : baseEnd_6051041 < baseStart_6051041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051051 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 3]
def baseStart_6051051 : Nat := 118140960795 + 6051051 * 2 ^ 59
def prefixEnd_6051051 : Nat := 4983230072969 + 3 ^ 40 * 6051051 * 2
def baseEnd_6051051 : Nat := 3107097627869309968834229

theorem tailTrace_6051051 : CollatzResearch.WordTrace tailWord_6051051 prefixEnd_6051051 3107097627869309968834229 := by
  unfold tailWord_6051051
  simp only [CollatzResearch.WordTrace]
  refine ⟨220699961201083139079769007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147133307467388759386512671 220699961201083139079769007)
  ·
    refine ⟨331049941801624708619653511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220699961201083139079769007 331049941801624708619653511)
    ·
      refine ⟨496574912702437062929480267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331049941801624708619653511 496574912702437062929480267)
      ·
        refine ⟨744862369053655594394220401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496574912702437062929480267 744862369053655594394220401)
        ·
          refine ⟨558646776790241695795665301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744862369053655594394220401 558646776790241695795665301)
          ·
            refine ⟨26186567662042579490421811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 558646776790241695795665301 26186567662042579490421811)
            ·
              refine ⟨39279851493063869235632717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26186567662042579490421811 39279851493063869235632717)
              ·
                refine ⟨14729944309898950963362269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39279851493063869235632717 14729944309898950963362269)
                ·
                  refine ⟨5523729116212106611260851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14729944309898950963362269 5523729116212106611260851)
                  ·
                    refine ⟨8285593674318159916891277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5523729116212106611260851 8285593674318159916891277)
                    ·
                      refine ⟨3107097627869309968834229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8285593674318159916891277 3107097627869309968834229)
                      ·
                        rfl

theorem cell23_6051051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 3].length) (baseStart_6051051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051051 prefixEnd_6051051 := by exact prefixLift 6051051
  have htrace : WordTrace (prefixWord ++ tailWord_6051051) baseStart_6051051 baseEnd_6051051 := by
    simpa [prefixWord, tailWord_6051051, baseEnd_6051051] using wordTrace_append hprefix tailTrace_6051051
  have hstable : (prefixWord ++ tailWord_6051051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051051).length < 2 ^ (prefixWord ++ tailWord_6051051).sum := by decide
  have hdescent : baseEnd_6051051 < baseStart_6051051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051054 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6051054 : Nat := 118140960795 + 6051054 * 2 ^ 59
def prefixEnd_6051054 : Nat := 4983230072969 + 3 ^ 40 * 6051054 * 2
def baseEnd_6051054 : Nat := 1035699722770424485698905

theorem tailTrace_6051054 : CollatzResearch.WordTrace tailWord_6051054 prefixEnd_6051054 1035699722770424485698905 := by
  unfold tailWord_6051054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587508827509033824016027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147133380413381513728085477 27587508827509033824016027)
  ·
    refine ⟨41381263241263550736024041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27587508827509033824016027 41381263241263550736024041)
    ·
      refine ⟨31035947430947663052018031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41381263241263550736024041 31035947430947663052018031)
      ·
        refine ⟨46553921146421494578027047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31035947430947663052018031 46553921146421494578027047)
        ·
          refine ⟨69830881719632241867040571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46553921146421494578027047 69830881719632241867040571)
          ·
            refine ⟨104746322579448362800560857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69830881719632241867040571 104746322579448362800560857)
            ·
              refine ⟨78559741934586272100420643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104746322579448362800560857 78559741934586272100420643)
              ·
                refine ⟨117839612901879408150630965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78559741934586272100420643 117839612901879408150630965)
                ·
                  refine ⟨11047463709551194514121653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117839612901879408150630965 11047463709551194514121653)
                  ·
                    refine ⟨1035699722770424485698905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11047463709551194514121653 1035699722770424485698905)
                    ·
                      rfl

theorem cell23_6051054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6051054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051054 prefixEnd_6051054 := by exact prefixLift 6051054
  have htrace : WordTrace (prefixWord ++ tailWord_6051054) baseStart_6051054 baseEnd_6051054 := by
    simpa [prefixWord, tailWord_6051054, baseEnd_6051054] using wordTrace_append hprefix tailTrace_6051054
  have hstable : (prefixWord ++ tailWord_6051054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051054).length < 2 ^ (prefixWord ++ tailWord_6051054).sum := by decide
  have hdescent : baseEnd_6051054 < baseStart_6051054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051058 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_6051058 : Nat := 118140960795 + 6051058 * 2 ^ 59
def prefixEnd_6051058 : Nat := 4983230072969 + 3 ^ 40 * 6051058 * 2
def baseEnd_6051058 : Nat := 345233469137099049049633

theorem tailTrace_6051058 : CollatzResearch.WordTrace tailWord_6051058 prefixEnd_6051058 345233469137099049049633 := by
  unfold tailWord_6051058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55175054128014444818818457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147133477674705186183515885 55175054128014444818818457)
  ·
    refine ⟨41381290596010833614113843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55175054128014444818818457 41381290596010833614113843)
    ·
      refine ⟨62071935894016250421170765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41381290596010833614113843 62071935894016250421170765)
      ·
        refine ⟨23276975960256093907939037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62071935894016250421170765 23276975960256093907939037)
        ·
          refine ⟨8728865985096035215477139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23276975960256093907939037 8728865985096035215477139)
          ·
            refine ⟨13093298977644052823215709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728865985096035215477139 13093298977644052823215709)
            ·
              refine ⟨4909987116616519808705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13093298977644052823215709 4909987116616519808705891)
              ·
                refine ⟨7364980674924779713058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909987116616519808705891 7364980674924779713058837)
                ·
                  refine ⟨345233469137099049049633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7364980674924779713058837 345233469137099049049633)
                  ·
                    rfl

theorem cell23_6051058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_6051058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051058 prefixEnd_6051058 := by exact prefixLift 6051058
  have htrace : WordTrace (prefixWord ++ tailWord_6051058) baseStart_6051058 baseEnd_6051058 := by
    simpa [prefixWord, tailWord_6051058, baseEnd_6051058] using wordTrace_append hprefix tailTrace_6051058
  have hstable : (prefixWord ++ tailWord_6051058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051058).length < 2 ^ (prefixWord ++ tailWord_6051058).sum := by decide
  have hdescent : baseEnd_6051058 < baseStart_6051058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051071 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 1, 5]
def baseStart_6051071 : Nat := 118140960795 + 6051071 * 2 ^ 59
def prefixEnd_6051071 : Nat := 4983230072969 + 3 ^ 40 * 6051071 * 2
def baseEnd_6051071 : Nat := 1035702632494133296861379

theorem tailTrace_6051071 : CollatzResearch.WordTrace tailWord_6051071 prefixEnd_6051071 1035702632494133296861379 := by
  unfold tailWord_6051071
  simp only [CollatzResearch.WordTrace]
  refine ⟨220700690661010682495497067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147133793774007121663664711 220700690661010682495497067)
  ·
    refine ⟨331051035991516023743245601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220700690661010682495497067 331051035991516023743245601)
    ·
      refine ⟨248288276993637017807434201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331051035991516023743245601 248288276993637017807434201)
      ·
        refine ⟨186216207745227763355575651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248288276993637017807434201 186216207745227763355575651)
        ·
          refine ⟨279324311617841645033363477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186216207745227763355575651 279324311617841645033363477)
          ·
            refine ⟨13093327107086327110938913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279324311617841645033363477 13093327107086327110938913)
            ·
              refine ⟨9819995330314745333204185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13093327107086327110938913 9819995330314745333204185)
              ·
                refine ⟨7364996497736058999903139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9819995330314745333204185 7364996497736058999903139)
                ·
                  refine ⟨11047494746604088499854709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364996497736058999903139 11047494746604088499854709)
                  ·
                    refine ⟨1035702632494133296861379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11047494746604088499854709 1035702632494133296861379)
                    ·
                      rfl

theorem cell23_6051071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_6051071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051071 prefixEnd_6051071 := by exact prefixLift 6051071
  have htrace : WordTrace (prefixWord ++ tailWord_6051071) baseStart_6051071 baseEnd_6051071 := by
    simpa [prefixWord, tailWord_6051071, baseEnd_6051071] using wordTrace_append hprefix tailTrace_6051071
  have hstable : (prefixWord ++ tailWord_6051071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051071).length < 2 ^ (prefixWord ++ tailWord_6051071).sum := by decide
  have hdescent : baseEnd_6051071 < baseStart_6051071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051141 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_6051141 : Nat := 118140960795 + 6051141 * 2 ^ 59
def prefixEnd_6051141 : Nat := 4983230072969 + 3 ^ 40 * 6051141 * 2
def baseEnd_6051141 : Nat := 3107143841128214616708815

theorem tailTrace_6051141 : CollatzResearch.WordTrace tailWord_6051141 prefixEnd_6051141 3107143841128214616708815 := by
  unfold tailWord_6051141
  simp only [CollatzResearch.WordTrace]
  refine ⟨220703243770757084450545277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147135495847171389633696851 220703243770757084450545277)
  ·
    refine ⟨82763716414033906668954479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220703243770757084450545277 82763716414033906668954479)
    ·
      refine ⟨124145574621050860003431719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82763716414033906668954479 124145574621050860003431719)
      ·
        refine ⟨186218361931576290005147579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124145574621050860003431719 186218361931576290005147579)
        ·
          refine ⟨279327542897364435007721369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186218361931576290005147579 279327542897364435007721369)
          ·
            refine ⟨209495657173023326255791027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279327542897364435007721369 209495657173023326255791027)
            ·
              refine ⟨314243485759534989383686541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209495657173023326255791027 314243485759534989383686541)
              ·
                refine ⟨117841307159825621018882453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314243485759534989383686541 117841307159825621018882453)
                ·
                  refine ⟨5523811273116825985260115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117841307159825621018882453 5523811273116825985260115)
                  ·
                    refine ⟨8285716909675238977890173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5523811273116825985260115 8285716909675238977890173)
                    ·
                      refine ⟨3107143841128214616708815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8285716909675238977890173 3107143841128214616708815)
                      ·
                        rfl

theorem cell23_6051141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_6051141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051141 prefixEnd_6051141 := by exact prefixLift 6051141
  have htrace : WordTrace (prefixWord ++ tailWord_6051141) baseStart_6051141 baseEnd_6051141 := by
    simpa [prefixWord, tailWord_6051141, baseEnd_6051141] using wordTrace_append hprefix tailTrace_6051141
  have hstable : (prefixWord ++ tailWord_6051141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051141).length < 2 ^ (prefixWord ++ tailWord_6051141).sum := by decide
  have hdescent : baseEnd_6051141 < baseStart_6051141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051159 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_6051159 : Nat := 118140960795 + 6051159 * 2 ^ 59
def prefixEnd_6051159 : Nat := 4983230072969 + 3 ^ 40 * 6051159 * 2
def baseEnd_6051159 : Nat := 3107153083779995546283733

theorem tailTrace_6051159 : CollatzResearch.WordTrace tailWord_6051159 prefixEnd_6051159 3107153083779995546283733 := by
  unfold tailWord_6051159
  simp only [CollatzResearch.WordTrace]
  refine ⟨220703900284691873524700531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147135933523127915683133687 220703900284691873524700531)
  ·
    refine ⟨331055850427037810287050797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220703900284691873524700531 331055850427037810287050797)
    ·
      refine ⟨124145943910139178857644049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331055850427037810287050797 124145943910139178857644049)
      ·
        refine ⟨93109457932604384143233037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124145943910139178857644049 93109457932604384143233037)
        ·
          refine ⟨34916046724726644053712389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93109457932604384143233037 34916046724726644053712389)
          ·
            refine ⟨6546758760886245760071073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34916046724726644053712389 6546758760886245760071073)
            ·
              refine ⟨4910069070664684320053305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546758760886245760071073 4910069070664684320053305)
              ·
                refine ⟨3682551802998513240039979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910069070664684320053305 3682551802998513240039979)
                ·
                  refine ⟨5523827704497769860059969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682551802998513240039979 5523827704497769860059969)
                  ·
                    refine ⟨4142870778373327395044977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523827704497769860059969 4142870778373327395044977)
                    ·
                      refine ⟨3107153083779995546283733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142870778373327395044977 3107153083779995546283733)
                      ·
                        rfl

theorem cell23_6051159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_6051159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051159 prefixEnd_6051159 := by exact prefixLift 6051159
  have htrace : WordTrace (prefixWord ++ tailWord_6051159) baseStart_6051159 baseEnd_6051159 := by
    simpa [prefixWord, tailWord_6051159, baseEnd_6051159] using wordTrace_append hprefix tailTrace_6051159
  have hstable : (prefixWord ++ tailWord_6051159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051159).length < 2 ^ (prefixWord ++ tailWord_6051159).sum := by decide
  have hdescent : baseEnd_6051159 < baseStart_6051159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051168 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2]
def baseStart_6051168 : Nat := 118140960795 + 6051168 * 2 ^ 59
def prefixEnd_6051168 : Nat := 4983230072969 + 3 ^ 40 * 6051168 * 2
def baseEnd_6051168 : Nat := 3107157705105886011071191

theorem tailTrace_6051168 : CollatzResearch.WordTrace tailWord_6051168 prefixEnd_6051168 3107157705105886011071191 := by
  unfold tailWord_6051168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110352114270829634030889079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147136152361106178707852105 110352114270829634030889079)
  ·
    refine ⟨165528171406244451046333619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110352114270829634030889079 165528171406244451046333619)
    ·
      refine ⟨248292257109366676569500429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165528171406244451046333619 248292257109366676569500429)
      ·
        refine ⟨93109596416012503713562661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248292257109366676569500429 93109596416012503713562661)
        ·
          refine ⟨17458049328002344446292999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93109596416012503713562661 17458049328002344446292999)
          ·
            refine ⟨26187073992003516669439499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17458049328002344446292999 26187073992003516669439499)
            ·
              refine ⟨39280610988005275004159249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26187073992003516669439499 39280610988005275004159249)
              ·
                refine ⟨29460458241003956253119437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39280610988005275004159249 29460458241003956253119437)
                ·
                  refine ⟨11047671840376483594919789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29460458241003956253119437 11047671840376483594919789)
                  ·
                    refine ⟨4142876940141181348094921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11047671840376483594919789 4142876940141181348094921)
                    ·
                      refine ⟨3107157705105886011071191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142876940141181348094921 3107157705105886011071191)
                      ·
                        rfl

theorem cell23_6051168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_6051168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051168 prefixEnd_6051168 := by exact prefixLift 6051168
  have htrace : WordTrace (prefixWord ++ tailWord_6051168) baseStart_6051168 baseEnd_6051168 := by
    simpa [prefixWord, tailWord_6051168, baseEnd_6051168] using wordTrace_append hprefix tailTrace_6051168
  have hstable : (prefixWord ++ tailWord_6051168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051168).length < 2 ^ (prefixWord ++ tailWord_6051168).sum := by decide
  have hdescent : baseEnd_6051168 < baseStart_6051168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051232 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2]
def baseStart_6051232 : Nat := 118140960795 + 6051232 * 2 ^ 59
def prefixEnd_6051232 : Nat := 4983230072969 + 3 ^ 40 * 6051232 * 2
def baseEnd_6051232 : Nat := 3107190567867773760670897

theorem tailTrace_6051232 : CollatzResearch.WordTrace tailWord_6051232 prefixEnd_6051232 3107190567867773760670897 := by
  unfold tailWord_6051232
  simp only [CollatzResearch.WordTrace]
  refine ⟨110353281406713703496053975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147137708542284937994738633 110353281406713703496053975)
  ·
    refine ⟨165529922110070555244080963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110353281406713703496053975 165529922110070555244080963)
    ·
      refine ⟨248294883165105832866121445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165529922110070555244080963 248294883165105832866121445)
      ·
        refine ⟨46555290593457343662397771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248294883165105832866121445 46555290593457343662397771)
        ·
          refine ⟨69832935890186015493596657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46555290593457343662397771 69832935890186015493596657)
          ·
            refine ⟨52374701917639511620197493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69832935890186015493596657 52374701917639511620197493)
            ·
              refine ⟨4910128304778704214393515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52374701917639511620197493 4910128304778704214393515)
              ·
                refine ⟨7365192457168056321590273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910128304778704214393515 7365192457168056321590273)
                ·
                  refine ⟨5523894342876042241192705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365192457168056321590273 5523894342876042241192705)
                  ·
                    refine ⟨4142920757157031680894529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5523894342876042241192705 4142920757157031680894529)
                    ·
                      refine ⟨3107190567867773760670897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142920757157031680894529 3107190567867773760670897)
                      ·
                        rfl

theorem cell23_6051232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_6051232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051232 prefixEnd_6051232 := by exact prefixLift 6051232
  have htrace : WordTrace (prefixWord ++ tailWord_6051232) baseStart_6051232 baseEnd_6051232 := by
    simpa [prefixWord, tailWord_6051232, baseEnd_6051232] using wordTrace_append hprefix tailTrace_6051232
  have hstable : (prefixWord ++ tailWord_6051232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051232).length < 2 ^ (prefixWord ++ tailWord_6051232).sum := by decide
  have hdescent : baseEnd_6051232 < baseStart_6051232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051261 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6051261 : Nat := 118140960795 + 6051261 * 2 ^ 59
def prefixEnd_6051261 : Nat := 4983230072969 + 3 ^ 40 * 6051261 * 2
def baseEnd_6051261 : Nat := 3107205458806754147208263

theorem tailTrace_6051261 : CollatzResearch.WordTrace tailWord_6051261 prefixEnd_6051261 3107205458806754147208263 := by
  unfold tailWord_6051261
  simp only [CollatzResearch.WordTrace]
  refine ⟨220707620530322344944913637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147138413686881563296609091 220707620530322344944913637)
  ·
    refine ⟨41382678849435439677171307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220707620530322344944913637 41382678849435439677171307)
    ·
      refine ⟨62074018274153159515756961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41382678849435439677171307 62074018274153159515756961)
      ·
        refine ⟨46555513705614869636817721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62074018274153159515756961 46555513705614869636817721)
        ·
          refine ⟨34916635279211152227613291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46555513705614869636817721 34916635279211152227613291)
          ·
            refine ⟨52374952918816728341419937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34916635279211152227613291 52374952918816728341419937)
            ·
              refine ⟨39281214689112546256064953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52374952918816728341419937 39281214689112546256064953)
              ·
                refine ⟨29460911016834409692048715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39281214689112546256064953 29460911016834409692048715)
                ·
                  refine ⟨44191366525251614538073073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29460911016834409692048715 44191366525251614538073073)
                  ·
                    refine ⟨33143524893938710903554805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44191366525251614538073073 33143524893938710903554805)
                    ·
                      refine ⟨3107205458806754147208263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33143524893938710903554805 3107205458806754147208263)
                      ·
                        rfl

theorem cell23_6051261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6051261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051261 prefixEnd_6051261 := by exact prefixLift 6051261
  have htrace : WordTrace (prefixWord ++ tailWord_6051261) baseStart_6051261 baseEnd_6051261 := by
    simpa [prefixWord, tailWord_6051261, baseEnd_6051261] using wordTrace_append hprefix tailTrace_6051261
  have hstable : (prefixWord ++ tailWord_6051261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051261).length < 2 ^ (prefixWord ++ tailWord_6051261).sum := by decide
  have hdescent : baseEnd_6051261 < baseStart_6051261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051268 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6051268 : Nat := 118140960795 + 6051268 * 2 ^ 59
def prefixEnd_6051268 : Nat := 4983230072969 + 3 ^ 40 * 6051268 * 2
def baseEnd_6051268 : Nat := 1035736351057111873273577

theorem tailTrace_6051268 : CollatzResearch.WordTrace tailWord_6051268 prefixEnd_6051268 1035736351057111873273577 := by
  unfold tailWord_6051268
  simp only [CollatzResearch.WordTrace]
  refine ⟨110353937920648492570209229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147138583894197990093612305 110353937920648492570209229)
  ·
    refine ⟨41382726720243184713828461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110353937920648492570209229 41382726720243184713828461)
    ·
      refine ⟨15518522520091194267685673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41382726720243184713828461 15518522520091194267685673)
      ·
        refine ⟨11638891890068395700764255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15518522520091194267685673 11638891890068395700764255)
        ·
          refine ⟨17458337835102593551146383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638891890068395700764255 17458337835102593551146383)
          ·
            refine ⟨26187506752653890326719575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17458337835102593551146383 26187506752653890326719575)
            ·
              refine ⟨39281260128980835490079363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26187506752653890326719575 39281260128980835490079363)
              ·
                refine ⟨58921890193471253235119045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39281260128980835490079363 58921890193471253235119045)
                ·
                  refine ⟨11047854411275859981584821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58921890193471253235119045 11047854411275859981584821)
                  ·
                    refine ⟨1035736351057111873273577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11047854411275859981584821 1035736351057111873273577)
                    ·
                      rfl

theorem cell23_6051268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6051268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051268 prefixEnd_6051268 := by exact prefixLift 6051268
  have htrace : WordTrace (prefixWord ++ tailWord_6051268) baseStart_6051268 baseEnd_6051268 := by
    simpa [prefixWord, tailWord_6051268, baseEnd_6051268] using wordTrace_append hprefix tailTrace_6051268
  have hstable : (prefixWord ++ tailWord_6051268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051268).length < 2 ^ (prefixWord ++ tailWord_6051268).sum := by decide
  have hdescent : baseEnd_6051268 < baseStart_6051268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051288 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_6051288 : Nat := 118140960795 + 6051288 * 2 ^ 59
def prefixEnd_6051288 : Nat := 4983230072969 + 3 ^ 40 * 6051288 * 2
def baseEnd_6051288 : Nat := 3107219322784425541570639

theorem tailTrace_6051288 : CollatzResearch.WordTrace tailWord_6051288 prefixEnd_6051288 3107219322784425541570639 := by
  unfold tailWord_6051288
  simp only [CollatzResearch.WordTrace]
  refine ⟨110354302650612264278073259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147139070200816352370764345 110354302650612264278073259)
  ·
    refine ⟨165531453975918396417109889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110354302650612264278073259 165531453975918396417109889)
    ·
      refine ⟨124148590481938797312832417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165531453975918396417109889 124148590481938797312832417)
      ·
        refine ⟨93111442861454097984624313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124148590481938797312832417 93111442861454097984624313)
        ·
          refine ⟨69833582146090573488468235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93111442861454097984624313 69833582146090573488468235)
          ·
            refine ⟨104750373219135860232702353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69833582146090573488468235 104750373219135860232702353)
            ·
              refine ⟨78562779914351895174526765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104750373219135860232702353 78562779914351895174526765)
              ·
                refine ⟨29461042467881960690447537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78562779914351895174526765 29461042467881960690447537)
                ·
                  refine ⟨22095781850911470517835653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29461042467881960690447537 22095781850911470517835653)
                  ·
                    refine ⟨4142959097045900722094185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22095781850911470517835653 4142959097045900722094185)
                    ·
                      refine ⟨3107219322784425541570639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4142959097045900722094185 3107219322784425541570639)
                      ·
                        rfl

theorem cell23_6051288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_6051288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051288 prefixEnd_6051288 := by exact prefixLift 6051288
  have htrace : WordTrace (prefixWord ++ tailWord_6051288) baseStart_6051288 baseEnd_6051288 := by
    simpa [prefixWord, tailWord_6051288, baseEnd_6051288] using wordTrace_append hprefix tailTrace_6051288
  have hstable : (prefixWord ++ tailWord_6051288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051288).length < 2 ^ (prefixWord ++ tailWord_6051288).sum := by decide
  have hdescent : baseEnd_6051288 < baseStart_6051288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051412 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_6051412 : Nat := 118140960795 + 6051412 * 2 ^ 59
def prefixEnd_6051412 : Nat := 4983230072969 + 3 ^ 40 * 6051412 * 2
def baseEnd_6051412 : Nat := 3107282994385583056420069

theorem tailTrace_6051412 : CollatzResearch.WordTrace tailWord_6051412 prefixEnd_6051412 3107282994385583056420069 := by
  unfold tailWord_6051412
  simp only [CollatzResearch.WordTrace]
  refine ⟨110356563976387648866830245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147142085301850198489106993 110356563976387648866830245)
  ·
    refine ⟨20691855745572684162530671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110356563976387648866830245 20691855745572684162530671)
    ·
      refine ⟨31037783618359026243796007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691855745572684162530671 31037783618359026243796007)
      ·
        refine ⟨46556675427538539365694011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31037783618359026243796007 46556675427538539365694011)
        ·
          refine ⟨69835013141307809048541017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46556675427538539365694011 69835013141307809048541017)
          ·
            refine ⟨52376259855980856786405763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69835013141307809048541017 52376259855980856786405763)
            ·
              refine ⟨78564389783971285179608645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52376259855980856786405763 78564389783971285179608645)
              ·
                refine ⟨14730823084494615971176621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78564389783971285179608645 14730823084494615971176621)
                ·
                  refine ⟨5524058656685480989191233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14730823084494615971176621 5524058656685480989191233)
                  ·
                    refine ⟨4143043992514110741893425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524058656685480989191233 4143043992514110741893425)
                    ·
                      refine ⟨3107282994385583056420069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143043992514110741893425 3107282994385583056420069)
                      ·
                        rfl

theorem cell23_6051412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_6051412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051412 prefixEnd_6051412 := by exact prefixLift 6051412
  have htrace : WordTrace (prefixWord ++ tailWord_6051412) baseStart_6051412 baseEnd_6051412 := by
    simpa [prefixWord, tailWord_6051412, baseEnd_6051412] using wordTrace_append hprefix tailTrace_6051412
  have hstable : (prefixWord ++ tailWord_6051412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051412).length < 2 ^ (prefixWord ++ tailWord_6051412).sum := by decide
  have hdescent : baseEnd_6051412 < baseStart_6051412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051415 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_6051415 : Nat := 118140960795 + 6051415 * 2 ^ 59
def prefixEnd_6051415 : Nat := 4983230072969 + 3 ^ 40 * 6051415 * 2
def baseEnd_6051415 : Nat := 3107284534827546544682555

theorem tailTrace_6051415 : CollatzResearch.WordTrace tailWord_6051415 prefixEnd_6051415 3107284534827546544682555 := by
  unfold tailWord_6051415
  simp only [CollatzResearch.WordTrace]
  refine ⟨220713237371764429246019699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147142158247842952830679799 220713237371764429246019699)
  ·
    refine ⟨331069856057646643869029549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220713237371764429246019699 331069856057646643869029549)
    ·
      refine ⟨124151196021617491450886081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331069856057646643869029549 124151196021617491450886081)
      ·
        refine ⟨93113397016213118588164561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124151196021617491450886081 93113397016213118588164561)
        ·
          refine ⟨69835047762159838941123421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93113397016213118588164561 69835047762159838941123421)
          ·
            refine ⟨26188142910809939602921283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69835047762159838941123421 26188142910809939602921283)
            ·
              refine ⟨39282214366214909404381925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26188142910809939602921283 39282214366214909404381925)
              ·
                refine ⟨7365415193665295513321611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39282214366214909404381925 7365415193665295513321611)
                ·
                  refine ⟨11048122790497943269982417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365415193665295513321611 11048122790497943269982417)
                  ·
                    refine ⟨8286092092873457452486813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11048122790497943269982417 8286092092873457452486813)
                    ·
                      refine ⟨3107284534827546544682555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286092092873457452486813 3107284534827546544682555)
                      ·
                        rfl

theorem cell23_6051415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_6051415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051415 prefixEnd_6051415 := by exact prefixLift 6051415
  have htrace : WordTrace (prefixWord ++ tailWord_6051415) baseStart_6051415 baseEnd_6051415 := by
    simpa [prefixWord, tailWord_6051415, baseEnd_6051415] using wordTrace_append hprefix tailTrace_6051415
  have hstable : (prefixWord ++ tailWord_6051415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051415).length < 2 ^ (prefixWord ++ tailWord_6051415).sum := by decide
  have hdescent : baseEnd_6051415 < baseStart_6051415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051432 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6051432 : Nat := 118140960795 + 6051432 * 2 ^ 59
def prefixEnd_6051432 : Nat := 4983230072969 + 3 ^ 40 * 6051432 * 2
def baseEnd_6051432 : Nat := 3107293263998672978169977

theorem tailTrace_6051432 : CollatzResearch.WordTrace tailWord_6051432 prefixEnd_6051432 3107293263998672978169977 := by
  unfold tailWord_6051432
  simp only [CollatzResearch.WordTrace]
  refine ⟨110356928706351420574694275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147142571608468560766259033 110356928706351420574694275)
  ·
    refine ⟨165535393059527130862041413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110356928706351420574694275 165535393059527130862041413)
    ·
      refine ⟨31037886198661337036632765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165535393059527130862041413 31037886198661337036632765)
      ·
        refine ⟨11639207324498001388737287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31037886198661337036632765 11639207324498001388737287)
        ·
          refine ⟨17458810986747002083105931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639207324498001388737287 17458810986747002083105931)
          ·
            refine ⟨26188216480120503124658897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17458810986747002083105931 26188216480120503124658897)
            ·
              refine ⟨19641162360090377343494173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26188216480120503124658897 19641162360090377343494173)
              ·
                refine ⟨7365435885033891503810315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19641162360090377343494173 7365435885033891503810315)
                ·
                  refine ⟨11048153827550837255715473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365435885033891503810315 11048153827550837255715473)
                  ·
                    refine ⟨8286115370663127941786605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11048153827550837255715473 8286115370663127941786605)
                    ·
                      refine ⟨3107293263998672978169977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286115370663127941786605 3107293263998672978169977)
                      ·
                        rfl

theorem cell23_6051432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6051432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051432 prefixEnd_6051432 := by exact prefixLift 6051432
  have htrace : WordTrace (prefixWord ++ tailWord_6051432) baseStart_6051432 baseEnd_6051432 := by
    simpa [prefixWord, tailWord_6051432, baseEnd_6051432] using wordTrace_append hprefix tailTrace_6051432
  have hstable : (prefixWord ++ tailWord_6051432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051432).length < 2 ^ (prefixWord ++ tailWord_6051432).sum := by decide
  have hdescent : baseEnd_6051432 < baseStart_6051432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051446 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6051446 : Nat := 118140960795 + 6051446 * 2 ^ 59
def prefixEnd_6051446 : Nat := 4983230072969 + 3 ^ 40 * 6051446 * 2
def baseEnd_6051446 : Nat := 3107300452727835923394913

theorem tailTrace_6051446 : CollatzResearch.WordTrace tailWord_6051446 prefixEnd_6051446 3107300452727835923394913 := by
  unfold tailWord_6051446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794648002165757596274887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147142912023101414360265461 13794648002165757596274887)
  ·
    refine ⟨20691972003248636394412331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13794648002165757596274887 20691972003248636394412331)
    ·
      refine ⟨31037958004872954591618497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691972003248636394412331 31037958004872954591618497)
      ·
        refine ⟨23278468503654715943713873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31037958004872954591618497 23278468503654715943713873)
        ·
          refine ⟨17458851377741036957785405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23278468503654715943713873 17458851377741036957785405)
          ·
            refine ⟨6547069266652888859169527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17458851377741036957785405 6547069266652888859169527)
            ·
              refine ⟨9820603899979333288754291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547069266652888859169527 9820603899979333288754291)
              ·
                refine ⟨14730905849968999933131437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9820603899979333288754291 14730905849968999933131437)
                ·
                  refine ⟨5524089693738374974924289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14730905849968999933131437 5524089693738374974924289)
                  ·
                    refine ⟨4143067270303781231193217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524089693738374974924289 4143067270303781231193217)
                    ·
                      refine ⟨3107300452727835923394913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143067270303781231193217 3107300452727835923394913)
                      ·
                        rfl

theorem cell23_6051446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6051446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051446 prefixEnd_6051446 := by exact prefixLift 6051446
  have htrace : WordTrace (prefixWord ++ tailWord_6051446) baseStart_6051446 baseEnd_6051446 := by
    simpa [prefixWord, tailWord_6051446, baseEnd_6051446] using wordTrace_append hprefix tailTrace_6051446
  have hstable : (prefixWord ++ tailWord_6051446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051446).length < 2 ^ (prefixWord ++ tailWord_6051446).sum := by decide
  have hdescent : baseEnd_6051446 < baseStart_6051446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051553 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_6051553 : Nat := 118140960795 + 6051553 * 2 ^ 59
def prefixEnd_6051553 : Nat := 4983230072969 + 3 ^ 40 * 6051553 * 2
def baseEnd_6051553 : Nat := 3107355395157867004756921

theorem tailTrace_6051553 : CollatzResearch.WordTrace tailWord_6051553 prefixEnd_6051553 3107355395157867004756921 := by
  unfold tailWord_6051553
  simp only [CollatzResearch.WordTrace]
  refine ⟨220718270645264478814543313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147145513763509652543028875 220718270645264478814543313)
  ·
    refine ⟨165538702983948359110907485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220718270645264478814543313 165538702983948359110907485)
    ·
      refine ⟨62077013618980634666590307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165538702983948359110907485 62077013618980634666590307)
      ·
        refine ⟨93115520428470951999885461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62077013618980634666590307 93115520428470951999885461)
        ·
          refine ⟨4364790020084575874994631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93115520428470951999885461 4364790020084575874994631)
          ·
            refine ⟨6547185030126863812491947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364790020084575874994631 6547185030126863812491947)
            ·
              refine ⟨9820777545190295718737921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547185030126863812491947 9820777545190295718737921)
              ·
                refine ⟨7365583158892721789053441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9820777545190295718737921 7365583158892721789053441)
                ·
                  refine ⟨5524187369169541341790081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365583158892721789053441 5524187369169541341790081)
                  ·
                    refine ⟨4143140526877156006342561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524187369169541341790081 4143140526877156006342561)
                    ·
                      refine ⟨3107355395157867004756921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143140526877156006342561 3107355395157867004756921)
                      ·
                        rfl

theorem cell23_6051553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_6051553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051553 prefixEnd_6051553 := by exact prefixLift 6051553
  have htrace : WordTrace (prefixWord ++ tailWord_6051553) baseStart_6051553 baseEnd_6051553 := by
    simpa [prefixWord, tailWord_6051553, baseEnd_6051553] using wordTrace_append hprefix tailTrace_6051553
  have hstable : (prefixWord ++ tailWord_6051553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051553).length < 2 ^ (prefixWord ++ tailWord_6051553).sum := by decide
  have hdescent : baseEnd_6051553 < baseStart_6051553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051595 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3]
def baseStart_6051595 : Nat := 118140960795 + 6051595 * 2 ^ 59
def prefixEnd_6051595 : Nat := 4983230072969 + 3 ^ 40 * 6051595 * 2
def baseEnd_6051595 : Nat := 3107376961345355840431727

theorem tailTrace_6051595 : CollatzResearch.WordTrace tailWord_6051595 prefixEnd_6051595 3107376961345355840431727 := by
  unfold tailWord_6051595
  simp only [CollatzResearch.WordTrace]
  refine ⟨220719802511112319987572239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147146535007408213325048159 220719802511112319987572239)
  ·
    refine ⟨331079703766668479981358359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220719802511112319987572239 331079703766668479981358359)
    ·
      refine ⟨496619555650002719972037539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331079703766668479981358359 496619555650002719972037539)
      ·
        refine ⟨744929333475004079958056309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496619555650002719972037539 744929333475004079958056309)
        ·
          refine ⟨69837125013281632496067779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 744929333475004079958056309 69837125013281632496067779)
          ·
            refine ⟨104755687519922448744101669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69837125013281632496067779 104755687519922448744101669)
            ·
              refine ⟨19641691409985459139519063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104755687519922448744101669 19641691409985459139519063)
              ·
                refine ⟨29462537114978188709278595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641691409985459139519063 29462537114978188709278595)
                ·
                  refine ⟨44193805672467283063917893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29462537114978188709278595 44193805672467283063917893)
                  ·
                    refine ⟨8286338563587615574484605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44193805672467283063917893 8286338563587615574484605)
                    ·
                      refine ⟨3107376961345355840431727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286338563587615574484605 3107376961345355840431727)
                      ·
                        rfl

theorem cell23_6051595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].length) (baseStart_6051595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051595 prefixEnd_6051595 := by exact prefixLift 6051595
  have htrace : WordTrace (prefixWord ++ tailWord_6051595) baseStart_6051595 baseEnd_6051595 := by
    simpa [prefixWord, tailWord_6051595, baseEnd_6051595] using wordTrace_append hprefix tailTrace_6051595
  have hstable : (prefixWord ++ tailWord_6051595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051595).length < 2 ^ (prefixWord ++ tailWord_6051595).sum := by decide
  have hdescent : baseEnd_6051595 < baseStart_6051595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051612 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6051612 : Nat := 118140960795 + 6051612 * 2 ^ 59
def prefixEnd_6051612 : Nat := 4983230072969 + 3 ^ 40 * 6051612 * 2
def baseEnd_6051612 : Nat := 3107385690516482273919149

theorem tailTrace_6051612 : CollatzResearch.WordTrace tailWord_6051612 prefixEnd_6051612 3107385690516482273919149 := by
  unfold tailWord_6051612
  simp only [CollatzResearch.WordTrace]
  refine ⟨110360211276025365945470545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147146948368033821260627393 110360211276025365945470545)
  ·
    refine ⟨82770158457019024459102909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110360211276025365945470545 82770158457019024459102909)
    ·
      refine ⟨31038809421382134172163591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82770158457019024459102909 31038809421382134172163591)
      ·
        refine ⟨46558214132073201258245387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31038809421382134172163591 46558214132073201258245387)
        ·
          refine ⟨69837321198109801887368081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46558214132073201258245387 69837321198109801887368081)
          ·
            refine ⟨52377990898582351415526061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69837321198109801887368081 52377990898582351415526061)
            ·
              refine ⟨19641746586968381780822273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52377990898582351415526061 19641746586968381780822273)
              ·
                refine ⟨14731309940226286335616705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19641746586968381780822273 14731309940226286335616705)
                ·
                  refine ⟨11048482455169714751712529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14731309940226286335616705 11048482455169714751712529)
                  ·
                    refine ⟨8286361841377286063784397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11048482455169714751712529 8286361841377286063784397)
                    ·
                      refine ⟨3107385690516482273919149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286361841377286063784397 3107385690516482273919149)
                      ·
                        rfl

theorem cell23_6051612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6051612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051612 prefixEnd_6051612 := by exact prefixLift 6051612
  have htrace : WordTrace (prefixWord ++ tailWord_6051612) baseStart_6051612 baseEnd_6051612 := by
    simpa [prefixWord, tailWord_6051612, baseEnd_6051612] using wordTrace_append hprefix tailTrace_6051612
  have hstable : (prefixWord ++ tailWord_6051612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051612).length < 2 ^ (prefixWord ++ tailWord_6051612).sum := by decide
  have hdescent : baseEnd_6051612 < baseStart_6051612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051615 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 6]
def baseStart_6051615 : Nat := 118140960795 + 6051615 * 2 ^ 59
def prefixEnd_6051615 : Nat := 4983230072969 + 3 ^ 40 * 6051615 * 2
def baseEnd_6051615 : Nat := 345265247884271751353515

theorem tailTrace_6051615 : CollatzResearch.WordTrace tailWord_6051615 prefixEnd_6051615 345265247884271751353515 := by
  unfold tailWord_6051615
  simp only [CollatzResearch.WordTrace]
  refine ⟨220720531971039863403300299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147147021314026575602200199 220720531971039863403300299)
  ·
    refine ⟨331080797956559795104950449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220720531971039863403300299 331080797956559795104950449)
    ·
      refine ⟨248310598467419846328712837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331080797956559795104950449 248310598467419846328712837)
      ·
        refine ⟨46558237212641221186633657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248310598467419846328712837 46558237212641221186633657)
        ·
          refine ⟨34918677909480915889975243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46558237212641221186633657 34918677909480915889975243)
          ·
            refine ⟨52378016864221373834962865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34918677909480915889975243 52378016864221373834962865)
            ·
              refine ⟨39283512648166030376222149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52378016864221373834962865 39283512648166030376222149)
              ·
                refine ⟨7365658621531130695541653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39283512648166030376222149 7365658621531130695541653)
                ·
                  refine ⟨345265247884271751353515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7365658621531130695541653 345265247884271751353515)
                  ·
                    rfl

theorem cell23_6051615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 6].length) (baseStart_6051615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051615 prefixEnd_6051615 := by exact prefixLift 6051615
  have htrace : WordTrace (prefixWord ++ tailWord_6051615) baseStart_6051615 baseEnd_6051615 := by
    simpa [prefixWord, tailWord_6051615, baseEnd_6051615] using wordTrace_append hprefix tailTrace_6051615
  have hstable : (prefixWord ++ tailWord_6051615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051615).length < 2 ^ (prefixWord ++ tailWord_6051615).sum := by decide
  have hdescent : baseEnd_6051615 < baseStart_6051615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051669 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6051669 : Nat := 118140960795 + 6051669 * 2 ^ 59
def prefixEnd_6051669 : Nat := 4983230072969 + 3 ^ 40 * 6051669 * 2
def baseEnd_6051669 : Nat := 3107414958913788550906387

theorem tailTrace_6051669 : CollatzResearch.WordTrace tailWord_6051669 prefixEnd_6051669 3107414958913788550906387 := by
  unfold tailWord_6051669
  simp only [CollatzResearch.WordTrace]
  refine ⟨220722501512844230625766061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147148334341896153750510707 220722501512844230625766061)
  ·
    refine ⟨82770938067316586484662273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220722501512844230625766061 82770938067316586484662273)
    ·
      refine ⟨62078203550487439863496705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82770938067316586484662273 62078203550487439863496705)
      ·
        refine ⟨46558652662865579897622529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62078203550487439863496705 46558652662865579897622529)
        ·
          refine ⟨34918989497149184923216897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46558652662865579897622529 34918989497149184923216897)
          ·
            refine ⟨26189242122861888692412673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34918989497149184923216897 26189242122861888692412673)
            ·
              refine ⟨19641931592146416519309505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26189242122861888692412673 19641931592146416519309505)
              ·
                refine ⟨14731448694109812389482129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19641931592146416519309505 14731448694109812389482129)
                ·
                  refine ⟨11048586520582359292111597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14731448694109812389482129 11048586520582359292111597)
                  ·
                    refine ⟨4143219945218384734541849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11048586520582359292111597 4143219945218384734541849)
                    ·
                      refine ⟨3107414958913788550906387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143219945218384734541849 3107414958913788550906387)
                      ·
                        rfl

theorem cell23_6051669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6051669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051669 prefixEnd_6051669 := by exact prefixLift 6051669
  have htrace : WordTrace (prefixWord ++ tailWord_6051669) baseStart_6051669 baseEnd_6051669 := by
    simpa [prefixWord, tailWord_6051669, baseEnd_6051669] using wordTrace_append hprefix tailTrace_6051669
  have hstable : (prefixWord ++ tailWord_6051669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051669).length < 2 ^ (prefixWord ++ tailWord_6051669).sum := by decide
  have hdescent : baseEnd_6051669 < baseStart_6051669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051685 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6051685 : Nat := 118140960795 + 6051685 * 2 ^ 59
def prefixEnd_6051685 : Nat := 4983230072969 + 3 ^ 40 * 6051685 * 2
def baseEnd_6051685 : Nat := 3107423174604260488306313

theorem tailTrace_6051685 : CollatzResearch.WordTrace tailWord_6051685 prefixEnd_6051685 3107423174604260488306313 := by
  unfold tailWord_6051685
  simp only [CollatzResearch.WordTrace]
  refine ⟨220723085080786265358348509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147148723387190843572232339 220723085080786265358348509)
  ·
    refine ⟨82771156905294849509380691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220723085080786265358348509 82771156905294849509380691)
    ·
      refine ⟨124156735357942274264071037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82771156905294849509380691 124156735357942274264071037)
      ·
        refine ⟨46558775759228352849026639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124156735357942274264071037 46558775759228352849026639)
        ·
          refine ⟨69838163638842529273539959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46558775759228352849026639 69838163638842529273539959)
          ·
            refine ⟨104757245458263793910309939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69838163638842529273539959 104757245458263793910309939)
            ·
              refine ⟨157135868187395690865464909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104757245458263793910309939 157135868187395690865464909)
              ·
                refine ⟨58925950570273384074549341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157135868187395690865464909 58925950570273384074549341)
                ·
                  refine ⟨22097231463852519027956003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58925950570273384074549341 22097231463852519027956003)
                  ·
                    refine ⟨33145847195778778541934005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22097231463852519027956003 33145847195778778541934005)
                    ·
                      refine ⟨3107423174604260488306313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33145847195778778541934005 3107423174604260488306313)
                      ·
                        rfl

theorem cell23_6051685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6051685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051685 prefixEnd_6051685 := by exact prefixLift 6051685
  have htrace : WordTrace (prefixWord ++ tailWord_6051685) baseStart_6051685 baseEnd_6051685 := by
    simpa [prefixWord, tailWord_6051685, baseEnd_6051685] using wordTrace_append hprefix tailTrace_6051685
  have hstable : (prefixWord ++ tailWord_6051685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051685).length < 2 ^ (prefixWord ++ tailWord_6051685).sum := by decide
  have hdescent : baseEnd_6051685 < baseStart_6051685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051692 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_6051692 : Nat := 118140960795 + 6051692 * 2 ^ 59
def prefixEnd_6051692 : Nat := 4983230072969 + 3 ^ 40 * 6051692 * 2
def baseEnd_6051692 : Nat := 1035808922989613986972927

theorem tailTrace_6051692 : CollatzResearch.WordTrace tailWord_6051692 prefixEnd_6051692 1035808922989613986972927 := by
  unfold tailWord_6051692
  simp only [CollatzResearch.WordTrace]
  refine ⟨110361670195880452776926665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147148893594507270369235553 110361670195880452776926665)
  ·
    refine ⟨82771252646910339582694999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110361670195880452776926665 82771252646910339582694999)
    ·
      refine ⟨124156878970365509374042499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82771252646910339582694999 124156878970365509374042499)
      ·
        refine ⟨186235318455548264061063749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124156878970365509374042499 186235318455548264061063749)
        ·
          refine ⟨34919122210415299511449453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186235318455548264061063749 34919122210415299511449453)
          ·
            refine ⟨13094670828905737316793545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34919122210415299511449453 13094670828905737316793545)
            ·
              refine ⟨9821003121679302987595159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094670828905737316793545 9821003121679302987595159)
              ·
                refine ⟨14731504682518954481392739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821003121679302987595159 14731504682518954481392739)
                ·
                  refine ⟨22097257023778431722089109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14731504682518954481392739 22097257023778431722089109)
                  ·
                    refine ⟨1035808922989613986972927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22097257023778431722089109 1035808922989613986972927)
                    ·
                      rfl

theorem cell23_6051692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_6051692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051692 prefixEnd_6051692 := by exact prefixLift 6051692
  have htrace : WordTrace (prefixWord ++ tailWord_6051692) baseStart_6051692 baseEnd_6051692 := by
    simpa [prefixWord, tailWord_6051692, baseEnd_6051692] using wordTrace_append hprefix tailTrace_6051692
  have hstable : (prefixWord ++ tailWord_6051692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051692).length < 2 ^ (prefixWord ++ tailWord_6051692).sum := by decide
  have hdescent : baseEnd_6051692 < baseStart_6051692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051710 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6051710 : Nat := 118140960795 + 6051710 * 2 ^ 59
def prefixEnd_6051710 : Nat := 4983230072969 + 3 ^ 40 * 6051710 * 2
def baseEnd_6051710 : Nat := 3107436011620622890493699

theorem tailTrace_6051710 : CollatzResearch.WordTrace tailWord_6051710 prefixEnd_6051710 3107436011620622890493699 := by
  unfold tailWord_6051710
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590499613211961828501073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147149331270463796418672389 27590499613211961828501073)
  ·
    refine ⟨20692874709908971371375805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27590499613211961828501073 20692874709908971371375805)
    ·
      refine ⟨7759828016215864264265927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20692874709908971371375805 7759828016215864264265927)
      ·
        refine ⟨11639742024323796396398891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759828016215864264265927 11639742024323796396398891)
        ·
          refine ⟨17459613036485694594598337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639742024323796396398891 17459613036485694594598337)
          ·
            refine ⟨13094709777364270945948753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17459613036485694594598337 13094709777364270945948753)
            ·
              refine ⟨9821032333023203209461565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094709777364270945948753 9821032333023203209461565)
              ·
                refine ⟨3682887124883701203548087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821032333023203209461565 3682887124883701203548087)
                ·
                  refine ⟨5524330687325551805322131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682887124883701203548087 5524330687325551805322131)
                  ·
                    refine ⟨8286496030988327707983197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524330687325551805322131 8286496030988327707983197)
                    ·
                      refine ⟨3107436011620622890493699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286496030988327707983197 3107436011620622890493699)
                      ·
                        rfl

theorem cell23_6051710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6051710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051710 prefixEnd_6051710 := by exact prefixLift 6051710
  have htrace : WordTrace (prefixWord ++ tailWord_6051710) baseStart_6051710 baseEnd_6051710 := by
    simpa [prefixWord, tailWord_6051710, baseEnd_6051710] using wordTrace_append hprefix tailTrace_6051710
  have hstable : (prefixWord ++ tailWord_6051710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051710).length < 2 ^ (prefixWord ++ tailWord_6051710).sum := by decide
  have hdescent : baseEnd_6051710 < baseStart_6051710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051713 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6051713 : Nat := 118140960795 + 6051713 * 2 ^ 59
def prefixEnd_6051713 : Nat := 4983230072969 + 3 ^ 40 * 6051713 * 2
def baseEnd_6051713 : Nat := 1035812517354195459585395

theorem tailTrace_6051713 : CollatzResearch.WordTrace tailWord_6051713 prefixEnd_6051713 1035812517354195459585395 := by
  unfold tailWord_6051713
  simp only [CollatzResearch.WordTrace]
  refine ⟨220724106324684826140367793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147149404216456550760245195 220724106324684826140367793)
  ·
    refine ⟨165543079743513619605275845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220724106324684826140367793 165543079743513619605275845)
    ·
      refine ⟨31039327451908803675989221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165543079743513619605275845 31039327451908803675989221)
      ·
        refine ⟨5819873897232900689247979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31039327451908803675989221 5819873897232900689247979)
        ·
          refine ⟨8729810845849351033871969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819873897232900689247979 8729810845849351033871969)
          ·
            refine ⟨6547358134387013275403977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729810845849351033871969 6547358134387013275403977)
            ·
              refine ⟨4910518600790259956552983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6547358134387013275403977 4910518600790259956552983)
              ·
                refine ⟨7365777901185389934829475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910518600790259956552983 7365777901185389934829475)
                ·
                  refine ⟨11048666851778084902244213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365777901185389934829475 11048666851778084902244213)
                  ·
                    refine ⟨1035812517354195459585395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11048666851778084902244213 1035812517354195459585395)
                    ·
                      rfl

theorem cell23_6051713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6051713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051713 prefixEnd_6051713 := by exact prefixLift 6051713
  have htrace : WordTrace (prefixWord ++ tailWord_6051713) baseStart_6051713 baseEnd_6051713 := by
    simpa [prefixWord, tailWord_6051713, baseEnd_6051713] using wordTrace_append hprefix tailTrace_6051713
  have hstable : (prefixWord ++ tailWord_6051713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051713).length < 2 ^ (prefixWord ++ tailWord_6051713).sum := by decide
  have hdescent : baseEnd_6051713 < baseStart_6051713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051722 : List Nat := [3, 1, 2, 4, 2, 1, 10]
def baseStart_6051722 : Nat := 118140960795 + 6051722 * 2 ^ 59
def prefixEnd_6051722 : Nat := 4983230072969 + 3 ^ 40 * 6051722 * 2
def baseEnd_6051722 : Nat := 38363483622079961031403

theorem tailTrace_6051722 : CollatzResearch.WordTrace tailWord_6051722 prefixEnd_6051722 38363483622079961031403 := by
  unfold tailWord_6051722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55181108645413055169361355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147149623054434813784963613 55181108645413055169361355)
  ·
    refine ⟨82771662968119582754042033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55181108645413055169361355 82771662968119582754042033)
    ·
      refine ⟨62078747226089687065531525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82771662968119582754042033 62078747226089687065531525)
      ·
        refine ⟨11639765104891816324787161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62078747226089687065531525 11639765104891816324787161)
        ·
          refine ⟨8729823828668862243590371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11639765104891816324787161 8729823828668862243590371)
          ·
            refine ⟨13094735743003293365385557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729823828668862243590371 13094735743003293365385557)
            ·
              refine ⟨38363483622079961031403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13094735743003293365385557 38363483622079961031403)
              ·
                rfl

theorem cell23_6051722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 10].length) (baseStart_6051722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051722 prefixEnd_6051722 := by exact prefixLift 6051722
  have htrace : WordTrace (prefixWord ++ tailWord_6051722) baseStart_6051722 baseEnd_6051722 := by
    simpa [prefixWord, tailWord_6051722, baseEnd_6051722] using wordTrace_append hprefix tailTrace_6051722
  have hstable : (prefixWord ++ tailWord_6051722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051722).length < 2 ^ (prefixWord ++ tailWord_6051722).sum := by decide
  have hdescent : baseEnd_6051722 < baseStart_6051722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051726 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_6051726 : Nat := 118140960795 + 6051726 * 2 ^ 59
def prefixEnd_6051726 : Nat := 4983230072969 + 3 ^ 40 * 6051726 * 2
def baseEnd_6051726 : Nat := 1035814742437031609297875

theorem tailTrace_6051726 : CollatzResearch.WordTrace tailWord_6051726 prefixEnd_6051726 1035814742437031609297875 := by
  unfold tailWord_6051726
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590572559204716170073879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147149720315758486240394021 27590572559204716170073879)
  ·
    refine ⟨41385858838807074255110819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590572559204716170073879 41385858838807074255110819)
    ·
      refine ⟨62078788258210611382666229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41385858838807074255110819 62078788258210611382666229)
      ·
        refine ⟨5819886399207244817124959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62078788258210611382666229 5819886399207244817124959)
        ·
          refine ⟨8729829598810867225687439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819886399207244817124959 8729829598810867225687439)
          ·
            refine ⟨13094744398216300838531159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729829598810867225687439 13094744398216300838531159)
            ·
              refine ⟨19642116597324451257796739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13094744398216300838531159 19642116597324451257796739)
              ·
                refine ⟨29463174895986676886695109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19642116597324451257796739 29463174895986676886695109)
                ·
                  refine ⟨5524345292997501916255333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29463174895986676886695109 5524345292997501916255333)
                  ·
                    refine ⟨1035814742437031609297875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524345292997501916255333 1035814742437031609297875)
                    ·
                      rfl

theorem cell23_6051726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_6051726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051726 prefixEnd_6051726 := by exact prefixLift 6051726
  have htrace : WordTrace (prefixWord ++ tailWord_6051726) baseStart_6051726 baseEnd_6051726 := by
    simpa [prefixWord, tailWord_6051726, baseEnd_6051726] using wordTrace_append hprefix tailTrace_6051726
  have hstable : (prefixWord ++ tailWord_6051726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051726).length < 2 ^ (prefixWord ++ tailWord_6051726).sum := by decide
  have hdescent : baseEnd_6051726 < baseStart_6051726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051746 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6051746 : Nat := 118140960795 + 6051746 * 2 ^ 59
def prefixEnd_6051746 : Nat := 4983230072969 + 3 ^ 40 * 6051746 * 2
def baseEnd_6051746 : Nat := 3107454496924184749643533

theorem tailTrace_6051746 : CollatzResearch.WordTrace tailWord_6051746 prefixEnd_6051746 3107454496924184749643533 := by
  unfold tailWord_6051746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55181327483391318194079773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147150206622376848517546061 55181327483391318194079773)
  ·
    refine ⟨20692997806271744322779915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55181327483391318194079773 20692997806271744322779915)
    ·
      refine ⟨31039496709407616484169873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20692997806271744322779915 31039496709407616484169873)
      ·
        refine ⟨23279622532055712363127405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31039496709407616484169873 23279622532055712363127405)
        ·
          refine ⟨8729858449520892136172777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23279622532055712363127405 8729858449520892136172777)
          ·
            refine ⟨6547393837140669102129583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729858449520892136172777 6547393837140669102129583)
            ·
              refine ⟨9821090755711003653194375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547393837140669102129583 9821090755711003653194375)
              ·
                refine ⟨14731636133566505479791563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821090755711003653194375 14731636133566505479791563)
                ·
                  refine ⟨22097454200349758219687345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14731636133566505479791563 22097454200349758219687345)
                  ·
                    refine ⟨16573090650262318664765509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22097454200349758219687345 16573090650262318664765509)
                    ·
                      refine ⟨3107454496924184749643533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16573090650262318664765509 3107454496924184749643533)
                      ·
                        rfl

theorem cell23_6051746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6051746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051746 prefixEnd_6051746 := by exact prefixLift 6051746
  have htrace : WordTrace (prefixWord ++ tailWord_6051746) baseStart_6051746 baseEnd_6051746 := by
    simpa [prefixWord, tailWord_6051746, baseEnd_6051746] using wordTrace_append hprefix tailTrace_6051746
  have hstable : (prefixWord ++ tailWord_6051746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051746).length < 2 ^ (prefixWord ++ tailWord_6051746).sum := by decide
  have hdescent : baseEnd_6051746 < baseStart_6051746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051749 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_6051749 : Nat := 118140960795 + 6051749 * 2 ^ 59
def prefixEnd_6051749 : Nat := 4983230072969 + 3 ^ 40 * 6051749 * 2
def baseEnd_6051749 : Nat := 3107456037366148237906019

theorem tailTrace_6051749 : CollatzResearch.WordTrace tailWord_6051749 prefixEnd_6051749 3107456037366148237906019 := by
  unfold tailWord_6051749
  simp only [CollatzResearch.WordTrace]
  refine ⟨220725419352554404288678301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147150279568369602859118867 220725419352554404288678301)
  ·
    refine ⟨82772032257207901608254363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220725419352554404288678301 82772032257207901608254363)
    ·
      refine ⟨124158048385811852412381545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82772032257207901608254363 124158048385811852412381545)
      ·
        refine ⟨93118536289358889309286159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124158048385811852412381545 93118536289358889309286159)
        ·
          refine ⟨139677804434038333963929239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93118536289358889309286159 139677804434038333963929239)
          ·
            refine ⟨209516706651057500945893859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139677804434038333963929239 209516706651057500945893859)
            ·
              refine ⟨314275059976586251418840789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209516706651057500945893859 314275059976586251418840789)
              ·
                refine ⟨7365821718201240267629081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 314275059976586251418840789 7365821718201240267629081)
                ·
                  refine ⟨5524366288650930200721811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365821718201240267629081 5524366288650930200721811)
                  ·
                    refine ⟨8286549432976395301082717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524366288650930200721811 8286549432976395301082717)
                    ·
                      refine ⟨3107456037366148237906019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286549432976395301082717 3107456037366148237906019)
                      ·
                        rfl

theorem cell23_6051749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_6051749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051749 prefixEnd_6051749 := by exact prefixLift 6051749
  have htrace : WordTrace (prefixWord ++ tailWord_6051749) baseStart_6051749 baseEnd_6051749 := by
    simpa [prefixWord, tailWord_6051749, baseEnd_6051749] using wordTrace_append hprefix tailTrace_6051749
  have hstable : (prefixWord ++ tailWord_6051749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051749).length < 2 ^ (prefixWord ++ tailWord_6051749).sum := by decide
  have hdescent : baseEnd_6051749 < baseStart_6051749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051852 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6051852 : Nat := 118140960795 + 6051852 * 2 ^ 59
def prefixEnd_6051852 : Nat := 4983230072969 + 3 ^ 40 * 6051852 * 2
def baseEnd_6051852 : Nat := 3107508925873561334918045

theorem tailTrace_6051852 : CollatzResearch.WordTrace tailWord_6051852 prefixEnd_6051852 3107508925873561334918045 := by
  unfold tailWord_6051852
  simp only [CollatzResearch.WordTrace]
  refine ⟨110364588035590626439838905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147152784047454168586451873 110364588035590626439838905)
  ·
    refine ⟨82773441026692969829879179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110364588035590626439838905 82773441026692969829879179)
    ·
      refine ⟨124160161540039454744818769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82773441026692969829879179 124160161540039454744818769)
      ·
        refine ⟨93120121155029591058614077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124160161540039454744818769 93120121155029591058614077)
        ·
          refine ⟨34920045433136096646980279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93120121155029591058614077 34920045433136096646980279)
          ·
            refine ⟨52380068149704144970470419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34920045433136096646980279 52380068149704144970470419)
            ·
              refine ⟨78570102224556217455705629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52380068149704144970470419 78570102224556217455705629)
              ·
                refine ⟨29463788334208581545889611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78570102224556217455705629 29463788334208581545889611)
                ·
                  refine ⟨44195682501312872318834417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29463788334208581545889611 44195682501312872318834417)
                  ·
                    refine ⟨33146761875984654239125813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44195682501312872318834417 33146761875984654239125813)
                    ·
                      refine ⟨3107508925873561334918045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33146761875984654239125813 3107508925873561334918045)
                      ·
                        rfl

theorem cell23_6051852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6051852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051852 prefixEnd_6051852 := by exact prefixLift 6051852
  have htrace : WordTrace (prefixWord ++ tailWord_6051852) baseStart_6051852 baseEnd_6051852 := by
    simpa [prefixWord, tailWord_6051852, baseEnd_6051852] using wordTrace_append hprefix tailTrace_6051852
  have hstable : (prefixWord ++ tailWord_6051852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051852).length < 2 ^ (prefixWord ++ tailWord_6051852).sum := by decide
  have hdescent : baseEnd_6051852 < baseStart_6051852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6051986 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6051986 : Nat := 118140960795 + 6051986 * 2 ^ 59
def prefixEnd_6051986 : Nat := 4983230072969 + 3 ^ 40 * 6051986 * 2
def baseEnd_6051986 : Nat := 3107577732281263810642429

theorem tailTrace_6051986 : CollatzResearch.WordTrace tailWord_6051986 prefixEnd_6051986 3107577732281263810642429 := by
  unfold tailWord_6051986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55183515863173948441263953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147156042301797195843370541 55183515863173948441263953)
  ·
    refine ⟨41387636897380461330947965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55183515863173948441263953 41387636897380461330947965)
    ·
      refine ⟨15520363836517672999105487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41387636897380461330947965 15520363836517672999105487)
      ·
        refine ⟨23280545754776509498658231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15520363836517672999105487 23280545754776509498658231)
        ·
          refine ⟨34920818632164764247987347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23280545754776509498658231 34920818632164764247987347)
          ·
            refine ⟨52381227948247146371981021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34920818632164764247987347 52381227948247146371981021)
            ·
              refine ⟨19642960480592679889492883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52381227948247146371981021 19642960480592679889492883)
              ·
                refine ⟨29464440720889019834239325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19642960480592679889492883 29464440720889019834239325)
                ·
                  refine ⟨11049165270333382437839747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29464440720889019834239325 11049165270333382437839747)
                  ·
                    refine ⟨16573747905500073656759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11049165270333382437839747 16573747905500073656759621)
                    ·
                      refine ⟨3107577732281263810642429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16573747905500073656759621 3107577732281263810642429)
                      ·
                        rfl

theorem cell23_6051986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6051986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6051986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6051986 prefixEnd_6051986 := by exact prefixLift 6051986
  have htrace : WordTrace (prefixWord ++ tailWord_6051986) baseStart_6051986 baseEnd_6051986 := by
    simpa [prefixWord, tailWord_6051986, baseEnd_6051986] using wordTrace_append hprefix tailTrace_6051986
  have hstable : (prefixWord ++ tailWord_6051986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6051986).length < 2 ^ (prefixWord ++ tailWord_6051986).sum := by decide
  have hdescent : baseEnd_6051986 < baseStart_6051986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6051986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052013 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6052013 : Nat := 118140960795 + 6052013 * 2 ^ 59
def prefixEnd_6052013 : Nat := 4983230072969 + 3 ^ 40 * 6052013 * 2
def baseEnd_6052013 : Nat := 1035863865419645068334935

theorem tailTrace_6052013 : CollatzResearch.WordTrace tailWord_6052013 prefixEnd_6052013 1035863865419645068334935 := by
  unfold tailWord_6052013
  simp only [CollatzResearch.WordTrace]
  refine ⟨220735048223597977376288693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147156698815731984917525795 220735048223597977376288693)
  ·
    refine ⟨20693910770962310379027065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220735048223597977376288693 20693910770962310379027065)
    ·
      refine ⟨15520433078221732784270299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20693910770962310379027065 15520433078221732784270299)
      ·
        refine ⟨23280649617332599176405449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15520433078221732784270299 23280649617332599176405449)
        ·
          refine ⟨17460487212999449382304087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23280649617332599176405449 17460487212999449382304087)
          ·
            refine ⟨26190730819499174073456131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17460487212999449382304087 26190730819499174073456131)
            ·
              refine ⟨39286096229248761110184197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26190730819499174073456131 39286096229248761110184197)
              ·
                refine ⟨7366143042984142708159537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39286096229248761110184197 7366143042984142708159537)
                ·
                  refine ⟨5524607282238107031119653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7366143042984142708159537 5524607282238107031119653)
                  ·
                    refine ⟨1035863865419645068334935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524607282238107031119653 1035863865419645068334935)
                    ·
                      rfl

theorem cell23_6052013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6052013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052013 prefixEnd_6052013 := by exact prefixLift 6052013
  have htrace : WordTrace (prefixWord ++ tailWord_6052013) baseStart_6052013 baseEnd_6052013 := by
    simpa [prefixWord, tailWord_6052013, baseEnd_6052013] using wordTrace_append hprefix tailTrace_6052013
  have hstable : (prefixWord ++ tailWord_6052013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052013).length < 2 ^ (prefixWord ++ tailWord_6052013).sum := by decide
  have hdescent : baseEnd_6052013 < baseStart_6052013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052014 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6052014 : Nat := 118140960795 + 6052014 * 2 ^ 59
def prefixEnd_6052014 : Nat := 4983230072969 + 3 ^ 40 * 6052014 * 2
def baseEnd_6052014 : Nat := 3107592109739589701092301

theorem tailTrace_6052014 : CollatzResearch.WordTrace tailWord_6052014 prefixEnd_6052014 3107592109739589701092301 := by
  unfold tailWord_6052014
  simp only [CollatzResearch.WordTrace]
  refine ⟨27591885587074294318384387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147156723131062903031383397 27591885587074294318384387)
  ·
    refine ⟨41387828380611441477576581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27591885587074294318384387 41387828380611441477576581)
    ·
      refine ⟨7760217821364645277045609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41387828380611441477576581 7760217821364645277045609)
      ·
        refine ⟨5820163366023483957784207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7760217821364645277045609 5820163366023483957784207)
        ·
          refine ⟨8730245049035225936676311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820163366023483957784207 8730245049035225936676311)
          ·
            refine ⟨13095367573552838905014467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730245049035225936676311 13095367573552838905014467)
            ·
              refine ⟨19643051360329258357521701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13095367573552838905014467 19643051360329258357521701)
              ·
                refine ⟨3683072130061735942035319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19643051360329258357521701 3683072130061735942035319)
                ·
                  refine ⟨5524608195092603913052979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683072130061735942035319 5524608195092603913052979)
                  ·
                    refine ⟨8286912292638905869579469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524608195092603913052979 8286912292638905869579469)
                    ·
                      refine ⟨3107592109739589701092301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286912292638905869579469 3107592109739589701092301)
                      ·
                        rfl

theorem cell23_6052014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6052014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052014 prefixEnd_6052014 := by exact prefixLift 6052014
  have htrace : WordTrace (prefixWord ++ tailWord_6052014) baseStart_6052014 baseEnd_6052014 := by
    simpa [prefixWord, tailWord_6052014, baseEnd_6052014] using wordTrace_append hprefix tailTrace_6052014
  have hstable : (prefixWord ++ tailWord_6052014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052014).length < 2 ^ (prefixWord ++ tailWord_6052014).sum := by decide
  have hdescent : baseEnd_6052014 < baseStart_6052014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052019 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3]
def baseStart_6052019 : Nat := 118140960795 + 6052019 * 2 ^ 59
def prefixEnd_6052019 : Nat := 4983230072969 + 3 ^ 40 * 6052019 * 2
def baseEnd_6052019 : Nat := 3107594677142862181529777

theorem tailTrace_6052019 : CollatzResearch.WordTrace tailWord_6052019 prefixEnd_6052019 3107594677142862181529777 := by
  unfold tailWord_6052019
  simp only [CollatzResearch.WordTrace]
  refine ⟨220735267061576240401007111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147156844707717493600671407 220735267061576240401007111)
  ·
    refine ⟨331102900592364360601510667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220735267061576240401007111 331102900592364360601510667)
    ·
      refine ⟨496654350888546540902266001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331102900592364360601510667 496654350888546540902266001)
      ·
        refine ⟨372490763166409905676699501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496654350888546540902266001 372490763166409905676699501)
        ·
          refine ⟨139684036187403714628762313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372490763166409905676699501 139684036187403714628762313)
          ·
            refine ⟨104763027140552785971571735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139684036187403714628762313 104763027140552785971571735)
            ·
              refine ⟨157144540710829178957357603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104763027140552785971571735 157144540710829178957357603)
              ·
                refine ⟨235716811066243768436036405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157144540710829178957357603 235716811066243768436036405)
                ·
                  refine ⟨22098451037460353290878413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235716811066243768436036405 22098451037460353290878413)
                  ·
                    refine ⟨8286919139047632484079405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22098451037460353290878413 8286919139047632484079405)
                    ·
                      refine ⟨3107594677142862181529777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8286919139047632484079405 3107594677142862181529777)
                      ·
                        rfl

theorem cell23_6052019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_6052019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052019 prefixEnd_6052019 := by exact prefixLift 6052019
  have htrace : WordTrace (prefixWord ++ tailWord_6052019) baseStart_6052019 baseEnd_6052019 := by
    simpa [prefixWord, tailWord_6052019, baseEnd_6052019] using wordTrace_append hprefix tailTrace_6052019
  have hstable : (prefixWord ++ tailWord_6052019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052019).length < 2 ^ (prefixWord ++ tailWord_6052019).sum := by decide
  have hdescent : baseEnd_6052019 < baseStart_6052019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052054 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6052054 : Nat := 118140960795 + 6052054 * 2 ^ 59
def prefixEnd_6052054 : Nat := 4983230072969 + 3 ^ 40 * 6052054 * 2
def baseEnd_6052054 : Nat := 3107612648965769544592117

theorem tailTrace_6052054 : CollatzResearch.WordTrace tailWord_6052054 prefixEnd_6052054 3107612648965769544592117 := by
  unfold tailWord_6052054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796033976028090086158201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147157695744299627585687477 13796033976028090086158201)
  ·
    refine ⟨10347025482021067564618651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13796033976028090086158201 10347025482021067564618651)
    ·
      refine ⟨15520538223031601346927977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347025482021067564618651 15520538223031601346927977)
      ·
        refine ⟨11640403667273701010195983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15520538223031601346927977 11640403667273701010195983)
        ·
          refine ⟨17460605500910551515293975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640403667273701010195983 17460605500910551515293975)
          ·
            refine ⟨26190908251365827272940963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17460605500910551515293975 26190908251365827272940963)
            ·
              refine ⟨39286362377048740909411445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26190908251365827272940963 39286362377048740909411445)
              ·
                refine ⟨3683096472848319460257323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39286362377048740909411445 3683096472848319460257323)
                ·
                  refine ⟨5524644709272479190385985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683096472848319460257323 5524644709272479190385985)
                  ·
                    refine ⟨4143483531954359392789489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5524644709272479190385985 4143483531954359392789489)
                    ·
                      refine ⟨3107612648965769544592117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143483531954359392789489 3107612648965769544592117)
                      ·
                        rfl

theorem cell23_6052054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6052054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052054 prefixEnd_6052054 := by exact prefixLift 6052054
  have htrace : WordTrace (prefixWord ++ tailWord_6052054) baseStart_6052054 baseEnd_6052054 := by
    simpa [prefixWord, tailWord_6052054, baseEnd_6052054] using wordTrace_append hprefix tailTrace_6052054
  have hstable : (prefixWord ++ tailWord_6052054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052054).length < 2 ^ (prefixWord ++ tailWord_6052054).sum := by decide
  have hdescent : baseEnd_6052054 < baseStart_6052054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052086 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6052086 : Nat := 118140960795 + 6052086 * 2 ^ 59
def prefixEnd_6052086 : Nat := 4983230072969 + 3 ^ 40 * 6052086 * 2
def baseEnd_6052086 : Nat := 1035876360115571139797323

theorem tailTrace_6052086 : CollatzResearch.WordTrace tailWord_6052086 prefixEnd_6052086 1035876360115571139797323 := by
  unfold tailWord_6052086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796106922020844427731007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147158473834889007229130741 13796106922020844427731007)
  ·
    refine ⟨20694160383031266641596511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13796106922020844427731007 20694160383031266641596511)
    ·
      refine ⟨31041240574546899962394767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20694160383031266641596511 31041240574546899962394767)
      ·
        refine ⟨46561860861820349943592151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31041240574546899962394767 46561860861820349943592151)
        ·
          refine ⟨69842791292730524915388227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46561860861820349943592151 69842791292730524915388227)
          ·
            refine ⟨104764186939095787373082341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69842791292730524915388227 104764186939095787373082341)
            ·
              refine ⟨19643285051080460132452939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104764186939095787373082341 19643285051080460132452939)
              ·
                refine ⟨29464927576620690198679409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19643285051080460132452939 29464927576620690198679409)
                ·
                  refine ⟨22098695682465517649009557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29464927576620690198679409 22098695682465517649009557)
                  ·
                    refine ⟨1035876360115571139797323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22098695682465517649009557 1035876360115571139797323)
                    ·
                      rfl

theorem cell23_6052086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6052086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052086 prefixEnd_6052086 := by exact prefixLift 6052086
  have htrace : WordTrace (prefixWord ++ tailWord_6052086) baseStart_6052086 baseEnd_6052086 := by
    simpa [prefixWord, tailWord_6052086, baseEnd_6052086] using wordTrace_append hprefix tailTrace_6052086
  have hstable : (prefixWord ++ tailWord_6052086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052086).length < 2 ^ (prefixWord ++ tailWord_6052086).sum := by decide
  have hdescent : baseEnd_6052086 < baseStart_6052086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052089 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6052089 : Nat := 118140960795 + 6052089 * 2 ^ 59
def prefixEnd_6052089 : Nat := 4983230072969 + 3 ^ 40 * 6052089 * 2
def baseEnd_6052089 : Nat := 3107630620788676907654455

theorem tailTrace_6052089 : CollatzResearch.WordTrace tailWord_6052089 prefixEnd_6052089 3107630620788676907654455 := by
  unfold tailWord_6052089
  simp only [CollatzResearch.WordTrace]
  refine ⟨220737820171322642356055321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147158546780881761570703547 220737820171322642356055321)
  ·
    refine ⟨165553365128491981767041491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220737820171322642356055321 165553365128491981767041491)
    ·
      refine ⟨248330047692737972650562237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165553365128491981767041491 248330047692737972650562237)
      ·
        refine ⟨93123767884776739743960839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248330047692737972650562237 93123767884776739743960839)
        ·
          refine ⟨139685651827165109615941259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93123767884776739743960839 139685651827165109615941259)
          ·
            refine ⟨209528477740747664423911889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139685651827165109615941259 209528477740747664423911889)
            ·
              refine ⟨157146358305560748317933917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209528477740747664423911889 157146358305560748317933917)
              ·
                refine ⟨58929884364585280619225219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157146358305560748317933917 58929884364585280619225219)
                ·
                  refine ⟨88394826546877920928837829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58929884364585280619225219 88394826546877920928837829)
                  ·
                    refine ⟨16574029977539610174157093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88394826546877920928837829 16574029977539610174157093)
                    ·
                      refine ⟨3107630620788676907654455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16574029977539610174157093 3107630620788676907654455)
                      ·
                        rfl

theorem cell23_6052089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6052089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052089 prefixEnd_6052089 := by exact prefixLift 6052089
  have htrace : WordTrace (prefixWord ++ tailWord_6052089) baseStart_6052089 baseEnd_6052089 := by
    simpa [prefixWord, tailWord_6052089, baseEnd_6052089] using wordTrace_append hprefix tailTrace_6052089
  have hstable : (prefixWord ++ tailWord_6052089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052089).length < 2 ^ (prefixWord ++ tailWord_6052089).sum := by decide
  have hdescent : baseEnd_6052089 < baseStart_6052089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052099 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 7]
def baseStart_6052099 : Nat := 118140960795 + 6052099 * 2 ^ 59
def prefixEnd_6052099 : Nat := 4983230072969 + 3 ^ 40 * 6052099 * 2
def baseEnd_6052099 : Nat := 345292861732802429836601

theorem tailTrace_6052099 : CollatzResearch.WordTrace tailWord_6052099 prefixEnd_6052099 345292861732802429836601 := by
  unfold tailWord_6052099
  simp only [CollatzResearch.WordTrace]
  refine ⟨220738184901286414063919351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147158789934190942709279567 220738184901286414063919351)
  ·
    refine ⟨331107277351929621095879027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220738184901286414063919351 331107277351929621095879027)
    ·
      refine ⟨496660916027894431643818541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331107277351929621095879027 496660916027894431643818541)
      ·
        refine ⟨186247843510460411866431953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496660916027894431643818541 186247843510460411866431953)
        ·
          refine ⟨139685882632845308899823965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186247843510460411866431953 139685882632845308899823965)
          ·
            refine ⟨52382205987316990837433987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139685882632845308899823965 52382205987316990837433987)
            ·
              refine ⟨78573308980975486256150981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52382205987316990837433987 78573308980975486256150981)
              ·
                refine ⟨14732495433932903673028309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78573308980975486256150981 14732495433932903673028309)
                ·
                  refine ⟨345292861732802429836601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14732495433932903673028309 345292861732802429836601)
                  ·
                    rfl

theorem cell23_6052099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 7].length) (baseStart_6052099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052099 prefixEnd_6052099 := by exact prefixLift 6052099
  have htrace : WordTrace (prefixWord ++ tailWord_6052099) baseStart_6052099 baseEnd_6052099 := by
    simpa [prefixWord, tailWord_6052099, baseEnd_6052099] using wordTrace_append hprefix tailTrace_6052099
  have hstable : (prefixWord ++ tailWord_6052099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052099).length < 2 ^ (prefixWord ++ tailWord_6052099).sum := by decide
  have hdescent : baseEnd_6052099 < baseStart_6052099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052133 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 7]
def baseStart_6052133 : Nat := 118140960795 + 6052133 * 2 ^ 59
def prefixEnd_6052133 : Nat := 4983230072969 + 3 ^ 40 * 6052133 * 2
def baseEnd_6052133 : Nat := 345294801548608303944917

theorem tailTrace_6052133 : CollatzResearch.WordTrace tailWord_6052133 prefixEnd_6052133 345294801548608303944917 := by
  unfold tailWord_6052133
  simp only [CollatzResearch.WordTrace]
  refine ⟨220739424983163237870657053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147159616655442158580438035 220739424983163237870657053)
  ·
    refine ⟨82777284368686214201496395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220739424983163237870657053 82777284368686214201496395)
    ·
      refine ⟨124165926553029321302244593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82777284368686214201496395 124165926553029321302244593)
      ·
        refine ⟨93124444914771990976683445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124165926553029321302244593 93124444914771990976683445)
        ·
          refine ⟨8730416710759874154064073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93124444914771990976683445 8730416710759874154064073)
          ·
            refine ⟨6547812533069905615548055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8730416710759874154064073 6547812533069905615548055)
            ·
              refine ⟨9821718799604858423322083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547812533069905615548055 9821718799604858423322083)
              ·
                refine ⟨14732578199407287634983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821718799604858423322083 14732578199407287634983125)
                ·
                  refine ⟨345294801548608303944917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14732578199407287634983125 345294801548608303944917)
                  ·
                    rfl

theorem cell23_6052133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_6052133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052133 prefixEnd_6052133 := by exact prefixLift 6052133
  have htrace : WordTrace (prefixWord ++ tailWord_6052133) baseStart_6052133 baseEnd_6052133 := by
    simpa [prefixWord, tailWord_6052133, baseEnd_6052133] using wordTrace_append hprefix tailTrace_6052133
  have hstable : (prefixWord ++ tailWord_6052133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052133).length < 2 ^ (prefixWord ++ tailWord_6052133).sum := by decide
  have hdescent : baseEnd_6052133 < baseStart_6052133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052183 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_6052183 : Nat := 118140960795 + 6052183 * 2 ^ 59
def prefixEnd_6052183 : Nat := 4983230072969 + 3 ^ 40 * 6052183 * 2
def baseEnd_6052183 : Nat := 3107678887970199539879023

theorem tailTrace_6052183 : CollatzResearch.WordTrace tailWord_6052183 prefixEnd_6052183 3107678887970199539879023 := by
  unfold tailWord_6052183
  simp only [CollatzResearch.WordTrace]
  refine ⟨220741248632982096409977203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147160832421988064273318135 220741248632982096409977203)
  ·
    refine ⟨331111872949473144614965805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220741248632982096409977203 331111872949473144614965805)
    ·
      refine ⟨124166952356052429230612177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331111872949473144614965805 124166952356052429230612177)
      ·
        refine ⟨93125214267039321922959133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124166952356052429230612177 93125214267039321922959133)
        ·
          refine ⟨34921955350139745721109675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93125214267039321922959133 34921955350139745721109675)
          ·
            refine ⟨52382933025209618581664513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34921955350139745721109675 52382933025209618581664513)
            ·
              refine ⟨39287199768907213936248385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52382933025209618581664513 39287199768907213936248385)
              ·
                refine ⟨29465399826680410452186289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39287199768907213936248385 29465399826680410452186289)
                ·
                  refine ⟨22099049870010307839139717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29465399826680410452186289 22099049870010307839139717)
                  ·
                    refine ⟨4143571850626932719838697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22099049870010307839139717 4143571850626932719838697)
                    ·
                      refine ⟨3107678887970199539879023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143571850626932719838697 3107678887970199539879023)
                      ·
                        rfl

theorem cell23_6052183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_6052183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052183 prefixEnd_6052183 := by exact prefixLift 6052183
  have htrace : WordTrace (prefixWord ++ tailWord_6052183) baseStart_6052183 baseEnd_6052183 := by
    simpa [prefixWord, tailWord_6052183, baseEnd_6052183] using wordTrace_append hprefix tailTrace_6052183
  have hstable : (prefixWord ++ tailWord_6052183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052183).length < 2 ^ (prefixWord ++ tailWord_6052183).sum := by decide
  have hdescent : baseEnd_6052183 < baseStart_6052183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052186 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_6052186 : Nat := 118140960795 + 6052186 * 2 ^ 59
def prefixEnd_6052186 : Nat := 4983230072969 + 3 ^ 40 * 6052186 * 2
def baseEnd_6052186 : Nat := 3107680428412163028141509

theorem tailTrace_6052186 : CollatzResearch.WordTrace tailWord_6052186 prefixEnd_6052186 3107680428412163028141509 := by
  unfold tailWord_6052186
  simp only [CollatzResearch.WordTrace]
  refine ⟨55185339512992806980584103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147160905367980818614890941 55185339512992806980584103)
  ·
    refine ⟨82778009269489210470876155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55185339512992806980584103 82778009269489210470876155)
    ·
      refine ⟨124167013904233815706314233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82778009269489210470876155 124167013904233815706314233)
      ·
        refine ⟨93125260428175361779735675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124167013904233815706314233 93125260428175361779735675)
        ·
          refine ⟨139687890642263042669603513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93125260428175361779735675 139687890642263042669603513)
          ·
            refine ⟨104765917981697282002202635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139687890642263042669603513 104765917981697282002202635)
            ·
              refine ⟨157148876972545923003303953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104765917981697282002202635 157148876972545923003303953)
              ·
                refine ⟨117861657729409442252477965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157148876972545923003303953 117861657729409442252477965)
                ·
                  refine ⟨44198121648528540844679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117861657729409442252477965 44198121648528540844679237)
                  ·
                    refine ⟨8287147809099101408377357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44198121648528540844679237 8287147809099101408377357)
                    ·
                      refine ⟨3107680428412163028141509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287147809099101408377357 3107680428412163028141509)
                      ·
                        rfl

theorem cell23_6052186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_6052186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052186 prefixEnd_6052186 := by exact prefixLift 6052186
  have htrace : WordTrace (prefixWord ++ tailWord_6052186) baseStart_6052186 baseEnd_6052186 := by
    simpa [prefixWord, tailWord_6052186, baseEnd_6052186] using wordTrace_append hprefix tailTrace_6052186
  have hstable : (prefixWord ++ tailWord_6052186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052186).length < 2 ^ (prefixWord ++ tailWord_6052186).sum := by decide
  have hdescent : baseEnd_6052186 < baseStart_6052186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052200 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6052200 : Nat := 118140960795 + 6052200 * 2 ^ 59
def prefixEnd_6052200 : Nat := 4983230072969 + 3 ^ 40 * 6052200 * 2
def baseEnd_6052200 : Nat := 3107687617141325973366445

theorem tailTrace_6052200 : CollatzResearch.WordTrace tailWord_6052200 prefixEnd_6052200 3107687617141325973366445 := by
  unfold tailWord_6052200
  simp only [CollatzResearch.WordTrace]
  refine ⟨110370934336960254156673027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147161245782613672208897369 110370934336960254156673027)
  ·
    refine ⟨165556401505440381235009541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110370934336960254156673027 165556401505440381235009541)
    ·
      refine ⟨31041825282270071481564289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165556401505440381235009541 31041825282270071481564289)
      ·
        refine ⟨23281368961702553611173217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31041825282270071481564289 23281368961702553611173217)
        ·
          refine ⟨17461026721276915208379913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23281368961702553611173217 17461026721276915208379913)
          ·
            refine ⟨13095770040957686406284935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17461026721276915208379913 13095770040957686406284935)
            ·
              refine ⟨19643655061436529609427403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13095770040957686406284935 19643655061436529609427403)
              ·
                refine ⟨29465482592154794414141105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19643655061436529609427403 29465482592154794414141105)
                ·
                  refine ⟨22099111944116095810605829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29465482592154794414141105 22099111944116095810605829)
                  ·
                    refine ⟨4143583489521767964488593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22099111944116095810605829 4143583489521767964488593)
                    ·
                      refine ⟨3107687617141325973366445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143583489521767964488593 3107687617141325973366445)
                      ·
                        rfl

theorem cell23_6052200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6052200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052200 prefixEnd_6052200 := by exact prefixLift 6052200
  have htrace : WordTrace (prefixWord ++ tailWord_6052200) baseStart_6052200 baseEnd_6052200 := by
    simpa [prefixWord, tailWord_6052200, baseEnd_6052200] using wordTrace_append hprefix tailTrace_6052200
  have hstable : (prefixWord ++ tailWord_6052200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052200).length < 2 ^ (prefixWord ++ tailWord_6052200).sum := by decide
  have hdescent : baseEnd_6052200 < baseStart_6052200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052214 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6052214 : Nat := 118140960795 + 6052214 * 2 ^ 59
def prefixEnd_6052214 : Nat := 4983230072969 + 3 ^ 40 * 6052214 * 2
def baseEnd_6052214 : Nat := 1035898268623496306197127

theorem tailTrace_6052214 : CollatzResearch.WordTrace tailWord_6052214 prefixEnd_6052214 1035898268623496306197127 := by
  unfold tailWord_6052214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796398705991861794022231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147161586197246525802903797 13796398705991861794022231)
  ·
    refine ⟨20694598058987792691033347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13796398705991861794022231 20694598058987792691033347)
    ·
      refine ⟨31041897088481689036550021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20694598058987792691033347 31041897088481689036550021)
      ·
        refine ⟨5820355704090316694353129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31041897088481689036550021 5820355704090316694353129)
        ·
          refine ⟨4365266778067737520764847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5820355704090316694353129 4365266778067737520764847)
          ·
            refine ⟨6547900167101606281147271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365266778067737520764847 6547900167101606281147271)
            ·
              refine ⟨9821850250652409421720907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547900167101606281147271 9821850250652409421720907)
              ·
                refine ⟨14732775375978614132581361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9821850250652409421720907 14732775375978614132581361)
                ·
                  refine ⟨11049581531983960599436021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14732775375978614132581361 11049581531983960599436021)
                  ·
                    refine ⟨1035898268623496306197127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11049581531983960599436021 1035898268623496306197127)
                    ·
                      rfl

theorem cell23_6052214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6052214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052214 prefixEnd_6052214 := by exact prefixLift 6052214
  have htrace : WordTrace (prefixWord ++ tailWord_6052214) baseStart_6052214 baseEnd_6052214 := by
    simpa [prefixWord, tailWord_6052214, baseEnd_6052214] using wordTrace_append hprefix tailTrace_6052214
  have hstable : (prefixWord ++ tailWord_6052214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052214).length < 2 ^ (prefixWord ++ tailWord_6052214).sum := by decide
  have hdescent : baseEnd_6052214 < baseStart_6052214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052227 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 1, 4]
def baseStart_6052227 : Nat := 118140960795 + 6052227 * 2 ^ 59
def prefixEnd_6052227 : Nat := 4983230072969 + 3 ^ 40 * 6052227 * 2
def baseEnd_6052227 : Nat := 1035900493706332455909607

theorem tailTrace_6052227 : CollatzResearch.WordTrace tailWord_6052227 prefixEnd_6052227 1035900493706332455909607 := by
  unfold tailWord_6052227
  simp only [CollatzResearch.WordTrace]
  refine ⟨220742853444822691924578935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147161902296548461283052623 220742853444822691924578935)
  ·
    refine ⟨331114280167234037886868403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220742853444822691924578935 331114280167234037886868403)
    ·
      refine ⟨496671420250851056830302605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331114280167234037886868403 496671420250851056830302605)
      ·
        refine ⟨186251782594069146311363477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496671420250851056830302605 186251782594069146311363477)
        ·
          refine ⟨8730552309096991233345163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186251782594069146311363477 8730552309096991233345163)
          ·
            refine ⟨13095828463645486850017745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730552309096991233345163 13095828463645486850017745)
            ·
              refine ⟨9821871347734115137513309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13095828463645486850017745 9821871347734115137513309)
              ·
                refine ⟨3683201755400293176567491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821871347734115137513309 3683201755400293176567491)
                ·
                  refine ⟨5524802633100439764851237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683201755400293176567491 5524802633100439764851237)
                  ·
                    refine ⟨1035900493706332455909607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5524802633100439764851237 1035900493706332455909607)
                    ·
                      rfl

theorem cell23_6052227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 4].length) (baseStart_6052227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052227 prefixEnd_6052227 := by exact prefixLift 6052227
  have htrace : WordTrace (prefixWord ++ tailWord_6052227) baseStart_6052227 baseEnd_6052227 := by
    simpa [prefixWord, tailWord_6052227, baseEnd_6052227] using wordTrace_append hprefix tailTrace_6052227
  have hstable : (prefixWord ++ tailWord_6052227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052227).length < 2 ^ (prefixWord ++ tailWord_6052227).sum := by decide
  have hdescent : baseEnd_6052227 < baseStart_6052227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052250 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6052250 : Nat := 118140960795 + 6052250 * 2 ^ 59
def prefixEnd_6052250 : Nat := 4983230072969 + 3 ^ 40 * 6052250 * 2
def baseEnd_6052250 : Nat := 3107713291174050777741215

theorem tailTrace_6052250 : CollatzResearch.WordTrace tailWord_6052250 prefixEnd_6052250 3107713291174050777741215 := by
  unfold tailWord_6052250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55185923080934841713166551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147162461549159577901777469 55185923080934841713166551)
  ·
    refine ⟨82778884621402262569749827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55185923080934841713166551 82778884621402262569749827)
    ·
      refine ⟨124168326932103393854624741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82778884621402262569749827 124168326932103393854624741)
      ·
        refine ⟨23281561299769386347742139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124168326932103393854624741 23281561299769386347742139)
        ·
          refine ⟨34922341949654079521613209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23281561299769386347742139 34922341949654079521613209)
          ·
            refine ⟨26191756462240559641209907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34922341949654079521613209 26191756462240559641209907)
            ·
              refine ⟨39287634693360839461814861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26191756462240559641209907 39287634693360839461814861)
              ·
                refine ⟨14732863010010314798180573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39287634693360839461814861 14732863010010314798180573)
                ·
                  refine ⟨5524823628753868049317715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14732863010010314798180573 5524823628753868049317715)
                  ·
                    refine ⟨8287235443130802073976573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524823628753868049317715 8287235443130802073976573)
                    ·
                      refine ⟨3107713291174050777741215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287235443130802073976573 3107713291174050777741215)
                      ·
                        rfl

theorem cell23_6052250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6052250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052250 prefixEnd_6052250 := by exact prefixLift 6052250
  have htrace : WordTrace (prefixWord ++ tailWord_6052250) baseStart_6052250 baseEnd_6052250 := by
    simpa [prefixWord, tailWord_6052250, baseEnd_6052250] using wordTrace_append hprefix tailTrace_6052250
  have hstable : (prefixWord ++ tailWord_6052250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052250).length < 2 ^ (prefixWord ++ tailWord_6052250).sum := by decide
  have hdescent : baseEnd_6052250 < baseStart_6052250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052257 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 6]
def baseStart_6052257 : Nat := 118140960795 + 6052257 * 2 ^ 59
def prefixEnd_6052257 : Nat := 4983230072969 + 3 ^ 40 * 6052257 * 2
def baseEnd_6052257 : Nat := 345301876170959138928187

theorem tailTrace_6052257 : CollatzResearch.WordTrace tailWord_6052257 prefixEnd_6052257 345301876170959138928187 := by
  unfold tailWord_6052257
  simp only [CollatzResearch.WordTrace]
  refine ⟨220743947634714007048171025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147162631756476004698780683 220743947634714007048171025)
  ·
    refine ⟨165557960726035505286128269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220743947634714007048171025 165557960726035505286128269)
    ·
      refine ⟨62084235272263314482298101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165557960726035505286128269 62084235272263314482298101)
      ·
        refine ⟨5820397056774685732715447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62084235272263314482298101 5820397056774685732715447)
        ·
          refine ⟨8730595585162028599073171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820397056774685732715447 8730595585162028599073171)
          ·
            refine ⟨13095893377743042898609757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730595585162028599073171 13095893377743042898609757)
            ·
              refine ⟨4910960016653641086978659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13095893377743042898609757 4910960016653641086978659)
              ·
                refine ⟨7366440024980461630467989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910960016653641086978659 7366440024980461630467989)
                ·
                  refine ⟨345301876170959138928187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7366440024980461630467989 345301876170959138928187)
                  ·
                    rfl

theorem cell23_6052257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_6052257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052257 prefixEnd_6052257 := by exact prefixLift 6052257
  have htrace : WordTrace (prefixWord ++ tailWord_6052257) baseStart_6052257 baseEnd_6052257 := by
    simpa [prefixWord, tailWord_6052257, baseEnd_6052257] using wordTrace_append hprefix tailTrace_6052257
  have hstable : (prefixWord ++ tailWord_6052257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052257).length < 2 ^ (prefixWord ++ tailWord_6052257).sum := by decide
  have hdescent : baseEnd_6052257 < baseStart_6052257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052284 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6052284 : Nat := 118140960795 + 6052284 * 2 ^ 59
def prefixEnd_6052284 : Nat := 4983230072969 + 3 ^ 40 * 6052284 * 2
def baseEnd_6052284 : Nat := 3107730749516303644716059

theorem tailTrace_6052284 : CollatzResearch.WordTrace tailWord_6052284 prefixEnd_6052284 3107730749516303644716059 := by
  unfold tailWord_6052284
  simp only [CollatzResearch.WordTrace]
  refine ⟨110372466202808095329701953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147163288270410793772935937 110372466202808095329701953)
  ·
    refine ⟨82779349652106071497276465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110372466202808095329701953 82779349652106071497276465)
    ·
      refine ⟨62084512239079553622957349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82779349652106071497276465 62084512239079553622957349)
      ·
        refine ⟨11640846044827416304304503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62084512239079553622957349 11640846044827416304304503)
        ·
          refine ⟨17461269067241124456456755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640846044827416304304503 17461269067241124456456755)
          ·
            refine ⟨26191903600861686684685133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17461269067241124456456755 26191903600861686684685133)
            ·
              refine ⟨9821963850323132506756925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26191903600861686684685133 9821963850323132506756925)
              ·
                refine ⟨3683236443871174690033847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821963850323132506756925 3683236443871174690033847)
                ·
                  refine ⟨5524854665806762035050771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683236443871174690033847 5524854665806762035050771)
                  ·
                    refine ⟨8287281998710143052576157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524854665806762035050771 8287281998710143052576157)
                    ·
                      refine ⟨3107730749516303644716059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287281998710143052576157 3107730749516303644716059)
                      ·
                        rfl

theorem cell23_6052284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6052284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052284 prefixEnd_6052284 := by exact prefixLift 6052284
  have htrace : WordTrace (prefixWord ++ tailWord_6052284) baseStart_6052284 baseEnd_6052284 := by
    simpa [prefixWord, tailWord_6052284, baseEnd_6052284] using wordTrace_append hprefix tailTrace_6052284
  have hstable : (prefixWord ++ tailWord_6052284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052284).length < 2 ^ (prefixWord ++ tailWord_6052284).sum := by decide
  have hdescent : baseEnd_6052284 < baseStart_6052284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052296 : List Nat := [2, 1, 3, 1, 3, 2, 11]
def baseStart_6052296 : Nat := 118140960795 + 6052296 * 2 ^ 59
def prefixEnd_6052296 : Nat := 4983230072969 + 3 ^ 40 * 6052296 * 2
def baseEnd_6052296 : Nat := 38367122361532809848963

theorem tailTrace_6052296 : CollatzResearch.WordTrace tailWord_6052296 prefixEnd_6052296 38367122361532809848963 := by
  unfold tailWord_6052296
  simp only [CollatzResearch.WordTrace]
  refine ⟨110372685040786358354420371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147163580054381811139227161 110372685040786358354420371)
  ·
    refine ⟨165559027561179537531630557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110372685040786358354420371 165559027561179537531630557)
    ·
      refine ⟨62084635335442326574361459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165559027561179537531630557 62084635335442326574361459)
      ·
        refine ⟨93126953003163489861542189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62084635335442326574361459 93126953003163489861542189)
        ·
          refine ⟨34922607376186308698078321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93126953003163489861542189 34922607376186308698078321)
          ·
            refine ⟨26191955532139731523558741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34922607376186308698078321 26191955532139731523558741)
            ·
              refine ⟨38367122361532809848963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26191955532139731523558741 38367122361532809848963)
              ·
                rfl

theorem cell23_6052296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 11].length) (baseStart_6052296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052296 prefixEnd_6052296 := by exact prefixLift 6052296
  have htrace : WordTrace (prefixWord ++ tailWord_6052296) baseStart_6052296 baseEnd_6052296 := by
    simpa [prefixWord, tailWord_6052296, baseEnd_6052296] using wordTrace_append hprefix tailTrace_6052296
  have hstable : (prefixWord ++ tailWord_6052296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052296).length < 2 ^ (prefixWord ++ tailWord_6052296).sum := by decide
  have hdescent : baseEnd_6052296 < baseStart_6052296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052310 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6052310 : Nat := 118140960795 + 6052310 * 2 ^ 59
def prefixEnd_6052310 : Nat := 4983230072969 + 3 ^ 40 * 6052310 * 2
def baseEnd_6052310 : Nat := 3107744100013320542990939

theorem tailTrace_6052310 : CollatzResearch.WordTrace tailWord_6052310 prefixEnd_6052310 3107744100013320542990939 := by
  unfold tailWord_6052310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796617543970124818740649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147163920469014664733233589 13796617543970124818740649)
  ·
    refine ⟨10347463157977593614055487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13796617543970124818740649 10347463157977593614055487)
    ·
      refine ⟨15521194736966390421083231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347463157977593614055487 15521194736966390421083231)
      ·
        refine ⟨23281792105449585631624847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15521194736966390421083231 23281792105449585631624847)
        ·
          refine ⟨34922688158174378447437271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23281792105449585631624847 34922688158174378447437271)
          ·
            refine ⟨52384032237261567671155907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34922688158174378447437271 52384032237261567671155907)
            ·
              refine ⟨78576048355892351506733861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52384032237261567671155907 78576048355892351506733861)
              ·
                refine ⟨14733009066729815907512599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78576048355892351506733861 14733009066729815907512599)
                ·
                  refine ⟨22099513600094723861268899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14733009066729815907512599 22099513600094723861268899)
                  ·
                    refine ⟨33149270400142085791903349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22099513600094723861268899 33149270400142085791903349)
                    ·
                      refine ⟨3107744100013320542990939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33149270400142085791903349 3107744100013320542990939)
                      ·
                        rfl

theorem cell23_6052310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6052310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052310 prefixEnd_6052310 := by exact prefixLift 6052310
  have htrace : WordTrace (prefixWord ++ tailWord_6052310) baseStart_6052310 baseEnd_6052310 := by
    simpa [prefixWord, tailWord_6052310, baseEnd_6052310] using wordTrace_append hprefix tailTrace_6052310
  have hstable : (prefixWord ++ tailWord_6052310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052310).length < 2 ^ (prefixWord ++ tailWord_6052310).sum := by decide
  have hdescent : baseEnd_6052310 < baseStart_6052310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052363 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_6052363 : Nat := 118140960795 + 6052363 * 2 ^ 59
def prefixEnd_6052363 : Nat := 4983230072969 + 3 ^ 40 * 6052363 * 2
def baseEnd_6052363 : Nat := 3107771314488008835628195

theorem tailTrace_6052363 : CollatzResearch.WordTrace tailWord_6052363 prefixEnd_6052363 3107771314488008835628195 := by
  unfold tailWord_6052363
  simp only [CollatzResearch.WordTrace]
  refine ⟨220747813772329987151529743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147165209181553324767686495 220747813772329987151529743)
  ·
    refine ⟨331121720658494980727294615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220747813772329987151529743 331121720658494980727294615)
    ·
      refine ⟨496682580987742471090941923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331121720658494980727294615 496682580987742471090941923)
      ·
        refine ⟨745023871481613706636412885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496682580987742471090941923 745023871481613706636412885)
        ·
          refine ⟨17461496987850321249290927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 745023871481613706636412885 17461496987850321249290927)
          ·
            refine ⟨26192245481775481873936391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17461496987850321249290927 26192245481775481873936391)
            ·
              refine ⟨39288368222663222810904587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26192245481775481873936391 39288368222663222810904587)
              ·
                refine ⟨58932552333994834216356881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39288368222663222810904587 58932552333994834216356881)
                ·
                  refine ⟨44199414250496125662267661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58932552333994834216356881 44199414250496125662267661)
                  ·
                    refine ⟨16574780343936047123350373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44199414250496125662267661 16574780343936047123350373)
                    ·
                      refine ⟨3107771314488008835628195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16574780343936047123350373 3107771314488008835628195)
                      ·
                        rfl

theorem cell23_6052363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_6052363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052363 prefixEnd_6052363 := by exact prefixLift 6052363
  have htrace : WordTrace (prefixWord ++ tailWord_6052363) baseStart_6052363 baseEnd_6052363 := by
    simpa [prefixWord, tailWord_6052363, baseEnd_6052363] using wordTrace_append hprefix tailTrace_6052363
  have hstable : (prefixWord ++ tailWord_6052363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052363).length < 2 ^ (prefixWord ++ tailWord_6052363).sum := by decide
  have hdescent : baseEnd_6052363 < baseStart_6052363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052373 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_6052373 : Nat := 118140960795 + 6052373 * 2 ^ 59
def prefixEnd_6052373 : Nat := 4983230072969 + 3 ^ 40 * 6052373 * 2
def baseEnd_6052373 : Nat := 1035925483098184598834383

theorem tailTrace_6052373 : CollatzResearch.WordTrace tailWord_6052373 prefixEnd_6052373 1035925483098184598834383 := by
  unfold tailWord_6052373
  simp only [CollatzResearch.WordTrace]
  refine ⟨220748178502293758859393773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147165452334862505906262515 220748178502293758859393773)
  ·
    refine ⟨82780566938360159572272665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220748178502293758859393773 82780566938360159572272665)
    ·
      refine ⟨62085425203770119679204499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82780566938360159572272665 62085425203770119679204499)
      ·
        refine ⟨93128137805655179518806749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62085425203770119679204499 93128137805655179518806749)
        ·
          refine ⟨34923051677120692319552531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93128137805655179518806749 34923051677120692319552531)
          ·
            refine ⟨52384577515681038479328797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34923051677120692319552531 52384577515681038479328797)
            ·
              refine ⟨19644216568380389429748299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52384577515681038479328797 19644216568380389429748299)
              ·
                refine ⟨29466324852570584144622449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19644216568380389429748299 29466324852570584144622449)
                ·
                  refine ⟨22099743639427938108466837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29466324852570584144622449 22099743639427938108466837)
                  ·
                    refine ⟨1035925483098184598834383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22099743639427938108466837 1035925483098184598834383)
                    ·
                      rfl

theorem cell23_6052373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_6052373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052373 prefixEnd_6052373 := by exact prefixLift 6052373
  have htrace : WordTrace (prefixWord ++ tailWord_6052373) baseStart_6052373 baseEnd_6052373 := by
    simpa [prefixWord, tailWord_6052373, baseEnd_6052373] using wordTrace_append hprefix tailTrace_6052373
  have hstable : (prefixWord ++ tailWord_6052373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052373).length < 2 ^ (prefixWord ++ tailWord_6052373).sum := by decide
  have hdescent : baseEnd_6052373 < baseStart_6052373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052383 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_6052383 : Nat := 118140960795 + 6052383 * 2 ^ 59
def prefixEnd_6052383 : Nat := 4983230072969 + 3 ^ 40 * 6052383 * 2
def baseEnd_6052383 : Nat := 3107781584101098757378103

theorem tailTrace_6052383 : CollatzResearch.WordTrace tailWord_6052383 prefixEnd_6052383 3107781584101098757378103 := by
  unfold tailWord_6052383
  simp only [CollatzResearch.WordTrace]
  refine ⟨220748543232257530567257803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147165695488171687044838535 220748543232257530567257803)
  ·
    refine ⟨331122814848386295850886705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220748543232257530567257803 331122814848386295850886705)
    ·
      refine ⟨248342111136289721888165029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331122814848386295850886705 248342111136289721888165029)
      ·
        refine ⟨46564145838054322854030943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248342111136289721888165029 46564145838054322854030943)
        ·
          refine ⟨69846218757081484281046415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46564145838054322854030943 69846218757081484281046415)
          ·
            refine ⟨104769328135622226421569623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69846218757081484281046415 104769328135622226421569623)
            ·
              refine ⟨157153992203433339632354435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104769328135622226421569623 157153992203433339632354435)
              ·
                refine ⟨235730988305150009448531653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157153992203433339632354435 235730988305150009448531653)
                ·
                  refine ⟨44199560307215626771599685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235730988305150009448531653 44199560307215626771599685)
                  ·
                    refine ⟨8287417557602930019674941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44199560307215626771599685 8287417557602930019674941)
                    ·
                      refine ⟨3107781584101098757378103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287417557602930019674941 3107781584101098757378103)
                      ·
                        rfl

theorem cell23_6052383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_6052383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052383 prefixEnd_6052383 := by exact prefixLift 6052383
  have htrace : WordTrace (prefixWord ++ tailWord_6052383) baseStart_6052383 baseEnd_6052383 := by
    simpa [prefixWord, tailWord_6052383, baseEnd_6052383] using wordTrace_append hprefix tailTrace_6052383
  have hstable : (prefixWord ++ tailWord_6052383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052383).length < 2 ^ (prefixWord ++ tailWord_6052383).sum := by decide
  have hdescent : baseEnd_6052383 < baseStart_6052383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052430 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_6052430 : Nat := 118140960795 + 6052430 * 2 ^ 59
def prefixEnd_6052430 : Nat := 4983230072969 + 3 ^ 40 * 6052430 * 2
def baseEnd_6052430 : Nat := 3107805717691860073490387

theorem tailTrace_6052430 : CollatzResearch.WordTrace tailWord_6052430 prefixEnd_6052430 3107805717691860073490387 := by
  unfold tailWord_6052430
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593782182885907199277343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147166838308724838396145829 27593782182885907199277343)
  ·
    refine ⟨41390673274328860798916015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27593782182885907199277343 41390673274328860798916015)
    ·
      refine ⟨62086009911493291198374023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41390673274328860798916015 62086009911493291198374023)
      ·
        refine ⟨93129014867239936797561035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62086009911493291198374023 93129014867239936797561035)
        ·
          refine ⟨139693522300859905196341553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93129014867239936797561035 139693522300859905196341553)
          ·
            refine ⟨104770141725644928897256165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139693522300859905196341553 104770141725644928897256165)
            ·
              refine ⟨19644401573558424168235531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104770141725644928897256165 19644401573558424168235531)
              ·
                refine ⟨29466602360337636252353297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19644401573558424168235531 29466602360337636252353297)
                ·
                  refine ⟨22099951770253227189264973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29466602360337636252353297 22099951770253227189264973)
                  ·
                    refine ⟨8287481913844960195974365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22099951770253227189264973 8287481913844960195974365)
                    ·
                      refine ⟨3107805717691860073490387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287481913844960195974365 3107805717691860073490387)
                      ·
                        rfl

theorem cell23_6052430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_6052430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052430 prefixEnd_6052430 := by exact prefixLift 6052430
  have htrace : WordTrace (prefixWord ++ tailWord_6052430) baseStart_6052430 baseEnd_6052430 := by
    simpa [prefixWord, tailWord_6052430, baseEnd_6052430] using wordTrace_append hprefix tailTrace_6052430
  have hstable : (prefixWord ++ tailWord_6052430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052430).length < 2 ^ (prefixWord ++ tailWord_6052430).sum := by decide
  have hdescent : baseEnd_6052430 < baseStart_6052430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052433 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_6052433 : Nat := 118140960795 + 6052433 * 2 ^ 59
def prefixEnd_6052433 : Nat := 4983230072969 + 3 ^ 40 * 6052433 * 2
def baseEnd_6052433 : Nat := 1035935752711274520584291

theorem tailTrace_6052433 : CollatzResearch.WordTrace tailWord_6052433 prefixEnd_6052433 1035935752711274520584291 := by
  unfold tailWord_6052433
  simp only [CollatzResearch.WordTrace]
  refine ⟨220750366882076389106577953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147166911254717592737718635 220750366882076389106577953)
  ·
    refine ⟨165562775161557291829933465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220750366882076389106577953 165562775161557291829933465)
    ·
      refine ⟨124172081371167968872450099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165562775161557291829933465 124172081371167968872450099)
      ·
        refine ⟨186258122056751953308675149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124172081371167968872450099 186258122056751953308675149)
        ·
          refine ⟨69846795771281982490753181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186258122056751953308675149 69846795771281982490753181)
          ·
            refine ⟨26192548414230743434032443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69846795771281982490753181 26192548414230743434032443)
            ·
              refine ⟨39288822621346115151048665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26192548414230743434032443 39288822621346115151048665)
              ·
                refine ⟨29466616966009586363286499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39288822621346115151048665 29466616966009586363286499)
                ·
                  refine ⟨44199925449014379544929749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29466616966009586363286499 44199925449014379544929749)
                  ·
                    refine ⟨1035935752711274520584291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44199925449014379544929749 1035935752711274520584291)
                    ·
                      rfl

theorem cell23_6052433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_6052433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052433 prefixEnd_6052433 := by exact prefixLift 6052433
  have htrace : WordTrace (prefixWord ++ tailWord_6052433) baseStart_6052433 baseEnd_6052433 := by
    simpa [prefixWord, tailWord_6052433, baseEnd_6052433] using wordTrace_append hprefix tailTrace_6052433
  have hstable : (prefixWord ++ tailWord_6052433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052433).length < 2 ^ (prefixWord ++ tailWord_6052433).sum := by decide
  have hdescent : baseEnd_6052433 < baseStart_6052433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052440 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_6052440 : Nat := 118140960795 + 6052440 * 2 ^ 59
def prefixEnd_6052440 : Nat := 4983230072969 + 3 ^ 40 * 6052440 * 2
def baseEnd_6052440 : Nat := 3107810852498405034365341

theorem tailTrace_6052440 : CollatzResearch.WordTrace tailWord_6052440 prefixEnd_6052440 3107810852498405034365341 := by
  unfold tailWord_6052440
  simp only [CollatzResearch.WordTrace]
  refine ⟨110375311096525514651041387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147167081462034019534721849 110375311096525514651041387)
  ·
    refine ⟨165562966644788271976562081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110375311096525514651041387 165562966644788271976562081)
    ·
      refine ⟨124172224983591203982421561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165562966644788271976562081 124172224983591203982421561)
      ·
        refine ⟨93129168737693402986816171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124172224983591203982421561 93129168737693402986816171)
        ·
          refine ⟨139693753106540104480224257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93129168737693402986816171 139693753106540104480224257)
          ·
            refine ⟨104770314829905078360168193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139693753106540104480224257 104770314829905078360168193)
            ·
              refine ⟨78577736122428808770126145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104770314829905078360168193 78577736122428808770126145)
              ·
                refine ⟨58933302091821606577594609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78577736122428808770126145 58933302091821606577594609)
                ·
                  refine ⟨44199976568866204933195957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58933302091821606577594609 44199976568866204933195957)
                  ·
                    refine ⟨4143747803331206712487121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44199976568866204933195957 4143747803331206712487121)
                    ·
                      refine ⟨3107810852498405034365341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143747803331206712487121 3107810852498405034365341)
                      ·
                        rfl

theorem cell23_6052440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_6052440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052440 prefixEnd_6052440 := by exact prefixLift 6052440
  have htrace : WordTrace (prefixWord ++ tailWord_6052440) baseStart_6052440 baseEnd_6052440 := by
    simpa [prefixWord, tailWord_6052440, baseEnd_6052440] using wordTrace_append hprefix tailTrace_6052440
  have hstable : (prefixWord ++ tailWord_6052440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052440).length < 2 ^ (prefixWord ++ tailWord_6052440).sum := by decide
  have hdescent : baseEnd_6052440 < baseStart_6052440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052483 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_6052483 : Nat := 118140960795 + 6052483 * 2 ^ 59
def prefixEnd_6052483 : Nat := 4983230072969 + 3 ^ 40 * 6052483 * 2
def baseEnd_6052483 : Nat := 3107832932166548366127643

theorem tailTrace_6052483 : CollatzResearch.WordTrace tailWord_6052483 prefixEnd_6052483 3107832932166548366127643 := by
  unfold tailWord_6052483
  simp only [CollatzResearch.WordTrace]
  refine ⟨220752190531895247645898103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147168127021263498430598735 220752190531895247645898103)
  ·
    refine ⟨331128285797842871468847155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220752190531895247645898103 331128285797842871468847155)
    ·
      refine ⟨496692428696764307203270733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331128285797842871468847155 496692428696764307203270733)
      ·
        refine ⟨186259660761286615201226525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496692428696764307203270733 186259660761286615201226525)
        ·
          refine ⟨69847372785482480700459947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186259660761286615201226525 69847372785482480700459947)
          ·
            refine ⟨104771059178223721050689921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69847372785482480700459947 104771059178223721050689921)
            ·
              refine ⟨78578294383667790788017441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104771059178223721050689921 78578294383667790788017441)
              ·
                refine ⟨58933720787750843091013081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78578294383667790788017441 58933720787750843091013081)
                ·
                  refine ⟨44200290590813132318259811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58933720787750843091013081 44200290590813132318259811)
                  ·
                    refine ⟨66300435886219698477389717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44200290590813132318259811 66300435886219698477389717)
                    ·
                      refine ⟨3107832932166548366127643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66300435886219698477389717 3107832932166548366127643)
                      ·
                        rfl

theorem cell23_6052483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_6052483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052483 prefixEnd_6052483 := by exact prefixLift 6052483
  have htrace : WordTrace (prefixWord ++ tailWord_6052483) baseStart_6052483 baseEnd_6052483 := by
    simpa [prefixWord, tailWord_6052483, baseEnd_6052483] using wordTrace_append hprefix tailTrace_6052483
  have hstable : (prefixWord ++ tailWord_6052483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052483).length < 2 ^ (prefixWord ++ tailWord_6052483).sum := by decide
  have hdescent : baseEnd_6052483 < baseStart_6052483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052531 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 1, 4]
def baseStart_6052531 : Nat := 118140960795 + 6052531 * 2 ^ 59
def prefixEnd_6052531 : Nat := 4983230072969 + 3 ^ 40 * 6052531 * 2
def baseEnd_6052531 : Nat := 1035952526412654726109141

theorem tailTrace_6052531 : CollatzResearch.WordTrace tailWord_6052531 prefixEnd_6052531 1035952526412654726109141 := by
  unfold tailWord_6052531
  simp only [CollatzResearch.WordTrace]
  refine ⟨220753941235721351843645447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147169294157147567895763631 220753941235721351843645447)
  ·
    refine ⟨331130911853582027765468171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220753941235721351843645447 331130911853582027765468171)
    ·
      refine ⟨496696367780373041648202257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331130911853582027765468171 496696367780373041648202257)
      ·
        refine ⟨372522275835279781236151693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496696367780373041648202257 372522275835279781236151693)
        ·
          refine ⟨139695853438229917963556885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372522275835279781236151693 139695853438229917963556885)
          ·
            refine ⟨6548243129917027404541729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139695853438229917963556885 6548243129917027404541729)
            ·
              refine ⟨4911182347437770553406297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6548243129917027404541729 4911182347437770553406297)
              ·
                refine ⟨3683386760578327915054723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4911182347437770553406297 3683386760578327915054723)
                ·
                  refine ⟨5525080140867491872582085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683386760578327915054723 5525080140867491872582085)
                  ·
                    refine ⟨1035952526412654726109141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525080140867491872582085 1035952526412654726109141)
                    ·
                      rfl

theorem cell23_6052531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 4].length) (baseStart_6052531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052531 prefixEnd_6052531 := by exact prefixLift 6052531
  have htrace : WordTrace (prefixWord ++ tailWord_6052531) baseStart_6052531 baseEnd_6052531 := by
    simpa [prefixWord, tailWord_6052531, baseEnd_6052531] using wordTrace_append hprefix tailTrace_6052531
  have hstable : (prefixWord ++ tailWord_6052531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052531).length < 2 ^ (prefixWord ++ tailWord_6052531).sum := by decide
  have hdescent : baseEnd_6052531 < baseStart_6052531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052537 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6052537 : Nat := 118140960795 + 6052537 * 2 ^ 59
def prefixEnd_6052537 : Nat := 4983230072969 + 3 ^ 40 * 6052537 * 2
def baseEnd_6052537 : Nat := 3107860660121891154852395

theorem tailTrace_6052537 : CollatzResearch.WordTrace tailWord_6052537 prefixEnd_6052537 3107860660121891154852395 := by
  unfold tailWord_6052537
  simp only [CollatzResearch.WordTrace]
  refine ⟨220754160073699614868363865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147169440049133076578909243 220754160073699614868363865)
  ·
    refine ⟨165565620055274711151272899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220754160073699614868363865 165565620055274711151272899)
    ·
      refine ⟨248348430082912066726909349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165565620055274711151272899 248348430082912066726909349)
      ·
        refine ⟨46565330640546012511295503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248348430082912066726909349 46565330640546012511295503)
        ·
          refine ⟨69847995960819018766943255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46565330640546012511295503 69847995960819018766943255)
          ·
            refine ⟨104771993941228528150414883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69847995960819018766943255 104771993941228528150414883)
            ·
              refine ⟨157157990911842792225622325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104771993941228528150414883 157157990911842792225622325)
              ·
                refine ⟨14733561647985261771152093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157157990911842792225622325 14733561647985261771152093)
                ·
                  refine ⟨5525085617994473164182035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14733561647985261771152093 5525085617994473164182035)
                  ·
                    refine ⟨8287628426991709746273053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525085617994473164182035 8287628426991709746273053)
                    ·
                      refine ⟨3107860660121891154852395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287628426991709746273053 3107860660121891154852395)
                      ·
                        rfl

theorem cell23_6052537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6052537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052537 prefixEnd_6052537 := by exact prefixLift 6052537
  have htrace : WordTrace (prefixWord ++ tailWord_6052537) baseStart_6052537 baseEnd_6052537 := by
    simpa [prefixWord, tailWord_6052537, baseEnd_6052537] using wordTrace_append hprefix tailTrace_6052537
  have hstable : (prefixWord ++ tailWord_6052537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052537).length < 2 ^ (prefixWord ++ tailWord_6052537).sum := by decide
  have hdescent : baseEnd_6052537 < baseStart_6052537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052540 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_6052540 : Nat := 118140960795 + 6052540 * 2 ^ 59
def prefixEnd_6052540 : Nat := 4983230072969 + 3 ^ 40 * 6052540 * 2
def baseEnd_6052540 : Nat := 1035954066854618214371627

theorem tailTrace_6052540 : CollatzResearch.WordTrace tailWord_6052540 prefixEnd_6052540 1035954066854618214371627 := by
  unfold tailWord_6052540
  simp only [CollatzResearch.WordTrace]
  refine ⟨110377134746344373190361537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147169512995125830920482049 110377134746344373190361537)
  ·
    refine ⟨82782851059758279892771153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110377134746344373190361537 82782851059758279892771153)
    ·
      refine ⟨62087138294818709919578365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82782851059758279892771153 62087138294818709919578365)
      ·
        refine ⟨23282676860557016219841887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62087138294818709919578365 23282676860557016219841887)
        ·
          refine ⟨34924015290835524329762831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23282676860557016219841887 34924015290835524329762831)
          ·
            refine ⟨52386022936253286494644247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34924015290835524329762831 52386022936253286494644247)
            ·
              refine ⟨78579034404379929741966371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52386022936253286494644247 78579034404379929741966371)
              ·
                refine ⟨117868551606569894612949557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78579034404379929741966371 117868551606569894612949557)
                ·
                  refine ⟨11050176713115927619964021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117868551606569894612949557 11050176713115927619964021)
                  ·
                    refine ⟨1035954066854618214371627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11050176713115927619964021 1035954066854618214371627)
                    ·
                      rfl

theorem cell23_6052540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_6052540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052540 prefixEnd_6052540 := by exact prefixLift 6052540
  have htrace : WordTrace (prefixWord ++ tailWord_6052540) baseStart_6052540 baseEnd_6052540 := by
    simpa [prefixWord, tailWord_6052540, baseEnd_6052540] using wordTrace_append hprefix tailTrace_6052540
  have hstable : (prefixWord ++ tailWord_6052540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052540).length < 2 ^ (prefixWord ++ tailWord_6052540).sum := by decide
  have hdescent : baseEnd_6052540 < baseStart_6052540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052554 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_6052554 : Nat := 118140960795 + 6052554 * 2 ^ 59
def prefixEnd_6052554 : Nat := 4983230072969 + 3 ^ 40 * 6052554 * 2
def baseEnd_6052554 : Nat := 3107869389293017588339817

theorem tailTrace_6052554 : CollatzResearch.WordTrace tailWord_6052554 prefixEnd_6052554 3107869389293017588339817 := by
  unfold tailWord_6052554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55188695028659506692933179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147169853409758684514488477 55188695028659506692933179)
  ·
    refine ⟨82783042542989260039399769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55188695028659506692933179 82783042542989260039399769)
    ·
      refine ⟨62087281907241945029549827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82783042542989260039399769 62087281907241945029549827)
      ·
        refine ⟨93130922860862917544324741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62087281907241945029549827 93130922860862917544324741)
        ·
          refine ⟨17462048036411797039560889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93130922860862917544324741 17462048036411797039560889)
          ·
            refine ⟨13096536027308847779670667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17462048036411797039560889 13096536027308847779670667)
            ·
              refine ⟨19644804040963271669506001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096536027308847779670667 19644804040963271669506001)
              ·
                refine ⟨14733603030722453752129501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19644804040963271669506001 14733603030722453752129501)
                ·
                  refine ⟨5525101136520920157048563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14733603030722453752129501 5525101136520920157048563)
                  ·
                    refine ⟨8287651704781380235572845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525101136520920157048563 8287651704781380235572845)
                    ·
                      refine ⟨3107869389293017588339817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287651704781380235572845 3107869389293017588339817)
                      ·
                        rfl

theorem cell23_6052554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_6052554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052554 prefixEnd_6052554 := by exact prefixLift 6052554
  have htrace : WordTrace (prefixWord ++ tailWord_6052554) baseStart_6052554 baseEnd_6052554 := by
    simpa [prefixWord, tailWord_6052554, baseEnd_6052554] using wordTrace_append hprefix tailTrace_6052554
  have hstable : (prefixWord ++ tailWord_6052554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052554).length < 2 ^ (prefixWord ++ tailWord_6052554).sum := by decide
  have hdescent : baseEnd_6052554 < baseStart_6052554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052570 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_6052570 : Nat := 118140960795 + 6052570 * 2 ^ 59
def prefixEnd_6052570 : Nat := 4983230072969 + 3 ^ 40 * 6052570 * 2
def baseEnd_6052570 : Nat := 1035959201661163175246581

theorem tailTrace_6052570 : CollatzResearch.WordTrace tailWord_6052570 prefixEnd_6052570 1035959201661163175246581 := by
  unfold tailWord_6052570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55188840920645015376078791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147170242455053374336210109 55188840920645015376078791)
  ·
    refine ⟨82783261380967523064118187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55188840920645015376078791 82783261380967523064118187)
    ·
      refine ⟨124174892071451284596177281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82783261380967523064118187 124174892071451284596177281)
      ·
        refine ⟨93131169053588463447132961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124174892071451284596177281 93131169053588463447132961)
        ·
          refine ⟨69848376790191347585349721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93131169053588463447132961 69848376790191347585349721)
          ·
            refine ⟨52386282592643510689012291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69848376790191347585349721 52386282592643510689012291)
            ·
              refine ⟨78579423888965266033518437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52386282592643510689012291 78579423888965266033518437)
              ·
                refine ⟨14733641979180987381284707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78579423888965266033518437 14733641979180987381284707)
                ·
                  refine ⟨22100462968771481071927061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14733641979180987381284707 22100462968771481071927061)
                  ·
                    refine ⟨1035959201661163175246581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22100462968771481071927061 1035959201661163175246581)
                    ·
                      rfl

theorem cell23_6052570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_6052570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052570 prefixEnd_6052570 := by exact prefixLift 6052570
  have htrace : WordTrace (prefixWord ++ tailWord_6052570) baseStart_6052570 baseEnd_6052570 := by
    simpa [prefixWord, tailWord_6052570, baseEnd_6052570] using wordTrace_append hprefix tailTrace_6052570
  have hstable : (prefixWord ++ tailWord_6052570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052570).length < 2 ^ (prefixWord ++ tailWord_6052570).sum := by decide
  have hdescent : baseEnd_6052570 < baseStart_6052570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052627 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 3]
def baseStart_6052627 : Nat := 118140960795 + 6052627 * 2 ^ 59
def prefixEnd_6052627 : Nat := 4983230072969 + 3 ^ 40 * 6052627 * 2
def baseEnd_6052627 : Nat := 3107906873380795802726981

theorem tailTrace_6052627 : CollatzResearch.WordTrace tailWord_6052627 prefixEnd_6052627 3107906873380795802726981 := by
  unfold tailWord_6052627
  simp only [CollatzResearch.WordTrace]
  refine ⟨220757442643373560239140135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147171628428915706826093423 220757442643373560239140135)
  ·
    refine ⟨331136163965060340358710203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220757442643373560239140135 331136163965060340358710203)
    ·
      refine ⟨496704245947590510538065305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331136163965060340358710203 496704245947590510538065305)
      ·
        refine ⟨372528184460692882903548979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496704245947590510538065305 372528184460692882903548979)
        ·
          refine ⟨558792276691039324355323469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372528184460692882903548979 558792276691039324355323469)
          ·
            refine ⟨209547103759139746633246301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558792276691039324355323469 209547103759139746633246301)
            ·
              refine ⟨78580163909677404987467363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209547103759139746633246301 78580163909677404987467363)
              ·
                refine ⟨117870245864516107481201045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78580163909677404987467363 117870245864516107481201045)
                ·
                  refine ⟨5525167774899192538181299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117870245864516107481201045 5525167774899192538181299)
                  ·
                    refine ⟨8287751662348788807271949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525167774899192538181299 8287751662348788807271949)
                    ·
                      refine ⟨3107906873380795802726981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287751662348788807271949 3107906873380795802726981)
                      ·
                        rfl

theorem cell23_6052627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_6052627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052627 prefixEnd_6052627 := by exact prefixLift 6052627
  have htrace : WordTrace (prefixWord ++ tailWord_6052627) baseStart_6052627 baseEnd_6052627 := by
    simpa [prefixWord, tailWord_6052627, baseEnd_6052627] using wordTrace_append hprefix tailTrace_6052627
  have hstable : (prefixWord ++ tailWord_6052627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052627).length < 2 ^ (prefixWord ++ tailWord_6052627).sum := by decide
  have hdescent : baseEnd_6052627 < baseStart_6052627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052661 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_6052661 : Nat := 118140960795 + 6052661 * 2 ^ 59
def prefixEnd_6052661 : Nat := 4983230072969 + 3 ^ 40 * 6052661 * 2
def baseEnd_6052661 : Nat := 3107924331723048669701825

theorem tailTrace_6052661 : CollatzResearch.WordTrace tailWord_6052661 prefixEnd_6052661 3107924331723048669701825 := by
  unfold tailWord_6052661
  simp only [CollatzResearch.WordTrace]
  refine ⟨220758682725250384045877837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147172455150166922697251891 220758682725250384045877837)
  ·
    refine ⟨82784506021968894017204189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220758682725250384045877837 82784506021968894017204189)
    ·
      refine ⟨31044189758238335256451571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82784506021968894017204189 31044189758238335256451571)
      ·
        refine ⟨46566284637357502884677357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31044189758238335256451571 46566284637357502884677357)
        ·
          refine ⟨17462356739009063581754009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46566284637357502884677357 17462356739009063581754009)
          ·
            refine ⟨13096767554256797686315507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17462356739009063581754009 13096767554256797686315507)
            ·
              refine ⟨19645151331385196529473261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096767554256797686315507 19645151331385196529473261)
              ·
                refine ⟨7366931749269448698552473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19645151331385196529473261 7366931749269448698552473)
                ·
                  refine ⟨5525198811952086523914355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7366931749269448698552473 5525198811952086523914355)
                  ·
                    refine ⟨8287798217928129785871533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525198811952086523914355 8287798217928129785871533)
                    ·
                      refine ⟨3107924331723048669701825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287798217928129785871533 3107924331723048669701825)
                      ·
                        rfl

theorem cell23_6052661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_6052661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052661 prefixEnd_6052661 := by exact prefixLift 6052661
  have htrace : WordTrace (prefixWord ++ tailWord_6052661) baseStart_6052661 baseEnd_6052661 := by
    simpa [prefixWord, tailWord_6052661, baseEnd_6052661] using wordTrace_append hprefix tailTrace_6052661
  have hstable : (prefixWord ++ tailWord_6052661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052661).length < 2 ^ (prefixWord ++ tailWord_6052661).sum := by decide
  have hdescent : baseEnd_6052661 < baseStart_6052661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052671 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 1, 3, 2]
def baseStart_6052671 : Nat := 118140960795 + 6052671 * 2 ^ 59
def prefixEnd_6052671 : Nat := 4983230072969 + 3 ^ 40 * 6052671 * 2
def baseEnd_6052671 : Nat := 3107929466529593630576779

theorem tailTrace_6052671 : CollatzResearch.WordTrace tailWord_6052671 prefixEnd_6052671 3107929466529593630576779 := by
  unfold tailWord_6052671
  simp only [CollatzResearch.WordTrace]
  refine ⟨220759047455214155753741867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147172698303476103835827911 220759047455214155753741867)
  ·
    refine ⟨331138571182821233630612801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220759047455214155753741867 331138571182821233630612801)
    ·
      refine ⟨248353928387115925222959601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331138571182821233630612801 248353928387115925222959601)
      ·
        refine ⟨186265446290336943917219701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248353928387115925222959601 186265446290336943917219701)
        ·
          refine ⟨17462385589719088492239347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186265446290336943917219701 17462385589719088492239347)
          ·
            refine ⟨26193578384578632738359021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17462385589719088492239347 26193578384578632738359021)
            ·
              refine ⟨9822591894216987276884633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26193578384578632738359021 9822591894216987276884633)
              ·
                refine ⟨7366943920662740457663475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9822591894216987276884633 7366943920662740457663475)
                ·
                  refine ⟨11050415880994110686495213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7366943920662740457663475 11050415880994110686495213)
                  ·
                    refine ⟨4143905955372791507435705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11050415880994110686495213 4143905955372791507435705)
                    ·
                      refine ⟨3107929466529593630576779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143905955372791507435705 3107929466529593630576779)
                      ·
                        rfl

theorem cell23_6052671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_6052671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052671 prefixEnd_6052671 := by exact prefixLift 6052671
  have htrace : WordTrace (prefixWord ++ tailWord_6052671) baseStart_6052671 baseEnd_6052671 := by
    simpa [prefixWord, tailWord_6052671, baseEnd_6052671] using wordTrace_append hprefix tailTrace_6052671
  have hstable : (prefixWord ++ tailWord_6052671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052671).length < 2 ^ (prefixWord ++ tailWord_6052671).sum := by decide
  have hdescent : baseEnd_6052671 < baseStart_6052671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052678 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6052678 : Nat := 118140960795 + 6052678 * 2 ^ 59
def prefixEnd_6052678 : Nat := 4983230072969 + 3 ^ 40 * 6052678 * 2
def baseEnd_6052678 : Nat := 3107933060894175103189247

theorem tailTrace_6052678 : CollatzResearch.WordTrace tailWord_6052678 prefixEnd_6052678 3107933060894175103189247 := by
  unfold tailWord_6052678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898728211443399873413959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147172868510792530632831125 6898728211443399873413959)
  ·
    refine ⟨10348092317165099810120939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898728211443399873413959 10348092317165099810120939)
    ·
      refine ⟨15522138475747649715181409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10348092317165099810120939 15522138475747649715181409)
      ·
        refine ⟨11641603856810737286386057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15522138475747649715181409 11641603856810737286386057)
        ·
          refine ⟨8731202892608052964789543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11641603856810737286386057 8731202892608052964789543)
          ·
            refine ⟨13096804338912079447184315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731202892608052964789543 13096804338912079447184315)
            ·
              refine ⟨19645206508368119170776473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096804338912079447184315 19645206508368119170776473)
              ·
                refine ⟨14733904881276089378082355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19645206508368119170776473 14733904881276089378082355)
                ·
                  refine ⟨22100857321914134067123533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14733904881276089378082355 22100857321914134067123533)
                  ·
                    refine ⟨8287821495717800275171325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22100857321914134067123533 8287821495717800275171325)
                    ·
                      refine ⟨3107933060894175103189247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287821495717800275171325 3107933060894175103189247)
                      ·
                        rfl

theorem cell23_6052678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6052678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052678 prefixEnd_6052678 := by exact prefixLift 6052678
  have htrace : WordTrace (prefixWord ++ tailWord_6052678) baseStart_6052678 baseEnd_6052678 := by
    simpa [prefixWord, tailWord_6052678, baseEnd_6052678] using wordTrace_append hprefix tailTrace_6052678
  have hstable : (prefixWord ++ tailWord_6052678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052678).length < 2 ^ (prefixWord ++ tailWord_6052678).sum := by decide
  have hdescent : baseEnd_6052678 < baseStart_6052678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052684 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6052684 : Nat := 118140960795 + 6052684 * 2 ^ 59
def prefixEnd_6052684 : Nat := 4983230072969 + 3 ^ 40 * 6052684 * 2
def baseEnd_6052684 : Nat := 3107936141778102079714219

theorem tailTrace_6052684 : CollatzResearch.WordTrace tailWord_6052684 prefixEnd_6052684 3107936141778102079714219 := by
  unfold tailWord_6052684
  simp only [CollatzResearch.WordTrace]
  refine ⟨110379760802083529486982553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147173014402778039315976737 110379760802083529486982553)
  ·
    refine ⟨82784820601562647115236915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110379760802083529486982553 82784820601562647115236915)
    ·
      refine ⟨124177230902343970672855373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82784820601562647115236915 124177230902343970672855373)
      ·
        refine ⟨46566461588378989002320765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124177230902343970672855373 46566461588378989002320765)
        ·
          refine ⟨17462423095642120875870287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46566461588378989002320765 17462423095642120875870287)
          ·
            refine ⟨26193634643463181313805431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17462423095642120875870287 26193634643463181313805431)
            ·
              refine ⟨39290451965194771970708147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26193634643463181313805431 39290451965194771970708147)
              ·
                refine ⟨58935677947792157956062221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39290451965194771970708147 58935677947792157956062221)
                ·
                  refine ⟨22100879230422059233523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58935677947792157956062221 22100879230422059233523333)
                  ·
                    refine ⟨4143914855704136106285625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22100879230422059233523333 4143914855704136106285625)
                    ·
                      refine ⟨3107936141778102079714219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143914855704136106285625 3107936141778102079714219)
                      ·
                        rfl

theorem cell23_6052684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6052684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052684 prefixEnd_6052684 := by exact prefixLift 6052684
  have htrace : WordTrace (prefixWord ++ tailWord_6052684) baseStart_6052684 baseEnd_6052684 := by
    simpa [prefixWord, tailWord_6052684, baseEnd_6052684] using wordTrace_append hprefix tailTrace_6052684
  have hstable : (prefixWord ++ tailWord_6052684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052684).length < 2 ^ (prefixWord ++ tailWord_6052684).sum := by decide
  have hdescent : baseEnd_6052684 < baseStart_6052684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052718 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6052718 : Nat := 118140960795 + 6052718 * 2 ^ 59
def prefixEnd_6052718 : Nat := 4983230072969 + 3 ^ 40 * 6052718 * 2
def baseEnd_6052718 : Nat := 3107953600120354946689063

theorem tailTrace_6052718 : CollatzResearch.WordTrace tailWord_6052718 prefixEnd_6052718 3107953600120354946689063 := by
  unfold tailWord_6052718
  simp only [CollatzResearch.WordTrace]
  refine ⟨27595095210755485347587851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147173841124029255187135205 27595095210755485347587851)
  ·
    refine ⟨41392642816133228021381777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27595095210755485347587851 41392642816133228021381777)
    ·
      refine ⟨31044482112099921016036333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41392642816133228021381777 31044482112099921016036333)
      ·
        refine ⟨11641680792037470381013625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31044482112099921016036333 11641680792037470381013625)
        ·
          refine ⟨8731260594028102785760219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11641680792037470381013625 8731260594028102785760219)
          ·
            refine ⟨13096890891042154178640329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731260594028102785760219 13096890891042154178640329)
            ·
              refine ⟨9822668168281615633980247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13096890891042154178640329 9822668168281615633980247)
              ·
                refine ⟨14734002252422423450970371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822668168281615633980247 14734002252422423450970371)
                ·
                  refine ⟨22101003378633635176455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14734002252422423450970371 22101003378633635176455557)
                  ·
                    refine ⟨4143938133493806595585417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22101003378633635176455557 4143938133493806595585417)
                    ·
                      refine ⟨3107953600120354946689063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4143938133493806595585417 3107953600120354946689063)
                      ·
                        rfl

theorem cell23_6052718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6052718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052718 prefixEnd_6052718 := by exact prefixLift 6052718
  have htrace : WordTrace (prefixWord ++ tailWord_6052718) baseStart_6052718 baseEnd_6052718 := by
    simpa [prefixWord, tailWord_6052718, baseEnd_6052718] using wordTrace_append hprefix tailTrace_6052718
  have hstable : (prefixWord ++ tailWord_6052718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052718).length < 2 ^ (prefixWord ++ tailWord_6052718).sum := by decide
  have hdescent : baseEnd_6052718 < baseStart_6052718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052758 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6052758 : Nat := 118140960795 + 6052758 * 2 ^ 59
def prefixEnd_6052758 : Nat := 4983230072969 + 3 ^ 40 * 6052758 * 2
def baseEnd_6052758 : Nat := 345330459927392754465431

theorem tailTrace_6052758 : CollatzResearch.WordTrace tailWord_6052758 prefixEnd_6052758 345330459927392754465431 := by
  unfold tailWord_6052758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797638787868685600759933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147174813737265979741439285 13797638787868685600759933)
  ·
    refine ⟨5174114545450757100284975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13797638787868685600759933 5174114545450757100284975)
    ·
      refine ⟨7761171818176135650427463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174114545450757100284975 7761171818176135650427463)
      ·
        refine ⟨11641757727264203475641195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761171818176135650427463 11641757727264203475641195)
        ·
          refine ⟨17462636590896305213461793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11641757727264203475641195 17462636590896305213461793)
          ·
            refine ⟨13096977443172228910096345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17462636590896305213461793 13096977443172228910096345)
            ·
              refine ⟨9822733082379171682572259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13096977443172228910096345 9822733082379171682572259)
              ·
                refine ⟨14734099623568757523858389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822733082379171682572259 14734099623568757523858389)
                ·
                  refine ⟨345330459927392754465431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14734099623568757523858389 345330459927392754465431)
                  ·
                    rfl

theorem cell23_6052758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6052758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052758 prefixEnd_6052758 := by exact prefixLift 6052758
  have htrace : WordTrace (prefixWord ++ tailWord_6052758) baseStart_6052758 baseEnd_6052758 := by
    simpa [prefixWord, tailWord_6052758, baseEnd_6052758] using wordTrace_append hprefix tailTrace_6052758
  have hstable : (prefixWord ++ tailWord_6052758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052758).length < 2 ^ (prefixWord ++ tailWord_6052758).sum := by decide
  have hdescent : baseEnd_6052758 < baseStart_6052758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052777 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_6052777 : Nat := 118140960795 + 6052777 * 2 ^ 59
def prefixEnd_6052777 : Nat := 4983230072969 + 3 ^ 40 * 6052777 * 2
def baseEnd_6052777 : Nat := 3107983895478970215851291

theorem tailTrace_6052777 : CollatzResearch.WordTrace tailWord_6052777 prefixEnd_6052777 3107983895478970215851291 := by
  unfold tailWord_6052777
  simp only [CollatzResearch.WordTrace]
  refine ⟨220762913592830135857100585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147175275728553423904733723 220762913592830135857100585)
  ·
    refine ⟨165572185194622601892825439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220762913592830135857100585 165572185194622601892825439)
    ·
      refine ⟨248358277791933902839238159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165572185194622601892825439 248358277791933902839238159)
      ·
        refine ⟨372537416687900854258857239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248358277791933902839238159 372537416687900854258857239)
        ·
          refine ⟨558806125031851281388285859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372537416687900854258857239 558806125031851281388285859)
          ·
            refine ⟨838209187547776922082428789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558806125031851281388285859 838209187547776922082428789)
            ·
              refine ⟨78582111332604086445227699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 838209187547776922082428789 78582111332604086445227699)
              ·
                refine ⟨117873166998906129667841549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78582111332604086445227699 117873166998906129667841549)
                ·
                  refine ⟨44202437624589798625440581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117873166998906129667841549 44202437624589798625440581)
                  ·
                    refine ⟨8287957054610587242270109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44202437624589798625440581 8287957054610587242270109)
                    ·
                      refine ⟨3107983895478970215851291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287957054610587242270109 3107983895478970215851291)
                      ·
                        rfl

theorem cell23_6052777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_6052777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052777 prefixEnd_6052777 := by exact prefixLift 6052777
  have htrace : WordTrace (prefixWord ++ tailWord_6052777) baseStart_6052777 baseEnd_6052777 := by
    simpa [prefixWord, tailWord_6052777, baseEnd_6052777] using wordTrace_append hprefix tailTrace_6052777
  have hstable : (prefixWord ++ tailWord_6052777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052777).length < 2 ^ (prefixWord ++ tailWord_6052777).sum := by decide
  have hdescent : baseEnd_6052777 < baseStart_6052777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052794 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_6052794 : Nat := 118140960795 + 6052794 * 2 ^ 59
def prefixEnd_6052794 : Nat := 4983230072969 + 3 ^ 40 * 6052794 * 2
def baseEnd_6052794 : Nat := 3107992624650096649338713

theorem tailTrace_6052794 : CollatzResearch.WordTrace tailWord_6052794 prefixEnd_6052794 3107992624650096649338713 := by
  unfold tailWord_6052794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55190883408442136940117359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147175689089179031840312957 55190883408442136940117359)
  ·
    refine ⟨82786325112663205410176039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55190883408442136940117359 82786325112663205410176039)
    ·
      refine ⟨124179487668994808115264059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82786325112663205410176039 124179487668994808115264059)
      ·
        refine ⟨186269231503492212172896089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124179487668994808115264059 186269231503492212172896089)
        ·
          refine ⟨139701923627619159129672067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186269231503492212172896089 139701923627619159129672067)
          ·
            refine ⟨209552885441428738694508101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139701923627619159129672067 209552885441428738694508101)
            ·
              refine ⟨39291166020267888505220269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209552885441428738694508101 39291166020267888505220269)
              ·
                refine ⟨14734187257600458189457601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39291166020267888505220269 14734187257600458189457601)
                ·
                  refine ⟨11050640443200343642093201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14734187257600458189457601 11050640443200343642093201)
                  ·
                    refine ⟨8287980332400257731569901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11050640443200343642093201 8287980332400257731569901)
                    ·
                      refine ⟨3107992624650096649338713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8287980332400257731569901 3107992624650096649338713)
                      ·
                        rfl

theorem cell23_6052794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_6052794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052794 prefixEnd_6052794 := by exact prefixLift 6052794
  have htrace : WordTrace (prefixWord ++ tailWord_6052794) baseStart_6052794 baseEnd_6052794 := by
    simpa [prefixWord, tailWord_6052794, baseEnd_6052794] using wordTrace_append hprefix tailTrace_6052794
  have hstable : (prefixWord ++ tailWord_6052794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052794).length < 2 ^ (prefixWord ++ tailWord_6052794).sum := by decide
  have hdescent : baseEnd_6052794 < baseStart_6052794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052818 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_6052818 : Nat := 118140960795 + 6052818 * 2 ^ 59
def prefixEnd_6052818 : Nat := 4983230072969 + 3 ^ 40 * 6052818 * 2
def baseEnd_6052818 : Nat := 1036001649395268185146201

theorem tailTrace_6052818 : CollatzResearch.WordTrace tailWord_6052818 prefixEnd_6052818 1036001649395268185146201 := by
  unfold tailWord_6052818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55191102246420399964835777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147176272657121066572895405 55191102246420399964835777)
  ·
    refine ⟨41393326684815299973626833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55191102246420399964835777 41393326684815299973626833)
    ·
      refine ⟨31044995013611474980220125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41393326684815299973626833 31044995013611474980220125)
      ·
        refine ⟨11641873130104303117582547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31044995013611474980220125 11641873130104303117582547)
        ·
          refine ⟨17462809695156454676373821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11641873130104303117582547 17462809695156454676373821)
          ·
            refine ⟨6548553635683670503640183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17462809695156454676373821 6548553635683670503640183)
            ·
              refine ⟨9822830453525505755460275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548553635683670503640183 9822830453525505755460275)
              ·
                refine ⟨14734245680288258633190413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822830453525505755460275 14734245680288258633190413)
                ·
                  refine ⟨5525342130108096987446405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14734245680288258633190413 5525342130108096987446405)
                  ·
                    refine ⟨1036001649395268185146201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525342130108096987446405 1036001649395268185146201)
                    ·
                      rfl

theorem cell23_6052818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_6052818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052818 prefixEnd_6052818 := by exact prefixLift 6052818
  have htrace : WordTrace (prefixWord ++ tailWord_6052818) baseStart_6052818 baseEnd_6052818 := by
    simpa [prefixWord, tailWord_6052818, baseEnd_6052818] using wordTrace_append hprefix tailTrace_6052818
  have hstable : (prefixWord ++ tailWord_6052818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052818).length < 2 ^ (prefixWord ++ tailWord_6052818).sum := by decide
  have hdescent : baseEnd_6052818 < baseStart_6052818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052864 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2]
def baseStart_6052864 : Nat := 118140960795 + 6052864 * 2 ^ 59
def prefixEnd_6052864 : Nat := 4983230072969 + 3 ^ 40 * 6052864 * 2
def baseEnd_6052864 : Nat := 3108028568295911375463391

theorem tailTrace_6052864 : CollatzResearch.WordTrace tailWord_6052864 prefixEnd_6052864 3108028568295911375463391 := by
  unfold tailWord_6052864
  simp only [CollatzResearch.WordTrace]
  refine ⟨110383043371757474857758823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147177391162343299810345097 110383043371757474857758823)
  ·
    refine ⟨165574565057636212286638235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110383043371757474857758823 165574565057636212286638235)
    ·
      refine ⟨248361847586454318429957353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165574565057636212286638235 248361847586454318429957353)
      ·
        refine ⟨186271385689840738822468015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248361847586454318429957353 186271385689840738822468015)
        ·
          refine ⟨279407078534761108233702023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186271385689840738822468015 279407078534761108233702023)
          ·
            refine ⟨419110617802141662350553035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279407078534761108233702023 419110617802141662350553035)
            ·
              refine ⟨628665926703212493525829553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419110617802141662350553035 628665926703212493525829553)
              ·
                refine ⟨471499445027409370144372165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628665926703212493525829553 471499445027409370144372165)
                ·
                  refine ⟨88406145942639256902069781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471499445027409370144372165 88406145942639256902069781)
                  ·
                    refine ⟨4144038091061215167284521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88406145942639256902069781 4144038091061215167284521)
                    ·
                      refine ⟨3108028568295911375463391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144038091061215167284521 3108028568295911375463391)
                      ·
                        rfl

theorem cell23_6052864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_6052864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052864 prefixEnd_6052864 := by exact prefixLift 6052864
  have htrace : WordTrace (prefixWord ++ tailWord_6052864) baseStart_6052864 baseEnd_6052864 := by
    simpa [prefixWord, tailWord_6052864, baseEnd_6052864] using wordTrace_append hprefix tailTrace_6052864
  have hstable : (prefixWord ++ tailWord_6052864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052864).length < 2 ^ (prefixWord ++ tailWord_6052864).sum := by decide
  have hdescent : baseEnd_6052864 < baseStart_6052864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052875 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 1, 1, 3]
def baseStart_6052875 : Nat := 118140960795 + 6052875 * 2 ^ 59
def prefixEnd_6052875 : Nat := 4983230072969 + 3 ^ 40 * 6052875 * 2
def baseEnd_6052875 : Nat := 3108034216583110832425841

theorem tailTrace_6052875 : CollatzResearch.WordTrace tailWord_6052875 prefixEnd_6052875 3108034216583110832425841 := by
  unfold tailWord_6052875
  simp only [CollatzResearch.WordTrace]
  refine ⟨220766487946475098594168079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147177658630983399062778719 220766487946475098594168079)
  ·
    refine ⟨331149731919712647891252119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220766487946475098594168079 331149731919712647891252119)
    ·
      refine ⟨496724597879568971836878179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331149731919712647891252119 496724597879568971836878179)
      ·
        refine ⟨745086896819353457755317269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496724597879568971836878179 745086896819353457755317269)
        ·
          refine ⟨34925948288407193332280497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 745086896819353457755317269 34925948288407193332280497)
          ·
            refine ⟨26194461216305394999210373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34925948288407193332280497 26194461216305394999210373)
            ·
              refine ⟨4911461478057261562351945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26194461216305394999210373 4911461478057261562351945)
              ·
                refine ⟨3683596108542946171763959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4911461478057261562351945 3683596108542946171763959)
                ·
                  refine ⟨5525394162814419257645939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683596108542946171763959 5525394162814419257645939)
                  ·
                    refine ⟨8288091244221628886468909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525394162814419257645939 8288091244221628886468909)
                    ·
                      refine ⟨3108034216583110832425841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288091244221628886468909 3108034216583110832425841)
                      ·
                        rfl

theorem cell23_6052875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 1, 3].length) (baseStart_6052875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052875 prefixEnd_6052875 := by exact prefixLift 6052875
  have htrace : WordTrace (prefixWord ++ tailWord_6052875) baseStart_6052875 baseEnd_6052875 := by
    simpa [prefixWord, tailWord_6052875, baseEnd_6052875] using wordTrace_append hprefix tailTrace_6052875
  have hstable : (prefixWord ++ tailWord_6052875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052875).length < 2 ^ (prefixWord ++ tailWord_6052875).sum := by decide
  have hdescent : baseEnd_6052875 < baseStart_6052875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_6052881 : Nat := 118140960795 + 6052881 * 2 ^ 59
def prefixEnd_6052881 : Nat := 4983230072969 + 3 ^ 40 * 6052881 * 2
def baseEnd_6052881 : Nat := 3108037297467037808950813

theorem tailTrace_6052881 : CollatzResearch.WordTrace tailWord_6052881 prefixEnd_6052881 3108037297467037808950813 := by
  unfold tailWord_6052881
  simp only [CollatzResearch.WordTrace]
  refine ⟨220766706784453361618886497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147177804522968907745924331 220766706784453361618886497)
  ·
    refine ⟨165575030088340021214164873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220766706784453361618886497 165575030088340021214164873)
    ·
      refine ⟨124181272566255015910623655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165575030088340021214164873 124181272566255015910623655)
      ·
        refine ⟨186271908849382523865935483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124181272566255015910623655 186271908849382523865935483)
        ·
          refine ⟨279407863274073785798903225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186271908849382523865935483 279407863274073785798903225)
          ·
            refine ⟨209555897455555339349177419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279407863274073785798903225 209555897455555339349177419)
            ·
              refine ⟨314333846183333009023766129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209555897455555339349177419 314333846183333009023766129)
              ·
                refine ⟨235750384637499756767824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314333846183333009023766129 235750384637499756767824597)
                ·
                  refine ⟨5525399639941400549245889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235750384637499756767824597 5525399639941400549245889)
                  ·
                    refine ⟨4144049729956050411934417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525399639941400549245889 4144049729956050411934417)
                    ·
                      refine ⟨3108037297467037808950813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144049729956050411934417 3108037297467037808950813)
                      ·
                        rfl

theorem cell23_6052881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_6052881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052881 prefixEnd_6052881 := by exact prefixLift 6052881
  have htrace : WordTrace (prefixWord ++ tailWord_6052881) baseStart_6052881 baseEnd_6052881 := by
    simpa [prefixWord, tailWord_6052881, baseEnd_6052881] using wordTrace_append hprefix tailTrace_6052881
  have hstable : (prefixWord ++ tailWord_6052881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052881).length < 2 ^ (prefixWord ++ tailWord_6052881).sum := by decide
  have hdescent : baseEnd_6052881 < baseStart_6052881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052898 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6052898 : Nat := 118140960795 + 6052898 * 2 ^ 59
def prefixEnd_6052898 : Nat := 4983230072969 + 3 ^ 40 * 6052898 * 2
def baseEnd_6052898 : Nat := 3108046026638164242438235

theorem tailTrace_6052898 : CollatzResearch.WordTrace tailWord_6052898 prefixEnd_6052898 3108046026638164242438235 := by
  unfold tailWord_6052898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55191831706347943380563837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147178217883594515681503565 55191831706347943380563837)
  ·
    refine ⟨20696936889880478767711439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55191831706347943380563837 20696936889880478767711439)
    ·
      refine ⟨31045405334820718151567159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696936889880478767711439 31045405334820718151567159)
      ·
        refine ⟨46568108002231077227350739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31045405334820718151567159 46568108002231077227350739)
        ·
          refine ⟨69852162003346615841026109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46568108002231077227350739 69852162003346615841026109)
          ·
            refine ⟨26194560751254980940384791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69852162003346615841026109 26194560751254980940384791)
            ·
              refine ⟨39291841126882471410577187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26194560751254980940384791 39291841126882471410577187)
              ·
                refine ⟨58937761690323707115865781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39291841126882471410577187 58937761690323707115865781)
                ·
                  refine ⟨5525415158467847542112417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58937761690323707115865781 5525415158467847542112417)
                  ·
                    refine ⟨4144061368850885656584313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525415158467847542112417 4144061368850885656584313)
                    ·
                      refine ⟨3108046026638164242438235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144061368850885656584313 3108046026638164242438235)
                      ·
                        rfl

theorem cell23_6052898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6052898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052898 prefixEnd_6052898 := by exact prefixLift 6052898
  have htrace : WordTrace (prefixWord ++ tailWord_6052898) baseStart_6052898 baseEnd_6052898 := by
    simpa [prefixWord, tailWord_6052898, baseEnd_6052898] using wordTrace_append hprefix tailTrace_6052898
  have hstable : (prefixWord ++ tailWord_6052898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052898).length < 2 ^ (prefixWord ++ tailWord_6052898).sum := by decide
  have hdescent : baseEnd_6052898 < baseStart_6052898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052901 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_6052901 : Nat := 118140960795 + 6052901 * 2 ^ 59
def prefixEnd_6052901 : Nat := 4983230072969 + 3 ^ 40 * 6052901 * 2
def baseEnd_6052901 : Nat := 3108047567080127730700721

theorem tailTrace_6052901 : CollatzResearch.WordTrace tailWord_6052901 prefixEnd_6052901 3108047567080127730700721 := by
  unfold tailWord_6052901
  simp only [CollatzResearch.WordTrace]
  refine ⟨220767436244380905034614557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147178290829587270023076371 220767436244380905034614557)
  ·
    refine ⟨82787788591642839387980459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220767436244380905034614557 82787788591642839387980459)
    ·
      refine ⟨124181682887464259081970689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82787788591642839387980459 124181682887464259081970689)
      ·
        refine ⟨93136262165598194311478017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124181682887464259081970689 93136262165598194311478017)
        ·
          refine ⟨69852196624198645733608513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93136262165598194311478017 69852196624198645733608513)
          ·
            refine ⟨52389147468148984300206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69852196624198645733608513 52389147468148984300206385)
            ·
              refine ⟨39291860601111738225154789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52389147468148984300206385 39291860601111738225154789)
              ·
                refine ⟨7367223862708450917216523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39291860601111738225154789 7367223862708450917216523)
                ·
                  refine ⟨11050835794062676375824785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7367223862708450917216523 11050835794062676375824785)
                  ·
                    refine ⟨8288126845547007281868589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11050835794062676375824785 8288126845547007281868589)
                    ·
                      refine ⟨3108047567080127730700721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288126845547007281868589 3108047567080127730700721)
                      ·
                        rfl

theorem cell23_6052901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_6052901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052901 prefixEnd_6052901 := by exact prefixLift 6052901
  have htrace : WordTrace (prefixWord ++ tailWord_6052901) baseStart_6052901 baseEnd_6052901 := by
    simpa [prefixWord, tailWord_6052901, baseEnd_6052901] using wordTrace_append hprefix tailTrace_6052901
  have hstable : (prefixWord ++ tailWord_6052901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052901).length < 2 ^ (prefixWord ++ tailWord_6052901).sum := by decide
  have hdescent : baseEnd_6052901 < baseStart_6052901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052931 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 3]
def baseStart_6052931 : Nat := 118140960795 + 6052931 * 2 ^ 59
def prefixEnd_6052931 : Nat := 4983230072969 + 3 ^ 40 * 6052931 * 2
def baseEnd_6052931 : Nat := 3108062971499762613325583

theorem tailTrace_6052931 : CollatzResearch.WordTrace tailWord_6052931 prefixEnd_6052931 3108062971499762613325583 := by
  unfold tailWord_6052931
  simp only [CollatzResearch.WordTrace]
  refine ⟨220768530434272220158206647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147179020289514813438804431 220768530434272220158206647)
  ·
    refine ⟨331152795651408330237309971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220768530434272220158206647 331152795651408330237309971)
    ·
      refine ⟨496729193477112495355964957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331152795651408330237309971 496729193477112495355964957)
      ·
        refine ⟨186273447553917185758486859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496729193477112495355964957 186273447553917185758486859)
        ·
          refine ⟨279410171330875778637730289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186273447553917185758486859 279410171330875778637730289)
          ·
            refine ⟨209557628498156833978297717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279410171330875778637730289 209557628498156833978297717)
            ·
              refine ⟨19646027671702203185465411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209557628498156833978297717 19646027671702203185465411)
              ·
                refine ⟨29469041507553304778198117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19646027671702203185465411 29469041507553304778198117)
                ·
                  refine ⟨5525445282666244645912147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29469041507553304778198117 5525445282666244645912147)
                  ·
                    refine ⟨8288167923999366968868221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525445282666244645912147 8288167923999366968868221)
                    ·
                      refine ⟨3108062971499762613325583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288167923999366968868221 3108062971499762613325583)
                      ·
                        rfl

theorem cell23_6052931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_6052931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052931 prefixEnd_6052931 := by exact prefixLift 6052931
  have htrace : WordTrace (prefixWord ++ tailWord_6052931) baseStart_6052931 baseEnd_6052931 := by
    simpa [prefixWord, tailWord_6052931, baseEnd_6052931] using wordTrace_append hprefix tailTrace_6052931
  have hstable : (prefixWord ++ tailWord_6052931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052931).length < 2 ^ (prefixWord ++ tailWord_6052931).sum := by decide
  have hdescent : baseEnd_6052931 < baseStart_6052931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052948 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_6052948 : Nat := 118140960795 + 6052948 * 2 ^ 59
def prefixEnd_6052948 : Nat := 4983230072969 + 3 ^ 40 * 6052948 * 2
def baseEnd_6052948 : Nat := 3108071700670889046813005

theorem tailTrace_6052948 : CollatzResearch.WordTrace tailWord_6052948 prefixEnd_6052948 3108071700670889046813005 := by
  unfold tailWord_6052948
  simp only [CollatzResearch.WordTrace]
  refine ⟨110384575237605316030787749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147179433650140421374383665 110384575237605316030787749)
  ·
    refine ⟨20697107857050996755772703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110384575237605316030787749 20697107857050996755772703)
    ·
      refine ⟨31045661785576495133659055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20697107857050996755772703 31045661785576495133659055)
      ·
        refine ⟨46568492678364742700488583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31045661785576495133659055 46568492678364742700488583)
        ·
          refine ⟨69852739017547114050732875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46568492678364742700488583 69852739017547114050732875)
          ·
            refine ⟨104779108526320671076099313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69852739017547114050732875 104779108526320671076099313)
            ·
              refine ⟨78584331394740503307074485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104779108526320671076099313 78584331394740503307074485)
              ·
                refine ⟨7367281068256922185038233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78584331394740503307074485 7367281068256922185038233)
                ·
                  refine ⟨5525460801192691638778675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367281068256922185038233 5525460801192691638778675)
                  ·
                    refine ⟨8288191201789037458168013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525460801192691638778675 8288191201789037458168013)
                    ·
                      refine ⟨3108071700670889046813005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288191201789037458168013 3108071700670889046813005)
                      ·
                        rfl

theorem cell23_6052948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_6052948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052948 prefixEnd_6052948 := by exact prefixLift 6052948
  have htrace : WordTrace (prefixWord ++ tailWord_6052948) baseStart_6052948 baseEnd_6052948 := by
    simpa [prefixWord, tailWord_6052948, baseEnd_6052948] using wordTrace_append hprefix tailTrace_6052948
  have hstable : (prefixWord ++ tailWord_6052948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052948).length < 2 ^ (prefixWord ++ tailWord_6052948).sum := by decide
  have hdescent : baseEnd_6052948 < baseStart_6052948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052984 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_6052984 : Nat := 118140960795 + 6052984 * 2 ^ 59
def prefixEnd_6052984 : Nat := 4983230072969 + 3 ^ 40 * 6052984 * 2
def baseEnd_6052984 : Nat := 3108090185974450905962839

theorem tailTrace_6052984 : CollatzResearch.WordTrace tailWord_6052984 prefixEnd_6052984 3108090185974450905962839 := by
  unfold tailWord_6052984
  simp only [CollatzResearch.WordTrace]
  refine ⟨110385231751540105104943003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147180309002053473473257337 110385231751540105104943003)
  ·
    refine ⟨165577847627310157657414505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110385231751540105104943003 165577847627310157657414505)
    ·
      refine ⟨124183385720482618243060879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165577847627310157657414505 124183385720482618243060879)
      ·
        refine ⟨186275078580723927364591319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124183385720482618243060879 186275078580723927364591319)
        ·
          refine ⟨279412617871085891046886979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186275078580723927364591319 279412617871085891046886979)
          ·
            refine ⟨419118926806628836570330469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279412617871085891046886979 419118926806628836570330469)
            ·
              refine ⟨78584798776242906856936963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419118926806628836570330469 78584798776242906856936963)
              ·
                refine ⟨117877198164364360285405445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78584798776242906856936963 117877198164364360285405445)
                ·
                  refine ⟨22101974655818317553513521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117877198164364360285405445 22101974655818317553513521)
                  ·
                    refine ⟨16576480991863738165135141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22101974655818317553513521 16576480991863738165135141)
                    ·
                      refine ⟨3108090185974450905962839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16576480991863738165135141 3108090185974450905962839)
                      ·
                        rfl

theorem cell23_6052984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_6052984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052984 prefixEnd_6052984 := by exact prefixLift 6052984
  have htrace : WordTrace (prefixWord ++ tailWord_6052984) baseStart_6052984 baseEnd_6052984 := by
    simpa [prefixWord, tailWord_6052984, baseEnd_6052984] using wordTrace_append hprefix tailTrace_6052984
  have hstable : (prefixWord ++ tailWord_6052984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052984).length < 2 ^ (prefixWord ++ tailWord_6052984).sum := by decide
  have hdescent : baseEnd_6052984 < baseStart_6052984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6052988 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_6052988 : Nat := 118140960795 + 6052988 * 2 ^ 59
def prefixEnd_6052988 : Nat := 4983230072969 + 3 ^ 40 * 6052988 * 2
def baseEnd_6052988 : Nat := 3108092239897068890312821

theorem tailTrace_6052988 : CollatzResearch.WordTrace tailWord_6052988 prefixEnd_6052988 3108092239897068890312821 := by
  unfold tailWord_6052988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110385304697532859446515809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147180406263377145928687745 110385304697532859446515809)
  ·
    refine ⟨82788978523149644584886857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110385304697532859446515809 82788978523149644584886857)
    ·
      refine ⟨62091733892362233438665143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82788978523149644584886857 62091733892362233438665143)
      ·
        refine ⟨93137600838543350157997715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62091733892362233438665143 93137600838543350157997715)
        ·
          refine ⟨139706401257815025236996573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93137600838543350157997715 139706401257815025236996573)
          ·
            refine ⟨52389900471680634463873715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139706401257815025236996573 52389900471680634463873715)
            ·
              refine ⟨78584850707520951695810573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52389900471680634463873715 78584850707520951695810573)
              ·
                refine ⟨29469319015320356885928965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78584850707520951695810573 29469319015320356885928965)
                ·
                  refine ⟨5525497315372566916111681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29469319015320356885928965 5525497315372566916111681)
                  ·
                    refine ⟨4144122986529425187083761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525497315372566916111681 4144122986529425187083761)
                    ·
                      refine ⟨3108092239897068890312821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144122986529425187083761 3108092239897068890312821)
                      ·
                        rfl

theorem cell23_6052988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_6052988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6052988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6052988 prefixEnd_6052988 := by exact prefixLift 6052988
  have htrace : WordTrace (prefixWord ++ tailWord_6052988) baseStart_6052988 baseEnd_6052988 := by
    simpa [prefixWord, tailWord_6052988, baseEnd_6052988] using wordTrace_append hprefix tailTrace_6052988
  have hstable : (prefixWord ++ tailWord_6052988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6052988).length < 2 ^ (prefixWord ++ tailWord_6052988).sum := by decide
  have hdescent : baseEnd_6052988 < baseStart_6052988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6052988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053062 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_6053062 : Nat := 118140960795 + 6053062 * 2 ^ 59
def prefixEnd_6053062 : Nat := 4983230072969 + 3 ^ 40 * 6053062 * 2
def baseEnd_6053062 : Nat := 345347804162833511198609

theorem tailTrace_6053062 : CollatzResearch.WordTrace tailWord_6053062 prefixEnd_6053062 345347804162833511198609 := by
  unfold tailWord_6053062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899165887399925922850795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147182205597865086354150293 6899165887399925922850795)
  ·
    refine ⟨10348748831099888884276193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899165887399925922850795 10348748831099888884276193)
    ·
      refine ⟨7761561623324916663207145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10348748831099888884276193 7761561623324916663207145)
      ·
        refine ⟨5821171217493687497405359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7761561623324916663207145 5821171217493687497405359)
        ·
          refine ⟨8731756826240531246108039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5821171217493687497405359 8731756826240531246108039)
          ·
            refine ⟨13097635239360796869162059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731756826240531246108039 13097635239360796869162059)
            ·
              refine ⟨19646452859041195303743089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097635239360796869162059 19646452859041195303743089)
              ·
                refine ⟨14734839644280896477807317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19646452859041195303743089 14734839644280896477807317)
                ·
                  refine ⟨345347804162833511198609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14734839644280896477807317 345347804162833511198609)
                  ·
                    rfl

theorem cell23_6053062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_6053062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053062 prefixEnd_6053062 := by exact prefixLift 6053062
  have htrace : WordTrace (prefixWord ++ tailWord_6053062) baseStart_6053062 baseEnd_6053062 := by
    simpa [prefixWord, tailWord_6053062, baseEnd_6053062] using wordTrace_append hprefix tailTrace_6053062
  have hstable : (prefixWord ++ tailWord_6053062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053062).length < 2 ^ (prefixWord ++ tailWord_6053062).sum := by decide
  have hdescent : baseEnd_6053062 < baseStart_6053062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053148 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6053148 : Nat := 118140960795 + 6053148 * 2 ^ 59
def prefixEnd_6053148 : Nat := 4983230072969 + 3 ^ 40 * 6053148 * 2
def baseEnd_6053148 : Nat := 1036058132267262754770695

theorem tailTrace_6053148 : CollatzResearch.WordTrace tailWord_6053148 prefixEnd_6053148 1036058132267262754770695 := by
  unfold tailWord_6053148
  simp only [CollatzResearch.WordTrace]
  refine ⟨110388222537243033109428049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147184296716324044145904065 110388222537243033109428049)
  ·
    refine ⟨82791166902932274832071037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110388222537243033109428049 82791166902932274832071037)
    ·
      refine ⟨31046687588599603062026639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82791166902932274832071037 31046687588599603062026639)
      ·
        refine ⟨46570031382899404593039959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31046687588599603062026639 46570031382899404593039959)
        ·
          refine ⟨69855047074349106889559939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46570031382899404593039959 69855047074349106889559939)
          ·
            refine ⟨104782570611523660334339909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69855047074349106889559939 104782570611523660334339909)
            ·
              refine ⟨19646731989660686312688733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104782570611523660334339909 19646731989660686312688733)
              ·
                refine ⟨7367524496122757367258275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19646731989660686312688733 7367524496122757367258275)
                ·
                  refine ⟨11051286744184136050887413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7367524496122757367258275 11051286744184136050887413)
                  ·
                    refine ⟨1036058132267262754770695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11051286744184136050887413 1036058132267262754770695)
                    ·
                      rfl

theorem cell23_6053148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6053148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053148 prefixEnd_6053148 := by exact prefixLift 6053148
  have htrace : WordTrace (prefixWord ++ tailWord_6053148) baseStart_6053148 baseEnd_6053148 := by
    simpa [prefixWord, tailWord_6053148, baseEnd_6053148] using wordTrace_append hprefix tailTrace_6053148
  have hstable : (prefixWord ++ tailWord_6053148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053148).length < 2 ^ (prefixWord ++ tailWord_6053148).sum := by decide
  have hdescent : baseEnd_6053148 < baseStart_6053148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053155 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 2, 3, 2]
def baseStart_6053155 : Nat := 118140960795 + 6053155 * 2 ^ 59
def prefixEnd_6053155 : Nat := 4983230072969 + 3 ^ 40 * 6053155 * 2
def baseEnd_6053155 : Nat := 3108177991166369736924553

theorem tailTrace_6053155 : CollatzResearch.WordTrace tailWord_6053155 prefixEnd_6053155 3108177991166369736924553 := by
  unfold tailWord_6053155
  simp only [CollatzResearch.WordTrace]
  refine ⟨220776700385460706414360919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147184466923640470942907279 220776700385460706414360919)
  ·
    refine ⟨331165050578191059621541379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220776700385460706414360919 331165050578191059621541379)
    ·
      refine ⟨496747575867286589432312069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331165050578191059621541379 496747575867286589432312069)
      ·
        refine ⟨93140170475116235518558513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 496747575867286589432312069 93140170475116235518558513)
        ·
          refine ⟨69855127856337176638918885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93140170475116235518558513 69855127856337176638918885)
          ·
            refine ⟨13097836473063220619797291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69855127856337176638918885 13097836473063220619797291)
            ·
              refine ⟨19646754709594830929695937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097836473063220619797291 19646754709594830929695937)
              ·
                refine ⟨14735066032196123197271953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19646754709594830929695937 14735066032196123197271953)
                ·
                  refine ⟨11051299524147092397953965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735066032196123197271953 11051299524147092397953965)
                  ·
                    refine ⟨4144237321555159649232737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11051299524147092397953965 4144237321555159649232737)
                    ·
                      refine ⟨3108177991166369736924553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144237321555159649232737 3108177991166369736924553)
                      ·
                        rfl

theorem cell23_6053155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_6053155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053155 prefixEnd_6053155 := by exact prefixLift 6053155
  have htrace : WordTrace (prefixWord ++ tailWord_6053155) baseStart_6053155 baseEnd_6053155 := by
    simpa [prefixWord, tailWord_6053155, baseEnd_6053155] using wordTrace_append hprefix tailTrace_6053155
  have hstable : (prefixWord ++ tailWord_6053155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053155).length < 2 ^ (prefixWord ++ tailWord_6053155).sum := by decide
  have hdescent : baseEnd_6053155 < baseStart_6053155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053162 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6053162 : Nat := 118140960795 + 6053162 * 2 ^ 59
def prefixEnd_6053162 : Nat := 4983230072969 + 3 ^ 40 * 6053162 * 2
def baseEnd_6053162 : Nat := 3108181585530951209537021

theorem tailTrace_6053162 : CollatzResearch.WordTrace tailWord_6053162 prefixEnd_6053162 3108181585530951209537021 := by
  unfold tailWord_6053162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55194238924108836652466435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147184637130956897739910493 55194238924108836652466435)
  ·
    refine ⟨82791358386163254978699653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55194238924108836652466435 82791358386163254978699653)
    ·
      refine ⟨15523379697405610308506185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82791358386163254978699653 15523379697405610308506185)
      ·
        refine ⟨11642534773054207731379639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15523379697405610308506185 11642534773054207731379639)
        ·
          refine ⟨17463802159581311597069459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642534773054207731379639 17463802159581311597069459)
          ·
            refine ⟨26195703239371967395604189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17463802159581311597069459 26195703239371967395604189)
            ·
              refine ⟨9823388714764487773351571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26195703239371967395604189 9823388714764487773351571)
              ·
                refine ⟨14735083072146731660027357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823388714764487773351571 14735083072146731660027357)
                ·
                  refine ⟨5525656152055024372510259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14735083072146731660027357 5525656152055024372510259)
                  ·
                    refine ⟨8288484228082536558765389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525656152055024372510259 8288484228082536558765389)
                    ·
                      refine ⟨3108181585530951209537021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288484228082536558765389 3108181585530951209537021)
                      ·
                        rfl

theorem cell23_6053162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6053162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053162 prefixEnd_6053162 := by exact prefixLift 6053162
  have htrace : WordTrace (prefixWord ++ tailWord_6053162) baseStart_6053162 baseEnd_6053162 := by
    simpa [prefixWord, tailWord_6053162, baseEnd_6053162] using wordTrace_append hprefix tailTrace_6053162
  have hstable : (prefixWord ++ tailWord_6053162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053162).length < 2 ^ (prefixWord ++ tailWord_6053162).sum := by decide
  have hdescent : baseEnd_6053162 < baseStart_6053162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053185 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6053185 : Nat := 118140960795 + 6053185 * 2 ^ 59
def prefixEnd_6053185 : Nat := 4983230072969 + 3 ^ 40 * 6053185 * 2
def baseEnd_6053185 : Nat := 3108193395586004619549415

theorem tailTrace_6053185 : CollatzResearch.WordTrace tailWord_6053185 prefixEnd_6053185 3108193395586004619549415 := by
  unfold tailWord_6053185
  simp only [CollatzResearch.WordTrace]
  refine ⟨220777794575352021537953009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147185196383568014358635339 220777794575352021537953009)
  ·
    refine ⟨165583345931514016153464757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220777794575352021537953009 165583345931514016153464757)
    ·
      refine ⟨15523438681079439014387321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165583345931514016153464757 15523438681079439014387321)
      ·
        refine ⟨11642579010809579260790491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15523438681079439014387321 11642579010809579260790491)
        ·
          refine ⟨17463868516214368891185737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642579010809579260790491 17463868516214368891185737)
          ·
            refine ⟨13097901387160776668389303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17463868516214368891185737 13097901387160776668389303)
            ·
              refine ⟨19646852080741165002583955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097901387160776668389303 19646852080741165002583955)
              ·
                refine ⟨29470278121111747503875933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19646852080741165002583955 29470278121111747503875933)
                ·
                  refine ⟨11051354295416905313953475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29470278121111747503875933 11051354295416905313953475)
                  ·
                    refine ⟨16577031443125357970930213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11051354295416905313953475 16577031443125357970930213)
                    ·
                      refine ⟨3108193395586004619549415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16577031443125357970930213 3108193395586004619549415)
                      ·
                        rfl

theorem cell23_6053185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6053185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053185 prefixEnd_6053185 := by exact prefixLift 6053185
  have htrace : WordTrace (prefixWord ++ tailWord_6053185) baseStart_6053185 baseEnd_6053185 := by
    simpa [prefixWord, tailWord_6053185, baseEnd_6053185] using wordTrace_append hprefix tailTrace_6053185
  have hstable : (prefixWord ++ tailWord_6053185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053185).length < 2 ^ (prefixWord ++ tailWord_6053185).sum := by decide
  have hdescent : baseEnd_6053185 < baseStart_6053185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053191 : List Nat := [1, 1, 4, 1, 2, 3, 2, 9]
def baseStart_6053191 : Nat := 118140960795 + 6053191 * 2 ^ 59
def prefixEnd_6053191 : Nat := 4983230072969 + 3 ^ 40 * 6053191 * 2
def baseEnd_6053191 : Nat := 115118388017404873928681

theorem tailTrace_6053191 : CollatzResearch.WordTrace tailWord_6053191 prefixEnd_6053191 115118388017404873928681 := by
  unfold tailWord_6053191
  simp only [CollatzResearch.WordTrace]
  refine ⟨220778013413330284562671427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147185342275553523041780951 220778013413330284562671427)
  ·
    refine ⟨331167020119995426844007141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220778013413330284562671427 331167020119995426844007141)
    ·
      refine ⟨62093816272499142533251339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331167020119995426844007141 62093816272499142533251339)
      ·
        refine ⟨93140724408748713799877009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62093816272499142533251339 93140724408748713799877009)
        ·
          refine ⟨69855543306561535349907757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93140724408748713799877009 69855543306561535349907757)
          ·
            refine ⟨26195828739960575756215409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69855543306561535349907757 26195828739960575756215409)
            ·
              refine ⟨19646871554970431817161557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26195828739960575756215409 19646871554970431817161557)
              ·
                refine ⟨115118388017404873928681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19646871554970431817161557 115118388017404873928681)
                ·
                  rfl

theorem cell23_6053191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 9].length) (baseStart_6053191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053191 prefixEnd_6053191 := by exact prefixLift 6053191
  have htrace : WordTrace (prefixWord ++ tailWord_6053191) baseStart_6053191 baseEnd_6053191 := by
    simpa [prefixWord, tailWord_6053191, baseEnd_6053191] using wordTrace_append hprefix tailTrace_6053191
  have hstable : (prefixWord ++ tailWord_6053191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053191).length < 2 ^ (prefixWord ++ tailWord_6053191).sum := by decide
  have hdescent : baseEnd_6053191 < baseStart_6053191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053198 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_6053198 : Nat := 118140960795 + 6053198 * 2 ^ 59
def prefixEnd_6053198 : Nat := 4983230072969 + 3 ^ 40 * 6053198 * 2
def baseEnd_6053198 : Nat := 3108200070834513068686855

theorem tailTrace_6053198 : CollatzResearch.WordTrace tailWord_6053198 prefixEnd_6053198 3108200070834513068686855 := by
  unfold tailWord_6053198
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597283590538115594772031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147185512482869949838784165 27597283590538115594772031)
  ·
    refine ⟨41395925385807173392158047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27597283590538115594772031 41395925385807173392158047)
    ·
      refine ⟨62093888078710760088237071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41395925385807173392158047 62093888078710760088237071)
      ·
        refine ⟨93140832118066140132355607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62093888078710760088237071 93140832118066140132355607)
        ·
          refine ⟨139711248177099210198533411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93140832118066140132355607 139711248177099210198533411)
          ·
            refine ⟨209566872265648815297800117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139711248177099210198533411 209566872265648815297800117)
            ·
              refine ⟨19646894274904576434168761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209566872265648815297800117 19646894274904576434168761)
              ·
                refine ⟨14735170706178432325626571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19646894274904576434168761 14735170706178432325626571)
                ·
                  refine ⟨22102756059267648488439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14735170706178432325626571 22102756059267648488439857)
                  ·
                    refine ⟨16577067044450736366329893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22102756059267648488439857 16577067044450736366329893)
                    ·
                      refine ⟨3108200070834513068686855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16577067044450736366329893 3108200070834513068686855)
                      ·
                        rfl

theorem cell23_6053198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_6053198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053198 prefixEnd_6053198 := by exact prefixLift 6053198
  have htrace : WordTrace (prefixWord ++ tailWord_6053198) baseStart_6053198 baseEnd_6053198 := by
    simpa [prefixWord, tailWord_6053198, baseEnd_6053198] using wordTrace_append hprefix tailTrace_6053198
  have hstable : (prefixWord ++ tailWord_6053198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053198).length < 2 ^ (prefixWord ++ tailWord_6053198).sum := by decide
  have hdescent : baseEnd_6053198 < baseStart_6053198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053205 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6053205 : Nat := 118140960795 + 6053205 * 2 ^ 59
def prefixEnd_6053205 : Nat := 4983230072969 + 3 ^ 40 * 6053205 * 2
def baseEnd_6053205 : Nat := 3108203665199094541299323

theorem tailTrace_6053205 : CollatzResearch.WordTrace tailWord_6053205 prefixEnd_6053205 3108203665199094541299323 := by
  unfold tailWord_6053205
  simp only [CollatzResearch.WordTrace]
  refine ⟨220778524035279564953681069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147185682690186376635787379 220778524035279564953681069)
  ·
    refine ⟨82791946513229836857630401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220778524035279564953681069 82791946513229836857630401)
    ·
      refine ⟨62093959884922377643222801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82791946513229836857630401 62093959884922377643222801)
      ·
        refine ⟨46570469913691783232417101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62093959884922377643222801 46570469913691783232417101)
        ·
          refine ⟨17463926217634418712156413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46570469913691783232417101 17463926217634418712156413)
          ·
            refine ⟨6548972331612907017058655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17463926217634418712156413 6548972331612907017058655)
            ·
              refine ⟨9823458497419360525587983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548972331612907017058655 9823458497419360525587983)
              ·
                refine ⟨14735187746129040788381975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823458497419360525587983 14735187746129040788381975)
                ·
                  refine ⟨22102781619193561182572963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14735187746129040788381975 22102781619193561182572963)
                  ·
                    refine ⟨33154172428790341773859445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22102781619193561182572963 33154172428790341773859445)
                    ·
                      refine ⟨3108203665199094541299323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33154172428790341773859445 3108203665199094541299323)
                      ·
                        rfl

theorem cell23_6053205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6053205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053205 prefixEnd_6053205 := by exact prefixLift 6053205
  have htrace : WordTrace (prefixWord ++ tailWord_6053205) baseStart_6053205 baseEnd_6053205 := by
    simpa [prefixWord, tailWord_6053205, baseEnd_6053205] using wordTrace_append hprefix tailTrace_6053205
  have hstable : (prefixWord ++ tailWord_6053205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053205).length < 2 ^ (prefixWord ++ tailWord_6053205).sum := by decide
  have hdescent : baseEnd_6053205 < baseStart_6053205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053213 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6053213 : Nat := 118140960795 + 6053213 * 2 ^ 59
def prefixEnd_6053213 : Nat := 4983230072969 + 3 ^ 40 * 6053213 * 2
def baseEnd_6053213 : Nat := 3108207773044330509999287

theorem tailTrace_6053213 : CollatzResearch.WordTrace tailWord_6053213 prefixEnd_6053213 3108207773044330509999287 := by
  unfold tailWord_6053213
  simp only [CollatzResearch.WordTrace]
  refine ⟨220778815819250582319972293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147185877212833721546648195 220778815819250582319972293)
  ·
    refine ⟨41396027966109484184994805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220778815819250582319972293 41396027966109484184994805)
    ·
      refine ⟨3880877621822764142343263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41396027966109484184994805 3880877621822764142343263)
      ·
        refine ⟨5821316432734146213514895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880877621822764142343263 5821316432734146213514895)
        ·
          refine ⟨8731974649101219320272343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5821316432734146213514895 8731974649101219320272343)
          ·
            refine ⟨13097961973651828980408515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731974649101219320272343 13097961973651828980408515)
            ·
              refine ⟨19646942960477743470612773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097961973651828980408515 19646942960477743470612773)
              ·
                refine ⟨3683801805089576900739895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19646942960477743470612773 3683801805089576900739895)
                ·
                  refine ⟨5525702707634365351109843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683801805089576900739895 5525702707634365351109843)
                  ·
                    refine ⟨8288554061451548026664765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525702707634365351109843 8288554061451548026664765)
                    ·
                      refine ⟨3108207773044330509999287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288554061451548026664765 3108207773044330509999287)
                      ·
                        rfl

theorem cell23_6053213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6053213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053213 prefixEnd_6053213 := by exact prefixLift 6053213
  have htrace : WordTrace (prefixWord ++ tailWord_6053213) baseStart_6053213 baseEnd_6053213 := by
    simpa [prefixWord, tailWord_6053213, baseEnd_6053213] using wordTrace_append hprefix tailTrace_6053213
  have hstable : (prefixWord ++ tailWord_6053213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053213).length < 2 ^ (prefixWord ++ tailWord_6053213).sum := by decide
  have hdescent : baseEnd_6053213 < baseStart_6053213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053219 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 1, 2, 2]
def baseStart_6053219 : Nat := 118140960795 + 6053219 * 2 ^ 59
def prefixEnd_6053219 : Nat := 4983230072969 + 3 ^ 40 * 6053219 * 2
def baseEnd_6053219 : Nat := 3108210853928257486524259

theorem tailTrace_6053219 : CollatzResearch.WordTrace tailWord_6053219 prefixEnd_6053219 3108210853928257486524259 := by
  unfold tailWord_6053219
  simp only [CollatzResearch.WordTrace]
  refine ⟨220779034657228845344690711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147186023104819230229793807 220779034657228845344690711)
  ·
    refine ⟨331168551985843268017036067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220779034657228845344690711 331168551985843268017036067)
    ·
      refine ⟨496752827978764902025554101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331168551985843268017036067 496752827978764902025554101)
      ·
        refine ⟨46570577623009209564895697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 496752827978764902025554101 46570577623009209564895697)
        ·
          refine ⟨34927933217256907173671773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46570577623009209564895697 34927933217256907173671773)
          ·
            refine ⟨13097974956471340190126915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34927933217256907173671773 13097974956471340190126915)
            ·
              refine ⟨19646962434707010285190373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13097974956471340190126915 19646962434707010285190373)
              ·
                refine ⟨3683805456507564428473195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19646962434707010285190373 3683805456507564428473195)
                ·
                  refine ⟨5525708184761346642709793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683805456507564428473195 5525708184761346642709793)
                  ·
                    refine ⟨4144281138571009982032345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525708184761346642709793 4144281138571009982032345)
                    ·
                      refine ⟨3108210853928257486524259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144281138571009982032345 3108210853928257486524259)
                      ·
                        rfl

theorem cell23_6053219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_6053219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053219 prefixEnd_6053219 := by exact prefixLift 6053219
  have htrace : WordTrace (prefixWord ++ tailWord_6053219) baseStart_6053219 baseEnd_6053219 := by
    simpa [prefixWord, tailWord_6053219, baseEnd_6053219] using wordTrace_append hprefix tailTrace_6053219
  have hstable : (prefixWord ++ tailWord_6053219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053219).length < 2 ^ (prefixWord ++ tailWord_6053219).sum := by decide
  have hdescent : baseEnd_6053219 < baseStart_6053219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053221 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_6053221 : Nat := 118140960795 + 6053221 * 2 ^ 59
def prefixEnd_6053221 : Nat := 4983230072969 + 3 ^ 40 * 6053221 * 2
def baseEnd_6053221 : Nat := 1036070626963188826233083

theorem tailTrace_6053221 : CollatzResearch.WordTrace tailWord_6053221 prefixEnd_6053221 1036070626963188826233083 := by
  unfold tailWord_6053221
  simp only [CollatzResearch.WordTrace]
  refine ⟨220779107603221599686263517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147186071735481066457509011 220779107603221599686263517)
  ·
    refine ⟨82792165351208099882348819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220779107603221599686263517 82792165351208099882348819)
    ·
      refine ⟨124188248026812149823523229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82792165351208099882348819 124188248026812149823523229)
      ·
        refine ⟨46570593010054556183821211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124188248026812149823523229 46570593010054556183821211)
        ·
          refine ⟨69855889515081834275731817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46570593010054556183821211 69855889515081834275731817)
          ·
            refine ⟨52391917136311375706798863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69855889515081834275731817 52391917136311375706798863)
            ·
              refine ⟨78587875704467063560198295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52391917136311375706798863 78587875704467063560198295)
              ·
                refine ⟨117881813556700595340297443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78587875704467063560198295 117881813556700595340297443)
                ·
                  refine ⟨176822720335050893010446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117881813556700595340297443 176822720335050893010446165)
                  ·
                    refine ⟨1036070626963188826233083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 176822720335050893010446165 1036070626963188826233083)
                    ·
                      rfl

theorem cell23_6053221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_6053221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053221 prefixEnd_6053221 := by exact prefixLift 6053221
  have htrace : WordTrace (prefixWord ++ tailWord_6053221) baseStart_6053221 baseEnd_6053221 := by
    simpa [prefixWord, tailWord_6053221, baseEnd_6053221] using wordTrace_append hprefix tailTrace_6053221
  have hstable : (prefixWord ++ tailWord_6053221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053221).length < 2 ^ (prefixWord ++ tailWord_6053221).sum := by decide
  have hdescent : baseEnd_6053221 < baseStart_6053221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053245 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_6053245 : Nat := 118140960795 + 6053245 * 2 ^ 59
def prefixEnd_6053245 : Nat := 4983230072969 + 3 ^ 40 * 6053245 * 2
def baseEnd_6053245 : Nat := 3108224204425274384799139

theorem tailTrace_6053245 : CollatzResearch.WordTrace tailWord_6053245 prefixEnd_6053245 3108224204425274384799139 := by
  unfold tailWord_6053245
  simp only [CollatzResearch.WordTrace]
  refine ⟨220779982955134651785137189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147186655303423101190091459 220779982955134651785137189)
  ·
    refine ⟨41396246804087747209713223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220779982955134651785137189 41396246804087747209713223)
    ·
      refine ⟨62094370206131620814569835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41396246804087747209713223 62094370206131620814569835)
      ·
        refine ⟨93141555309197431221854753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62094370206131620814569835 93141555309197431221854753)
        ·
          refine ⟨69856166481898073416391065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93141555309197431221854753 69856166481898073416391065)
          ·
            refine ⟨52392124861423555062293299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69856166481898073416391065 52392124861423555062293299)
            ·
              refine ⟨78588187292135332593439949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52392124861423555062293299 78588187292135332593439949)
              ·
                refine ⟨29470570234550749722539981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78588187292135332593439949 29470570234550749722539981)
                ·
                  refine ⟨11051463837956531145952493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29470570234550749722539981 11051463837956531145952493)
                  ·
                    refine ⟨4144298939233699179732185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11051463837956531145952493 4144298939233699179732185)
                    ·
                      refine ⟨3108224204425274384799139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144298939233699179732185 3108224204425274384799139)
                      ·
                        rfl

theorem cell23_6053245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_6053245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053245 prefixEnd_6053245 := by exact prefixLift 6053245
  have htrace : WordTrace (prefixWord ++ tailWord_6053245) baseStart_6053245 baseEnd_6053245 := by
    simpa [prefixWord, tailWord_6053245, baseEnd_6053245] using wordTrace_append hprefix tailTrace_6053245
  have hstable : (prefixWord ++ tailWord_6053245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053245).length < 2 ^ (prefixWord ++ tailWord_6053245).sum := by decide
  have hdescent : baseEnd_6053245 < baseStart_6053245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053275 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 10, 2, 2]
def baseStart_6053275 : Nat := 118140960795 + 6053275 * 2 ^ 59
def prefixEnd_6053275 : Nat := 4983230072969 + 3 ^ 40 * 6053275 * 2
def baseEnd_6053275 : Nat := 3108239608844909267424001

theorem tailTrace_6053275 : CollatzResearch.WordTrace tailWord_6053275 prefixEnd_6053275 3108239608844909267424001 := by
  unfold tailWord_6053275
  simp only [CollatzResearch.WordTrace]
  refine ⟨220781077145025966908729279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147187384763350644605819519 220781077145025966908729279)
  ·
    refine ⟨331171615717538950363093919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220781077145025966908729279 331171615717538950363093919)
    ·
      refine ⟨496757423576308425544640879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331171615717538950363093919 496757423576308425544640879)
      ·
        refine ⟨745136135364462638316961319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496757423576308425544640879 745136135364462638316961319)
        ·
          refine ⟨1117704203046693957475441979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745136135364462638316961319 1117704203046693957475441979)
          ·
            refine ⟨1676556304570040936213162969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117704203046693957475441979 1676556304570040936213162969)
            ·
              refine ⟨1257417228427530702159872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676556304570040936213162969 1257417228427530702159872227)
              ·
                refine ⟨1886125842641296053239808341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257417228427530702159872227 1886125842641296053239808341)
                ·
                  refine ⟨5525759304613172030976001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1886125842641296053239808341 5525759304613172030976001)
                  ·
                    refine ⟨4144319478459879023232001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525759304613172030976001 4144319478459879023232001)
                    ·
                      refine ⟨3108239608844909267424001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144319478459879023232001 3108239608844909267424001)
                      ·
                        rfl

theorem cell23_6053275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2, 2].length) (baseStart_6053275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053275 prefixEnd_6053275 := by exact prefixLift 6053275
  have htrace : WordTrace (prefixWord ++ tailWord_6053275) baseStart_6053275 baseEnd_6053275 := by
    simpa [prefixWord, tailWord_6053275, baseEnd_6053275] using wordTrace_append hprefix tailTrace_6053275
  have hstable : (prefixWord ++ tailWord_6053275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053275).length < 2 ^ (prefixWord ++ tailWord_6053275).sum := by decide
  have hdescent : baseEnd_6053275 < baseStart_6053275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053292 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_6053292 : Nat := 118140960795 + 6053292 * 2 ^ 59
def prefixEnd_6053292 : Nat := 4983230072969 + 3 ^ 40 * 6053292 * 2
def baseEnd_6053292 : Nat := 3108248338016035700911423

theorem tailTrace_6053292 : CollatzResearch.WordTrace tailWord_6053292 prefixEnd_6053292 3108248338016035700911423 := by
  unfold tailWord_6053292
  simp only [CollatzResearch.WordTrace]
  refine ⟨110390848592982189406049065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147187798123976252541398753 110390848592982189406049065)
  ·
    refine ⟨82793136444736642054536799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110390848592982189406049065 82793136444736642054536799)
    ·
      refine ⟨124189704667104963081805199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82793136444736642054536799 124189704667104963081805199)
      ·
        refine ⟨186284557000657444622707799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124189704667104963081805199 186284557000657444622707799)
        ·
          refine ⟨279426835500986166934061699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186284557000657444622707799 279426835500986166934061699)
          ·
            refine ⟨419140253251479250401092549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279426835500986166934061699 419140253251479250401092549)
            ·
              refine ⟨78588797484652359450204853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419140253251479250401092549 78588797484652359450204853)
              ·
                refine ⟨7367699764186158698456705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78588797484652359450204853 7367699764186158698456705)
                ·
                  refine ⟨5525774823139619023842529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7367699764186158698456705 5525774823139619023842529)
                  ·
                    refine ⟨4144331117354714267881897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525774823139619023842529 4144331117354714267881897)
                    ·
                      refine ⟨3108248338016035700911423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144331117354714267881897 3108248338016035700911423)
                      ·
                        rfl

theorem cell23_6053292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_6053292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053292 prefixEnd_6053292 := by exact prefixLift 6053292
  have htrace : WordTrace (prefixWord ++ tailWord_6053292) baseStart_6053292 baseEnd_6053292 := by
    simpa [prefixWord, tailWord_6053292, baseEnd_6053292] using wordTrace_append hprefix tailTrace_6053292
  have hstable : (prefixWord ++ tailWord_6053292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053292).length < 2 ^ (prefixWord ++ tailWord_6053292).sum := by decide
  have hdescent : baseEnd_6053292 < baseStart_6053292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053315 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 5]
def baseStart_6053315 : Nat := 118140960795 + 6053315 * 2 ^ 59
def prefixEnd_6053315 : Nat := 4983230072969 + 3 ^ 40 * 6053315 * 2
def baseEnd_6053315 : Nat := 345362238674565456769313

theorem tailTrace_6053315 : CollatzResearch.WordTrace tailWord_6053315 prefixEnd_6053315 345362238674565456769313 := by
  unfold tailWord_6053315
  simp only [CollatzResearch.WordTrace]
  refine ⟨220782536064881053740185399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147188357376587369160123599 220782536064881053740185399)
  ·
    refine ⟨331173804097321580610278099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220782536064881053740185399 331173804097321580610278099)
    ·
      refine ⟨496760706145982370915417149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331173804097321580610278099 496760706145982370915417149)
      ·
        refine ⟨186285264804743389093281431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496760706145982370915417149 186285264804743389093281431)
        ·
          refine ⟨279427897207115083639922147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186285264804743389093281431 279427897207115083639922147)
          ·
            refine ⟨419141845810672625459883221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279427897207115083639922147 419141845810672625459883221)
            ·
              refine ⟨9823637011187639659216013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 419141845810672625459883221 9823637011187639659216013)
              ·
                refine ⟨3683863879195364872206005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9823637011187639659216013 3683863879195364872206005)
                ·
                  refine ⟨345362238674565456769313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683863879195364872206005 345362238674565456769313)
                  ·
                    rfl

theorem cell23_6053315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 5].length) (baseStart_6053315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053315 prefixEnd_6053315 := by exact prefixLift 6053315
  have htrace : WordTrace (prefixWord ++ tailWord_6053315) baseStart_6053315 baseEnd_6053315 := by
    simpa [prefixWord, tailWord_6053315, baseEnd_6053315] using wordTrace_append hprefix tailTrace_6053315
  have hstable : (prefixWord ++ tailWord_6053315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053315).length < 2 ^ (prefixWord ++ tailWord_6053315).sum := by decide
  have hdescent : baseEnd_6053315 < baseStart_6053315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053328 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_6053328 : Nat := 118140960795 + 6053328 * 2 ^ 59
def prefixEnd_6053328 : Nat := 4983230072969 + 3 ^ 40 * 6053328 * 2
def baseEnd_6053328 : Nat := 1036088941106532520020419

theorem tailTrace_6053328 : CollatzResearch.WordTrace tailWord_6053328 prefixEnd_6053328 1036088941106532520020419 := by
  unfold tailWord_6053328
  simp only [CollatzResearch.WordTrace]
  refine ⟨110391505106916978480204319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147188673475889304640272425 110391505106916978480204319)
  ·
    refine ⟨165587257660375467720306479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110391505106916978480204319 165587257660375467720306479)
    ·
      refine ⟨248380886490563201580459719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165587257660375467720306479 248380886490563201580459719)
      ·
        refine ⟨372571329735844802370689579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248380886490563201580459719 372571329735844802370689579)
        ·
          refine ⟨558856994603767203556034369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372571329735844802370689579 558856994603767203556034369)
          ·
            refine ⟨419142745952825402667025777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558856994603767203556034369 419142745952825402667025777)
            ·
              refine ⟨314357059464619052000269333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419142745952825402667025777 314357059464619052000269333)
              ·
                refine ⟨14735487162404018062512625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 314357059464619052000269333 14735487162404018062512625)
                ·
                  refine ⟨11051615371803013546884469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735487162404018062512625 11051615371803013546884469)
                  ·
                    refine ⟨1036088941106532520020419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11051615371803013546884469 1036088941106532520020419)
                    ·
                      rfl

theorem cell23_6053328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_6053328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053328 prefixEnd_6053328 := by exact prefixLift 6053328
  have htrace : WordTrace (prefixWord ++ tailWord_6053328) baseStart_6053328 baseEnd_6053328 := by
    simpa [prefixWord, tailWord_6053328, baseEnd_6053328] using wordTrace_append hprefix tailTrace_6053328
  have hstable : (prefixWord ++ tailWord_6053328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053328).length < 2 ^ (prefixWord ++ tailWord_6053328).sum := by decide
  have hdescent : baseEnd_6053328 < baseStart_6053328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053332 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 7]
def baseStart_6053332 : Nat := 118140960795 + 6053332 * 2 ^ 59
def prefixEnd_6053332 : Nat := 4983230072969 + 3 ^ 40 * 6053332 * 2
def baseEnd_6053332 : Nat := 345363208582468393823471

theorem tailTrace_6053332 : CollatzResearch.WordTrace tailWord_6053332 prefixEnd_6053332 345363208582468393823471 := by
  unfold tailWord_6053332
  simp only [CollatzResearch.WordTrace]
  refine ⟨110391578052909732821777125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147188770737212977095702833 110391578052909732821777125)
  ·
    refine ⟨20698420884920574904083211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110391578052909732821777125 20698420884920574904083211)
    ·
      refine ⟨31047631327380862356124817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20698420884920574904083211 31047631327380862356124817)
      ·
        refine ⟨23285723495535646767093613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31047631327380862356124817 23285723495535646767093613)
        ·
          refine ⟨8732146310825867537660105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23285723495535646767093613 8732146310825867537660105)
          ·
            refine ⟨6549109733119400653245079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8732146310825867537660105 6549109733119400653245079)
            ·
              refine ⟨9823664599679100979867619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549109733119400653245079 9823664599679100979867619)
              ·
                refine ⟨14735496899518651469801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823664599679100979867619 14735496899518651469801429)
                ·
                  refine ⟨345363208582468393823471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14735496899518651469801429 345363208582468393823471)
                  ·
                    rfl

theorem cell23_6053332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_6053332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053332 prefixEnd_6053332 := by exact prefixLift 6053332
  have htrace : WordTrace (prefixWord ++ tailWord_6053332) baseStart_6053332 baseEnd_6053332 := by
    simpa [prefixWord, tailWord_6053332, baseEnd_6053332] using wordTrace_append hprefix tailTrace_6053332
  have hstable : (prefixWord ++ tailWord_6053332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053332).length < 2 ^ (prefixWord ++ tailWord_6053332).sum := by decide
  have hdescent : baseEnd_6053332 < baseStart_6053332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053338 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_6053338 : Nat := 118140960795 + 6053338 * 2 ^ 59
def prefixEnd_6053338 : Nat := 4983230072969 + 3 ^ 40 * 6053338 * 2
def baseEnd_6053338 : Nat := 3108271958126142520936211

theorem tailTrace_6053338 : CollatzResearch.WordTrace tailWord_6053338 prefixEnd_6053338 3108271958126142520936211 := by
  unfold tailWord_6053338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195843735949432167068167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147188916629198485778848445 55195843735949432167068167)
  ·
    refine ⟨82793765603924148250602251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55195843735949432167068167 82793765603924148250602251)
    ·
      refine ⟨124190648405886222375903377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82793765603924148250602251 124190648405886222375903377)
      ·
        refine ⟨93142986304414666781927533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124190648405886222375903377 93142986304414666781927533)
        ·
          refine ⟨34928619864155500043222825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93142986304414666781927533 34928619864155500043222825)
          ·
            refine ⟨26196464898116625032417119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34928619864155500043222825 26196464898116625032417119)
            ·
              refine ⟨39294697347174937548625679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26196464898116625032417119 39294697347174937548625679)
              ·
                refine ⟨58942046020762406322938519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39294697347174937548625679 58942046020762406322938519)
                ·
                  refine ⟨88413069031143609484407779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58942046020762406322938519 88413069031143609484407779)
                  ·
                    refine ⟨132619603546715414226611669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88413069031143609484407779 132619603546715414226611669)
                    ·
                      refine ⟨3108271958126142520936211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132619603546715414226611669 3108271958126142520936211)
                      ·
                        rfl

theorem cell23_6053338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_6053338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053338 prefixEnd_6053338 := by exact prefixLift 6053338
  have htrace : WordTrace (prefixWord ++ tailWord_6053338) baseStart_6053338 baseEnd_6053338 := by
    simpa [prefixWord, tailWord_6053338, baseEnd_6053338] using wordTrace_append hprefix tailTrace_6053338
  have hstable : (prefixWord ++ tailWord_6053338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053338).length < 2 ^ (prefixWord ++ tailWord_6053338).sum := by decide
  have hdescent : baseEnd_6053338 < baseStart_6053338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053348 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_6053348 : Nat := 118140960795 + 6053348 * 2 ^ 59
def prefixEnd_6053348 : Nat := 4983230072969 + 3 ^ 40 * 6053348 * 2
def baseEnd_6053348 : Nat := 3108277092932687481811165

theorem tailTrace_6053348 : CollatzResearch.WordTrace tailWord_6053348 prefixEnd_6053348 3108277092932687481811165 := by
  unfold tailWord_6053348
  simp only [CollatzResearch.WordTrace]
  refine ⟨110391869836880750188068349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147189159782507666917424465 110391869836880750188068349)
  ·
    refine ⟨41396951188830281320525631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110391869836880750188068349 41396951188830281320525631)
    ·
      refine ⟨62095426783245421980788447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41396951188830281320525631 62095426783245421980788447)
      ·
        refine ⟨93143140174868132971182671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62095426783245421980788447 93143140174868132971182671)
        ·
          refine ⟨139714710262302199456774007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93143140174868132971182671 139714710262302199456774007)
          ·
            refine ⟨209572065393453299185161011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139714710262302199456774007 209572065393453299185161011)
            ·
              refine ⟨314358098090179948777741517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209572065393453299185161011 314358098090179948777741517)
              ·
                refine ⟨117884286783817480791653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314358098090179948777741517 117884286783817480791653069)
                ·
                  refine ⟨44206607543931555296869901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117884286783817480791653069 44206607543931555296869901)
                  ·
                    refine ⟨16577477828974333236326213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44206607543931555296869901 16577477828974333236326213)
                    ·
                      refine ⟨3108277092932687481811165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16577477828974333236326213 3108277092932687481811165)
                      ·
                        rfl

theorem cell23_6053348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_6053348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053348 prefixEnd_6053348 := by exact prefixLift 6053348
  have htrace : WordTrace (prefixWord ++ tailWord_6053348) baseStart_6053348 baseEnd_6053348 := by
    simpa [prefixWord, tailWord_6053348, baseEnd_6053348] using wordTrace_append hprefix tailTrace_6053348
  have hstable : (prefixWord ++ tailWord_6053348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053348).length < 2 ^ (prefixWord ++ tailWord_6053348).sum := by decide
  have hdescent : baseEnd_6053348 < baseStart_6053348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053362 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_6053362 : Nat := 118140960795 + 6053362 * 2 ^ 59
def prefixEnd_6053362 : Nat := 4983230072969 + 3 ^ 40 * 6053362 * 2
def baseEnd_6053362 : Nat := 1036094760553950142345367

theorem tailTrace_6053362 : CollatzResearch.WordTrace tailWord_6053362 prefixEnd_6053362 1036094760553950142345367 := by
  unfold tailWord_6053362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55196062573927695191786585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147189500197140520511430893 55196062573927695191786585)
  ·
    refine ⟨41397046930445771393839939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55196062573927695191786585 41397046930445771393839939)
    ·
      refine ⟨62095570395668657090759909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41397046930445771393839939 62095570395668657090759909)
      ·
        refine ⟨11642919449187873204517483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62095570395668657090759909 11642919449187873204517483)
        ·
          refine ⟨17464379173781809806776225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642919449187873204517483 17464379173781809806776225)
          ·
            refine ⟨13098284380336357355082169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17464379173781809806776225 13098284380336357355082169)
            ·
              refine ⟨9823713285252268016311627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13098284380336357355082169 9823713285252268016311627)
              ·
                refine ⟨14735569927878402024467441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823713285252268016311627 14735569927878402024467441)
                ·
                  refine ⟨11051677445908801518350581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735569927878402024467441 11051677445908801518350581)
                  ·
                    refine ⟨1036094760553950142345367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11051677445908801518350581 1036094760553950142345367)
                    ·
                      rfl

theorem cell23_6053362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_6053362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053362 prefixEnd_6053362 := by exact prefixLift 6053362
  have htrace : WordTrace (prefixWord ++ tailWord_6053362) baseStart_6053362 baseEnd_6053362 := by
    simpa [prefixWord, tailWord_6053362, baseEnd_6053362] using wordTrace_append hprefix tailTrace_6053362
  have hstable : (prefixWord ++ tailWord_6053362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053362).length < 2 ^ (prefixWord ++ tailWord_6053362).sum := by decide
  have hdescent : baseEnd_6053362 < baseStart_6053362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053385 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_6053385 : Nat := 118140960795 + 6053385 * 2 ^ 59
def prefixEnd_6053385 : Nat := 4983230072969 + 3 ^ 40 * 6053385 * 2
def baseEnd_6053385 : Nat := 3108296091716903837048495

theorem tailTrace_6053385 : CollatzResearch.WordTrace tailWord_6053385 prefixEnd_6053385 3108296091716903837048495 := by
  unfold tailWord_6053385
  simp only [CollatzResearch.WordTrace]
  refine ⟨220785089174627455695233609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147190059449751637130155739 220785089174627455695233609)
  ·
    refine ⟨165588816880970591771425207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220785089174627455695233609 165588816880970591771425207)
    ·
      refine ⟨248383225321455887657137811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165588816880970591771425207 248383225321455887657137811)
      ·
        refine ⟨372574837982183831485706717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248383225321455887657137811 372574837982183831485706717)
        ·
          refine ⟨139715564243318936807140019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372574837982183831485706717 139715564243318936807140019)
          ·
            refine ⟨209573346364978405210710029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139715564243318936807140019 209573346364978405210710029)
            ·
              refine ⟨78590004886866901954016261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209573346364978405210710029 78590004886866901954016261)
              ·
                refine ⟨14735625916287544116378049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78590004886866901954016261 14735625916287544116378049)
                ·
                  refine ⟨11051719437215658087283537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735625916287544116378049 11051719437215658087283537)
                  ·
                    refine ⟨8288789577911743565462653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11051719437215658087283537 8288789577911743565462653)
                    ·
                      refine ⟨3108296091716903837048495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8288789577911743565462653 3108296091716903837048495)
                      ·
                        rfl

theorem cell23_6053385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_6053385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053385 prefixEnd_6053385 := by exact prefixLift 6053385
  have htrace : WordTrace (prefixWord ++ tailWord_6053385) baseStart_6053385 baseEnd_6053385 := by
    simpa [prefixWord, tailWord_6053385, baseEnd_6053385] using wordTrace_append hprefix tailTrace_6053385
  have hstable : (prefixWord ++ tailWord_6053385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053385).length < 2 ^ (prefixWord ++ tailWord_6053385).sum := by decide
  have hdescent : baseEnd_6053385 < baseStart_6053385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053405 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 6]
def baseStart_6053405 : Nat := 118140960795 + 6053405 * 2 ^ 59
def prefixEnd_6053405 : Nat := 4983230072969 + 3 ^ 40 * 6053405 * 2
def baseEnd_6053405 : Nat := 345367373481110417644267

theorem tailTrace_6053405 : CollatzResearch.WordTrace tailWord_6053405 prefixEnd_6053405 345367373481110417644267 := by
  unfold tailWord_6053405
  simp only [CollatzResearch.WordTrace]
  refine ⟨220785818634554999110961669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147190545756369999407307779 220785818634554999110961669)
  ·
    refine ⟨41397340993979062333305313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220785818634554999110961669 41397340993979062333305313)
    ·
      refine ⟨31048005745484296749978985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41397340993979062333305313 31048005745484296749978985)
      ·
        refine ⟨23286004309113222562484239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31048005745484296749978985 23286004309113222562484239)
        ·
          refine ⟨34929006463669833843726359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23286004309113222562484239 34929006463669833843726359)
          ·
            refine ⟨52393509695504750765589539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34929006463669833843726359 52393509695504750765589539)
            ·
              refine ⟨78590264543257126148384309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52393509695504750765589539 78590264543257126148384309)
              ·
                refine ⟨7367837300930355576411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78590264543257126148384309 7367837300930355576411029)
                ·
                  refine ⟨345367373481110417644267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7367837300930355576411029 345367373481110417644267)
                  ·
                    rfl

theorem cell23_6053405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_6053405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053405 prefixEnd_6053405 := by exact prefixLift 6053405
  have htrace : WordTrace (prefixWord ++ tailWord_6053405) baseStart_6053405 baseEnd_6053405 := by
    simpa [prefixWord, tailWord_6053405, baseEnd_6053405] using wordTrace_append hprefix tailTrace_6053405
  have hstable : (prefixWord ++ tailWord_6053405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053405).length < 2 ^ (prefixWord ++ tailWord_6053405).sum := by decide
  have hdescent : baseEnd_6053405 < baseStart_6053405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053416 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6053416 : Nat := 118140960795 + 6053416 * 2 ^ 59
def prefixEnd_6053416 : Nat := 4983230072969 + 3 ^ 40 * 6053416 * 2
def baseEnd_6053416 : Nat := 3108312009617193215760853

theorem tailTrace_6053416 : CollatzResearch.WordTrace tailWord_6053416 prefixEnd_6053416 3108312009617193215760853 := by
  unfold tailWord_6053416
  simp only [CollatzResearch.WordTrace]
  refine ⟨110393109918757573994806051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147190813225010098659741401 110393109918757573994806051)
  ·
    refine ⟨165589664878136360992209077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110393109918757573994806051 165589664878136360992209077)
    ·
      refine ⟨15524031082325283843019601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165589664878136360992209077 15524031082325283843019601)
      ·
        refine ⟨11643023311743962882264701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15524031082325283843019601 11643023311743962882264701)
        ·
          refine ⟨4366133741903986080849263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11643023311743962882264701 4366133741903986080849263)
          ·
            refine ⟨6549200612855979121273895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366133741903986080849263 6549200612855979121273895)
            ·
              refine ⟨9823800919283968681910843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549200612855979121273895 9823800919283968681910843)
              ·
                refine ⟨14735701378925953022866265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823800919283968681910843 14735701378925953022866265)
                ·
                  refine ⟨11051776034194464767149699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735701378925953022866265 11051776034194464767149699)
                  ·
                    refine ⟨16577664051291697150724549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11051776034194464767149699 16577664051291697150724549)
                    ·
                      refine ⟨3108312009617193215760853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16577664051291697150724549 3108312009617193215760853)
                      ·
                        rfl

theorem cell23_6053416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6053416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053416 prefixEnd_6053416 := by exact prefixLift 6053416
  have htrace : WordTrace (prefixWord ++ tailWord_6053416) baseStart_6053416 baseEnd_6053416 := by
    simpa [prefixWord, tailWord_6053416, baseEnd_6053416] using wordTrace_append hprefix tailTrace_6053416
  have hstable : (prefixWord ++ tailWord_6053416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053416).length < 2 ^ (prefixWord ++ tailWord_6053416).sum := by decide
  have hdescent : baseEnd_6053416 < baseStart_6053416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053448 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6053448 : Nat := 118140960795 + 6053448 * 2 ^ 59
def prefixEnd_6053448 : Nat := 4983230072969 + 3 ^ 40 * 6053448 * 2
def baseEnd_6053448 : Nat := 1036109480332712363520235

theorem tailTrace_6053448 : CollatzResearch.WordTrace tailWord_6053448 prefixEnd_6053448 1036109480332712363520235 := by
  unfold tailWord_6053448
  simp only [CollatzResearch.WordTrace]
  refine ⟨110393693486699608727388499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147191591315599478303184665 110393693486699608727388499)
  ·
    refine ⟨165590540230049413091082749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110393693486699608727388499 165590540230049413091082749)
    ·
      refine ⟨62096452586268529909156031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165590540230049413091082749 62096452586268529909156031)
      ·
        refine ⟨93144678879402794863734047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62096452586268529909156031 93144678879402794863734047)
        ·
          refine ⟨139717018319104192295601071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93144678879402794863734047 139717018319104192295601071)
          ·
            refine ⟨209575527478656288443401607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139717018319104192295601071 209575527478656288443401607)
            ·
              refine ⟨314363291217984432665102411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209575527478656288443401607 314363291217984432665102411)
              ·
                refine ⟨471544936826976648997653617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314363291217984432665102411 471544936826976648997653617)
                ·
                  refine ⟨353658702620232486748240213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471544936826976648997653617 353658702620232486748240213)
                  ·
                    refine ⟨1036109480332712363520235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 353658702620232486748240213 1036109480332712363520235)
                    ·
                      rfl

theorem cell23_6053448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6053448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053448 prefixEnd_6053448 := by exact prefixLift 6053448
  have htrace : WordTrace (prefixWord ++ tailWord_6053448) baseStart_6053448 baseEnd_6053448 := by
    simpa [prefixWord, tailWord_6053448, baseEnd_6053448] using wordTrace_append hprefix tailTrace_6053448
  have hstable : (prefixWord ++ tailWord_6053448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053448).length < 2 ^ (prefixWord ++ tailWord_6053448).sum := by decide
  have hdescent : baseEnd_6053448 < baseStart_6053448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053482 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_6053482 : Nat := 118140960795 + 6053482 * 2 ^ 59
def prefixEnd_6053482 : Nat := 4983230072969 + 3 ^ 40 * 6053482 * 2
def baseEnd_6053482 : Nat := 1036115299780129985845183

theorem tailTrace_6053482 : CollatzResearch.WordTrace tailWord_6053482 prefixEnd_6053482 1036115299780129985845183 := by
  unfold tailWord_6053482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55197156763819010315378675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147192418036850694174343133 55197156763819010315378675)
  ·
    refine ⟨82795735145728515473068013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55197156763819010315378675 82795735145728515473068013)
    ·
      refine ⟨31048400679648193302400505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82795735145728515473068013 31048400679648193302400505)
      ·
        refine ⟨23286300509736144976800379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31048400679648193302400505 23286300509736144976800379)
        ·
          refine ⟨34929450764604217465200569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23286300509736144976800379 34929450764604217465200569)
          ·
            refine ⟨26197088073453163098900427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34929450764604217465200569 26197088073453163098900427)
            ·
              refine ⟨39295632110179744648350641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26197088073453163098900427 39295632110179744648350641)
              ·
                refine ⟨29471724082634808486262981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39295632110179744648350641 29471724082634808486262981)
                ·
                  refine ⟨5525948265494026591174309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29471724082634808486262981 5525948265494026591174309)
                  ·
                    refine ⟨1036115299780129985845183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5525948265494026591174309 1036115299780129985845183)
                    ·
                      rfl

theorem cell23_6053482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_6053482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053482 prefixEnd_6053482 := by exact prefixLift 6053482
  have htrace : WordTrace (prefixWord ++ tailWord_6053482) baseStart_6053482 baseEnd_6053482 := by
    simpa [prefixWord, tailWord_6053482, baseEnd_6053482] using wordTrace_append hprefix tailTrace_6053482
  have hstable : (prefixWord ++ tailWord_6053482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053482).length < 2 ^ (prefixWord ++ tailWord_6053482).sum := by decide
  have hdescent : baseEnd_6053482 < baseStart_6053482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053555 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 6]
def baseStart_6053555 : Nat := 118140960795 + 6053555 * 2 ^ 59
def prefixEnd_6053555 : Nat := 4983230072969 + 3 ^ 40 * 6053555 * 2
def baseEnd_6053555 : Nat := 1036127794476056057307571

theorem tailTrace_6053555 : CollatzResearch.WordTrace tailWord_6053555 prefixEnd_6053555 1036127794476056057307571 := by
  unfold tailWord_6053555
  simp only [CollatzResearch.WordTrace]
  refine ⟨220791289584011574728922119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147194193056007716485948079 220791289584011574728922119)
  ·
    refine ⟨331186934376017362093383179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220791289584011574728922119 331186934376017362093383179)
    ·
      refine ⟨496780401564026043140074769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331186934376017362093383179 496780401564026043140074769)
      ·
        refine ⟨372585301173019532355056077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496780401564026043140074769 372585301173019532355056077)
        ·
          refine ⟨139719487939882324633146029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372585301173019532355056077 139719487939882324633146029)
          ·
            refine ⟨52394807977455871737429761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139719487939882324633146029 52394807977455871737429761)
            ·
              refine ⟨39296105983091903803072321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52394807977455871737429761 39296105983091903803072321)
              ·
                refine ⟨29472079487318927852304241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39296105983091903803072321 29472079487318927852304241)
                ·
                  refine ⟨22104059615489195889228181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29472079487318927852304241 22104059615489195889228181)
                  ·
                    refine ⟨1036127794476056057307571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22104059615489195889228181 1036127794476056057307571)
                    ·
                      rfl

theorem cell23_6053555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_6053555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053555 prefixEnd_6053555 := by exact prefixLift 6053555
  have htrace : WordTrace (prefixWord ++ tailWord_6053555) baseStart_6053555 baseEnd_6053555 := by
    simpa [prefixWord, tailWord_6053555, baseEnd_6053555] using wordTrace_append hprefix tailTrace_6053555
  have hstable : (prefixWord ++ tailWord_6053555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053555).length < 2 ^ (prefixWord ++ tailWord_6053555).sum := by decide
  have hdescent : baseEnd_6053555 < baseStart_6053555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053557 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6053557 : Nat := 118140960795 + 6053557 * 2 ^ 59
def prefixEnd_6053557 : Nat := 4983230072969 + 3 ^ 40 * 6053557 * 2
def baseEnd_6053557 : Nat := 3108384410389477164097705

theorem tailTrace_6053557 : CollatzResearch.WordTrace tailWord_6053557 prefixEnd_6053557 3108384410389477164097705 := by
  unfold tailWord_6053557
  simp only [CollatzResearch.WordTrace]
  refine ⟨220791362530004329070494925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147194241686669552713663283 220791362530004329070494925)
  ·
    refine ⟨82796760948751623401435597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220791362530004329070494925 82796760948751623401435597)
    ·
      refine ⟨31048785355781858775538349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82796760948751623401435597 31048785355781858775538349)
      ·
        refine ⟨11643294508418197040826881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31048785355781858775538349 11643294508418197040826881)
        ·
          refine ⟨8732470881313647780620161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11643294508418197040826881 8732470881313647780620161)
          ·
            refine ⟨6549353160985235835465121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8732470881313647780620161 6549353160985235835465121)
            ·
              refine ⟨4912014870738926876598841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6549353160985235835465121 4912014870738926876598841)
              ·
                refine ⟨3684011153054195157449131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912014870738926876598841 3684011153054195157449131)
                ·
                  refine ⟨5526016729581292736173697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684011153054195157449131 5526016729581292736173697)
                  ·
                    refine ⟨4144512547185969552130273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526016729581292736173697 4144512547185969552130273)
                    ·
                      refine ⟨3108384410389477164097705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144512547185969552130273 3108384410389477164097705)
                      ·
                        rfl

theorem cell23_6053557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6053557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053557 prefixEnd_6053557 := by exact prefixLift 6053557
  have htrace : WordTrace (prefixWord ++ tailWord_6053557) baseStart_6053557 baseEnd_6053557 := by
    simpa [prefixWord, tailWord_6053557, baseEnd_6053557] using wordTrace_append hprefix tailTrace_6053557
  have hstable : (prefixWord ++ tailWord_6053557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053557).length < 2 ^ (prefixWord ++ tailWord_6053557).sum := by decide
  have hdescent : baseEnd_6053557 < baseStart_6053557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053572 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6053572 : Nat := 118140960795 + 6053572 * 2 ^ 59
def prefixEnd_6053572 : Nat := 4983230072969 + 3 ^ 40 * 6053572 * 2
def baseEnd_6053572 : Nat := 1036130704199764868470045

theorem tailTrace_6053572 : CollatzResearch.WordTrace tailWord_6053572 prefixEnd_6053572 1036130704199764868470045 := by
  unfold tailWord_6053572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110395954812474993316145485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147194606416633324421527313 110395954812474993316145485)
  ·
    refine ⟨41398483054678122493554557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110395954812474993316145485 41398483054678122493554557)
    ·
      refine ⟨15524431145504295935082959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41398483054678122493554557 15524431145504295935082959)
      ·
        refine ⟨23286646718256443902624439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524431145504295935082959 23286646718256443902624439)
        ·
          refine ⟨34929970077384665853936659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23286646718256443902624439 34929970077384665853936659)
          ·
            refine ⟨52394955116076998780904989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34929970077384665853936659 52394955116076998780904989)
            ·
              refine ⟨19648108168528874542839371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52394955116076998780904989 19648108168528874542839371)
              ·
                refine ⟨29472162252793311814259057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19648108168528874542839371 29472162252793311814259057)
                ·
                  refine ⟨22104121689594983860694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29472162252793311814259057 22104121689594983860694293)
                  ·
                    refine ⟨1036130704199764868470045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22104121689594983860694293 1036130704199764868470045)
                    ·
                      rfl

theorem cell23_6053572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6053572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053572 prefixEnd_6053572 := by exact prefixLift 6053572
  have htrace : WordTrace (prefixWord ++ tailWord_6053572) baseStart_6053572 baseEnd_6053572 := by
    simpa [prefixWord, tailWord_6053572, baseEnd_6053572] using wordTrace_append hprefix tailTrace_6053572
  have hstable : (prefixWord ++ tailWord_6053572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053572).length < 2 ^ (prefixWord ++ tailWord_6053572).sum := by decide
  have hdescent : baseEnd_6053572 < baseStart_6053572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053582 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_6053582 : Nat := 118140960795 + 6053582 * 2 ^ 59
def prefixEnd_6053582 : Nat := 4983230072969 + 3 ^ 40 * 6053582 * 2
def baseEnd_6053582 : Nat := 3108397247405839566285089

theorem tailTrace_6053582 : CollatzResearch.WordTrace tailWord_6053582 prefixEnd_6053582 3108397247405839566285089 := by
  unfold tailWord_6053582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599034294364219792519375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147194849569942505560103333 27599034294364219792519375)
  ·
    refine ⟨41398551441546329688779063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27599034294364219792519375 41398551441546329688779063)
    ·
      refine ⟨62097827162319494533168595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41398551441546329688779063 62097827162319494533168595)
      ·
        refine ⟨93146740743479241799752893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62097827162319494533168595 93146740743479241799752893)
        ·
          refine ⟨34930027778804715674907335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93146740743479241799752893 34930027778804715674907335)
          ·
            refine ⟨52395041668207073512361003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34930027778804715674907335 52395041668207073512361003)
            ·
              refine ⟨78592562502310610268541505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52395041668207073512361003 78592562502310610268541505)
              ·
                refine ⟨58944421876732957701406129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78592562502310610268541505 58944421876732957701406129)
                ·
                  refine ⟨44208316407549718276054597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58944421876732957701406129 44208316407549718276054597)
                  ·
                    refine ⟨8289059326415572176760237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44208316407549718276054597 8289059326415572176760237)
                    ·
                      refine ⟨3108397247405839566285089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289059326415572176760237 3108397247405839566285089)
                      ·
                        rfl

theorem cell23_6053582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_6053582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053582 prefixEnd_6053582 := by exact prefixLift 6053582
  have htrace : WordTrace (prefixWord ++ tailWord_6053582) baseStart_6053582 baseEnd_6053582 := by
    simpa [prefixWord, tailWord_6053582, baseEnd_6053582] using wordTrace_append hprefix tailTrace_6053582
  have hstable : (prefixWord ++ tailWord_6053582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053582).length < 2 ^ (prefixWord ++ tailWord_6053582).sum := by decide
  have hdescent : baseEnd_6053582 < baseStart_6053582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053585 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 9]
def baseStart_6053585 : Nat := 118140960795 + 6053585 * 2 ^ 59
def prefixEnd_6053585 : Nat := 4983230072969 + 3 ^ 40 * 6053585 * 2
def baseEnd_6053585 : Nat := 345377643094200339394175

theorem tailTrace_6053585 : CollatzResearch.WordTrace tailWord_6053585 prefixEnd_6053585 345377643094200339394175 := by
  unfold tailWord_6053585
  simp only [CollatzResearch.WordTrace]
  refine ⟨220792383773902889852514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147194922515935259901676139 220792383773902889852514209)
  ·
    refine ⟨165594287830427167389385657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220792383773902889852514209 165594287830427167389385657)
    ·
      refine ⟨124195715872820375542039243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165594287830427167389385657 124195715872820375542039243)
      ·
        refine ⟨186293573809230563313058865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124195715872820375542039243 186293573809230563313058865)
        ·
          refine ⟨139720180356922922484794149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186293573809230563313058865 139720180356922922484794149)
          ·
            refine ⟨26197533816923047965898903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139720180356922922484794149 26197533816923047965898903)
            ·
              refine ⟨39296300725384571948848355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26197533816923047965898903 39296300725384571948848355)
              ·
                refine ⟨58944451088076857923272533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39296300725384571948848355 58944451088076857923272533)
                ·
                  refine ⟨345377643094200339394175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58944451088076857923272533 345377643094200339394175)
                  ·
                    rfl

theorem cell23_6053585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_6053585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053585 prefixEnd_6053585 := by exact prefixLift 6053585
  have htrace : WordTrace (prefixWord ++ tailWord_6053585) baseStart_6053585 baseEnd_6053585 := by
    simpa [prefixWord, tailWord_6053585, baseEnd_6053585] using wordTrace_append hprefix tailTrace_6053585
  have hstable : (prefixWord ++ tailWord_6053585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053585).length < 2 ^ (prefixWord ++ tailWord_6053585).sum := by decide
  have hdescent : baseEnd_6053585 < baseStart_6053585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053612 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_6053612 : Nat := 118140960795 + 6053612 * 2 ^ 59
def prefixEnd_6053612 : Nat := 4983230072969 + 3 ^ 40 * 6053612 * 2
def baseEnd_6053612 : Nat := 3108412651825474448909951

theorem tailTrace_6053612 : CollatzResearch.WordTrace tailWord_6053612 prefixEnd_6053612 3108412651825474448909951 := by
  unfold tailWord_6053612
  simp only [CollatzResearch.WordTrace]
  refine ⟨110396684272402536731873545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147195579029870048975831393 110396684272402536731873545)
  ·
    refine ⟨82797513204301902548905159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110396684272402536731873545 82797513204301902548905159)
    ·
      refine ⟨124196269806452853823357739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82797513204301902548905159 124196269806452853823357739)
      ·
        refine ⟨186294404709679280735036609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124196269806452853823357739 186294404709679280735036609)
        ·
          refine ⟨139720803532259460551277457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186294404709679280735036609 139720803532259460551277457)
          ·
            refine ⟨104790602649194595413458093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139720803532259460551277457 104790602649194595413458093)
            ·
              refine ⟨39296475993447973280046785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104790602649194595413458093 39296475993447973280046785)
              ·
                refine ⟨29472356995085979960035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39296475993447973280046785 29472356995085979960035089)
                ·
                  refine ⟨22104267746314484970026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29472356995085979960035089 22104267746314484970026317)
                  ·
                    refine ⟨8289100404867931863759869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22104267746314484970026317 8289100404867931863759869)
                    ·
                      refine ⟨3108412651825474448909951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289100404867931863759869 3108412651825474448909951)
                      ·
                        rfl

theorem cell23_6053612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_6053612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053612 prefixEnd_6053612 := by exact prefixLift 6053612
  have htrace : WordTrace (prefixWord ++ tailWord_6053612) baseStart_6053612 baseEnd_6053612 := by
    simpa [prefixWord, tailWord_6053612, baseEnd_6053612] using wordTrace_append hprefix tailTrace_6053612
  have hstable : (prefixWord ++ tailWord_6053612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053612).length < 2 ^ (prefixWord ++ tailWord_6053612).sum := by decide
  have hdescent : baseEnd_6053612 < baseStart_6053612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053613 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6053613 : Nat := 118140960795 + 6053613 * 2 ^ 59
def prefixEnd_6053613 : Nat := 4983230072969 + 3 ^ 40 * 6053613 * 2
def baseEnd_6053613 : Nat := 3108413165306128944997447

theorem tailTrace_6053613 : CollatzResearch.WordTrace tailWord_6053613 prefixEnd_6053613 3108413165306128944997447 := by
  unfold tailWord_6053613
  simp only [CollatzResearch.WordTrace]
  refine ⟨220793405017801450634533493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147195603345200967089688995 220793405017801450634533493)
  ·
    refine ⟨20699381720418885996987515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220793405017801450634533493 20699381720418885996987515)
    ·
      refine ⟨31049072580628328995481273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20699381720418885996987515 31049072580628328995481273)
      ·
        refine ⟨23286804435471246746610955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31049072580628328995481273 23286804435471246746610955)
        ·
          refine ⟨34930206653206870119916433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23286804435471246746610955 34930206653206870119916433)
          ·
            refine ⟨26197654989905152589937325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34930206653206870119916433 26197654989905152589937325)
            ·
              refine ⟨9824120621214432221226497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26197654989905152589937325 9824120621214432221226497)
              ·
                refine ⟨7368090465910824165919873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9824120621214432221226497 7368090465910824165919873)
                ·
                  refine ⟨5526067849433118124439905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368090465910824165919873 5526067849433118124439905)
                  ·
                    refine ⟨4144550887074838593329929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526067849433118124439905 4144550887074838593329929)
                    ·
                      refine ⟨3108413165306128944997447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144550887074838593329929 3108413165306128944997447)
                      ·
                        rfl

theorem cell23_6053613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6053613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053613 prefixEnd_6053613 := by exact prefixLift 6053613
  have htrace : WordTrace (prefixWord ++ tailWord_6053613) baseStart_6053613 baseEnd_6053613 := by
    simpa [prefixWord, tailWord_6053613, baseEnd_6053613] using wordTrace_append hprefix tailTrace_6053613
  have hstable : (prefixWord ++ tailWord_6053613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053613).length < 2 ^ (prefixWord ++ tailWord_6053613).sum := by decide
  have hdescent : baseEnd_6053613 < baseStart_6053613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053630 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_6053630 : Nat := 118140960795 + 6053630 * 2 ^ 59
def prefixEnd_6053630 : Nat := 4983230072969 + 3 ^ 40 * 6053630 * 2
def baseEnd_6053630 : Nat := 3108421894477255378484869

theorem tailTrace_6053630 : CollatzResearch.WordTrace tailWord_6053630 prefixEnd_6053630 3108421894477255378484869 := by
  unfold tailWord_6053630
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599253132342482817237793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147196016705826575025268229 27599253132342482817237793)
  ·
    refine ⟨20699439849256862112928345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27599253132342482817237793 20699439849256862112928345)
    ·
      refine ⟨15524579886942646584696259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20699439849256862112928345 15524579886942646584696259)
      ·
        refine ⟨23286869830413969877044389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524579886942646584696259 23286869830413969877044389)
        ·
          refine ⟨4366288093202619351945823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23286869830413969877044389 4366288093202619351945823)
          ·
            refine ⟨6549432139803929027918735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366288093202619351945823 6549432139803929027918735)
            ·
              refine ⟨9824148209705893541878103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549432139803929027918735 9824148209705893541878103)
              ·
                refine ⟨14736222314558840312817155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824148209705893541878103 14736222314558840312817155)
                ·
                  refine ⟨22104333471838260469225733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14736222314558840312817155 22104333471838260469225733)
                  ·
                    refine ⟨4144562525969673837979825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22104333471838260469225733 4144562525969673837979825)
                    ·
                      refine ⟨3108421894477255378484869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144562525969673837979825 3108421894477255378484869)
                      ·
                        rfl

theorem cell23_6053630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_6053630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053630 prefixEnd_6053630 := by exact prefixLift 6053630
  have htrace : WordTrace (prefixWord ++ tailWord_6053630) baseStart_6053630 baseEnd_6053630 := by
    simpa [prefixWord, tailWord_6053630, baseEnd_6053630] using wordTrace_append hprefix tailTrace_6053630
  have hstable : (prefixWord ++ tailWord_6053630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053630).length < 2 ^ (prefixWord ++ tailWord_6053630).sum := by decide
  have hdescent : baseEnd_6053630 < baseStart_6053630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053669 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_6053669 : Nat := 118140960795 + 6053669 * 2 ^ 59
def prefixEnd_6053669 : Nat := 4983230072969 + 3 ^ 40 * 6053669 * 2
def baseEnd_6053669 : Nat := 3108441920222780725897189

theorem tailTrace_6053669 : CollatzResearch.WordTrace tailWord_6053669 prefixEnd_6053669 3108441920222780725897189 := by
  unfold tailWord_6053669
  simp only [CollatzResearch.WordTrace]
  refine ⟨220795447505598572198572061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147196965003732381465714707 220795447505598572198572061)
  ·
    refine ⟨82798292814599464574464523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220795447505598572198572061 82798292814599464574464523)
    ·
      refine ⟨124197439221899196861696785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82798292814599464574464523 124197439221899196861696785)
      ·
        refine ⟨93148079416424397646272589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124197439221899196861696785 93148079416424397646272589)
        ·
          refine ⟨34930529781159149117352221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93148079416424397646272589 34930529781159149117352221)
          ·
            refine ⟨13098948667934680919007083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34930529781159149117352221 13098948667934680919007083)
            ·
              refine ⟨19648423001902021378510625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13098948667934680919007083 19648423001902021378510625)
              ·
                refine ⟨14736317251426516033882969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19648423001902021378510625 14736317251426516033882969)
                ·
                  refine ⟨11052237938569887025412227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14736317251426516033882969 11052237938569887025412227)
                  ·
                    refine ⟨16578356907854830538118341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11052237938569887025412227 16578356907854830538118341)
                    ·
                      refine ⟨3108441920222780725897189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16578356907854830538118341 3108441920222780725897189)
                      ·
                        rfl

theorem cell23_6053669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_6053669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053669 prefixEnd_6053669 := by exact prefixLift 6053669
  have htrace : WordTrace (prefixWord ++ tailWord_6053669) baseStart_6053669 baseEnd_6053669 := by
    simpa [prefixWord, tailWord_6053669, baseEnd_6053669] using wordTrace_append hprefix tailTrace_6053669
  have hstable : (prefixWord ++ tailWord_6053669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053669).length < 2 ^ (prefixWord ++ tailWord_6053669).sum := by decide
  have hdescent : baseEnd_6053669 < baseStart_6053669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053675 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 12]
def baseStart_6053675 : Nat := 118140960795 + 6053675 * 2 ^ 59
def prefixEnd_6053675 : Nat := 4983230072969 + 3 ^ 40 * 6053675 * 2
def baseEnd_6053675 : Nat := 345382777900745300269129

theorem tailTrace_6053675 : CollatzResearch.WordTrace tailWord_6053675 prefixEnd_6053675 345382777900745300269129 := by
  unfold tailWord_6053675
  simp only [CollatzResearch.WordTrace]
  refine ⟨220795666343576835223290479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147197110895717890148860319 220795666343576835223290479)
  ·
    refine ⟨331193499515365252834935719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220795666343576835223290479 331193499515365252834935719)
    ·
      refine ⟨496790249273047879252403579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331193499515365252834935719 496790249273047879252403579)
      ·
        refine ⟨745185373909571818878605369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496790249273047879252403579 745185373909571818878605369)
        ·
          refine ⟨558889030432178864158954027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745185373909571818878605369 558889030432178864158954027)
          ·
            refine ⟨838333545648268296238431041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558889030432178864158954027 838333545648268296238431041)
            ·
              refine ⟨628750159236201222178823281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838333545648268296238431041 628750159236201222178823281)
              ·
                refine ⟨471562619427150916634117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628750159236201222178823281 471562619427150916634117461)
                ·
                  refine ⟨345382777900745300269129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 471562619427150916634117461 345382777900745300269129)
                  ·
                    rfl

theorem cell23_6053675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_6053675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053675 prefixEnd_6053675 := by exact prefixLift 6053675
  have htrace : WordTrace (prefixWord ++ tailWord_6053675) baseStart_6053675 baseEnd_6053675 := by
    simpa [prefixWord, tailWord_6053675, baseEnd_6053675] using wordTrace_append hprefix tailTrace_6053675
  have hstable : (prefixWord ++ tailWord_6053675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053675).length < 2 ^ (prefixWord ++ tailWord_6053675).sum := by decide
  have hdescent : baseEnd_6053675 < baseStart_6053675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053730 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6053730 : Nat := 118140960795 + 6053730 * 2 ^ 59
def prefixEnd_6053730 : Nat := 4983230072969 + 3 ^ 40 * 6053730 * 2
def baseEnd_6053730 : Nat := 1036157747514234995744803

theorem tailTrace_6053730 : CollatzResearch.WordTrace tailWord_6053730 prefixEnd_6053730 1036157747514234995744803 := by
  unfold tailWord_6053730
  simp only [CollatzResearch.WordTrace]
  refine ⟨55199418089594394904135661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147198448238918386411028429 55199418089594394904135661)
  ·
    refine ⟨20699781783597898089050873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55199418089594394904135661 20699781783597898089050873)
    ·
      refine ⟨15524836337698423566788155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20699781783597898089050873 15524836337698423566788155)
      ·
        refine ⟨23287254506547635350182233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524836337698423566788155 23287254506547635350182233)
        ·
          refine ⟨17465440879910726512636675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23287254506547635350182233 17465440879910726512636675)
          ·
            refine ⟨26198161319866089768955013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17465440879910726512636675 26198161319866089768955013)
            ·
              refine ⟨4912155247474891831679065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26198161319866089768955013 4912155247474891831679065)
              ·
                refine ⟨3684116435606168873759299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912155247474891831679065 3684116435606168873759299)
                ·
                  refine ⟨5526174653409253310638949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684116435606168873759299 5526174653409253310638949)
                  ·
                    refine ⟨1036157747514234995744803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526174653409253310638949 1036157747514234995744803)
                    ·
                      rfl

theorem cell23_6053730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6053730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053730 prefixEnd_6053730 := by exact prefixLift 6053730
  have htrace : WordTrace (prefixWord ++ tailWord_6053730) baseStart_6053730 baseEnd_6053730 := by
    simpa [prefixWord, tailWord_6053730, baseEnd_6053730] using wordTrace_append hprefix tailTrace_6053730
  have hstable : (prefixWord ++ tailWord_6053730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053730).length < 2 ^ (prefixWord ++ tailWord_6053730).sum := by decide
  have hdescent : baseEnd_6053730 < baseStart_6053730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053736 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6053736 : Nat := 118140960795 + 6053736 * 2 ^ 59
def prefixEnd_6053736 : Nat := 4983230072969 + 3 ^ 40 * 6053736 * 2
def baseEnd_6053736 : Nat := 3108476323426631963759381

theorem tailTrace_6053736 : CollatzResearch.WordTrace tailWord_6053736 prefixEnd_6053736 3108476323426631963759381 := by
  unfold tailWord_6053736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110398945598177921320630531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147198594130903895094174041 110398945598177921320630531)
  ·
    refine ⟨165598418397266881980945797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110398945598177921320630531 165598418397266881980945797)
    ·
      refine ⟨31049703449487540371427337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165598418397266881980945797 31049703449487540371427337)
      ·
        refine ⟨23287277587115655278570503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31049703449487540371427337 23287277587115655278570503)
        ·
          refine ⟨34930916380673482917855755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23287277587115655278570503 34930916380673482917855755)
          ·
            refine ⟨52396374571010224376783633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34930916380673482917855755 52396374571010224376783633)
            ·
              refine ⟨39297280928257668282587725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52396374571010224376783633 39297280928257668282587725)
              ·
                refine ⟨14736480348096625605970397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39297280928257668282587725 14736480348096625605970397)
                ·
                  refine ⟨5526180130536234602238899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14736480348096625605970397 5526180130536234602238899)
                  ·
                    refine ⟨8289270195804351903358349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526180130536234602238899 8289270195804351903358349)
                    ·
                      refine ⟨3108476323426631963759381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289270195804351903358349 3108476323426631963759381)
                      ·
                        rfl

theorem cell23_6053736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6053736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053736 prefixEnd_6053736 := by exact prefixLift 6053736
  have htrace : WordTrace (prefixWord ++ tailWord_6053736) baseStart_6053736 baseEnd_6053736 := by
    simpa [prefixWord, tailWord_6053736, baseEnd_6053736] using wordTrace_append hprefix tailTrace_6053736
  have hstable : (prefixWord ++ tailWord_6053736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053736).length < 2 ^ (prefixWord ++ tailWord_6053736).sum := by decide
  have hdescent : baseEnd_6053736 < baseStart_6053736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_6053759 : Nat := 118140960795 + 6053759 * 2 ^ 59
def prefixEnd_6053759 : Nat := 4983230072969 + 3 ^ 40 * 6053759 * 2
def baseEnd_6053759 : Nat := 3108488133481685373771775

theorem tailTrace_6053759 : CollatzResearch.WordTrace tailWord_6053759 prefixEnd_6053759 3108488133481685373771775 := by
  unfold tailWord_6053759
  simp only [CollatzResearch.WordTrace]
  refine ⟨220798730075272517569348331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147199153383515011712898887 220798730075272517569348331)
  ·
    refine ⟨331198095112908776354022497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220798730075272517569348331 331198095112908776354022497)
    ·
      refine ⟨248398571334681582265516873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331198095112908776354022497 248398571334681582265516873)
      ·
        refine ⟨186298928501011186699137655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248398571334681582265516873 186298928501011186699137655)
        ·
          refine ⟨279448392751516780048706483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186298928501011186699137655 279448392751516780048706483)
          ·
            refine ⟨419172589127275170073059725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279448392751516780048706483 419172589127275170073059725)
            ·
              refine ⟨157189720922728188777397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419172589127275170073059725 157189720922728188777397397)
              ·
                refine ⟨7368268168252883848940503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157189720922728188777397397 7368268168252883848940503)
                ·
                  refine ⟨11052402252379325773410755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368268168252883848940503 11052402252379325773410755)
                  ·
                    refine ⟨16578603378568988660116133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11052402252379325773410755 16578603378568988660116133)
                    ·
                      refine ⟨3108488133481685373771775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16578603378568988660116133 3108488133481685373771775)
                      ·
                        rfl

theorem cell23_6053759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_6053759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053759 prefixEnd_6053759 := by exact prefixLift 6053759
  have htrace : WordTrace (prefixWord ++ tailWord_6053759) baseStart_6053759 baseEnd_6053759 := by
    simpa [prefixWord, tailWord_6053759, baseEnd_6053759] using wordTrace_append hprefix tailTrace_6053759
  have hstable : (prefixWord ++ tailWord_6053759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053759).length < 2 ^ (prefixWord ++ tailWord_6053759).sum := by decide
  have hdescent : baseEnd_6053759 < baseStart_6053759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053763 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 2, 3, 2]
def baseStart_6053763 : Nat := 118140960795 + 6053763 * 2 ^ 59
def prefixEnd_6053763 : Nat := 4983230072969 + 3 ^ 40 * 6053763 * 2
def baseEnd_6053763 : Nat := 3108490187404303358121757

theorem tailTrace_6053763 : CollatzResearch.WordTrace tailWord_6053763 prefixEnd_6053763 3108490187404303358121757 := by
  unfold tailWord_6053763
  simp only [CollatzResearch.WordTrace]
  refine ⟨220798875967258026252493943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147199250644838684168329295 220798875967258026252493943)
  ·
    refine ⟨331198313950887039378740915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220798875967258026252493943 331198313950887039378740915)
    ·
      refine ⟨496797470926330559068111373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331198313950887039378740915 496797470926330559068111373)
      ·
        refine ⟨186299051597373959650541765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496797470926330559068111373 186299051597373959650541765)
        ·
          refine ⟨34931072174507617434476581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186299051597373959650541765 34931072174507617434476581)
          ·
            refine ⟨6549576032720178268964359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34931072174507617434476581 6549576032720178268964359)
            ·
              refine ⟨9824364049080267403446539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549576032720178268964359 9824364049080267403446539)
              ·
                refine ⟨14736546073620401105169809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824364049080267403446539 14736546073620401105169809)
                ·
                  refine ⟨11052409555215300828877357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14736546073620401105169809 11052409555215300828877357)
                  ·
                    refine ⟨4144653583205737810829009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11052409555215300828877357 4144653583205737810829009)
                    ·
                      refine ⟨3108490187404303358121757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144653583205737810829009 3108490187404303358121757)
                      ·
                        rfl

theorem cell23_6053763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_6053763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053763 prefixEnd_6053763 := by exact prefixLift 6053763
  have htrace : WordTrace (prefixWord ++ tailWord_6053763) baseStart_6053763 baseEnd_6053763 := by
    simpa [prefixWord, tailWord_6053763, baseEnd_6053763] using wordTrace_append hprefix tailTrace_6053763
  have hstable : (prefixWord ++ tailWord_6053763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053763).length < 2 ^ (prefixWord ++ tailWord_6053763).sum := by decide
  have hdescent : baseEnd_6053763 < baseStart_6053763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053769 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_6053769 : Nat := 118140960795 + 6053769 * 2 ^ 59
def prefixEnd_6053769 : Nat := 4983230072969 + 3 ^ 40 * 6053769 * 2
def baseEnd_6053769 : Nat := 1036164422762743444882243

theorem tailTrace_6053769 : CollatzResearch.WordTrace tailWord_6053769 prefixEnd_6053769 1036164422762743444882243 := by
  unfold tailWord_6053769
  simp only [CollatzResearch.WordTrace]
  refine ⟨220799094805236289277212361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147199396536824192851474907 220799094805236289277212361)
  ·
    refine ⟨165599321103927216957909271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220799094805236289277212361 165599321103927216957909271)
    ·
      refine ⟨248398981655890825436863907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165599321103927216957909271 248398981655890825436863907)
      ·
        refine ⟨372598472483836238155295861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248398981655890825436863907 372598472483836238155295861)
        ·
          refine ⟨34931106795359647327058987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372598472483836238155295861 34931106795359647327058987)
          ·
            refine ⟨52396660193039470990588481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34931106795359647327058987 52396660193039470990588481)
            ·
              refine ⟨39297495144779603242941361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52396660193039470990588481 39297495144779603242941361)
              ·
                refine ⟨29473121358584702432206021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39297495144779603242941361 29473121358584702432206021)
                ·
                  refine ⟨5526210254734631706038629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29473121358584702432206021 5526210254734631706038629)
                  ·
                    refine ⟨1036164422762743444882243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526210254734631706038629 1036164422762743444882243)
                    ·
                      rfl

theorem cell23_6053769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_6053769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053769 prefixEnd_6053769 := by exact prefixLift 6053769
  have htrace : WordTrace (prefixWord ++ tailWord_6053769) baseStart_6053769 baseEnd_6053769 := by
    simpa [prefixWord, tailWord_6053769, baseEnd_6053769] using wordTrace_append hprefix tailTrace_6053769
  have hstable : (prefixWord ++ tailWord_6053769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053769).length < 2 ^ (prefixWord ++ tailWord_6053769).sum := by decide
  have hdescent : baseEnd_6053769 < baseStart_6053769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053772 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6053772 : Nat := 118140960795 + 6053772 * 2 ^ 59
def prefixEnd_6053772 : Nat := 4983230072969 + 3 ^ 40 * 6053772 * 2
def baseEnd_6053772 : Nat := 3108494808730193822909215

theorem tailTrace_6053772 : CollatzResearch.WordTrace tailWord_6053772 prefixEnd_6053772 3108494808730193822909215 := by
  unfold tailWord_6053772
  simp only [CollatzResearch.WordTrace]
  refine ⟨110399602112112710394785785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147199469482816947193047713 110399602112112710394785785)
  ·
    refine ⟨82799701584084532796089339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110399602112112710394785785 82799701584084532796089339)
    ·
      refine ⟨124199552376126799194134009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82799701584084532796089339 124199552376126799194134009)
      ·
        refine ⟨93149664282095099395600507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124199552376126799194134009 93149664282095099395600507)
        ·
          refine ⟨139724496423142649093400761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93149664282095099395600507 139724496423142649093400761)
          ·
            refine ⟨104793372317356986820050571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139724496423142649093400761 104793372317356986820050571)
            ·
              refine ⟨157190058476035480230075857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104793372317356986820050571 157190058476035480230075857)
              ·
                refine ⟨117892543857026610172556893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157190058476035480230075857 117892543857026610172556893)
                ·
                  refine ⟨44209703946384978814708835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117892543857026610172556893 44209703946384978814708835)
                  ·
                    refine ⟨66314555919577468222063253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44209703946384978814708835 66314555919577468222063253)
                    ·
                      refine ⟨3108494808730193822909215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66314555919577468222063253 3108494808730193822909215)
                      ·
                        rfl

theorem cell23_6053772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6053772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053772 prefixEnd_6053772 := by exact prefixLift 6053772
  have htrace : WordTrace (prefixWord ++ tailWord_6053772) baseStart_6053772 baseEnd_6053772 := by
    simpa [prefixWord, tailWord_6053772, baseEnd_6053772] using wordTrace_append hprefix tailTrace_6053772
  have hstable : (prefixWord ++ tailWord_6053772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053772).length < 2 ^ (prefixWord ++ tailWord_6053772).sum := by decide
  have hdescent : baseEnd_6053772 < baseStart_6053772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053786 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_6053786 : Nat := 118140960795 + 6053786 * 2 ^ 59
def prefixEnd_6053786 : Nat := 4983230072969 + 3 ^ 40 * 6053786 * 2
def baseEnd_6053786 : Nat := 1036167332486452256044717

theorem tailTrace_6053786 : CollatzResearch.WordTrace tailWord_6053786 prefixEnd_6053786 1036167332486452256044717 := by
  unfold tailWord_6053786
  simp only [CollatzResearch.WordTrace]
  refine ⟨55199928711543675295145303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147199809897449800787054141 55199928711543675295145303)
  ·
    refine ⟨82799893067315512942717955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55199928711543675295145303 82799893067315512942717955)
    ·
      refine ⟨124199839600973269414076933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82799893067315512942717955 124199839600973269414076933)
      ·
        refine ⟨23287469925182488015139425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124199839600973269414076933 23287469925182488015139425)
        ·
          refine ⟨17465602443886866011354569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23287469925182488015139425 17465602443886866011354569)
          ·
            refine ⟨13099201832915149508515927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465602443886866011354569 13099201832915149508515927)
            ·
              refine ⟨19648802749372724262773891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099201832915149508515927 19648802749372724262773891)
              ·
                refine ⟨29473204124059086394160837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19648802749372724262773891 29473204124059086394160837)
                ·
                  refine ⟨5526225773261078698905157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29473204124059086394160837 5526225773261078698905157)
                  ·
                    refine ⟨1036167332486452256044717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526225773261078698905157 1036167332486452256044717)
                    ·
                      rfl

theorem cell23_6053786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_6053786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053786 prefixEnd_6053786 := by exact prefixLift 6053786
  have htrace : WordTrace (prefixWord ++ tailWord_6053786) baseStart_6053786 baseEnd_6053786 := by
    simpa [prefixWord, tailWord_6053786, baseEnd_6053786] using wordTrace_append hprefix tailTrace_6053786
  have hstable : (prefixWord ++ tailWord_6053786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053786).length < 2 ^ (prefixWord ++ tailWord_6053786).sum := by decide
  have hdescent : baseEnd_6053786 < baseStart_6053786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6053792 : Nat := 118140960795 + 6053792 * 2 ^ 59
def prefixEnd_6053792 : Nat := 4983230072969 + 3 ^ 40 * 6053792 * 2
def baseEnd_6053792 : Nat := 3108505078343283744659123

theorem tailTrace_6053792 : CollatzResearch.WordTrace tailWord_6053792 prefixEnd_6053792 3108505078343283744659123 := by
  unfold tailWord_6053792
  simp only [CollatzResearch.WordTrace]
  refine ⟨110399966842076482102649815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147199955789435309470199753 110399966842076482102649815)
  ·
    refine ⟨165599950263114723153974723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110399966842076482102649815 165599950263114723153974723)
    ·
      refine ⟨248399925394672084730962085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165599950263114723153974723 248399925394672084730962085)
      ·
        refine ⟨46574986011501015887055391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248399925394672084730962085 46574986011501015887055391)
        ·
          refine ⟨69862479017251523830583087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46574986011501015887055391 69862479017251523830583087)
          ·
            refine ⟨104793718525877285745874631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69862479017251523830583087 104793718525877285745874631)
            ·
              refine ⟨157190577788815928618811947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104793718525877285745874631 157190577788815928618811947)
              ·
                refine ⟨235785866683223892928217921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157190577788815928618811947 235785866683223892928217921)
                ·
                  refine ⟨176839400012417919696163441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235785866683223892928217921 176839400012417919696163441)
                  ·
                    refine ⟨132629550009313439772122581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176839400012417919696163441 132629550009313439772122581)
                    ·
                      refine ⟨3108505078343283744659123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132629550009313439772122581 3108505078343283744659123)
                      ·
                        rfl

theorem cell23_6053792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6053792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053792 prefixEnd_6053792 := by exact prefixLift 6053792
  have htrace : WordTrace (prefixWord ++ tailWord_6053792) baseStart_6053792 baseEnd_6053792 := by
    simpa [prefixWord, tailWord_6053792, baseEnd_6053792] using wordTrace_append hprefix tailTrace_6053792
  have hstable : (prefixWord ++ tailWord_6053792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053792).length < 2 ^ (prefixWord ++ tailWord_6053792).sum := by decide
  have hdescent : baseEnd_6053792 < baseStart_6053792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053813 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_6053813 : Nat := 118140960795 + 6053813 * 2 ^ 59
def prefixEnd_6053813 : Nat := 4983230072969 + 3 ^ 40 * 6053813 * 2
def baseEnd_6053813 : Nat := 3108515861437028162496527

theorem tailTrace_6053813 : CollatzResearch.WordTrace tailWord_6053813 prefixEnd_6053813 3108515861437028162496527 := by
  unfold tailWord_6053813
  simp only [CollatzResearch.WordTrace]
  refine ⟨220800699617076884791814093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147200466411384589861209395 220800699617076884791814093)
  ·
    refine ⟨82800262356403831796930285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220800699617076884791814093 82800262356403831796930285)
    ·
      refine ⟨31050098383651436923848857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82800262356403831796930285 31050098383651436923848857)
      ·
        refine ⟨23287573787738577692886643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31050098383651436923848857 23287573787738577692886643)
        ·
          refine ⟨34931360681607866539329965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23287573787738577692886643 34931360681607866539329965)
          ·
            refine ⟨13099260255602949952248737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34931360681607866539329965 13099260255602949952248737)
            ·
              refine ⟨9824445191702212464186553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13099260255602949952248737 9824445191702212464186553)
              ·
                refine ⟨7368333893776659348139915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9824445191702212464186553 7368333893776659348139915)
                ·
                  refine ⟨11052500840664989022209873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368333893776659348139915 11052500840664989022209873)
                  ·
                    refine ⟨8289375630498741766657405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11052500840664989022209873 8289375630498741766657405)
                    ·
                      refine ⟨3108515861437028162496527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289375630498741766657405 3108515861437028162496527)
                      ·
                        rfl

theorem cell23_6053813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_6053813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053813 prefixEnd_6053813 := by exact prefixLift 6053813
  have htrace : WordTrace (prefixWord ++ tailWord_6053813) baseStart_6053813 baseEnd_6053813 := by
    simpa [prefixWord, tailWord_6053813, baseEnd_6053813] using wordTrace_append hprefix tailTrace_6053813
  have hstable : (prefixWord ++ tailWord_6053813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053813).length < 2 ^ (prefixWord ++ tailWord_6053813).sum := by decide
  have hdescent : baseEnd_6053813 < baseStart_6053813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053870 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_6053870 : Nat := 118140960795 + 6053870 * 2 ^ 59
def prefixEnd_6053870 : Nat := 4983230072969 + 3 ^ 40 * 6053870 * 2
def baseEnd_6053870 : Nat := 3108545129834334439483765

theorem tailTrace_6053870 : CollatzResearch.WordTrace tailWord_6053870 prefixEnd_6053870 3108545129834334439483765 := by
  unfold tailWord_6053870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27600347322233797940829883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147201852385246922351092709 27600347322233797940829883)
  ·
    refine ⟨41400520983350696911244825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27600347322233797940829883 41400520983350696911244825)
    ·
      refine ⟨31050390737513022683433619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41400520983350696911244825 31050390737513022683433619)
      ·
        refine ⟨46575586106269534025150429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31050390737513022683433619 46575586106269534025150429)
        ·
          refine ⟨17465844789851075259431411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46575586106269534025150429 17465844789851075259431411)
          ·
            refine ⟨26198767184776612889147117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17465844789851075259431411 26198767184776612889147117)
            ·
              refine ⟨9824537694291229833430169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26198767184776612889147117 9824537694291229833430169)
              ·
                refine ⟨7368403270718422375072627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9824537694291229833430169 7368403270718422375072627)
                ·
                  refine ⟨11052604906077633562608941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368403270718422375072627 11052604906077633562608941)
                  ·
                    refine ⟨4144726839779112585978353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11052604906077633562608941 4144726839779112585978353)
                    ·
                      refine ⟨3108545129834334439483765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144726839779112585978353 3108545129834334439483765)
                      ·
                        rfl

theorem cell23_6053870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_6053870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053870 prefixEnd_6053870 := by exact prefixLift 6053870
  have htrace : WordTrace (prefixWord ++ tailWord_6053870) baseStart_6053870 baseEnd_6053870 := by
    simpa [prefixWord, tailWord_6053870, baseEnd_6053870] using wordTrace_append hprefix tailTrace_6053870
  have hstable : (prefixWord ++ tailWord_6053870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053870).length < 2 ^ (prefixWord ++ tailWord_6053870).sum := by decide
  have hdescent : baseEnd_6053870 < baseStart_6053870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053900 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_6053900 : Nat := 118140960795 + 6053900 * 2 ^ 59
def prefixEnd_6053900 : Nat := 4983230072969 + 3 ^ 40 * 6053900 * 2
def baseEnd_6053900 : Nat := 3108560534253969322108627

theorem tailTrace_6053900 : CollatzResearch.WordTrace tailWord_6053900 prefixEnd_6053900 3108560534253969322108627 := by
  unfold tailWord_6053900
  simp only [CollatzResearch.WordTrace]
  refine ⟨110401936383880849325115577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147202581845174465766820769 110401936383880849325115577)
  ·
    refine ⟨82801452287910636993836683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110401936383880849325115577 82801452287910636993836683)
    ·
      refine ⟨124202178431865955490755025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82801452287910636993836683 124202178431865955490755025)
      ·
        refine ⟨93151633823899466618066269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124202178431865955490755025 93151633823899466618066269)
        ·
          refine ⟨34931862683962299981774851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93151633823899466618066269 34931862683962299981774851)
          ·
            refine ⟨52397794025943449972662277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34931862683962299981774851 52397794025943449972662277)
            ·
              refine ⟨9824586379864396869874177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52397794025943449972662277 9824586379864396869874177)
              ·
                refine ⟨7368439784898297652405633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9824586379864396869874177 7368439784898297652405633)
                ·
                  refine ⟨5526329838673723239304225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368439784898297652405633 5526329838673723239304225)
                  ·
                    refine ⟨4144747379005292429478169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526329838673723239304225 4144747379005292429478169)
                    ·
                      refine ⟨3108560534253969322108627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144747379005292429478169 3108560534253969322108627)
                      ·
                        rfl

theorem cell23_6053900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_6053900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053900 prefixEnd_6053900 := by exact prefixLift 6053900
  have htrace : WordTrace (prefixWord ++ tailWord_6053900) baseStart_6053900 baseEnd_6053900 := by
    simpa [prefixWord, tailWord_6053900, baseEnd_6053900] using wordTrace_append hprefix tailTrace_6053900
  have hstable : (prefixWord ++ tailWord_6053900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053900).length < 2 ^ (prefixWord ++ tailWord_6053900).sum := by decide
  have hdescent : baseEnd_6053900 < baseStart_6053900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053916 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6053916 : Nat := 118140960795 + 6053916 * 2 ^ 59
def prefixEnd_6053916 : Nat := 4983230072969 + 3 ^ 40 * 6053916 * 2
def baseEnd_6053916 : Nat := 3108568749944441259508553

theorem tailTrace_6053916 : CollatzResearch.WordTrace tailWord_6053916 prefixEnd_6053916 3108568749944441259508553 := by
  unfold tailWord_6053916
  simp only [CollatzResearch.WordTrace]
  refine ⟨110402228167851866691406801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147202970890469155588542401 110402228167851866691406801)
  ·
    refine ⟨82801671125888900018555101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110402228167851866691406801 82801671125888900018555101)
    ·
      refine ⟨31050626672208337506958163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82801671125888900018555101 31050626672208337506958163)
      ·
        refine ⟨46575940008312506260437245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31050626672208337506958163 46575940008312506260437245)
        ·
          refine ⟨17465977503117189847663967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46575940008312506260437245 17465977503117189847663967)
          ·
            refine ⟨26198966254675784771495951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17465977503117189847663967 26198966254675784771495951)
            ·
              refine ⟨39298449382013677157243927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26198966254675784771495951 39298449382013677157243927)
              ·
                refine ⟨58947674073020515735865891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39298449382013677157243927 58947674073020515735865891)
                ·
                  refine ⟨88421511109530773603798837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58947674073020515735865891 88421511109530773603798837)
                  ·
                    refine ⟨8289516666518510025356141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88421511109530773603798837 8289516666518510025356141)
                    ·
                      refine ⟨3108568749944441259508553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289516666518510025356141 3108568749944441259508553)
                      ·
                        rfl

theorem cell23_6053916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6053916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053916 prefixEnd_6053916 := by exact prefixLift 6053916
  have htrace : WordTrace (prefixWord ++ tailWord_6053916) baseStart_6053916 baseEnd_6053916 := by
    simpa [prefixWord, tailWord_6053916, baseEnd_6053916] using wordTrace_append hprefix tailTrace_6053916
  have hstable : (prefixWord ++ tailWord_6053916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053916).length < 2 ^ (prefixWord ++ tailWord_6053916).sum := by decide
  have hdescent : baseEnd_6053916 < baseStart_6053916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053919 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 7]
def baseStart_6053919 : Nat := 118140960795 + 6053919 * 2 ^ 59
def prefixEnd_6053919 : Nat := 4983230072969 + 3 ^ 40 * 6053919 * 2
def baseEnd_6053919 : Nat := 1036190096795468249257013

theorem tailTrace_6053919 : CollatzResearch.WordTrace tailWord_6053919 prefixEnd_6053919 1036190096795468249257013 := by
  unfold tailWord_6053919
  simp only [CollatzResearch.WordTrace]
  refine ⟨220804565754692864895172811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147203043836461909930115207 220804565754692864895172811)
  ·
    refine ⟨331206848632039297342759217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220804565754692864895172811 331206848632039297342759217)
    ·
      refine ⟨248405136474029473007069413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331206848632039297342759217 248405136474029473007069413)
      ·
        refine ⟨46575963088880526188825515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248405136474029473007069413 46575963088880526188825515)
        ·
          refine ⟨69863944633320789283238273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46575963088880526188825515 69863944633320789283238273)
          ·
            refine ⟨52397958474990591962428705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69863944633320789283238273 52397958474990591962428705)
            ·
              refine ⟨39298468856242943971821529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52397958474990591962428705 39298468856242943971821529)
              ·
                refine ⟨29473851642182207978866147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39298468856242943971821529 29473851642182207978866147)
                ·
                  refine ⟨44210777463273311968299221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29473851642182207978866147 44210777463273311968299221)
                  ·
                    refine ⟨1036190096795468249257013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44210777463273311968299221 1036190096795468249257013)
                    ·
                      rfl

theorem cell23_6053919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_6053919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053919 prefixEnd_6053919 := by exact prefixLift 6053919
  have htrace : WordTrace (prefixWord ++ tailWord_6053919) baseStart_6053919 baseEnd_6053919 := by
    simpa [prefixWord, tailWord_6053919, baseEnd_6053919] using wordTrace_append hprefix tailTrace_6053919
  have hstable : (prefixWord ++ tailWord_6053919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053919).length < 2 ^ (prefixWord ++ tailWord_6053919).sum := by decide
  have hdescent : baseEnd_6053919 < baseStart_6053919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053936 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_6053936 : Nat := 118140960795 + 6053936 * 2 ^ 59
def prefixEnd_6053936 : Nat := 4983230072969 + 3 ^ 40 * 6053936 * 2
def baseEnd_6053936 : Nat := 1036193006519177060419487

theorem tailTrace_6053936 : CollatzResearch.WordTrace tailWord_6053936 prefixEnd_6053936 1036193006519177060419487 := by
  unfold tailWord_6053936
  simp only [CollatzResearch.WordTrace]
  refine ⟨110402592897815638399270831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147203457197087517865694441 110402592897815638399270831)
  ·
    refine ⟨165603889346723457598906247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110402592897815638399270831 165603889346723457598906247)
    ·
      refine ⟨248405834020085186398359371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165603889346723457598906247 248405834020085186398359371)
      ·
        refine ⟨372608751030127779597539057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248405834020085186398359371 372608751030127779597539057)
        ·
          refine ⟨279456563272595834698154293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372608751030127779597539057 279456563272595834698154293)
          ·
            refine ⟨26199052806805859502951965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279456563272595834698154293 26199052806805859502951965)
            ·
              refine ⟨9824644802552197313606987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26199052806805859502951965 9824644802552197313606987)
              ·
                refine ⟨14736967203828295970410481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824644802552197313606987 14736967203828295970410481)
                ·
                  refine ⟨11052725402871221977807861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14736967203828295970410481 11052725402871221977807861)
                  ·
                    refine ⟨1036193006519177060419487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11052725402871221977807861 1036193006519177060419487)
                    ·
                      rfl

theorem cell23_6053936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_6053936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053936 prefixEnd_6053936 := by exact prefixLift 6053936
  have htrace : WordTrace (prefixWord ++ tailWord_6053936) baseStart_6053936 baseEnd_6053936 := by
    simpa [prefixWord, tailWord_6053936, baseEnd_6053936] using wordTrace_append hprefix tailTrace_6053936
  have hstable : (prefixWord ++ tailWord_6053936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053936).length < 2 ^ (prefixWord ++ tailWord_6053936).sum := by decide
  have hdescent : baseEnd_6053936 < baseStart_6053936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053969 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_6053969 : Nat := 118140960795 + 6053969 * 2 ^ 59
def prefixEnd_6053969 : Nat := 4983230072969 + 3 ^ 40 * 6053969 * 2
def baseEnd_6053969 : Nat := 3108595964419129552145809

theorem tailTrace_6053969 : CollatzResearch.WordTrace tailWord_6053969 prefixEnd_6053969 3108595964419129552145809 := by
  unfold tailWord_6053969
  simp only [CollatzResearch.WordTrace]
  refine ⟨220806389404511723434492961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147204259603007815622995307 220806389404511723434492961)
  ·
    refine ⟨165604792053383792575869721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220806389404511723434492961 165604792053383792575869721)
    ·
      refine ⟨124203594040037844431902291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165604792053383792575869721 124203594040037844431902291)
      ·
        refine ⟨186305391060056766647853437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124203594040037844431902291 186305391060056766647853437)
        ·
          refine ⟨69864521647521287492945039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186305391060056766647853437 69864521647521287492945039)
          ·
            refine ⟨104796782471281931239417559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69864521647521287492945039 104796782471281931239417559)
            ·
              refine ⟨157195173706922896859126339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104796782471281931239417559 157195173706922896859126339)
              ·
                refine ⟨235792760560384345288689509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157195173706922896859126339 235792760560384345288689509)
                ·
                  refine ⟨44211142605072064741629283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235792760560384345288689509 44211142605072064741629283)
                  ·
                    refine ⟨66316713907608097112443925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44211142605072064741629283 66316713907608097112443925)
                    ·
                      refine ⟨3108595964419129552145809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66316713907608097112443925 3108595964419129552145809)
                      ·
                        rfl

theorem cell23_6053969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_6053969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053969 prefixEnd_6053969 := by exact prefixLift 6053969
  have htrace : WordTrace (prefixWord ++ tailWord_6053969) baseStart_6053969 baseEnd_6053969 := by
    simpa [prefixWord, tailWord_6053969, baseEnd_6053969] using wordTrace_append hprefix tailTrace_6053969
  have hstable : (prefixWord ++ tailWord_6053969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053969).length < 2 ^ (prefixWord ++ tailWord_6053969).sum := by decide
  have hdescent : baseEnd_6053969 < baseStart_6053969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053973 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6053973 : Nat := 118140960795 + 6053973 * 2 ^ 59
def prefixEnd_6053973 : Nat := 4983230072969 + 3 ^ 40 * 6053973 * 2
def baseEnd_6053973 : Nat := 3108598018341747536495791

theorem tailTrace_6053973 : CollatzResearch.WordTrace tailWord_6053973 prefixEnd_6053973 3108598018341747536495791 := by
  unfold tailWord_6053973
  simp only [CollatzResearch.WordTrace]
  refine ⟨220806535296497232117638573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147204356864331488078425715 220806535296497232117638573)
  ·
    refine ⟨82802450736186462044114465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220806535296497232117638573 82802450736186462044114465)
    ·
      refine ⟨62101838052139846533085849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82802450736186462044114465 62101838052139846533085849)
      ·
        refine ⟨46576378539104884899814387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62101838052139846533085849 46576378539104884899814387)
        ·
          refine ⟨69864567808657327349721581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46576378539104884899814387 69864567808657327349721581)
          ·
            refine ⟨26199212928246497756145593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69864567808657327349721581 26199212928246497756145593)
            ·
              refine ⟨19649409696184873317109195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26199212928246497756145593 19649409696184873317109195)
              ·
                refine ⟨29474114544277309975663793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19649409696184873317109195 29474114544277309975663793)
                ·
                  refine ⟨22105585908207982481747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29474114544277309975663793 22105585908207982481747845)
                  ·
                    refine ⟨4144797357788996715327721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22105585908207982481747845 4144797357788996715327721)
                    ·
                      refine ⟨3108598018341747536495791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4144797357788996715327721 3108598018341747536495791)
                      ·
                        rfl

theorem cell23_6053973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6053973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053973 prefixEnd_6053973 := by exact prefixLift 6053973
  have htrace : WordTrace (prefixWord ++ tailWord_6053973) baseStart_6053973 baseEnd_6053973 := by
    simpa [prefixWord, tailWord_6053973, baseEnd_6053973] using wordTrace_append hprefix tailTrace_6053973
  have hstable : (prefixWord ++ tailWord_6053973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053973).length < 2 ^ (prefixWord ++ tailWord_6053973).sum := by decide
  have hdescent : baseEnd_6053973 < baseStart_6053973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6053976 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_6053976 : Nat := 118140960795 + 6053976 * 2 ^ 59
def prefixEnd_6053976 : Nat := 4983230072969 + 3 ^ 40 * 6053976 * 2
def baseEnd_6053976 : Nat := 3108599558783711024758277

theorem tailTrace_6053976 : CollatzResearch.WordTrace tailWord_6053976 prefixEnd_6053976 3108599558783711024758277 := by
  unfold tailWord_6053976
  simp only [CollatzResearch.WordTrace]
  refine ⟨110403322357743181814998891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147204429810324242419998521 110403322357743181814998891)
  ·
    refine ⟨165604983536614772722498337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110403322357743181814998891 165604983536614772722498337)
    ·
      refine ⟨124203737652461079541873753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165604983536614772722498337 124203737652461079541873753)
      ·
        refine ⟨93152803239345809656405315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124203737652461079541873753 93152803239345809656405315)
        ·
          refine ⟨139729204859018714484607973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93152803239345809656405315 139729204859018714484607973)
          ·
            refine ⟨26199225911066008965863995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139729204859018714484607973 26199225911066008965863995)
            ·
              refine ⟨39298838866599013448795993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26199225911066008965863995 39298838866599013448795993)
              ·
                refine ⟨29474129149949260086596995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39298838866599013448795993 29474129149949260086596995)
                ·
                  refine ⟨44211193724923890129895493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29474129149949260086596995 44211193724923890129895493)
                  ·
                    refine ⟨8289598823423229399355405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44211193724923890129895493 8289598823423229399355405)
                    ·
                      refine ⟨3108599558783711024758277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289598823423229399355405 3108599558783711024758277)
                      ·
                        rfl

theorem cell23_6053976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_6053976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6053976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6053976 prefixEnd_6053976 := by exact prefixLift 6053976
  have htrace : WordTrace (prefixWord ++ tailWord_6053976) baseStart_6053976 baseEnd_6053976 := by
    simpa [prefixWord, tailWord_6053976, baseEnd_6053976] using wordTrace_append hprefix tailTrace_6053976
  have hstable : (prefixWord ++ tailWord_6053976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6053976).length < 2 ^ (prefixWord ++ tailWord_6053976).sum := by decide
  have hdescent : baseEnd_6053976 < baseStart_6053976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6053976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054000 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 1, 4]
def baseStart_6054000 : Nat := 118140960795 + 6054000 * 2 ^ 59
def prefixEnd_6054000 : Nat := 4983230072969 + 3 ^ 40 * 6054000 * 2
def baseEnd_6054000 : Nat := 1036203960773139643619389

theorem tailTrace_6054000 : CollatzResearch.WordTrace tailWord_6054000 prefixEnd_6054000 1036203960773139643619389 := by
  unfold tailWord_6054000
  simp only [CollatzResearch.WordTrace]
  refine ⟨110403760033699707864435727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147205013378266277152580969 110403760033699707864435727)
  ·
    refine ⟨165605640050549561796653591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110403760033699707864435727 165605640050549561796653591)
    ·
      refine ⟨248408460075824342694980387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165605640050549561796653591 248408460075824342694980387)
      ·
        refine ⟨372612690113736514042470581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248408460075824342694980387 372612690113736514042470581)
        ·
          refine ⟨34932439698162798191481617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372612690113736514042470581 34932439698162798191481617)
          ·
            refine ⟨26199329773622098643611213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34932439698162798191481617 26199329773622098643611213)
            ·
              refine ⟨9824748665108286991354205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26199329773622098643611213 9824748665108286991354205)
              ·
                refine ⟨3684280749415607621757827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9824748665108286991354205 3684280749415607621757827)
                ·
                  refine ⟨5526421124123411432636741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684280749415607621757827 5526421124123411432636741)
                  ·
                    refine ⟨1036203960773139643619389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526421124123411432636741 1036203960773139643619389)
                    ·
                      rfl

theorem cell23_6054000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_6054000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054000 prefixEnd_6054000 := by exact prefixLift 6054000
  have htrace : WordTrace (prefixWord ++ tailWord_6054000) baseStart_6054000 baseEnd_6054000 := by
    simpa [prefixWord, tailWord_6054000, baseEnd_6054000] using wordTrace_append hprefix tailTrace_6054000
  have hstable : (prefixWord ++ tailWord_6054000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054000).length < 2 ^ (prefixWord ++ tailWord_6054000).sum := by decide
  have hdescent : baseEnd_6054000 < baseStart_6054000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054017 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6054017 : Nat := 118140960795 + 6054017 * 2 ^ 59
def prefixEnd_6054017 : Nat := 4983230072969 + 3 ^ 40 * 6054017 * 2
def baseEnd_6054017 : Nat := 1036206870496848454781863

theorem tailTrace_6054017 : CollatzResearch.WordTrace tailWord_6054017 prefixEnd_6054017 1036206870496848454781863 := by
  unfold tailWord_6054017
  simp only [CollatzResearch.WordTrace]
  refine ⟨220808140108337827632240305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147205426738891885088160203 220808140108337827632240305)
  ·
    refine ⟨165606105081253370724180229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220808140108337827632240305 165606105081253370724180229)
    ·
      refine ⟨31051144702735007010783793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165606105081253370724180229 31051144702735007010783793)
      ·
        refine ⟨23288358527051255258087845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31051144702735007010783793 23288358527051255258087845)
        ·
          refine ⟨4366567223822110360891471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23288358527051255258087845 4366567223822110360891471)
          ·
            refine ⟨6549850835733165541337207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366567223822110360891471 6549850835733165541337207)
            ·
              refine ⟨9824776253599748312005811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549850835733165541337207 9824776253599748312005811)
              ·
                refine ⟨14737164380399622468008717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9824776253599748312005811 14737164380399622468008717)
                ·
                  refine ⟨5526436642649858425503269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14737164380399622468008717 5526436642649858425503269)
                  ·
                    refine ⟨1036206870496848454781863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526436642649858425503269 1036206870496848454781863)
                    ·
                      rfl

theorem cell23_6054017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6054017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054017 prefixEnd_6054017 := by exact prefixLift 6054017
  have htrace : WordTrace (prefixWord ++ tailWord_6054017) baseStart_6054017 baseEnd_6054017 := by
    simpa [prefixWord, tailWord_6054017, baseEnd_6054017] using wordTrace_append hprefix tailTrace_6054017
  have hstable : (prefixWord ++ tailWord_6054017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054017).length < 2 ^ (prefixWord ++ tailWord_6054017).sum := by decide
  have hdescent : baseEnd_6054017 < baseStart_6054017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054113 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_6054113 : Nat := 118140960795 + 6054113 * 2 ^ 59
def prefixEnd_6054113 : Nat := 4983230072969 + 3 ^ 40 * 6054113 * 2
def baseEnd_6054113 : Nat := 3108669905633376988745147

theorem tailTrace_6054113 : CollatzResearch.WordTrace tailWord_6054113 prefixEnd_6054113 3108669905633376988745147 := by
  unfold tailWord_6054113
  simp only [CollatzResearch.WordTrace]
  refine ⟨220811641515990036027734993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147207761010660024018489995 220811641515990036027734993)
  ·
    refine ⟨165608731136992527020801245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220811641515990036027734993 165608731136992527020801245)
    ·
      refine ⟨62103274176372197632800467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165608731136992527020801245 62103274176372197632800467)
      ·
        refine ⟨93154911264558296449200701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62103274176372197632800467 93154911264558296449200701)
        ·
          refine ⟨34933091724209361168450263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93154911264558296449200701 34933091724209361168450263)
          ·
            refine ⟨52399637586314041752675395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34933091724209361168450263 52399637586314041752675395)
            ·
              refine ⟨78599456379471062629013093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52399637586314041752675395 78599456379471062629013093)
              ·
                refine ⟨14737398071150824242939955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78599456379471062629013093 14737398071150824242939955)
                ·
                  refine ⟨22106097106726236364409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14737398071150824242939955 22106097106726236364409933)
                  ·
                    refine ⟨8289786415022338636653725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22106097106726236364409933 8289786415022338636653725)
                    ·
                      refine ⟨3108669905633376988745147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289786415022338636653725 3108669905633376988745147)
                      ·
                        rfl

theorem cell23_6054113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_6054113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054113 prefixEnd_6054113 := by exact prefixLift 6054113
  have htrace : WordTrace (prefixWord ++ tailWord_6054113) baseStart_6054113 baseEnd_6054113 := by
    simpa [prefixWord, tailWord_6054113, baseEnd_6054113] using wordTrace_append hprefix tailTrace_6054113
  have hstable : (prefixWord ++ tailWord_6054113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054113).length < 2 ^ (prefixWord ++ tailWord_6054113).sum := by decide
  have hdescent : baseEnd_6054113 < baseStart_6054113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054117 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6054117 : Nat := 118140960795 + 6054117 * 2 ^ 59
def prefixEnd_6054117 : Nat := 4983230072969 + 3 ^ 40 * 6054117 * 2
def baseEnd_6054117 : Nat := 3108671959555994973095129

theorem tailTrace_6054117 : CollatzResearch.WordTrace tailWord_6054117 prefixEnd_6054117 3108671959555994973095129 := by
  unfold tailWord_6054117
  simp only [CollatzResearch.WordTrace]
  refine ⟨220811787407975544710880605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147207858271983696473920403 220811787407975544710880605)
  ·
    refine ⟨82804420277990829266580227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220811787407975544710880605 82804420277990829266580227)
    ·
      refine ⟨124206630416986243899870341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82804420277990829266580227 124206630416986243899870341)
      ·
        refine ⟨23288743203184920731225689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124206630416986243899870341 23288743203184920731225689)
        ·
          refine ⟨17466557402388690548419267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23288743203184920731225689 17466557402388690548419267)
          ·
            refine ⟨26199836103583035822628901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17466557402388690548419267 26199836103583035822628901)
            ·
              refine ⟨4912469269421819216742919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26199836103583035822628901 4912469269421819216742919)
              ·
                refine ⟨7368703904132728825114379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912469269421819216742919 7368703904132728825114379)
                ·
                  refine ⟨11053055856199093237671569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7368703904132728825114379 11053055856199093237671569)
                  ·
                    refine ⟨8289791892149319928253677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11053055856199093237671569 8289791892149319928253677)
                    ·
                      refine ⟨3108671959555994973095129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289791892149319928253677 3108671959555994973095129)
                      ·
                        rfl

theorem cell23_6054117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6054117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054117 prefixEnd_6054117 := by exact prefixLift 6054117
  have htrace : WordTrace (prefixWord ++ tailWord_6054117) baseStart_6054117 baseEnd_6054117 := by
    simpa [prefixWord, tailWord_6054117, baseEnd_6054117] using wordTrace_append hprefix tailTrace_6054117
  have hstable : (prefixWord ++ tailWord_6054117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054117).length < 2 ^ (prefixWord ++ tailWord_6054117).sum := by decide
  have hdescent : baseEnd_6054117 < baseStart_6054117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054136 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_6054136 : Nat := 118140960795 + 6054136 * 2 ^ 59
def prefixEnd_6054136 : Nat := 4983230072969 + 3 ^ 40 * 6054136 * 2
def baseEnd_6054136 : Nat := 3108681715688430398757541

theorem tailTrace_6054136 : CollatzResearch.WordTrace tailWord_6054136 prefixEnd_6054136 3108681715688430398757541 := by
  unfold tailWord_6054136
  simp only [CollatzResearch.WordTrace]
  refine ⟨110406240197453355477911131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147208320263271140637214841 110406240197453355477911131)
  ·
    refine ⟨165609360296180033216866697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110406240197453355477911131 165609360296180033216866697)
    ·
      refine ⟨124207020222135024912650023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165609360296180033216866697 124207020222135024912650023)
      ·
        refine ⟨186310530333202537368975035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124207020222135024912650023 186310530333202537368975035)
        ·
          refine ⟨279465795499803806053462553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186310530333202537368975035 279465795499803806053462553)
          ·
            refine ⟨209599346624852854540096915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279465795499803806053462553 209599346624852854540096915)
            ·
              refine ⟨314399019937279281810145373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209599346624852854540096915 314399019937279281810145373)
              ·
                refine ⟨117899632476479730678804515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314399019937279281810145373 117899632476479730678804515)
                ·
                  refine ⟨176849448714719596018206773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117899632476479730678804515 176849448714719596018206773)
                  ·
                    refine ⟨16579635817004962126706885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176849448714719596018206773 16579635817004962126706885)
                    ·
                      refine ⟨3108681715688430398757541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16579635817004962126706885 3108681715688430398757541)
                      ·
                        rfl

theorem cell23_6054136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_6054136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054136 prefixEnd_6054136 := by exact prefixLift 6054136
  have htrace : WordTrace (prefixWord ++ tailWord_6054136) baseStart_6054136 baseEnd_6054136 := by
    simpa [prefixWord, tailWord_6054136, baseEnd_6054136] using wordTrace_append hprefix tailTrace_6054136
  have hstable : (prefixWord ++ tailWord_6054136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054136).length < 2 ^ (prefixWord ++ tailWord_6054136).sum := by decide
  have hdescent : baseEnd_6054136 < baseStart_6054136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054147 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 2, 1, 3]
def baseStart_6054147 : Nat := 118140960795 + 6054147 * 2 ^ 59
def prefixEnd_6054147 : Nat := 4983230072969 + 3 ^ 40 * 6054147 * 2
def baseEnd_6054147 : Nat := 3108687363975629855719991

theorem tailTrace_6054147 : CollatzResearch.WordTrace tailWord_6054147 prefixEnd_6054147 3108687363975629855719991 := by
  unfold tailWord_6054147
  simp only [CollatzResearch.WordTrace]
  refine ⟨220812881597866859834472695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147208587731911239889648463 220812881597866859834472695)
  ·
    refine ⟨331219322396800289751709043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220812881597866859834472695 331219322396800289751709043)
    ·
      refine ⟨496828983595200434627563565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331219322396800289751709043 496828983595200434627563565)
      ·
        refine ⟨186310868848200162985336337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496828983595200434627563565 186310868848200162985336337)
        ·
          refine ⟨139733151636150122239002253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186310868848200162985336337 139733151636150122239002253)
          ·
            refine ⟨52399931863556295839625845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139733151636150122239002253 52399931863556295839625845)
            ·
              refine ⟨4912493612208402734964923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52399931863556295839625845 4912493612208402734964923)
              ·
                refine ⟨7368740418312604102447385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912493612208402734964923 7368740418312604102447385)
                ·
                  refine ⟨5526555313734453076835539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368740418312604102447385 5526555313734453076835539)
                  ·
                    refine ⟨8289832970601679615253309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526555313734453076835539 8289832970601679615253309)
                    ·
                      refine ⟨3108687363975629855719991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8289832970601679615253309 3108687363975629855719991)
                      ·
                        rfl

theorem cell23_6054147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_6054147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054147 prefixEnd_6054147 := by exact prefixLift 6054147
  have htrace : WordTrace (prefixWord ++ tailWord_6054147) baseStart_6054147 baseEnd_6054147 := by
    simpa [prefixWord, tailWord_6054147, baseEnd_6054147] using wordTrace_append hprefix tailTrace_6054147
  have hstable : (prefixWord ++ tailWord_6054147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054147).length < 2 ^ (prefixWord ++ tailWord_6054147).sum := by decide
  have hdescent : baseEnd_6054147 < baseStart_6054147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054250 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6054250 : Nat := 118140960795 + 6054250 * 2 ^ 59
def prefixEnd_6054250 : Nat := 4983230072969 + 3 ^ 40 * 6054250 * 2
def baseEnd_6054250 : Nat := 3108740252483042952732017

theorem tailTrace_6054250 : CollatzResearch.WordTrace tailWord_6054250 prefixEnd_6054250 3108740252483042952732017 := by
  unfold tailWord_6054250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55204159579123427106368051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147211092210995805616981469 55204159579123427106368051)
  ·
    refine ⟨82806239368685140659552077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55204159579123427106368051 82806239368685140659552077)
    ·
      refine ⟨31052339763256927747332029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82806239368685140659552077 31052339763256927747332029)
      ·
        refine ⟨11644627411221347905249511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31052339763256927747332029 11644627411221347905249511)
        ·
          refine ⟨17466941116832021857874267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644627411221347905249511 17466941116832021857874267)
          ·
            refine ⟨26200411675248032786811401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17466941116832021857874267 26200411675248032786811401)
            ·
              refine ⟨19650308756436024590108551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26200411675248032786811401 19650308756436024590108551)
              ·
                refine ⟨29475463134654036885162827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19650308756436024590108551 29475463134654036885162827)
                ·
                  refine ⟨44213194701981055327744241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29475463134654036885162827 44213194701981055327744241)
                  ·
                    refine ⟨33159896026485791495808181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44213194701981055327744241 33159896026485791495808181)
                    ·
                      refine ⟨3108740252483042952732017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33159896026485791495808181 3108740252483042952732017)
                      ·
                        rfl

theorem cell23_6054250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6054250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054250 prefixEnd_6054250 := by exact prefixLift 6054250
  have htrace : WordTrace (prefixWord ++ tailWord_6054250) baseStart_6054250 baseEnd_6054250 := by
    simpa [prefixWord, tailWord_6054250, baseEnd_6054250] using wordTrace_append hprefix tailTrace_6054250
  have hstable : (prefixWord ++ tailWord_6054250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054250).length < 2 ^ (prefixWord ++ tailWord_6054250).sum := by decide
  have hdescent : baseEnd_6054250 < baseStart_6054250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054280 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_6054280 : Nat := 118140960795 + 6054280 * 2 ^ 59
def prefixEnd_6054280 : Nat := 4983230072969 + 3 ^ 40 * 6054280 * 2
def baseEnd_6054280 : Nat := 3108755656902677835356879

theorem tailTrace_6054280 : CollatzResearch.WordTrace tailWord_6054280 prefixEnd_6054280 3108755656902677835356879 := by
  unfold tailWord_6054280
  simp only [CollatzResearch.WordTrace]
  refine ⟨110408866253192511774532147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147211821670923349032709529 110408866253192511774532147)
  ·
    refine ⟨165613299379788767661798221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110408866253192511774532147 165613299379788767661798221)
    ·
      refine ⟨62104987267420787873174333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165613299379788767661798221 62104987267420787873174333)
      ·
        refine ⟨23289370225282795452440375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62104987267420787873174333 23289370225282795452440375)
        ·
          refine ⟨34934055337924193178660563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23289370225282795452440375 34934055337924193178660563)
          ·
            refine ⟨52401083006886289767990845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34934055337924193178660563 52401083006886289767990845)
            ·
              refine ⟨19650406127582358662996567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52401083006886289767990845 19650406127582358662996567)
              ·
                refine ⟨29475609191373537994494851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19650406127582358662996567 29475609191373537994494851)
                ·
                  refine ⟨44213413787060306991742277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29475609191373537994494851 44213413787060306991742277)
                  ·
                    refine ⟨8290015085073807560951677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44213413787060306991742277 8290015085073807560951677)
                    ·
                      refine ⟨3108755656902677835356879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8290015085073807560951677 3108755656902677835356879)
                      ·
                        rfl

theorem cell23_6054280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_6054280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054280 prefixEnd_6054280 := by exact prefixLift 6054280
  have htrace : WordTrace (prefixWord ++ tailWord_6054280) baseStart_6054280 baseEnd_6054280 := by
    simpa [prefixWord, tailWord_6054280, baseEnd_6054280] using wordTrace_append hprefix tailTrace_6054280
  have hstable : (prefixWord ++ tailWord_6054280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054280).length < 2 ^ (prefixWord ++ tailWord_6054280).sum := by decide
  have hdescent : baseEnd_6054280 < baseStart_6054280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054303 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6054303 : Nat := 118140960795 + 6054303 * 2 ^ 59
def prefixEnd_6054303 : Nat := 4983230072969 + 3 ^ 40 * 6054303 * 2
def baseEnd_6054303 : Nat := 3108767466957731245369273

theorem tailTrace_6054303 : CollatzResearch.WordTrace tailWord_6054303 prefixEnd_6054303 3108767466957731245369273 := by
  unfold tailWord_6054303
  simp only [CollatzResearch.WordTrace]
  refine ⟨220818571385301698477151563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147212380923534465651434375 220818571385301698477151563)
  ·
    refine ⟨331227857077952547715727345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220818571385301698477151563 331227857077952547715727345)
    ·
      refine ⟨248420892808464410786795509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331227857077952547715727345 248420892808464410786795509)
      ·
        refine ⟨23289458700793538511262079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248420892808464410786795509 23289458700793538511262079)
        ·
          refine ⟨34934188051190307766893119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23289458700793538511262079 34934188051190307766893119)
          ·
            refine ⟨52401282076785461650339679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34934188051190307766893119 52401282076785461650339679)
            ·
              refine ⟨78601923115178192475509519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52401282076785461650339679 78601923115178192475509519)
              ·
                refine ⟨117902884672767288713264279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78601923115178192475509519 117902884672767288713264279)
                ·
                  refine ⟨176854327009150933069896419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117902884672767288713264279 176854327009150933069896419)
                  ·
                    refine ⟨265281490513726399604844629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176854327009150933069896419 265281490513726399604844629)
                    ·
                      refine ⟨3108767466957731245369273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265281490513726399604844629 3108767466957731245369273)
                      ·
                        rfl

theorem cell23_6054303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6054303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054303 prefixEnd_6054303 := by exact prefixLift 6054303
  have htrace : WordTrace (prefixWord ++ tailWord_6054303) baseStart_6054303 baseEnd_6054303 := by
    simpa [prefixWord, tailWord_6054303, baseEnd_6054303] using wordTrace_append hprefix tailTrace_6054303
  have hstable : (prefixWord ++ tailWord_6054303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054303).length < 2 ^ (prefixWord ++ tailWord_6054303).sum := by decide
  have hdescent : baseEnd_6054303 < baseStart_6054303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054313 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_6054313 : Nat := 118140960795 + 6054313 * 2 ^ 59
def prefixEnd_6054313 : Nat := 4983230072969 + 3 ^ 40 * 6054313 * 2
def baseEnd_6054313 : Nat := 1036257533921425402081409

theorem tailTrace_6054313 : CollatzResearch.WordTrace tailWord_6054313 prefixEnd_6054313 1036257533921425402081409 := by
  unfold tailWord_6054313
  simp only [CollatzResearch.WordTrace]
  refine ⟨220818936115265470185015593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147212624076843646790010395 220818936115265470185015593)
  ·
    refine ⟨165614202086449102638761695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220818936115265470185015593 165614202086449102638761695)
    ·
      refine ⟨248421303129673653958142543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165614202086449102638761695 248421303129673653958142543)
      ·
        refine ⟨372631954694510480937213815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248421303129673653958142543 372631954694510480937213815)
        ·
          refine ⟨558947932041765721405820723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372631954694510480937213815 558947932041765721405820723)
          ·
            refine ⟨838421898062648582108731085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558947932041765721405820723 838421898062648582108731085)
            ·
              refine ⟨314408211773493218290774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838421898062648582108731085 314408211773493218290774157)
              ·
                refine ⟨117903079415059956859040309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314408211773493218290774157 117903079415059956859040309)
                ·
                  refine ⟨11053413695161870955535029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117903079415059956859040309 11053413695161870955535029)
                  ·
                    refine ⟨1036257533921425402081409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11053413695161870955535029 1036257533921425402081409)
                    ·
                      rfl

theorem cell23_6054313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_6054313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054313 prefixEnd_6054313 := by exact prefixLift 6054313
  have htrace : WordTrace (prefixWord ++ tailWord_6054313) baseStart_6054313 baseEnd_6054313 := by
    simpa [prefixWord, tailWord_6054313, baseEnd_6054313] using wordTrace_append hprefix tailTrace_6054313
  have hstable : (prefixWord ++ tailWord_6054313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054313).length < 2 ^ (prefixWord ++ tailWord_6054313).sum := by decide
  have hdescent : baseEnd_6054313 < baseStart_6054313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054327 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_6054327 : Nat := 118140960795 + 6054327 * 2 ^ 59
def prefixEnd_6054327 : Nat := 4983230072969 + 3 ^ 40 * 6054327 * 2
def baseEnd_6054327 : Nat := 3108779790493439151469163

theorem tailTrace_6054327 : CollatzResearch.WordTrace tailWord_6054327 prefixEnd_6054327 3108779790493439151469163 := by
  unfold tailWord_6054327
  simp only [CollatzResearch.WordTrace]
  refine ⟨220819446737214750576025235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147212964491476500384016823 220819446737214750576025235)
  ·
    refine ⟨331229170105822125864037853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220819446737214750576025235 331229170105822125864037853)
    ·
      refine ⟨124210938789683297199014195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331229170105822125864037853 124210938789683297199014195)
      ·
        refine ⟨186316408184524945798521293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124210938789683297199014195 186316408184524945798521293)
        ·
          refine ⟨69868653069196854674445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186316408184524945798521293 69868653069196854674445485)
          ·
            refine ⟨26200744900948820502917057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69868653069196854674445485 26200744900948820502917057)
            ·
              refine ⟨19650558675711615377187793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26200744900948820502917057 19650558675711615377187793)
              ·
                refine ⟨14737919006783711532890845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19650558675711615377187793 14737919006783711532890845)
                ·
                  refine ⟨5526719627543891824834067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14737919006783711532890845 5526719627543891824834067)
                  ·
                    refine ⟨8290079441315837737251101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526719627543891824834067 8290079441315837737251101)
                    ·
                      refine ⟨3108779790493439151469163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8290079441315837737251101 3108779790493439151469163)
                      ·
                        rfl

theorem cell23_6054327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_6054327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054327 prefixEnd_6054327 := by exact prefixLift 6054327
  have htrace : WordTrace (prefixWord ++ tailWord_6054327) baseStart_6054327 baseEnd_6054327 := by
    simpa [prefixWord, tailWord_6054327, baseEnd_6054327] using wordTrace_append hprefix tailTrace_6054327
  have hstable : (prefixWord ++ tailWord_6054327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054327).length < 2 ^ (prefixWord ++ tailWord_6054327).sum := by decide
  have hdescent : baseEnd_6054327 < baseStart_6054327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054350 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_6054350 : Nat := 118140960795 + 6054350 * 2 ^ 59
def prefixEnd_6054350 : Nat := 4983230072969 + 3 ^ 40 * 6054350 * 2
def baseEnd_6054350 : Nat := 3108791600548492561481557

theorem tailTrace_6054350 : CollatzResearch.WordTrace tailWord_6054350 prefixEnd_6054350 3108791600548492561481557 := by
  unfold tailWord_6054350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27602535702016428188014063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147213523744087617002741669 27602535702016428188014063)
  ·
    refine ⟨41403803553024642282021095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27602535702016428188014063 41403803553024642282021095)
    ·
      refine ⟨62105705329536963423031643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41403803553024642282021095 62105705329536963423031643)
      ·
        refine ⟨93158557994305445134547465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62105705329536963423031643 93158557994305445134547465)
        ·
          refine ⟨69868918495729083850910599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93158557994305445134547465 69868918495729083850910599)
          ·
            refine ⟨104803377743593625776365899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69868918495729083850910599 104803377743593625776365899)
            ·
              refine ⟨157205066615390438664548849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104803377743593625776365899 157205066615390438664548849)
              ·
                refine ⟨117903799961542828998411637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157205066615390438664548849 117903799961542828998411637)
                ·
                  refine ⟨11053481246394640218601091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117903799961542828998411637 11053481246394640218601091)
                  ·
                    refine ⟨16580221869591960327901637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11053481246394640218601091 16580221869591960327901637)
                    ·
                      refine ⟨3108791600548492561481557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16580221869591960327901637 3108791600548492561481557)
                      ·
                        rfl

theorem cell23_6054350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_6054350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054350 prefixEnd_6054350 := by exact prefixLift 6054350
  have htrace : WordTrace (prefixWord ++ tailWord_6054350) baseStart_6054350 baseEnd_6054350 := by
    simpa [prefixWord, tailWord_6054350, baseEnd_6054350] using wordTrace_append hprefix tailTrace_6054350
  have hstable : (prefixWord ++ tailWord_6054350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054350).length < 2 ^ (prefixWord ++ tailWord_6054350).sum := by decide
  have hdescent : baseEnd_6054350 < baseStart_6054350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054361 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 1, 1, 3]
def baseStart_6054361 : Nat := 118140960795 + 6054361 * 2 ^ 59
def prefixEnd_6054361 : Nat := 4983230072969 + 3 ^ 40 * 6054361 * 2
def baseEnd_6054361 : Nat := 3108797248835692018444007

theorem tailTrace_6054361 : CollatzResearch.WordTrace tailWord_6054361 prefixEnd_6054361 3108797248835692018444007 := by
  unfold tailWord_6054361
  simp only [CollatzResearch.WordTrace]
  refine ⟨220820686819091574382762937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147213791212727716255175291 220820686819091574382762937)
  ·
    refine ⟨165615515114318680787072203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220820686819091574382762937 165615515114318680787072203)
    ·
      refine ⟨248423272671478021180608305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165615515114318680787072203 248423272671478021180608305)
      ·
        refine ⟨186317454503608515885456229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248423272671478021180608305 186317454503608515885456229)
        ·
          refine ⟨34934522719426596728523043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186317454503608515885456229 34934522719426596728523043)
          ·
            refine ⟨52401784079139895092784565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34934522719426596728523043 52401784079139895092784565)
            ·
              refine ⟨4912667257419365164948553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52401784079139895092784565 4912667257419365164948553)
              ·
                refine ⟨3684500443064523873711415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912667257419365164948553 3684500443064523873711415)
                ·
                  refine ⟨5526750664596785810567123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684500443064523873711415 5526750664596785810567123)
                  ·
                    refine ⟨8290125996895178715850685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526750664596785810567123 8290125996895178715850685)
                    ·
                      refine ⟨3108797248835692018444007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8290125996895178715850685 3108797248835692018444007)
                      ·
                        rfl

theorem cell23_6054361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_6054361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054361 prefixEnd_6054361 := by exact prefixLift 6054361
  have htrace : WordTrace (prefixWord ++ tailWord_6054361) baseStart_6054361 baseEnd_6054361 := by
    simpa [prefixWord, tailWord_6054361, baseEnd_6054361] using wordTrace_append hprefix tailTrace_6054361
  have hstable : (prefixWord ++ tailWord_6054361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054361).length < 2 ^ (prefixWord ++ tailWord_6054361).sum := by decide
  have hdescent : baseEnd_6054361 < baseStart_6054361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054380 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_6054380 : Nat := 118140960795 + 6054380 * 2 ^ 59
def prefixEnd_6054380 : Nat := 4983230072969 + 3 ^ 40 * 6054380 * 2
def baseEnd_6054380 : Nat := 3108807004968127444106419

theorem tailTrace_6054380 : CollatzResearch.WordTrace tailWord_6054380 prefixEnd_6054380 3108807004968127444106419 := by
  unfold tailWord_6054380
  simp only [CollatzResearch.WordTrace]
  refine ⟨110410689903011370313852297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147214253204015160418469729 110410689903011370313852297)
  ·
    refine ⟨82808017427258527735389223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110410689903011370313852297 82808017427258527735389223)
    ·
      refine ⟨124212026140887791603083835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82808017427258527735389223 124212026140887791603083835)
      ·
        refine ⟨186318039211331687404625753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124212026140887791603083835 186318039211331687404625753)
        ·
          refine ⟨139738529408498765553469315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186318039211331687404625753 139738529408498765553469315)
          ·
            refine ⟨209607794112748148330203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139738529408498765553469315 209607794112748148330203973)
            ·
              refine ⟨39301461396140277811913245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209607794112748148330203973 39301461396140277811913245)
              ·
                refine ⟨14738048023552604179467467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39301461396140277811913245 14738048023552604179467467)
                ·
                  refine ⟨22107072035328906269201201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14738048023552604179467467 22107072035328906269201201)
                  ·
                    refine ⟨16580304026496679701900901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22107072035328906269201201 16580304026496679701900901)
                    ·
                      refine ⟨3108807004968127444106419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16580304026496679701900901 3108807004968127444106419)
                      ·
                        rfl

theorem cell23_6054380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_6054380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054380 prefixEnd_6054380 := by exact prefixLift 6054380
  have htrace : WordTrace (prefixWord ++ tailWord_6054380) baseStart_6054380 baseEnd_6054380 := by
    simpa [prefixWord, tailWord_6054380, baseEnd_6054380] using wordTrace_append hprefix tailTrace_6054380
  have hstable : (prefixWord ++ tailWord_6054380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054380).length < 2 ^ (prefixWord ++ tailWord_6054380).sum := by decide
  have hdescent : baseEnd_6054380 < baseStart_6054380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054390 : List Nat := [5, 1, 1, 1, 2, 1, 1, 11]
def baseStart_6054390 : Nat := 118140960795 + 6054390 * 2 ^ 59
def prefixEnd_6054390 : Nat := 4983230072969 + 3 ^ 40 * 6054390 * 2
def baseEnd_6054390 : Nat := 115141190362024903888199

theorem tailTrace_6054390 : CollatzResearch.WordTrace tailWord_6054390 prefixEnd_6054390 115141190362024903888199 := by
  unfold tailWord_6054390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801359033499157020973039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147214496357324341557045749 13801359033499157020973039)
  ·
    refine ⟨20702038550248735531459559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13801359033499157020973039 20702038550248735531459559)
    ·
      refine ⟨31053057825373103297189339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20702038550248735531459559 31053057825373103297189339)
      ·
        refine ⟨46579586738059654945784009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31053057825373103297189339 46579586738059654945784009)
        ·
          refine ⟨34934690053544741209338007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46579586738059654945784009 34934690053544741209338007)
          ·
            refine ⟨52402035080317111814007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34934690053544741209338007 52402035080317111814007011)
            ·
              refine ⟨78603052620475667721010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52402035080317111814007011 78603052620475667721010517)
              ·
                refine ⟨115141190362024903888199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 78603052620475667721010517 115141190362024903888199)
                ·
                  rfl

theorem cell23_6054390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_6054390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054390 prefixEnd_6054390 := by exact prefixLift 6054390
  have htrace : WordTrace (prefixWord ++ tailWord_6054390) baseStart_6054390 baseEnd_6054390 := by
    simpa [prefixWord, tailWord_6054390, baseEnd_6054390] using wordTrace_append hprefix tailTrace_6054390
  have hstable : (prefixWord ++ tailWord_6054390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054390).length < 2 ^ (prefixWord ++ tailWord_6054390).sum := by decide
  have hdescent : baseEnd_6054390 < baseStart_6054390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054404 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6054404 : Nat := 118140960795 + 6054404 * 2 ^ 59
def prefixEnd_6054404 : Nat := 4983230072969 + 3 ^ 40 * 6054404 * 2
def baseEnd_6054404 : Nat := 3108819328503835350206309

theorem tailTrace_6054404 : CollatzResearch.WordTrace tailWord_6054404 prefixEnd_6054404 3108819328503835350206309 := by
  unfold tailWord_6054404
  simp only [CollatzResearch.WordTrace]
  refine ⟨110411127578967896363289133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147214836771957195151052177 110411127578967896363289133)
  ·
    refine ⟨41404172842112961136233425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110411127578967896363289133 41404172842112961136233425)
    ·
      refine ⟨31053129631584720852175069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41404172842112961136233425 31053129631584720852175069)
      ·
        refine ⟨11644923611844270319565651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31053129631584720852175069 11644923611844270319565651)
        ·
          refine ⟨17467385417766405479348477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644923611844270319565651 17467385417766405479348477)
          ·
            refine ⟨6550269531662402054755679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17467385417766405479348477 6550269531662402054755679)
            ·
              refine ⟨9825404297493603082133519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550269531662402054755679 9825404297493603082133519)
              ·
                refine ⟨14738106446240404623200279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9825404297493603082133519 14738106446240404623200279)
                ·
                  refine ⟨22107159669360606934800419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14738106446240404623200279 22107159669360606934800419)
                  ·
                    refine ⟨33160739504040910402200629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22107159669360606934800419 33160739504040910402200629)
                    ·
                      refine ⟨3108819328503835350206309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33160739504040910402200629 3108819328503835350206309)
                      ·
                        rfl

theorem cell23_6054404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6054404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054404 prefixEnd_6054404 := by exact prefixLift 6054404
  have htrace : WordTrace (prefixWord ++ tailWord_6054404) baseStart_6054404 baseEnd_6054404 := by
    simpa [prefixWord, tailWord_6054404, baseEnd_6054404] using wordTrace_append hprefix tailTrace_6054404
  have hstable : (prefixWord ++ tailWord_6054404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054404).length < 2 ^ (prefixWord ++ tailWord_6054404).sum := by decide
  have hdescent : baseEnd_6054404 < baseStart_6054404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054452 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6054452 : Nat := 118140960795 + 6054452 * 2 ^ 59
def prefixEnd_6054452 : Nat := 4983230072969 + 3 ^ 40 * 6054452 * 2
def baseEnd_6054452 : Nat := 3108843975575251162406089

theorem tailTrace_6054452 : CollatzResearch.WordTrace tailWord_6054452 prefixEnd_6054452 3108843975575251162406089 := by
  unfold tailWord_6054452
  simp only [CollatzResearch.WordTrace]
  refine ⟨110412002930880948462162805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147216003907841264616217073 110412002930880948462162805)
  ·
    refine ⟨10351125274770088918327763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110412002930880948462162805 10351125274770088918327763)
    ·
      refine ⟨15526687912155133377491645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10351125274770088918327763 15526687912155133377491645)
      ·
        refine ⟨5822507967058175016559367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15526687912155133377491645 5822507967058175016559367)
        ·
          refine ⟨8733761950587262524839051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822507967058175016559367 8733761950587262524839051)
          ·
            refine ⟨13100642925880893787258577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8733761950587262524839051 13100642925880893787258577)
            ·
              refine ⟨9825482194410670340443933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13100642925880893787258577 9825482194410670340443933)
              ·
                refine ⟨3684555822904001377666475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9825482194410670340443933 3684555822904001377666475)
                ·
                  refine ⟨5526833734356002066499713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684555822904001377666475 5526833734356002066499713)
                  ·
                    refine ⟨4145125300767001549874785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526833734356002066499713 4145125300767001549874785)
                    ·
                      refine ⟨3108843975575251162406089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145125300767001549874785 3108843975575251162406089)
                      ·
                        rfl

theorem cell23_6054452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6054452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054452 prefixEnd_6054452 := by exact prefixLift 6054452
  have htrace : WordTrace (prefixWord ++ tailWord_6054452) baseStart_6054452 baseEnd_6054452 := by
    simpa [prefixWord, tailWord_6054452, baseEnd_6054452] using wordTrace_append hprefix tailTrace_6054452
  have hstable : (prefixWord ++ tailWord_6054452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054452).length < 2 ^ (prefixWord ++ tailWord_6054452).sum := by decide
  have hdescent : baseEnd_6054452 < baseStart_6054452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054461 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6054461 : Nat := 118140960795 + 6054461 * 2 ^ 59
def prefixEnd_6054461 : Nat := 4983230072969 + 3 ^ 40 * 6054461 * 2
def baseEnd_6054461 : Nat := 3108848596901141627193547

theorem tailTrace_6054461 : CollatzResearch.WordTrace tailWord_6054461 prefixEnd_6054461 3108848596901141627193547 := by
  unfold tailWord_6054461
  simp only [CollatzResearch.WordTrace]
  refine ⟨220824334118729291461403237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147216222745819527640935491 220824334118729291461403237)
  ·
    refine ⟨41404562647261742149013107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220824334118729291461403237 41404562647261742149013107)
    ·
      refine ⟨62106843970892613223519661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41404562647261742149013107 62106843970892613223519661)
      ·
        refine ⟨23290066489084729958819873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62106843970892613223519661 23290066489084729958819873)
        ·
          refine ⟨17467549866813547469114905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23290066489084729958819873 17467549866813547469114905)
          ·
            refine ⟨13100662400110160601836179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17467549866813547469114905 13100662400110160601836179)
            ·
              refine ⟨19650993600165240902754269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13100662400110160601836179 19650993600165240902754269)
              ·
                refine ⟨7369122600061965338532851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19650993600165240902754269 7369122600061965338532851)
                ·
                  refine ⟨11053683900092948007799277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369122600061965338532851 11053683900092948007799277)
                  ·
                    refine ⟨4145131462534855502924729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11053683900092948007799277 4145131462534855502924729)
                    ·
                      refine ⟨3108848596901141627193547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145131462534855502924729 3108848596901141627193547)
                      ·
                        rfl

theorem cell23_6054461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6054461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054461 prefixEnd_6054461 := by exact prefixLift 6054461
  have htrace : WordTrace (prefixWord ++ tailWord_6054461) baseStart_6054461 baseEnd_6054461 := by
    simpa [prefixWord, tailWord_6054461, baseEnd_6054461] using wordTrace_append hprefix tailTrace_6054461
  have hstable : (prefixWord ++ tailWord_6054461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054461).length < 2 ^ (prefixWord ++ tailWord_6054461).sum := by decide
  have hdescent : baseEnd_6054461 < baseStart_6054461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054520 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_6054520 : Nat := 118140960795 + 6054520 * 2 ^ 59
def prefixEnd_6054520 : Nat := 4983230072969 + 3 ^ 40 * 6054520 * 2
def baseEnd_6054520 : Nat := 3108878892259756896355775

theorem tailTrace_6054520 : CollatzResearch.WordTrace tailWord_6054520 prefixEnd_6054520 3108878892259756896355775 := by
  unfold tailWord_6054520
  simp only [CollatzResearch.WordTrace]
  refine ⟨110413243012757772268900507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147217657350343696358534009 110413243012757772268900507)
  ·
    refine ⟨165619864519136658403350761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110413243012757772268900507 165619864519136658403350761)
    ·
      refine ⟨124214898389352493802513071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165619864519136658403350761 124214898389352493802513071)
      ·
        refine ⟨186322347584028740703769607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124214898389352493802513071 186322347584028740703769607)
        ·
          refine ⟨279483521376043111055654411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186322347584028740703769607 279483521376043111055654411)
          ·
            refine ⟨419225282064064666583481617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279483521376043111055654411 419225282064064666583481617)
            ·
              refine ⟨314418961548048499937611213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419225282064064666583481617 314418961548048499937611213)
              ·
                refine ⟨117907110580518187476604205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314418961548048499937611213 117907110580518187476604205)
                ·
                  refine ⟨44215166467694320303726577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117907110580518187476604205 44215166467694320303726577)
                  ·
                    refine ⟨33161374850770740227794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44215166467694320303726577 33161374850770740227794933)
                    ·
                      refine ⟨3108878892259756896355775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33161374850770740227794933 3108878892259756896355775)
                      ·
                        rfl

theorem cell23_6054520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_6054520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054520 prefixEnd_6054520 := by exact prefixLift 6054520
  have htrace : WordTrace (prefixWord ++ tailWord_6054520) baseStart_6054520 baseEnd_6054520 := by
    simpa [prefixWord, tailWord_6054520, baseEnd_6054520] using wordTrace_append hprefix tailTrace_6054520
  have hstable : (prefixWord ++ tailWord_6054520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054520).length < 2 ^ (prefixWord ++ tailWord_6054520).sum := by decide
  have hdescent : baseEnd_6054520 < baseStart_6054520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054540 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_6054540 : Nat := 118140960795 + 6054540 * 2 ^ 59
def prefixEnd_6054540 : Nat := 4983230072969 + 3 ^ 40 * 6054540 * 2
def baseEnd_6054540 : Nat := 1036296387290948939368561

theorem tailTrace_6054540 : CollatzResearch.WordTrace tailWord_6054540 prefixEnd_6054540 1036296387290948939368561 := by
  unfold tailWord_6054540
  simp only [CollatzResearch.WordTrace]
  refine ⟨110413607742721543976764537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147218143656962058635686049 110413607742721543976764537)
  ·
    refine ⟨82810205807041157982573403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110413607742721543976764537 82810205807041157982573403)
    ·
      refine ⟨124215308710561736973860105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82810205807041157982573403 124215308710561736973860105)
      ·
        refine ⟨93161481532921302730395079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124215308710561736973860105 93161481532921302730395079)
        ·
          refine ⟨139742222299381954095592619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93161481532921302730395079 139742222299381954095592619)
          ·
            refine ⟨209613333449072931143388929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139742222299381954095592619 209613333449072931143388929)
            ·
              refine ⟨157210000086804698357541697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209613333449072931143388929 157210000086804698357541697)
              ·
                refine ⟨117907500065103523768156273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157210000086804698357541697 117907500065103523768156273)
                ·
                  refine ⟨88430625048827642826117205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117907500065103523768156273 88430625048827642826117205)
                  ·
                    refine ⟨1036296387290948939368561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88430625048827642826117205 1036296387290948939368561)
                    ·
                      rfl

theorem cell23_6054540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_6054540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054540 prefixEnd_6054540 := by exact prefixLift 6054540
  have htrace : WordTrace (prefixWord ++ tailWord_6054540) baseStart_6054540 baseEnd_6054540 := by
    simpa [prefixWord, tailWord_6054540, baseEnd_6054540] using wordTrace_append hprefix tailTrace_6054540
  have hstable : (prefixWord ++ tailWord_6054540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054540).length < 2 ^ (prefixWord ++ tailWord_6054540).sum := by decide
  have hdescent : baseEnd_6054540 < baseStart_6054540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054564 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_6054564 : Nat := 118140960795 + 6054564 * 2 ^ 59
def prefixEnd_6054564 : Nat := 4983230072969 + 3 ^ 40 * 6054564 * 2
def baseEnd_6054564 : Nat := 3108901485408554724205573

theorem tailTrace_6054564 : CollatzResearch.WordTrace tailWord_6054564 prefixEnd_6054564 3108901485408554724205573 := by
  unfold tailWord_6054564
  simp only [CollatzResearch.WordTrace]
  refine ⟨110414045418678070026201373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147218727224904093368268497 110414045418678070026201373)
  ·
    refine ⟨41405267032004276259825515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110414045418678070026201373 41405267032004276259825515)
    ·
      refine ⟨62107900548006414389738273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41405267032004276259825515 62107900548006414389738273)
      ·
        refine ⟨46580925411004810792303705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62107900548006414389738273 46580925411004810792303705)
        ·
          refine ⟨34935694058253608094227779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46580925411004810792303705 34935694058253608094227779)
          ·
            refine ⟨52403541087380412141341669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34935694058253608094227779 52403541087380412141341669)
            ·
              refine ⟨9825663953883827276501563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52403541087380412141341669 9825663953883827276501563)
              ·
                refine ⟨14738495930825740914752345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9825663953883827276501563 14738495930825740914752345)
                ·
                  refine ⟨11053871948119305686064259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14738495930825740914752345 11053871948119305686064259)
                  ·
                    refine ⟨16580807922178958529096389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11053871948119305686064259 16580807922178958529096389)
                    ·
                      refine ⟨3108901485408554724205573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16580807922178958529096389 3108901485408554724205573)
                      ·
                        rfl

theorem cell23_6054564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_6054564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054564 prefixEnd_6054564 := by exact prefixLift 6054564
  have htrace : WordTrace (prefixWord ++ tailWord_6054564) baseStart_6054564 baseEnd_6054564 := by
    simpa [prefixWord, tailWord_6054564, baseEnd_6054564] using wordTrace_append hprefix tailTrace_6054564
  have hstable : (prefixWord ++ tailWord_6054564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054564).length < 2 ^ (prefixWord ++ tailWord_6054564).sum := by decide
  have hdescent : baseEnd_6054564 < baseStart_6054564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054582 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_6054582 : Nat := 118140960795 + 6054582 * 2 ^ 59
def prefixEnd_6054582 : Nat := 4983230072969 + 3 ^ 40 * 6054582 * 2
def baseEnd_6054582 : Nat := 345434525340037294864499

theorem tailTrace_6054582 : CollatzResearch.WordTrace tailWord_6054582 prefixEnd_6054582 345434525340037294864499 := by
  unfold tailWord_6054582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801796709455683070409875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147219164900860619417705333 13801796709455683070409875)
  ·
    refine ⟨20702695064183524605614813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13801796709455683070409875 20702695064183524605614813)
    ·
      refine ⟨7763510649068821727105555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20702695064183524605614813 7763510649068821727105555)
      ·
        refine ⟨11645265973603232590658333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7763510649068821727105555 11645265973603232590658333)
        ·
          refine ⟨4366974740101212221496875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11645265973603232590658333 4366974740101212221496875)
          ·
            refine ⟨6550462110151818332245313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366974740101212221496875 6550462110151818332245313)
            ·
              refine ⟨4912846582613863749183985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6550462110151818332245313 4912846582613863749183985)
              ·
                refine ⟨3684634936960397811887989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912846582613863749183985 3684634936960397811887989)
                ·
                  refine ⟨345434525340037294864499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684634936960397811887989 345434525340037294864499)
                  ·
                    rfl

theorem cell23_6054582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_6054582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054582 prefixEnd_6054582 := by exact prefixLift 6054582
  have htrace : WordTrace (prefixWord ++ tailWord_6054582) baseStart_6054582 baseEnd_6054582 := by
    simpa [prefixWord, tailWord_6054582, baseEnd_6054582] using wordTrace_append hprefix tailTrace_6054582
  have hstable : (prefixWord ++ tailWord_6054582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054582).length < 2 ^ (prefixWord ++ tailWord_6054582).sum := by decide
  have hdescent : baseEnd_6054582 < baseStart_6054582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054591 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 1, 4]
def baseStart_6054591 : Nat := 118140960795 + 6054591 * 2 ^ 59
def prefixEnd_6054591 : Nat := 4983230072969 + 3 ^ 40 * 6054591 * 2
def baseEnd_6054591 : Nat := 1036305116462075372855983

theorem tailTrace_6054591 : CollatzResearch.WordTrace tailWord_6054591 prefixEnd_6054591 1036305116462075372855983 := by
  unfold tailWord_6054591
  simp only [CollatzResearch.WordTrace]
  refine ⟨220829075608258323663635627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147219383738838882442423751 220829075608258323663635627)
  ·
    refine ⟨331243613412387485495453441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220829075608258323663635627 331243613412387485495453441)
    ·
      refine ⟨248432710059290614121590081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331243613412387485495453441 248432710059290614121590081)
      ·
        refine ⟨186324532544467960591192561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248432710059290614121590081 186324532544467960591192561)
        ·
          refine ⟨139743399408350970443394421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186324532544467960591192561 139743399408350970443394421)
          ·
            refine ⟨13100943694532903479068227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139743399408350970443394421 13100943694532903479068227)
            ·
              refine ⟨19651415541799355218602341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13100943694532903479068227 19651415541799355218602341)
              ·
                refine ⟨3684640414087379103487939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19651415541799355218602341 3684640414087379103487939)
                ·
                  refine ⟨5526960621131068655231909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684640414087379103487939 5526960621131068655231909)
                  ·
                    refine ⟨1036305116462075372855983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5526960621131068655231909 1036305116462075372855983)
                    ·
                      rfl

theorem cell23_6054591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_6054591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054591 prefixEnd_6054591 := by exact prefixLift 6054591
  have htrace : WordTrace (prefixWord ++ tailWord_6054591) baseStart_6054591 baseEnd_6054591 := by
    simpa [prefixWord, tailWord_6054591, baseEnd_6054591] using wordTrace_append hprefix tailTrace_6054591
  have hstable : (prefixWord ++ tailWord_6054591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054591).length < 2 ^ (prefixWord ++ tailWord_6054591).sum := by decide
  have hdescent : baseEnd_6054591 < baseStart_6054591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054604 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 6]
def baseStart_6054604 : Nat := 118140960795 + 6054604 * 2 ^ 59
def prefixEnd_6054604 : Nat := 4983230072969 + 3 ^ 40 * 6054604 * 2
def baseEnd_6054604 : Nat := 345435780514970507522821

theorem tailTrace_6054604 : CollatzResearch.WordTrace tailWord_6054604 prefixEnd_6054604 345435780514970507522821 := by
  unfold tailWord_6054604
  simp only [CollatzResearch.WordTrace]
  refine ⟨110414774878605613441929433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147219699838140817922572577 110414774878605613441929433)
  ·
    refine ⟨82811081158954210081447075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110414774878605613441929433 82811081158954210081447075)
    ·
      refine ⟨124216621738431315122170613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82811081158954210081447075 124216621738431315122170613)
      ·
        refine ⟨11645308287977935792703495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124216621738431315122170613 11645308287977935792703495)
        ·
          refine ⟨17467962431966903689055243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11645308287977935792703495 17467962431966903689055243)
          ·
            refine ⟨26201943647950355533582865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467962431966903689055243 26201943647950355533582865)
            ·
              refine ⟨19651457735962766650187149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26201943647950355533582865 19651457735962766650187149)
              ·
                refine ⟨7369296650986037493820181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19651457735962766650187149 7369296650986037493820181)
                ·
                  refine ⟨345435780514970507522821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7369296650986037493820181 345435780514970507522821)
                  ·
                    rfl

theorem cell23_6054604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_6054604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054604 prefixEnd_6054604 := by exact prefixLift 6054604
  have htrace : WordTrace (prefixWord ++ tailWord_6054604) baseStart_6054604 baseEnd_6054604 := by
    simpa [prefixWord, tailWord_6054604, baseEnd_6054604] using wordTrace_append hprefix tailTrace_6054604
  have hstable : (prefixWord ++ tailWord_6054604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054604).length < 2 ^ (prefixWord ++ tailWord_6054604).sum := by decide
  have hdescent : baseEnd_6054604 < baseStart_6054604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054617 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_6054617 : Nat := 118140960795 + 6054617 * 2 ^ 59
def prefixEnd_6054617 : Nat := 4983230072969 + 3 ^ 40 * 6054617 * 2
def baseEnd_6054617 : Nat := 1036309566627747672280943

theorem tailTrace_6054617 : CollatzResearch.WordTrace tailWord_6054617 prefixEnd_6054617 1036309566627747672280943 := by
  unfold tailWord_6054617
  simp only [CollatzResearch.WordTrace]
  refine ⟨220830023906164130104082105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147220015937442753402721403 220830023906164130104082105)
  ·
    refine ⟨165622517929623097578061579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220830023906164130104082105 165622517929623097578061579)
    ·
      refine ⟨248433776894434646367092369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165622517929623097578061579 248433776894434646367092369)
      ·
        refine ⟨186325332670825984775319277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248433776894434646367092369 186325332670825984775319277)
        ·
          refine ⟨69871999751559744290744729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186325332670825984775319277 69871999751559744290744729)
          ·
            refine ⟨52403999813669808218058547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69871999751559744290744729 52403999813669808218058547)
            ·
              refine ⟨78605999720504712327087821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52403999813669808218058547 78605999720504712327087821)
              ·
                refine ⟨29477249895189267122657933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78605999720504712327087821 29477249895189267122657933)
                ·
                  refine ⟨11053968710695975170996725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29477249895189267122657933 11053968710695975170996725)
                  ·
                    refine ⟨1036309566627747672280943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11053968710695975170996725 1036309566627747672280943)
                    ·
                      rfl

theorem cell23_6054617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_6054617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054617 prefixEnd_6054617 := by exact prefixLift 6054617
  have htrace : WordTrace (prefixWord ++ tailWord_6054617) baseStart_6054617 baseEnd_6054617 := by
    simpa [prefixWord, tailWord_6054617, baseEnd_6054617] using wordTrace_append hprefix tailTrace_6054617
  have hstable : (prefixWord ++ tailWord_6054617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054617).length < 2 ^ (prefixWord ++ tailWord_6054617).sum := by decide
  have hdescent : baseEnd_6054617 < baseStart_6054617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054664 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_6054664 : Nat := 118140960795 + 6054664 * 2 ^ 59
def prefixEnd_6054664 : Nat := 4983230072969 + 3 ^ 40 * 6054664 * 2
def baseEnd_6054664 : Nat := 1036317611158001444318371

theorem tailTrace_6054664 : CollatzResearch.WordTrace tailWord_6054664 prefixEnd_6054664 1036317611158001444318371 := by
  unfold tailWord_6054664
  simp only [CollatzResearch.WordTrace]
  refine ⟨110415869068496928565521523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147221158757995904754028697 110415869068496928565521523)
  ·
    refine ⟨165623803602745392848282285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110415869068496928565521523 165623803602745392848282285)
    ·
      refine ⟨62108926351029522318105857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165623803602745392848282285 62108926351029522318105857)
      ·
        refine ⟨46581694763272141738579393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62108926351029522318105857 46581694763272141738579393)
        ·
          refine ⟨34936271072454106303934545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46581694763272141738579393 34936271072454106303934545)
          ·
            refine ⟨26202203304340579727950909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34936271072454106303934545 26202203304340579727950909)
            ·
              refine ⟨9825826239127717397981591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26202203304340579727950909 9825826239127717397981591)
              ·
                refine ⟨14738739358691576096972387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9825826239127717397981591 14738739358691576096972387)
                ·
                  refine ⟨22108109038037364145458581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14738739358691576096972387 22108109038037364145458581)
                  ·
                    refine ⟨1036317611158001444318371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22108109038037364145458581 1036317611158001444318371)
                    ·
                      rfl

theorem cell23_6054664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_6054664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054664 prefixEnd_6054664 := by exact prefixLift 6054664
  have htrace : WordTrace (prefixWord ++ tailWord_6054664) baseStart_6054664 baseEnd_6054664 := by
    simpa [prefixWord, tailWord_6054664, baseEnd_6054664] using wordTrace_append hprefix tailTrace_6054664
  have hstable : (prefixWord ++ tailWord_6054664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054664).length < 2 ^ (prefixWord ++ tailWord_6054664).sum := by decide
  have hdescent : baseEnd_6054664 < baseStart_6054664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054671 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 3, 2, 2]
def baseStart_6054671 : Nat := 118140960795 + 6054671 * 2 ^ 59
def prefixEnd_6054671 : Nat := 4983230072969 + 3 ^ 40 * 6054671 * 2
def baseEnd_6054671 : Nat := 3108956427838585805567581

theorem tailTrace_6054671 : CollatzResearch.WordTrace tailWord_6054671 prefixEnd_6054671 3108956427838585805567581 := by
  unfold tailWord_6054671
  simp only [CollatzResearch.WordTrace]
  refine ⟨220831993447968497326547867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147221328965312331551031911 220831993447968497326547867)
  ·
    refine ⟨331247990171952745989821801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220831993447968497326547867 331247990171952745989821801)
    ·
      refine ⟨248435992628964559492366351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331247990171952745989821801 248435992628964559492366351)
      ·
        refine ⟨372653988943446839238549527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248435992628964559492366351 372653988943446839238549527)
        ·
          refine ⟨558980983415170258857824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372653988943446839238549527 558980983415170258857824291)
          ·
            refine ⟨838471475122755388286736437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558980983415170258857824291 838471475122755388286736437)
            ·
              refine ⟨78606700792758317651881541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 838471475122755388286736437 78606700792758317651881541)
              ·
                refine ⟨14738756398642184559727789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78606700792758317651881541 14738756398642184559727789)
                ·
                  refine ⟨5527033649490819209897921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14738756398642184559727789 5527033649490819209897921)
                  ·
                    refine ⟨4145275237118114407423441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5527033649490819209897921 4145275237118114407423441)
                    ·
                      refine ⟨3108956427838585805567581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145275237118114407423441 3108956427838585805567581)
                      ·
                        rfl

theorem cell23_6054671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2, 2].length) (baseStart_6054671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054671 prefixEnd_6054671 := by exact prefixLift 6054671
  have htrace : WordTrace (prefixWord ++ tailWord_6054671) baseStart_6054671 baseEnd_6054671 := by
    simpa [prefixWord, tailWord_6054671, baseEnd_6054671] using wordTrace_append hprefix tailTrace_6054671
  have hstable : (prefixWord ++ tailWord_6054671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054671).length < 2 ^ (prefixWord ++ tailWord_6054671).sum := by decide
  have hdescent : baseEnd_6054671 < baseStart_6054671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054677 : List Nat := [1, 3, 2, 1, 2, 2, 3, 9]
def baseStart_6054677 : Nat := 118140960795 + 6054677 * 2 ^ 59
def prefixEnd_6054677 : Nat := 4983230072969 + 3 ^ 40 * 6054677 * 2
def baseEnd_6054677 : Nat := 115146648471204177114539

theorem tailTrace_6054677 : CollatzResearch.WordTrace tailWord_6054677 prefixEnd_6054677 115146648471204177114539 := by
  unfold tailWord_6054677
  simp only [CollatzResearch.WordTrace]
  refine ⟨220832212285946760351266285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147221474857297840234177523 220832212285946760351266285)
  ·
    refine ⟨82812079607230035131724857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220832212285946760351266285 82812079607230035131724857)
    ·
      refine ⟨62109059705422526348793643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82812079607230035131724857 62109059705422526348793643)
      ·
        refine ⟨93163589558133789523190465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62109059705422526348793643 93163589558133789523190465)
        ·
          refine ⟨69872692168600342142392849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93163589558133789523190465 69872692168600342142392849)
          ·
            refine ⟨52404519126450256606794637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69872692168600342142392849 52404519126450256606794637)
            ·
              refine ⟨19651694672418846227547989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52404519126450256606794637 19651694672418846227547989)
              ·
                refine ⟨115146648471204177114539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19651694672418846227547989 115146648471204177114539)
                ·
                  rfl

theorem cell23_6054677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 9].length) (baseStart_6054677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054677 prefixEnd_6054677 := by exact prefixLift 6054677
  have htrace : WordTrace (prefixWord ++ tailWord_6054677) baseStart_6054677 baseEnd_6054677 := by
    simpa [prefixWord, tailWord_6054677, baseEnd_6054677] using wordTrace_append hprefix tailTrace_6054677
  have hstable : (prefixWord ++ tailWord_6054677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054677).length < 2 ^ (prefixWord ++ tailWord_6054677).sum := by decide
  have hdescent : baseEnd_6054677 < baseStart_6054677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054727 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6054727 : Nat := 118140960795 + 6054727 * 2 ^ 59
def prefixEnd_6054727 : Nat := 4983230072969 + 3 ^ 40 * 6054727 * 2
def baseEnd_6054727 : Nat := 3108985182755237586467323

theorem tailTrace_6054727 : CollatzResearch.WordTrace tailWord_6054727 prefixEnd_6054727 3108985182755237586467323 := by
  unfold tailWord_6054727
  simp only [CollatzResearch.WordTrace]
  refine ⟨220834035935765618890586435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147222690623843745927057623 220834035935765618890586435)
  ·
    refine ⟨331251053903648428335879653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220834035935765618890586435 331251053903648428335879653)
    ·
      refine ⟨62109572606934080312977435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331251053903648428335879653 62109572606934080312977435)
      ·
        refine ⟨93164358910401120469466153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62109572606934080312977435 93164358910401120469466153)
        ·
          refine ⟨69873269182800840352099615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93164358910401120469466153 69873269182800840352099615)
          ·
            refine ⟨104809903774201260528149423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69873269182800840352099615 104809903774201260528149423)
            ·
              refine ⟨157214855661301890792224135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104809903774201260528149423 157214855661301890792224135)
              ·
                refine ⟨235822283491952836188336203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157214855661301890792224135 235822283491952836188336203)
                ·
                  refine ⟨353733425237929254282504305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235822283491952836188336203 353733425237929254282504305)
                  ·
                    refine ⟨265300068928446940711878229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353733425237929254282504305 265300068928446940711878229)
                    ·
                      refine ⟨3108985182755237586467323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265300068928446940711878229 3108985182755237586467323)
                      ·
                        rfl

theorem cell23_6054727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6054727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054727 prefixEnd_6054727 := by exact prefixLift 6054727
  have htrace : WordTrace (prefixWord ++ tailWord_6054727) baseStart_6054727 baseEnd_6054727 := by
    simpa [prefixWord, tailWord_6054727, baseEnd_6054727] using wordTrace_append hprefix tailTrace_6054727
  have hstable : (prefixWord ++ tailWord_6054727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054727).length < 2 ^ (prefixWord ++ tailWord_6054727).sum := by decide
  have hdescent : baseEnd_6054727 < baseStart_6054727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054747 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_6054747 : Nat := 118140960795 + 6054747 * 2 ^ 59
def prefixEnd_6054747 : Nat := 4983230072969 + 3 ^ 40 * 6054747 * 2
def baseEnd_6054747 : Nat := 3108995452368327508217231

theorem tailTrace_6054747 : CollatzResearch.WordTrace tailWord_6054747 prefixEnd_6054747 3108995452368327508217231 := by
  unfold tailWord_6054747
  simp only [CollatzResearch.WordTrace]
  refine ⟨220834765395693162306314495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147223176930462108204209663 220834765395693162306314495)
  ·
    refine ⟨331252148093539743459471743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220834765395693162306314495 331252148093539743459471743)
    ·
      refine ⟨496878222140309615189207615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331252148093539743459471743 496878222140309615189207615)
      ·
        refine ⟨745317333210464422783811423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496878222140309615189207615 745317333210464422783811423)
        ·
          refine ⟨1117975999815696634175717135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745317333210464422783811423 1117975999815696634175717135)
          ·
            refine ⟨1676963999723544951263575703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117975999815696634175717135 1676963999723544951263575703)
            ·
              refine ⟨2515445999585317426895363555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676963999723544951263575703 2515445999585317426895363555)
              ·
                refine ⟨3773168999377976140343045333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515445999585317426895363555 3773168999377976140343045333)
                ·
                  refine ⟨88433648422921315789290125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3773168999377976140343045333 88433648422921315789290125)
                  ·
                    refine ⟨33162618158595493420983797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88433648422921315789290125 33162618158595493420983797)
                    ·
                      refine ⟨3108995452368327508217231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33162618158595493420983797 3108995452368327508217231)
                      ·
                        rfl

theorem cell23_6054747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_6054747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054747 prefixEnd_6054747 := by exact prefixLift 6054747
  have htrace : WordTrace (prefixWord ++ tailWord_6054747) baseStart_6054747 baseEnd_6054747 := by
    simpa [prefixWord, tailWord_6054747, baseEnd_6054747] using wordTrace_append hprefix tailTrace_6054747
  have hstable : (prefixWord ++ tailWord_6054747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054747).length < 2 ^ (prefixWord ++ tailWord_6054747).sum := by decide
  have hdescent : baseEnd_6054747 < baseStart_6054747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054764 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_6054764 : Nat := 118140960795 + 6054764 * 2 ^ 59
def prefixEnd_6054764 : Nat := 4983230072969 + 3 ^ 40 * 6054764 * 2
def baseEnd_6054764 : Nat := 3109004181539453941704653

theorem tailTrace_6054764 : CollatzResearch.WordTrace tailWord_6054764 prefixEnd_6054764 3109004181539453941704653 := by
  unfold tailWord_6054764
  simp only [CollatzResearch.WordTrace]
  refine ⟨110417692718315787104841673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147223590291087716139788897 110417692718315787104841673)
  ·
    refine ⟨82813269538736840328631255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110417692718315787104841673 82813269538736840328631255)
    ·
      refine ⟨124219904308105260492946883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82813269538736840328631255 124219904308105260492946883)
      ·
        refine ⟨186329856462157890739420325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124219904308105260492946883 186329856462157890739420325)
        ·
          refine ⟨34936848086654604513641311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186329856462157890739420325 34936848086654604513641311)
          ·
            refine ⟨52405272129981906770461967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34936848086654604513641311 52405272129981906770461967)
            ·
              refine ⟨78607908194972860155692951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52405272129981906770461967 78607908194972860155692951)
              ·
                refine ⟨117911862292459290233539427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78607908194972860155692951 117911862292459290233539427)
                ·
                  refine ⟨176867793438688935350309141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117911862292459290233539427 176867793438688935350309141)
                  ·
                    refine ⟨8290677817438543844545741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176867793438688935350309141 8290677817438543844545741)
                    ·
                      refine ⟨3109004181539453941704653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8290677817438543844545741 3109004181539453941704653)
                      ·
                        rfl

theorem cell23_6054764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_6054764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054764 prefixEnd_6054764 := by exact prefixLift 6054764
  have htrace : WordTrace (prefixWord ++ tailWord_6054764) baseStart_6054764 baseEnd_6054764 := by
    simpa [prefixWord, tailWord_6054764, baseEnd_6054764] using wordTrace_append hprefix tailTrace_6054764
  have hstable : (prefixWord ++ tailWord_6054764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054764).length < 2 ^ (prefixWord ++ tailWord_6054764).sum := by decide
  have hdescent : baseEnd_6054764 < baseStart_6054764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054767 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 11]
def baseStart_6054767 : Nat := 118140960795 + 6054767 * 2 ^ 59
def prefixEnd_6054767 : Nat := 4983230072969 + 3 ^ 40 * 6054767 * 2
def baseEnd_6054767 : Nat := 345445080220157492218571

theorem tailTrace_6054767 : CollatzResearch.WordTrace tailWord_6054767 prefixEnd_6054767 345445080220157492218571 := by
  unfold tailWord_6054767
  simp only [CollatzResearch.WordTrace]
  refine ⟨220835494855620705722042555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147223663237080470481361703 220835494855620705722042555)
  ·
    refine ⟨331253242283431058583063833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220835494855620705722042555 331253242283431058583063833)
    ·
      refine ⟨248439931712573293937297875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331253242283431058583063833 248439931712573293937297875)
      ·
        refine ⟨372659897568859940905946813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248439931712573293937297875 372659897568859940905946813)
        ·
          refine ⟨139747461588322477839730055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372659897568859940905946813 139747461588322477839730055)
          ·
            refine ⟨209621192382483716759595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139747461588322477839730055 209621192382483716759595083)
            ·
              refine ⟨314431788573725575139392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209621192382483716759595083 314431788573725575139392625)
              ·
                refine ⟨235823841430294181354544469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314431788573725575139392625 235823841430294181354544469)
                ·
                  refine ⟨345445080220157492218571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 235823841430294181354544469 345445080220157492218571)
                  ·
                    rfl

theorem cell23_6054767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 11].length) (baseStart_6054767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054767 prefixEnd_6054767 := by exact prefixLift 6054767
  have htrace : WordTrace (prefixWord ++ tailWord_6054767) baseStart_6054767 baseEnd_6054767 := by
    simpa [prefixWord, tailWord_6054767, baseEnd_6054767] using wordTrace_append hprefix tailTrace_6054767
  have hstable : (prefixWord ++ tailWord_6054767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054767).length < 2 ^ (prefixWord ++ tailWord_6054767).sum := by decide
  have hdescent : baseEnd_6054767 < baseStart_6054767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054818 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_6054818 : Nat := 118140960795 + 6054818 * 2 ^ 59
def prefixEnd_6054818 : Nat := 4983230072969 + 3 ^ 40 * 6054818 * 2
def baseEnd_6054818 : Nat := 345447989943866303381045

theorem tailTrace_6054818 : CollatzResearch.WordTrace tailWord_6054818 prefixEnd_6054818 345447989943866303381045 := by
  unfold tailWord_6054818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55209338744608985358037277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147224903318957294288099405 55209338744608985358037277)
  ·
    refine ⟨20703502029228369509263979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55209338744608985358037277 20703502029228369509263979)
    ·
      refine ⟨31055253043842554263895969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20703502029228369509263979 31055253043842554263895969)
      ·
        refine ⟨23291439782881915697921977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31055253043842554263895969 23291439782881915697921977)
        ·
          refine ⟨17468579837161436773441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23291439782881915697921977 17468579837161436773441483)
          ·
            refine ⟨26202869755742155160162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17468579837161436773441483 26202869755742155160162225)
            ·
              refine ⟨19652152316806616370121669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26202869755742155160162225 19652152316806616370121669)
              ·
                refine ⟨3684778559401240569397813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19652152316806616370121669 3684778559401240569397813)
                ·
                  refine ⟨345447989943866303381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684778559401240569397813 345447989943866303381045)
                  ·
                    rfl

theorem cell23_6054818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_6054818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054818 prefixEnd_6054818 := by exact prefixLift 6054818
  have htrace : WordTrace (prefixWord ++ tailWord_6054818) baseStart_6054818 baseEnd_6054818 := by
    simpa [prefixWord, tailWord_6054818, baseEnd_6054818] using wordTrace_append hprefix tailTrace_6054818
  have hstable : (prefixWord ++ tailWord_6054818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054818).length < 2 ^ (prefixWord ++ tailWord_6054818).sum := by decide
  have hdescent : baseEnd_6054818 < baseStart_6054818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054829 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6054829 : Nat := 118140960795 + 6054829 * 2 ^ 59
def prefixEnd_6054829 : Nat := 4983230072969 + 3 ^ 40 * 6054829 * 2
def baseEnd_6054829 : Nat := 3109037557781996187391855

theorem tailTrace_6054829 : CollatzResearch.WordTrace tailWord_6054829 prefixEnd_6054829 3109037557781996187391855 := by
  unfold tailWord_6054829
  simp only [CollatzResearch.WordTrace]
  refine ⟨220837756181396090310799541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147225170787597393540533027 220837756181396090310799541)
  ·
    refine ⟨20703539642005883466637457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220837756181396090310799541 20703539642005883466637457)
    ·
      refine ⟨15527654731504412599978093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20703539642005883466637457 15527654731504412599978093)
      ·
        refine ⟨5822870524314154724991785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15527654731504412599978093 5822870524314154724991785)
        ·
          refine ⟨4367152893235616043743839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822870524314154724991785 4367152893235616043743839)
          ·
            refine ⟨6550729339853424065615759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367152893235616043743839 6550729339853424065615759)
            ·
              refine ⟨9826094009780136098423639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550729339853424065615759 9826094009780136098423639)
              ·
                refine ⟨14739141014670204147635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9826094009780136098423639 14739141014670204147635459)
                ·
                  refine ⟨22108711522005306221453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14739141014670204147635459 22108711522005306221453189)
                  ·
                    refine ⟨4145383410375994916522473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22108711522005306221453189 4145383410375994916522473)
                    ·
                      refine ⟨3109037557781996187391855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145383410375994916522473 3109037557781996187391855)
                      ·
                        rfl

theorem cell23_6054829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6054829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054829 prefixEnd_6054829 := by exact prefixLift 6054829
  have htrace : WordTrace (prefixWord ++ tailWord_6054829) baseStart_6054829 baseEnd_6054829 := by
    simpa [prefixWord, tailWord_6054829, baseEnd_6054829] using wordTrace_append hprefix tailTrace_6054829
  have hstable : (prefixWord ++ tailWord_6054829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054829).length < 2 ^ (prefixWord ++ tailWord_6054829).sum := by decide
  have hdescent : baseEnd_6054829 < baseStart_6054829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054852 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 5]
def baseStart_6054852 : Nat := 118140960795 + 6054852 * 2 ^ 59
def prefixEnd_6054852 : Nat := 4983230072969 + 3 ^ 40 * 6054852 * 2
def baseEnd_6054852 : Nat := 345449929759672177489361

theorem tailTrace_6054852 : CollatzResearch.WordTrace tailWord_6054852 prefixEnd_6054852 345449929759672177489361 := by
  unfold tailWord_6054852
  simp only [CollatzResearch.WordTrace]
  refine ⟨110419297530156382619443405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147225730040208510159257873 110419297530156382619443405)
  ·
    refine ⟨41407236573808643482291277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110419297530156382619443405 41407236573808643482291277)
    ·
      refine ⟨15527713715178241305859229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41407236573808643482291277 15527713715178241305859229)
      ·
        refine ⟨5822892643191840489697211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15527713715178241305859229 5822892643191840489697211)
        ·
          refine ⟨8734338964787760734545817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822892643191840489697211 8734338964787760734545817)
          ·
            refine ⟨6550754223590820550909363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8734338964787760734545817 6550754223590820550909363)
            ·
              refine ⟨9826131335386230826364045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550754223590820550909363 9826131335386230826364045)
              ·
                refine ⟨3684799250769836559886517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9826131335386230826364045 3684799250769836559886517)
                ·
                  refine ⟨345449929759672177489361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684799250769836559886517 345449929759672177489361)
                  ·
                    rfl

theorem cell23_6054852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_6054852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054852 prefixEnd_6054852 := by exact prefixLift 6054852
  have htrace : WordTrace (prefixWord ++ tailWord_6054852) baseStart_6054852 baseEnd_6054852 := by
    simpa [prefixWord, tailWord_6054852, baseEnd_6054852] using wordTrace_append hprefix tailTrace_6054852
  have hstable : (prefixWord ++ tailWord_6054852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054852).length < 2 ^ (prefixWord ++ tailWord_6054852).sum := by decide
  have hdescent : baseEnd_6054852 < baseStart_6054852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054868 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6054868 : Nat := 118140960795 + 6054868 * 2 ^ 59
def prefixEnd_6054868 : Nat := 4983230072969 + 3 ^ 40 * 6054868 * 2
def baseEnd_6054868 : Nat := 3109057583527521534804175

theorem tailTrace_6054868 : CollatzResearch.WordTrace tailWord_6054868 prefixEnd_6054868 3109057583527521534804175 := by
  unfold tailWord_6054868
  simp only [CollatzResearch.WordTrace]
  refine ⟨110419589314127399985734629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147226119085503199980979505 110419589314127399985734629)
  ·
    refine ⟨20703672996398887497325243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110419589314127399985734629 20703672996398887497325243)
    ·
      refine ⟨31055509494598331245987865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20703672996398887497325243 31055509494598331245987865)
      ·
        refine ⟨23291632120948748434490899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31055509494598331245987865 23291632120948748434490899)
        ·
          refine ⟨34937448181423122651736349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23291632120948748434490899 34937448181423122651736349)
          ·
            refine ⟨13101543068033670994401131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34937448181423122651736349 13101543068033670994401131)
            ·
              refine ⟨19652314602050506491601697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101543068033670994401131 19652314602050506491601697)
              ·
                refine ⟨14739235951537879868701273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19652314602050506491601697 14739235951537879868701273)
                ·
                  refine ⟨11054426963653409901525955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14739235951537879868701273 11054426963653409901525955)
                  ·
                    refine ⟨16581640445480114852288933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11054426963653409901525955 16581640445480114852288933)
                    ·
                      refine ⟨3109057583527521534804175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16581640445480114852288933 3109057583527521534804175)
                      ·
                        rfl

theorem cell23_6054868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6054868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054868 prefixEnd_6054868 := by exact prefixLift 6054868
  have htrace : WordTrace (prefixWord ++ tailWord_6054868) baseStart_6054868 baseEnd_6054868 := by
    simpa [prefixWord, tailWord_6054868, baseEnd_6054868] using wordTrace_append hprefix tailTrace_6054868
  have hstable : (prefixWord ++ tailWord_6054868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054868).length < 2 ^ (prefixWord ++ tailWord_6054868).sum := by decide
  have hdescent : baseEnd_6054868 < baseStart_6054868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054921 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_6054921 : Nat := 118140960795 + 6054921 * 2 ^ 59
def prefixEnd_6054921 : Nat := 4983230072969 + 3 ^ 40 * 6054921 * 2
def baseEnd_6054921 : Nat := 1036361599334069942480477

theorem tailTrace_6054921 : CollatzResearch.WordTrace tailWord_6054921 prefixEnd_6054921 1036361599334069942480477 := by
  unfold tailWord_6054921
  simp only [CollatzResearch.WordTrace]
  refine ⟨220841111697062790023148617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147227407798041860015432411 220841111697062790023148617)
  ·
    refine ⟨165630833772797092517361463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220841111697062790023148617 165630833772797092517361463)
    ·
      refine ⟨248446250659195638776042195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165630833772797092517361463 248446250659195638776042195)
      ·
        refine ⟨372669375988793458164063293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248446250659195638776042195 372669375988793458164063293)
        ·
          refine ⟨139751015995797546811523735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372669375988793458164063293 139751015995797546811523735)
          ·
            refine ⟨209626523993696320217285603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139751015995797546811523735 209626523993696320217285603)
            ·
              refine ⟨314439785990544480325928405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209626523993696320217285603 314439785990544480325928405)
              ·
                refine ⟨7369682484153386257638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 314439785990544480325928405 7369682484153386257638947)
                ·
                  refine ⟨11054523726230079386458421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369682484153386257638947 11054523726230079386458421)
                  ·
                    refine ⟨1036361599334069942480477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11054523726230079386458421 1036361599334069942480477)
                    ·
                      rfl

theorem cell23_6054921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_6054921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054921 prefixEnd_6054921 := by exact prefixLift 6054921
  have htrace : WordTrace (prefixWord ++ tailWord_6054921) baseStart_6054921 baseEnd_6054921 := by
    simpa [prefixWord, tailWord_6054921, baseEnd_6054921] using wordTrace_append hprefix tailTrace_6054921
  have hstable : (prefixWord ++ tailWord_6054921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054921).length < 2 ^ (prefixWord ++ tailWord_6054921).sum := by decide
  have hdescent : baseEnd_6054921 < baseStart_6054921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6054958 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6054958 : Nat := 118140960795 + 6054958 * 2 ^ 59
def prefixEnd_6054958 : Nat := 4983230072969 + 3 ^ 40 * 6054958 * 2
def baseEnd_6054958 : Nat := 3109103796786426182678761

theorem tailTrace_6054958 : CollatzResearch.WordTrace tailWord_6054958 prefixEnd_6054958 3109103796786426182678761 := by
  unfold tailWord_6054958
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605307649741093167780691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147228307465285830228163685 27605307649741093167780691)
  ·
    refine ⟨41407961474611639751671037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27605307649741093167780691 41407961474611639751671037)
    ·
      refine ⟨15527985552979364906876639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41407961474611639751671037 15527985552979364906876639)
      ·
        refine ⟨23291978329469047360314959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15527985552979364906876639 23291978329469047360314959)
        ·
          refine ⟨34937967494203571040472439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23291978329469047360314959 34937967494203571040472439)
          ·
            refine ⟨52406951241305356560708659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34937967494203571040472439 52406951241305356560708659)
            ·
              refine ⟨78610426861958034841062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52406951241305356560708659 78610426861958034841062989)
              ·
                refine ⟨29478910073234263065398621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78610426861958034841062989 29478910073234263065398621)
                ·
                  refine ⟨11054591277462848649524483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29478910073234263065398621 11054591277462848649524483)
                  ·
                    refine ⟨16581886916194272974286725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11054591277462848649524483 16581886916194272974286725)
                    ·
                      refine ⟨3109103796786426182678761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16581886916194272974286725 3109103796786426182678761)
                      ·
                        rfl

theorem cell23_6054958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6054958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6054958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6054958 prefixEnd_6054958 := by exact prefixLift 6054958
  have htrace : WordTrace (prefixWord ++ tailWord_6054958) baseStart_6054958 baseEnd_6054958 := by
    simpa [prefixWord, tailWord_6054958, baseEnd_6054958] using wordTrace_append hprefix tailTrace_6054958
  have hstable : (prefixWord ++ tailWord_6054958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6054958).length < 2 ^ (prefixWord ++ tailWord_6054958).sum := by decide
  have hdescent : baseEnd_6054958 < baseStart_6054958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6054958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055005 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6055005 : Nat := 118140960795 + 6055005 * 2 ^ 59
def prefixEnd_6055005 : Nat := 4983230072969 + 3 ^ 40 * 6055005 * 2
def baseEnd_6055005 : Nat := 3109127930377187498791045

theorem tailTrace_6055005 : CollatzResearch.WordTrace tailWord_6055005 prefixEnd_6055005 3109127930377187498791045 := by
  unfold tailWord_6055005
  simp only [CollatzResearch.WordTrace]
  refine ⟨220844175428758472369206469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147229450285838981579470979 220844175428758472369206469)
  ·
    refine ⟨41408282892892213569226213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220844175428758472369206469 41408282892892213569226213)
    ·
      refine ⟨7764053042417290044229915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41408282892892213569226213 7764053042417290044229915)
      ·
        refine ⟨11646079563625935066344873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764053042417290044229915 11646079563625935066344873)
        ·
          refine ⟨8734559672719451299758655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11646079563625935066344873 8734559672719451299758655)
          ·
            refine ⟨13101839509079176949637983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8734559672719451299758655 13101839509079176949637983)
            ·
              refine ⟨19652759263618765424456975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101839509079176949637983 19652759263618765424456975)
              ·
                refine ⟨29479138895428148136685463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19652759263618765424456975 29479138895428148136685463)
                ·
                  refine ⟨44218708343142222205028195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29479138895428148136685463 44218708343142222205028195)
                  ·
                    refine ⟨66328062514713333307542293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44218708343142222205028195 66328062514713333307542293)
                    ·
                      refine ⟨3109127930377187498791045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66328062514713333307542293 3109127930377187498791045)
                      ·
                        rfl

theorem cell23_6055005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6055005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055005 prefixEnd_6055005 := by exact prefixLift 6055005
  have htrace : WordTrace (prefixWord ++ tailWord_6055005) baseStart_6055005 baseEnd_6055005 := by
    simpa [prefixWord, tailWord_6055005, baseEnd_6055005] using wordTrace_append hprefix tailTrace_6055005
  have hstable : (prefixWord ++ tailWord_6055005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055005).length < 2 ^ (prefixWord ++ tailWord_6055005).sum := by decide
  have hdescent : baseEnd_6055005 < baseStart_6055005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055068 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6055068 : Nat := 118140960795 + 6055068 * 2 ^ 59
def prefixEnd_6055068 : Nat := 4983230072969 + 3 ^ 40 * 6055068 * 2
def baseEnd_6055068 : Nat := 3109160279658420752303255

theorem tailTrace_6055068 : CollatzResearch.WordTrace tailWord_6055068 prefixEnd_6055068 3109160279658420752303255 := by
  unfold tailWord_6055068
  simp only [CollatzResearch.WordTrace]
  refine ⟨110423236613765117064374929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147230982151686822752499905 110423236613765117064374929)
  ·
    refine ⟨82817427460323837798281197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110423236613765117064374929 82817427460323837798281197)
    ·
      refine ⟨31056535297621439174355449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82817427460323837798281197 31056535297621439174355449)
      ·
        refine ⟨23292401473216079380766587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31056535297621439174355449 23292401473216079380766587)
        ·
          refine ⟨34938602209824119071149881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23292401473216079380766587 34938602209824119071149881)
          ·
            refine ⟨26203951657368089303362411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34938602209824119071149881 26203951657368089303362411)
            ·
              refine ⟨39305927486052133955043617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26203951657368089303362411 39305927486052133955043617)
              ·
                refine ⟨29479445614539100466282713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39305927486052133955043617 29479445614539100466282713)
                ·
                  refine ⟨22109584210904325349712035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29479445614539100466282713 22109584210904325349712035)
                  ·
                    refine ⟨33164376316356488024568053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22109584210904325349712035 33164376316356488024568053)
                    ·
                      refine ⟨3109160279658420752303255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33164376316356488024568053 3109160279658420752303255)
                      ·
                        rfl

theorem cell23_6055068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6055068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055068 prefixEnd_6055068 := by exact prefixLift 6055068
  have htrace : WordTrace (prefixWord ++ tailWord_6055068) baseStart_6055068 baseEnd_6055068 := by
    simpa [prefixWord, tailWord_6055068, baseEnd_6055068] using wordTrace_append hprefix tailTrace_6055068
  have hstable : (prefixWord ++ tailWord_6055068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055068).length < 2 ^ (prefixWord ++ tailWord_6055068).sum := by decide
  have hdescent : baseEnd_6055068 < baseStart_6055068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055082 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6055082 : Nat := 118140960795 + 6055082 * 2 ^ 59
def prefixEnd_6055082 : Nat := 4983230072969 + 3 ^ 40 * 6055082 * 2
def baseEnd_6055082 : Nat := 3109167468387583697528191

theorem tailTrace_6055082 : CollatzResearch.WordTrace tailWord_6055082 prefixEnd_6055082 3109167468387583697528191 := by
  unfold tailWord_6055082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55211745962369878629939875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147231322566319676346506333 55211745962369878629939875)
  ·
    refine ⟨82817618943554817944909813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55211745962369878629939875 82817618943554817944909813)
    ·
      refine ⟨7764151775958264182335295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82817618943554817944909813 7764151775958264182335295)
      ·
        refine ⟨11646227663937396273502943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764151775958264182335295 11646227663937396273502943)
        ·
          refine ⟨17469341495906094410254415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646227663937396273502943 17469341495906094410254415)
          ·
            refine ⟨26204012243859141615381623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469341495906094410254415 26204012243859141615381623)
            ·
              refine ⟨39306018365788712423072435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26204012243859141615381623 39306018365788712423072435)
              ·
                refine ⟨58959027548683068634608653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39306018365788712423072435 58959027548683068634608653)
                ·
                  refine ⟨22109635330756150737978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58959027548683068634608653 22109635330756150737978245)
                  ·
                    refine ⟨4145556624516778263370921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22109635330756150737978245 4145556624516778263370921)
                    ·
                      refine ⟨3109167468387583697528191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145556624516778263370921 3109167468387583697528191)
                      ·
                        rfl

theorem cell23_6055082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6055082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055082 prefixEnd_6055082 := by exact prefixLift 6055082
  have htrace : WordTrace (prefixWord ++ tailWord_6055082) baseStart_6055082 baseEnd_6055082 := by
    simpa [prefixWord, tailWord_6055082, baseEnd_6055082] using wordTrace_append hprefix tailTrace_6055082
  have hstable : (prefixWord ++ tailWord_6055082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055082).length < 2 ^ (prefixWord ++ tailWord_6055082).sum := by decide
  have hdescent : baseEnd_6055082 < baseStart_6055082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055098 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_6055098 : Nat := 118140960795 + 6055098 * 2 ^ 59
def prefixEnd_6055098 : Nat := 4983230072969 + 3 ^ 40 * 6055098 * 2
def baseEnd_6055098 : Nat := 3109175684078055634928117

theorem tailTrace_6055098 : CollatzResearch.WordTrace tailWord_6055098 prefixEnd_6055098 3109175684078055634928117 := by
  unfold tailWord_6055098
  simp only [CollatzResearch.WordTrace]
  refine ⟨55211891854355387313085487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147231711611614366168227965 55211891854355387313085487)
  ·
    refine ⟨82817837781533080969628231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55211891854355387313085487 82817837781533080969628231)
    ·
      refine ⟨124226756672299621454442347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82817837781533080969628231 124226756672299621454442347)
      ·
        refine ⟨186340135008449432181663521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124226756672299621454442347 186340135008449432181663521)
        ·
          refine ⟨139755101256337074136247641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186340135008449432181663521 139755101256337074136247641)
          ·
            refine ⟨104816325942252805602185731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139755101256337074136247641 104816325942252805602185731)
            ·
              refine ⟨157224488913379208403278597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104816325942252805602185731 157224488913379208403278597)
              ·
                refine ⟨29479591671258601575614737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157224488913379208403278597 29479591671258601575614737)
                ·
                  refine ⟨22109693753443951181711053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29479591671258601575614737 22109693753443951181711053)
                  ·
                    refine ⟨8291135157541481693141645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22109693753443951181711053 8291135157541481693141645)
                    ·
                      refine ⟨3109175684078055634928117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8291135157541481693141645 3109175684078055634928117)
                      ·
                        rfl

theorem cell23_6055098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_6055098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055098 prefixEnd_6055098 := by exact prefixLift 6055098
  have htrace : WordTrace (prefixWord ++ tailWord_6055098) baseStart_6055098 baseEnd_6055098 := by
    simpa [prefixWord, tailWord_6055098, baseEnd_6055098] using wordTrace_append hprefix tailTrace_6055098
  have hstable : (prefixWord ++ tailWord_6055098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055098).length < 2 ^ (prefixWord ++ tailWord_6055098).sum := by decide
  have hdescent : baseEnd_6055098 < baseStart_6055098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055155 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 4, 2]
def baseStart_6055155 : Nat := 118140960795 + 6055155 * 2 ^ 59
def prefixEnd_6055155 : Nat := 4983230072969 + 3 ^ 40 * 6055155 * 2
def baseEnd_6055155 : Nat := 3109204952475361911915355

theorem tailTrace_6055155 : CollatzResearch.WordTrace tailWord_6055155 prefixEnd_6055155 3109204952475361911915355 := by
  unfold tailWord_6055155
  simp only [CollatzResearch.WordTrace]
  refine ⟨220849646378215047987166919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147233097585476698658111279 220849646378215047987166919)
  ·
    refine ⟨331274469567322571980750379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220849646378215047987166919 331274469567322571980750379)
    ·
      refine ⟨496911704350983857971125569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331274469567322571980750379 496911704350983857971125569)
      ·
        refine ⟨372683778263237893478344177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496911704350983857971125569 372683778263237893478344177)
        ·
          refine ⟨279512833697428420108758133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372683778263237893478344177 279512833697428420108758133)
          ·
            refine ⟨26204328159133914385196075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279512833697428420108758133 26204328159133914385196075)
            ·
              refine ⟨39306492238700871577794113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26204328159133914385196075 39306492238700871577794113)
              ·
                refine ⟨29479869179025653683345585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39306492238700871577794113 29479869179025653683345585)
                ·
                  refine ⟨22109901884269240262509189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29479869179025653683345585 22109901884269240262509189)
                  ·
                    refine ⟨4145606603300482549220473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22109901884269240262509189 4145606603300482549220473)
                    ·
                      refine ⟨3109204952475361911915355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145606603300482549220473 3109204952475361911915355)
                      ·
                        rfl

theorem cell23_6055155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4, 2].length) (baseStart_6055155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055155 prefixEnd_6055155 := by exact prefixLift 6055155
  have htrace : WordTrace (prefixWord ++ tailWord_6055155) baseStart_6055155 baseEnd_6055155 := by
    simpa [prefixWord, tailWord_6055155, baseEnd_6055155] using wordTrace_append hprefix tailTrace_6055155
  have hstable : (prefixWord ++ tailWord_6055155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055155).length < 2 ^ (prefixWord ++ tailWord_6055155).sum := by decide
  have hdescent : baseEnd_6055155 < baseStart_6055155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055172 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6055172 : Nat := 118140960795 + 6055172 * 2 ^ 59
def prefixEnd_6055172 : Nat := 4983230072969 + 3 ^ 40 * 6055172 * 2
def baseEnd_6055172 : Nat := 3109213681646488345402777

theorem tailTrace_6055172 : CollatzResearch.WordTrace tailWord_6055172 prefixEnd_6055172 3109213681646488345402777 := by
  unfold tailWord_6055172
  simp only [CollatzResearch.WordTrace]
  refine ⟨110425133209576729945267885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147233510946102306593690513 110425133209576729945267885)
  ·
    refine ⟨41409424953591273729475457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110425133209576729945267885 41409424953591273729475457)
    ·
      refine ⟨31057068715193455297106593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41409424953591273729475457 31057068715193455297106593)
      ·
        refine ⟨23292801536395091472829945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31057068715193455297106593 23292801536395091472829945)
        ·
          refine ⟨17469601152296318604622459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23292801536395091472829945 17469601152296318604622459)
          ·
            refine ⟨26204401728444477906933689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469601152296318604622459 26204401728444477906933689)
            ·
              refine ⟨19653301296333358430200267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26204401728444477906933689 19653301296333358430200267)
              ·
                refine ⟨29479951944500037645300401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19653301296333358430200267 29479951944500037645300401)
                ·
                  refine ⟨22109963958375028233975301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29479951944500037645300401 22109963958375028233975301)
                  ·
                    refine ⟨4145618242195317793870369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22109963958375028233975301 4145618242195317793870369)
                    ·
                      refine ⟨3109213681646488345402777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145618242195317793870369 3109213681646488345402777)
                      ·
                        rfl

theorem cell23_6055172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6055172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055172 prefixEnd_6055172 := by exact prefixLift 6055172
  have htrace : WordTrace (prefixWord ++ tailWord_6055172) baseStart_6055172 baseEnd_6055172 := by
    simpa [prefixWord, tailWord_6055172, baseEnd_6055172] using wordTrace_append hprefix tailTrace_6055172
  have hstable : (prefixWord ++ tailWord_6055172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055172).length < 2 ^ (prefixWord ++ tailWord_6055172).sum := by decide
  have hdescent : baseEnd_6055172 < baseStart_6055172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055255 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 6]
def baseStart_6055255 : Nat := 118140960795 + 6055255 * 2 ^ 59
def prefixEnd_6055255 : Nat := 4983230072969 + 3 ^ 40 * 6055255 * 2
def baseEnd_6055255 : Nat := 1036418766846937173554965

theorem tailTrace_6055255 : CollatzResearch.WordTrace tailWord_6055255 prefixEnd_6055255 1036418766846937173554965 := by
  unfold tailWord_6055255
  simp only [CollatzResearch.WordTrace]
  refine ⟨220853293677852765065807219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147235529118568510043871479 220853293677852765065807219)
  ·
    refine ⟨331279940516779147598710829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220853293677852765065807219 331279940516779147598710829)
    ·
      refine ⟨124229977693792180349516561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331279940516779147598710829 124229977693792180349516561)
      ·
        refine ⟨93172483270344135262137421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124229977693792180349516561 93172483270344135262137421)
        ·
          refine ⟨34939681226379050723301533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93172483270344135262137421 34939681226379050723301533)
          ·
            refine ⟨13102380459892144021238075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34939681226379050723301533 13102380459892144021238075)
            ·
              refine ⟨19653570689838216031857113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13102380459892144021238075 19653570689838216031857113)
              ·
                refine ⟨14740178017378662023892835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19653570689838216031857113 14740178017378662023892835)
                ·
                  refine ⟨22110267026067993035839253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740178017378662023892835 22110267026067993035839253)
                  ·
                    refine ⟨1036418766846937173554965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22110267026067993035839253 1036418766846937173554965)
                    ·
                      rfl

theorem cell23_6055255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_6055255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055255 prefixEnd_6055255 := by exact prefixLift 6055255
  have htrace : WordTrace (prefixWord ++ tailWord_6055255) baseStart_6055255 baseEnd_6055255 := by
    simpa [prefixWord, tailWord_6055255, baseEnd_6055255] using wordTrace_append hprefix tailTrace_6055255
  have hstable : (prefixWord ++ tailWord_6055255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055255).length < 2 ^ (prefixWord ++ tailWord_6055255).sum := by decide
  have hdescent : baseEnd_6055255 < baseStart_6055255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055268 : List Nat := [2, 3, 1, 1, 3, 13]
def baseStart_6055268 : Nat := 118140960795 + 6055268 * 2 ^ 59
def prefixEnd_6055268 : Nat := 4983230072969 + 3 ^ 40 * 6055268 * 2
def baseEnd_6055268 : Nat := 12795320888021892879845

theorem tailTrace_6055268 : CollatzResearch.WordTrace tailWord_6055268 prefixEnd_6055268 12795320888021892879845 := by
  unfold tailWord_6055268
  simp only [CollatzResearch.WordTrace]
  refine ⟨110426883913402834143015229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147235845217870445524020305 110426883913402834143015229)
  ·
    refine ⟨41410081467526062803630711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110426883913402834143015229 41410081467526062803630711)
    ·
      refine ⟨62115122201289094205446067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41410081467526062803630711 62115122201289094205446067)
      ·
        refine ⟨93172683301933641308169101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62115122201289094205446067 93172683301933641308169101)
        ·
          refine ⟨34939756238225115490563413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93172683301933641308169101 34939756238225115490563413)
          ·
            refine ⟨12795320888021892879845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 34939756238225115490563413 12795320888021892879845)
            ·
              rfl

theorem cell23_6055268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 13].length) (baseStart_6055268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055268 prefixEnd_6055268 := by exact prefixLift 6055268
  have htrace : WordTrace (prefixWord ++ tailWord_6055268) baseStart_6055268 baseEnd_6055268 := by
    simpa [prefixWord, tailWord_6055268, baseEnd_6055268] using wordTrace_append hprefix tailTrace_6055268
  have hstable : (prefixWord ++ tailWord_6055268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055268).length < 2 ^ (prefixWord ++ tailWord_6055268).sum := by decide
  have hdescent : baseEnd_6055268 < baseStart_6055268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055316 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6055316 : Nat := 118140960795 + 6055316 * 2 ^ 59
def prefixEnd_6055316 : Nat := 4983230072969 + 3 ^ 40 * 6055316 * 2
def baseEnd_6055316 : Nat := 3109287622860735782002115

theorem tailTrace_6055316 : CollatzResearch.WordTrace tailWord_6055316 prefixEnd_6055316 3109287622860735782002115 := by
  unfold tailWord_6055316
  simp only [CollatzResearch.WordTrace]
  refine ⟨110427759265315886241888901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147237012353754514989185201 110427759265315886241888901)
  ·
    refine ⟨20705204862246728670354169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110427759265315886241888901 20705204862246728670354169)
    ·
      refine ⟨15528903646685046502765627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20705204862246728670354169 15528903646685046502765627)
      ·
        refine ⟨23293355470027569754148441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528903646685046502765627 23293355470027569754148441)
        ·
          refine ⟨17470016602520677315611331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23293355470027569754148441 17470016602520677315611331)
          ·
            refine ⟨26205024903781015973416997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17470016602520677315611331 26205024903781015973416997)
            ·
              refine ⟨4913442169458940495015687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26205024903781015973416997 4913442169458940495015687)
              ·
                refine ⟨7370163254188410742523531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913442169458940495015687 7370163254188410742523531)
                ·
                  refine ⟨11055244881282616113785297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370163254188410742523531 11055244881282616113785297)
                  ·
                    refine ⟨8291433660961962085338973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11055244881282616113785297 8291433660961962085338973)
                    ·
                      refine ⟨3109287622860735782002115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8291433660961962085338973 3109287622860735782002115)
                      ·
                        rfl

theorem cell23_6055316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6055316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055316 prefixEnd_6055316 := by exact prefixLift 6055316
  have htrace : WordTrace (prefixWord ++ tailWord_6055316) baseStart_6055316 baseEnd_6055316 := by
    simpa [prefixWord, tailWord_6055316, baseEnd_6055316] using wordTrace_append hprefix tailTrace_6055316
  have hstable : (prefixWord ++ tailWord_6055316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055316).length < 2 ^ (prefixWord ++ tailWord_6055316).sum := by decide
  have hdescent : baseEnd_6055316 < baseStart_6055316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055345 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_6055345 : Nat := 118140960795 + 6055345 * 2 ^ 59
def prefixEnd_6055345 : Nat := 4983230072969 + 3 ^ 40 * 6055345 * 2
def baseEnd_6055345 : Nat := 1036434171266572056179827

theorem tailTrace_6055345 : CollatzResearch.WordTrace tailWord_6055345 prefixEnd_6055345 1036434171266572056179827 := by
  unfold tailWord_6055345
  simp only [CollatzResearch.WordTrace]
  refine ⟨220856576247526710436583489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147237717498351140291055659 220856576247526710436583489)
  ·
    refine ⟨165642432185645032827437617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220856576247526710436583489 165642432185645032827437617)
    ·
      refine ⟨124231824139233774620578213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165642432185645032827437617 124231824139233774620578213)
      ·
        refine ⟨23293467026106332741358415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124231824139233774620578213 23293467026106332741358415)
        ·
          refine ⟨34940200539159499112037623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23293467026106332741358415 34940200539159499112037623)
          ·
            refine ⟨52410300808739248668056435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34940200539159499112037623 52410300808739248668056435)
            ·
              refine ⟨78615451213108873002084653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52410300808739248668056435 78615451213108873002084653)
              ·
                refine ⟨29480794204915827375781745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78615451213108873002084653 29480794204915827375781745)
                ·
                  refine ⟨22110595653686870531836309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29480794204915827375781745 22110595653686870531836309)
                  ·
                    refine ⟨1036434171266572056179827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22110595653686870531836309 1036434171266572056179827)
                    ·
                      rfl

theorem cell23_6055345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_6055345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055345 prefixEnd_6055345 := by exact prefixLift 6055345
  have htrace : WordTrace (prefixWord ++ tailWord_6055345) baseStart_6055345 baseEnd_6055345 := by
    simpa [prefixWord, tailWord_6055345, baseEnd_6055345] using wordTrace_append hprefix tailTrace_6055345
  have hstable : (prefixWord ++ tailWord_6055345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055345).length < 2 ^ (prefixWord ++ tailWord_6055345).sum := by decide
  have hdescent : baseEnd_6055345 < baseStart_6055345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055372 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6055372 : Nat := 118140960795 + 6055372 * 2 ^ 59
def prefixEnd_6055372 : Nat := 4983230072969 + 3 ^ 40 * 6055372 * 2
def baseEnd_6055372 : Nat := 3109316377777387562901857

theorem tailTrace_6055372 : CollatzResearch.WordTrace tailWord_6055372 prefixEnd_6055372 3109316377777387562901857 := by
  unfold tailWord_6055372
  simp only [CollatzResearch.WordTrace]
  refine ⟨110428780509214447023908185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147238374012285929365210913 110428780509214447023908185)
  ·
    refine ⟨82821585381910835267931139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110428780509214447023908185 82821585381910835267931139)
    ·
      refine ⟨124232378072866252901896709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82821585381910835267931139 124232378072866252901896709)
      ·
        refine ⟨23293570888662422419105633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124232378072866252901896709 23293570888662422419105633)
        ·
          refine ⟨17470178166496816814329225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23293570888662422419105633 17470178166496816814329225)
          ·
            refine ⟨13102633624872612610746919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17470178166496816814329225 13102633624872612610746919)
            ·
              refine ⟨19653950437308918916120379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13102633624872612610746919 19653950437308918916120379)
              ·
                refine ⟨29480925655963378374180569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19653950437308918916120379 29480925655963378374180569)
                ·
                  refine ⟨22110694241972533780635427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29480925655963378374180569 22110694241972533780635427)
                  ·
                    refine ⟨33166041362958800670953141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22110694241972533780635427 33166041362958800670953141)
                    ·
                      refine ⟨3109316377777387562901857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33166041362958800670953141 3109316377777387562901857)
                      ·
                        rfl

theorem cell23_6055372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6055372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055372 prefixEnd_6055372 := by exact prefixLift 6055372
  have htrace : WordTrace (prefixWord ++ tailWord_6055372) baseStart_6055372 baseEnd_6055372 := by
    simpa [prefixWord, tailWord_6055372, baseEnd_6055372] using wordTrace_append hprefix tailTrace_6055372
  have hstable : (prefixWord ++ tailWord_6055372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055372).length < 2 ^ (prefixWord ++ tailWord_6055372).sum := by decide
  have hdescent : baseEnd_6055372 < baseStart_6055372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055437 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6055437 : Nat := 118140960795 + 6055437 * 2 ^ 59
def prefixEnd_6055437 : Nat := 4983230072969 + 3 ^ 40 * 6055437 * 2
def baseEnd_6055437 : Nat := 3109349754019929808589059

theorem tailTrace_6055437 : CollatzResearch.WordTrace tailWord_6055437 prefixEnd_6055437 3109349754019929808589059 := by
  unfold tailWord_6055437
  simp only [CollatzResearch.WordTrace]
  refine ⟨220859931763193410148932565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147239954508795606765955043 220859931763193410148932565)
  ·
    refine ⟨5176404650699845550365607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 220859931763193410148932565 5176404650699845550365607)
    ·
      refine ⟨7764606976049768325548411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176404650699845550365607 7764606976049768325548411)
      ·
        refine ⟨11646910464074652488322617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764606976049768325548411 11646910464074652488322617)
        ·
          refine ⟨8735182848055989366241963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11646910464074652488322617 8735182848055989366241963)
          ·
            refine ⟨13102774272083984049362945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735182848055989366241963 13102774272083984049362945)
            ·
              refine ⟨9827080704062988037022209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13102774272083984049362945 9827080704062988037022209)
              ·
                refine ⟨7370310528047241027766657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9827080704062988037022209 7370310528047241027766657)
                ·
                  refine ⟨5527732896035430770824993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370310528047241027766657 5527732896035430770824993)
                  ·
                    refine ⟨4145799672026573078118745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5527732896035430770824993 4145799672026573078118745)
                    ·
                      refine ⟨3109349754019929808589059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4145799672026573078118745 3109349754019929808589059)
                      ·
                        rfl

theorem cell23_6055437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6055437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055437 prefixEnd_6055437 := by exact prefixLift 6055437
  have htrace : WordTrace (prefixWord ++ tailWord_6055437) baseStart_6055437 baseEnd_6055437 := by
    simpa [prefixWord, tailWord_6055437, baseEnd_6055437] using wordTrace_append hprefix tailTrace_6055437
  have hstable : (prefixWord ++ tailWord_6055437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055437).length < 2 ^ (prefixWord ++ tailWord_6055437).sum := by decide
  have hdescent : baseEnd_6055437 < baseStart_6055437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055479 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_6055479 : Nat := 118140960795 + 6055479 * 2 ^ 59
def prefixEnd_6055479 : Nat := 4983230072969 + 3 ^ 40 * 6055479 * 2
def baseEnd_6055479 : Nat := 3109371320207418644263865

theorem tailTrace_6055479 : CollatzResearch.WordTrace tailWord_6055479 prefixEnd_6055479 3109371320207418644263865 := by
  unfold tailWord_6055479
  simp only [CollatzResearch.WordTrace]
  refine ⟨220861463629041251321961491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147240975752694167547974327 220861463629041251321961491)
  ·
    refine ⟨331292195443561876982942237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220861463629041251321961491 331292195443561876982942237)
    ·
      refine ⟨124234573291335703868603339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331292195443561876982942237 124234573291335703868603339)
      ·
        refine ⟨186351859937003555802905009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124234573291335703868603339 186351859937003555802905009)
        ·
          refine ⟨139763894952752666852178757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186351859937003555802905009 139763894952752666852178757)
          ·
            refine ⟨26205730303641125034783517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139763894952752666852178757 26205730303641125034783517)
            ·
              refine ⟨9827148863865421888043819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26205730303641125034783517 9827148863865421888043819)
              ·
                refine ⟨14740723295798132832065729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9827148863865421888043819 14740723295798132832065729)
                ·
                  refine ⟨11055542471848599624049297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14740723295798132832065729 11055542471848599624049297)
                  ·
                    refine ⟨8291656853886449718036973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11055542471848599624049297 8291656853886449718036973)
                    ·
                      refine ⟨3109371320207418644263865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8291656853886449718036973 3109371320207418644263865)
                      ·
                        rfl

theorem cell23_6055479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_6055479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055479 prefixEnd_6055479 := by exact prefixLift 6055479
  have htrace : WordTrace (prefixWord ++ tailWord_6055479) baseStart_6055479 baseEnd_6055479 := by
    simpa [prefixWord, tailWord_6055479, baseEnd_6055479] using wordTrace_append hprefix tailTrace_6055479
  have hstable : (prefixWord ++ tailWord_6055479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055479).length < 2 ^ (prefixWord ++ tailWord_6055479).sum := by decide
  have hdescent : baseEnd_6055479 < baseStart_6055479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055516 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 6]
def baseStart_6055516 : Nat := 118140960795 + 6055516 * 2 ^ 59
def prefixEnd_6055516 : Nat := 4983230072969 + 3 ^ 40 * 6055516 * 2
def baseEnd_6055516 : Nat := 345487813221292777722355

theorem tailTrace_6055516 : CollatzResearch.WordTrace tailWord_6055516 prefixEnd_6055516 345487813221292777722355 := by
  unfold tailWord_6055516
  simp only [CollatzResearch.WordTrace]
  refine ⟨110431406564953603320529201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147241875419938137760705601 110431406564953603320529201)
  ·
    refine ⟨82823554923715202490396901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110431406564953603320529201 82823554923715202490396901)
    ·
      refine ⟨15529416548196600466949419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82823554923715202490396901 15529416548196600466949419)
      ·
        refine ⟨23294124822294900700424129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529416548196600466949419 23294124822294900700424129)
        ·
          refine ⟨17470593616721175525318097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23294124822294900700424129 17470593616721175525318097)
          ·
            refine ⟨13102945212540881643988573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17470593616721175525318097 13102945212540881643988573)
            ·
              refine ⟨4913604454702830616495715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13102945212540881643988573 4913604454702830616495715)
              ·
                refine ⟨7370406682054245924743573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913604454702830616495715 7370406682054245924743573)
                ·
                  refine ⟨345487813221292777722355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7370406682054245924743573 345487813221292777722355)
                  ·
                    rfl

theorem cell23_6055516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_6055516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055516 prefixEnd_6055516 := by exact prefixLift 6055516
  have htrace : WordTrace (prefixWord ++ tailWord_6055516) baseStart_6055516 baseEnd_6055516 := by
    simpa [prefixWord, tailWord_6055516, baseEnd_6055516] using wordTrace_append hprefix tailTrace_6055516
  have hstable : (prefixWord ++ tailWord_6055516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055516).length < 2 ^ (prefixWord ++ tailWord_6055516).sum := by decide
  have hdescent : baseEnd_6055516 < baseStart_6055516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055559 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 4, 4]
def baseStart_6055559 : Nat := 118140960795 + 6055559 * 2 ^ 59
def prefixEnd_6055559 : Nat := 4983230072969 + 3 ^ 40 * 6055559 * 2
def baseEnd_6055559 : Nat := 1036470799553259443754499

theorem tailTrace_6055559 : CollatzResearch.WordTrace tailWord_6055559 prefixEnd_6055559 1036470799553259443754499 := by
  unfold tailWord_6055559
  simp only [CollatzResearch.WordTrace]
  refine ⟨220864381468751424984873731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147242920979167616656582487 220864381468751424984873731)
  ·
    refine ⟨331296572203127137477310597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220864381468751424984873731 331296572203127137477310597)
    ·
      refine ⟨62118107288086338276995737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331296572203127137477310597 62118107288086338276995737)
      ·
        refine ⟨46588580466064753707746803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62118107288086338276995737 46588580466064753707746803)
        ·
          refine ⟨69882870699097130561620205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46588580466064753707746803 69882870699097130561620205)
          ·
            refine ⟨26206076512161423960607577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69882870699097130561620205 26206076512161423960607577)
            ·
              refine ⟨19654557384121067970455683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26206076512161423960607577 19654557384121067970455683)
              ·
                refine ⟨29481836076181601955683525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19654557384121067970455683 29481836076181601955683525)
                ·
                  refine ⟨5527844264284050366690661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29481836076181601955683525 5527844264284050366690661)
                  ·
                    refine ⟨1036470799553259443754499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5527844264284050366690661 1036470799553259443754499)
                    ·
                      rfl

theorem cell23_6055559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_6055559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055559 prefixEnd_6055559 := by exact prefixLift 6055559
  have htrace : WordTrace (prefixWord ++ tailWord_6055559) baseStart_6055559 baseEnd_6055559 := by
    simpa [prefixWord, tailWord_6055559, baseEnd_6055559] using wordTrace_append hprefix tailTrace_6055559
  have hstable : (prefixWord ++ tailWord_6055559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055559).length < 2 ^ (prefixWord ++ tailWord_6055559).sum := by decide
  have hdescent : baseEnd_6055559 < baseStart_6055559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055560 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6055560 : Nat := 118140960795 + 6055560 * 2 ^ 59
def prefixEnd_6055560 : Nat := 4983230072969 + 3 ^ 40 * 6055560 * 2
def baseEnd_6055560 : Nat := 3109412912140432827350993

theorem tailTrace_6055560 : CollatzResearch.WordTrace tailWord_6055560 prefixEnd_6055560 3109412912140432827350993 := by
  unfold tailWord_6055560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110432208970873901077830067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147242945294498534770440089 110432208970873901077830067)
  ·
    refine ⟨165648313456310851616745101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110432208970873901077830067 165648313456310851616745101)
    ·
      refine ⟨62118117546116569356279413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165648313456310851616745101 62118117546116569356279413)
      ·
        refine ⟨5823573519948428377151195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62118117546116569356279413 5823573519948428377151195)
        ·
          refine ⟨8735360279922642565726793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823573519948428377151195 8735360279922642565726793)
          ·
            refine ⟨6551520209941981924295095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735360279922642565726793 6551520209941981924295095)
            ·
              refine ⟨9827280314912972886442643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551520209941981924295095 9827280314912972886442643)
              ·
                refine ⟨14740920472369459329663965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9827280314912972886442643 14740920472369459329663965)
                ·
                  refine ⟨5527845177138547248623987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14740920472369459329663965 5527845177138547248623987)
                  ·
                    refine ⟨8291767765707820872935981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5527845177138547248623987 8291767765707820872935981)
                    ·
                      refine ⟨3109412912140432827350993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8291767765707820872935981 3109412912140432827350993)
                      ·
                        rfl

theorem cell23_6055560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6055560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055560 prefixEnd_6055560 := by exact prefixLift 6055560
  have htrace : WordTrace (prefixWord ++ tailWord_6055560) baseStart_6055560 baseEnd_6055560 := by
    simpa [prefixWord, tailWord_6055560, baseEnd_6055560] using wordTrace_append hprefix tailTrace_6055560
  have hstable : (prefixWord ++ tailWord_6055560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055560).length < 2 ^ (prefixWord ++ tailWord_6055560).sum := by decide
  have hdescent : baseEnd_6055560 < baseStart_6055560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055576 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_6055576 : Nat := 118140960795 + 6055576 * 2 ^ 59
def prefixEnd_6055576 : Nat := 4983230072969 + 3 ^ 40 * 6055576 * 2
def baseEnd_6055576 : Nat := 1036473709276968254916973

theorem tailTrace_6055576 : CollatzResearch.WordTrace tailWord_6055576 prefixEnd_6055576 1036473709276968254916973 := by
  unfold tailWord_6055576
  simp only [CollatzResearch.WordTrace]
  refine ⟨110432500754844918444121291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147243334339793224592161721 110432500754844918444121291)
  ·
    refine ⟨165648751132267377666181937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110432500754844918444121291 165648751132267377666181937)
    ·
      refine ⟨124236563349200533249636453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165648751132267377666181937 124236563349200533249636453)
      ·
        refine ⟨23294355627975099984306835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124236563349200533249636453 23294355627975099984306835)
        ·
          refine ⟨34941533441962649976460253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23294355627975099984306835 34941533441962649976460253)
          ·
            refine ⟨13103075040735993741172595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34941533441962649976460253 13103075040735993741172595)
            ·
              refine ⟨19654612561103990611758893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103075040735993741172595 19654612561103990611758893)
              ·
                refine ⟨7370479710413996479409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19654612561103990611758893 7370479710413996479409585)
                ·
                  refine ⟨5527859782810497359557189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370479710413996479409585 5527859782810497359557189)
                  ·
                    refine ⟨1036473709276968254916973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5527859782810497359557189 1036473709276968254916973)
                    ·
                      rfl

theorem cell23_6055576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_6055576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055576 prefixEnd_6055576 := by exact prefixLift 6055576
  have htrace : WordTrace (prefixWord ++ tailWord_6055576) baseStart_6055576 baseEnd_6055576 := by
    simpa [prefixWord, tailWord_6055576, baseEnd_6055576] using wordTrace_append hprefix tailTrace_6055576
  have hstable : (prefixWord ++ tailWord_6055576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055576).length < 2 ^ (prefixWord ++ tailWord_6055576).sum := by decide
  have hdescent : baseEnd_6055576 < baseStart_6055576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055599 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_6055599 : Nat := 118140960795 + 6055599 * 2 ^ 59
def prefixEnd_6055599 : Nat := 4983230072969 + 3 ^ 40 * 6055599 * 2
def baseEnd_6055599 : Nat := 3109432937885958174763313

theorem tailTrace_6055599 : CollatzResearch.WordTrace tailWord_6055599 prefixEnd_6055599 3109432937885958174763313 := by
  unfold tailWord_6055599
  simp only [CollatzResearch.WordTrace]
  refine ⟨220865840388606511816329851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147243893592404341210886567 220865840388606511816329851)
  ·
    refine ⟨331298760582909767724494777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220865840388606511816329851 331298760582909767724494777)
    ·
      refine ⟨248474070437182325793371083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331298760582909767724494777 248474070437182325793371083)
      ·
        refine ⟨372711105655773488690056625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248474070437182325793371083 372711105655773488690056625)
        ·
          refine ⟨279533329241830116517542469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372711105655773488690056625 279533329241830116517542469)
          ·
            refine ⟨52412499232843146847039213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279533329241830116517542469 52412499232843146847039213)
            ·
              refine ⟨19654687212316180067639705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52412499232843146847039213 19654687212316180067639705)
              ·
                refine ⟨14741015409237135050729779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19654687212316180067639705 14741015409237135050729779)
                ·
                  refine ⟨22111523113855702576094669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14741015409237135050729779 22111523113855702576094669)
                  ·
                    refine ⟨8291821167695888466035501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22111523113855702576094669 8291821167695888466035501)
                    ·
                      refine ⟨3109432937885958174763313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8291821167695888466035501 3109432937885958174763313)
                      ·
                        rfl

theorem cell23_6055599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_6055599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055599 prefixEnd_6055599 := by exact prefixLift 6055599
  have htrace : WordTrace (prefixWord ++ tailWord_6055599) baseStart_6055599 baseEnd_6055599 := by
    simpa [prefixWord, tailWord_6055599, baseEnd_6055599] using wordTrace_append hprefix tailTrace_6055599
  have hstable : (prefixWord ++ tailWord_6055599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055599).length < 2 ^ (prefixWord ++ tailWord_6055599).sum := by decide
  have hdescent : baseEnd_6055599 < baseStart_6055599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_6055672 : Nat := 118140960795 + 6055672 * 2 ^ 59
def prefixEnd_6055672 : Nat := 4983230072969 + 3 ^ 40 * 6055672 * 2
def baseEnd_6055672 : Nat := 3109470421973736389150477

theorem tailTrace_6055672 : CollatzResearch.WordTrace tailWord_6055672 prefixEnd_6055672 3109470421973736389150477 := by
  unfold tailWord_6055672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110434251458671022641868635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147245668611561363522491513 110434251458671022641868635)
  ·
    refine ⟨165651377188006533962802953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110434251458671022641868635 165651377188006533962802953)
    ·
      refine ⟨124238532891004900472102215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165651377188006533962802953 124238532891004900472102215)
      ·
        refine ⟨186357799336507350708153323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124238532891004900472102215 186357799336507350708153323)
        ·
          refine ⟨279536699004761026062229985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186357799336507350708153323 279536699004761026062229985)
          ·
            refine ⟨209652524253570769546672489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279536699004761026062229985 209652524253570769546672489)
            ·
              refine ⟨157239393190178077160004367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209652524253570769546672489 157239393190178077160004367)
              ·
                refine ⟨235859089785267115740006551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157239393190178077160004367 235859089785267115740006551)
                ·
                  refine ⟨353788634677900673610009827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235859089785267115740006551 353788634677900673610009827)
                  ·
                    refine ⟨530682952016851010415014741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353788634677900673610009827 530682952016851010415014741)
                    ·
                      refine ⟨3109470421973736389150477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 530682952016851010415014741 3109470421973736389150477)
                      ·
                        rfl

theorem cell23_6055672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_6055672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055672 prefixEnd_6055672 := by exact prefixLift 6055672
  have htrace : WordTrace (prefixWord ++ tailWord_6055672) baseStart_6055672 baseEnd_6055672 := by
    simpa [prefixWord, tailWord_6055672, baseEnd_6055672] using wordTrace_append hprefix tailTrace_6055672
  have hstable : (prefixWord ++ tailWord_6055672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055672).length < 2 ^ (prefixWord ++ tailWord_6055672).sum := by decide
  have hdescent : baseEnd_6055672 < baseStart_6055672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055710 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6055710 : Nat := 118140960795 + 6055710 * 2 ^ 59
def prefixEnd_6055710 : Nat := 4983230072969 + 3 ^ 40 * 6055710 * 2
def baseEnd_6055710 : Nat := 3109489934238607240475303

theorem tailTrace_6055710 : CollatzResearch.WordTrace tailWord_6055710 prefixEnd_6055710 3109489934238607240475303 := by
  unfold tailWord_6055710
  simp only [CollatzResearch.WordTrace]
  refine ⟨27608736111400547221702573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147246592594136251849080389 27608736111400547221702573)
  ·
    refine ⟨10353276041775205208138465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27608736111400547221702573 10353276041775205208138465)
    ·
      refine ⟨7764957031331403906103849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10353276041775205208138465 7764957031331403906103849)
      ·
        refine ⟨5823717773498552929577887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7764957031331403906103849 5823717773498552929577887)
        ·
          refine ⟨8735576660247829394366831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823717773498552929577887 8735576660247829394366831)
          ·
            refine ⟨13103364990371744091550247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735576660247829394366831 13103364990371744091550247)
            ·
              refine ⟨19655047485557616137325371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103364990371744091550247 19655047485557616137325371)
              ·
                refine ⟨29482571228336424205988057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19655047485557616137325371 29482571228336424205988057)
                ·
                  refine ⟨22111928421252318154491043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29482571228336424205988057 22111928421252318154491043)
                  ·
                    refine ⟨33167892631878477231736565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22111928421252318154491043 33167892631878477231736565)
                    ·
                      refine ⟨3109489934238607240475303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33167892631878477231736565 3109489934238607240475303)
                      ·
                        rfl

theorem cell23_6055710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6055710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055710 prefixEnd_6055710 := by exact prefixLift 6055710
  have htrace : WordTrace (prefixWord ++ tailWord_6055710) baseStart_6055710 baseEnd_6055710 := by
    simpa [prefixWord, tailWord_6055710, baseEnd_6055710] using wordTrace_append hprefix tailTrace_6055710
  have hstable : (prefixWord ++ tailWord_6055710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055710).length < 2 ^ (prefixWord ++ tailWord_6055710).sum := by decide
  have hdescent : baseEnd_6055710 < baseStart_6055710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055713 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 5]
def baseStart_6055713 : Nat := 118140960795 + 6055713 * 2 ^ 59
def prefixEnd_6055713 : Nat := 4983230072969 + 3 ^ 40 * 6055713 * 2
def baseEnd_6055713 : Nat := 345499052742285636526421

theorem tailTrace_6055713 : CollatzResearch.WordTrace tailWord_6055713 prefixEnd_6055713 345499052742285636526421 := by
  unfold tailWord_6055713
  simp only [CollatzResearch.WordTrace]
  refine ⟨220869998310193509285979793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147246665540129006190653195 220869998310193509285979793)
  ·
    refine ⟨165652498732645131964484845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220869998310193509285979793 165652498732645131964484845)
    ·
      refine ⟨62119687024741924486681817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165652498732645131964484845 62119687024741924486681817)
      ·
        refine ⟨46589765268556443365011363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62119687024741924486681817 46589765268556443365011363)
        ·
          refine ⟨69884647902834665047517045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46589765268556443365011363 69884647902834665047517045)
          ·
            refine ⟨6551685740890749848204723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69884647902834665047517045 6551685740890749848204723)
            ·
              refine ⟨9827528611336124772307085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551685740890749848204723 9827528611336124772307085)
              ·
                refine ⟨3685323229251046789615157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9827528611336124772307085 3685323229251046789615157)
                ·
                  refine ⟨345499052742285636526421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685323229251046789615157 345499052742285636526421)
                  ·
                    rfl

theorem cell23_6055713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 5].length) (baseStart_6055713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055713 prefixEnd_6055713 := by exact prefixLift 6055713
  have htrace : WordTrace (prefixWord ++ tailWord_6055713) baseStart_6055713 baseEnd_6055713 := by
    simpa [prefixWord, tailWord_6055713, baseEnd_6055713] using wordTrace_append hprefix tailTrace_6055713
  have hstable : (prefixWord ++ tailWord_6055713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055713).length < 2 ^ (prefixWord ++ tailWord_6055713).sum := by decide
  have hdescent : baseEnd_6055713 < baseStart_6055713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055813 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_6055813 : Nat := 118140960795 + 6055813 * 2 ^ 59
def prefixEnd_6055813 : Nat := 4983230072969 + 3 ^ 40 * 6055813 * 2
def baseEnd_6055813 : Nat := 3109542822746020337487329

theorem tailTrace_6055813 : CollatzResearch.WordTrace tailWord_6055813 prefixEnd_6055813 3109542822746020337487329 := by
  unfold tailWord_6055813
  simp only [CollatzResearch.WordTrace]
  refine ⟨220873645609831226364620093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147249097073220817576413395 220873645609831226364620093)
  ·
    refine ⟨82827617103686709886732535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220873645609831226364620093 82827617103686709886732535)
    ·
      refine ⟨124241425655530064830098803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82827617103686709886732535 124241425655530064830098803)
      ·
        refine ⟨186362138483295097245148205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124241425655530064830098803 186362138483295097245148205)
        ·
          refine ⟨69885801931235661466930577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186362138483295097245148205 69885801931235661466930577)
          ·
            refine ⟨52414351448426746100197933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69885801931235661466930577 52414351448426746100197933)
            ·
              refine ⟨19655381793160029787574225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52414351448426746100197933 19655381793160029787574225)
              ·
                refine ⟨14741536344870022340680669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19655381793160029787574225 14741536344870022340680669)
                ·
                  refine ⟨5528076129326258377755251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14741536344870022340680669 5528076129326258377755251)
                  ·
                    refine ⟨8292114193989387566632877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528076129326258377755251 8292114193989387566632877)
                    ·
                      refine ⟨3109542822746020337487329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292114193989387566632877 3109542822746020337487329)
                      ·
                        rfl

theorem cell23_6055813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_6055813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055813 prefixEnd_6055813 := by exact prefixLift 6055813
  have htrace : WordTrace (prefixWord ++ tailWord_6055813) baseStart_6055813 baseEnd_6055813 := by
    simpa [prefixWord, tailWord_6055813, baseEnd_6055813] using wordTrace_append hprefix tailTrace_6055813
  have hstable : (prefixWord ++ tailWord_6055813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055813).length < 2 ^ (prefixWord ++ tailWord_6055813).sum := by decide
  have hdescent : baseEnd_6055813 < baseStart_6055813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055833 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_6055833 : Nat := 118140960795 + 6055833 * 2 ^ 59
def prefixEnd_6055833 : Nat := 4983230072969 + 3 ^ 40 * 6055833 * 2
def baseEnd_6055833 : Nat := 1036517697453036753079079

theorem tailTrace_6055833 : CollatzResearch.WordTrace tailWord_6055833 prefixEnd_6055833 1036517697453036753079079 := by
  unfold tailWord_6055833
  simp only [CollatzResearch.WordTrace]
  refine ⟨220874375069758769780348153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147249583379839179853565435 220874375069758769780348153)
  ·
    refine ⟨165655781302319077335261115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220874375069758769780348153 165655781302319077335261115)
    ·
      refine ⟨248483671953478616002891673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165655781302319077335261115 248483671953478616002891673)
      ·
        refine ⟨186362753965108962002168755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248483671953478616002891673 186362753965108962002168755)
        ·
          refine ⟨279544130947663443003253133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186362753965108962002168755 279544130947663443003253133)
          ·
            refine ⟨104829049105373791126219925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279544130947663443003253133 104829049105373791126219925)
            ·
              refine ⟨4913861676814396459041559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104829049105373791126219925 4913861676814396459041559)
              ·
                refine ⟨7370792515221594688562339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913861676814396459041559 7370792515221594688562339)
                ·
                  refine ⟨11056188772832392032843509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370792515221594688562339 11056188772832392032843509)
                  ·
                    refine ⟨1036517697453036753079079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11056188772832392032843509 1036517697453036753079079)
                    ·
                      rfl

theorem cell23_6055833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_6055833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055833 prefixEnd_6055833 := by exact prefixLift 6055833
  have htrace : WordTrace (prefixWord ++ tailWord_6055833) baseStart_6055833 baseEnd_6055833 := by
    simpa [prefixWord, tailWord_6055833, baseEnd_6055833] using wordTrace_append hprefix tailTrace_6055833
  have hstable : (prefixWord ++ tailWord_6055833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055833).length < 2 ^ (prefixWord ++ tailWord_6055833).sum := by decide
  have hdescent : baseEnd_6055833 < baseStart_6055833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055847 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6055847 : Nat := 118140960795 + 6055847 * 2 ^ 59
def prefixEnd_6055847 : Nat := 4983230072969 + 3 ^ 40 * 6055847 * 2
def baseEnd_6055847 : Nat := 3109560281088273204462173

theorem tailTrace_6055847 : CollatzResearch.WordTrace tailWord_6055847 prefixEnd_6055847 3109560281088273204462173 := by
  unfold tailWord_6055847
  simp only [CollatzResearch.WordTrace]
  refine ⟨220874885691708050171357795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147249923794472033447571863 220874885691708050171357795)
  ·
    refine ⟨331312328537562075257036693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220874885691708050171357795 331312328537562075257036693)
    ·
      refine ⟨15530265400198222277673595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 331312328537562075257036693 15530265400198222277673595)
      ·
        refine ⟨23295398100297333416510393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15530265400198222277673595 23295398100297333416510393)
        ·
          refine ⟨17471548575223000062382795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23295398100297333416510393 17471548575223000062382795)
          ·
            refine ⟨26207322862834500093574193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17471548575223000062382795 26207322862834500093574193)
            ·
              refine ⟨19655492147125875070180645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26207322862834500093574193 19655492147125875070180645)
              ·
                refine ⟨3685404777586101575658871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19655492147125875070180645 3685404777586101575658871)
                ·
                  refine ⟨5528107166379152363488307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685404777586101575658871 5528107166379152363488307)
                  ·
                    refine ⟨8292160749568728545232461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528107166379152363488307 8292160749568728545232461)
                    ·
                      refine ⟨3109560281088273204462173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292160749568728545232461 3109560281088273204462173)
                      ·
                        rfl

theorem cell23_6055847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6055847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055847 prefixEnd_6055847 := by exact prefixLift 6055847
  have htrace : WordTrace (prefixWord ++ tailWord_6055847) baseStart_6055847 baseEnd_6055847 := by
    simpa [prefixWord, tailWord_6055847, baseEnd_6055847] using wordTrace_append hprefix tailTrace_6055847
  have hstable : (prefixWord ++ tailWord_6055847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055847).length < 2 ^ (prefixWord ++ tailWord_6055847).sum := by decide
  have hdescent : baseEnd_6055847 < baseStart_6055847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055854 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_6055854 : Nat := 118140960795 + 6055854 * 2 ^ 59
def prefixEnd_6055854 : Nat := 4983230072969 + 3 ^ 40 * 6055854 * 2
def baseEnd_6055854 : Nat := 345507097272539408563849

theorem tailTrace_6055854 : CollatzResearch.WordTrace tailWord_6055854 prefixEnd_6055854 345507097272539408563849 := by
  unfold tailWord_6055854
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609392625335336295857827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147250094001788460244575077 27609392625335336295857827)
  ·
    refine ⟨41414088938003004443786741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27609392625335336295857827 41414088938003004443786741)
    ·
      refine ⟨3882570837937781666605007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41414088938003004443786741 3882570837937781666605007)
      ·
        refine ⟨5823856256906672499907511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882570837937781666605007 5823856256906672499907511)
        ·
          refine ⟨8735784385360008749861267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823856256906672499907511 8735784385360008749861267)
          ·
            refine ⟨13103676578040013124791901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735784385360008749861267 13103676578040013124791901)
            ·
              refine ⟨4913878716765004921796963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13103676578040013124791901 4913878716765004921796963)
              ·
                refine ⟨7370818075147507382695445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913878716765004921796963 7370818075147507382695445)
                ·
                  refine ⟨345507097272539408563849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7370818075147507382695445 345507097272539408563849)
                  ·
                    rfl

theorem cell23_6055854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_6055854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055854 prefixEnd_6055854 := by exact prefixLift 6055854
  have htrace : WordTrace (prefixWord ++ tailWord_6055854) baseStart_6055854 baseEnd_6055854 := by
    simpa [prefixWord, tailWord_6055854, baseEnd_6055854] using wordTrace_append hprefix tailTrace_6055854
  have hstable : (prefixWord ++ tailWord_6055854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055854).length < 2 ^ (prefixWord ++ tailWord_6055854).sum := by decide
  have hdescent : baseEnd_6055854 < baseStart_6055854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055859 : List Nat := [1, 1, 1, 2, 3, 1, 4, 10]
def baseStart_6055859 : Nat := 118140960795 + 6055859 * 2 ^ 59
def prefixEnd_6055859 : Nat := 4983230072969 + 3 ^ 40 * 6055859 * 2
def baseEnd_6055859 : Nat := 115169127513189894722671

theorem tailTrace_6055859 : CollatzResearch.WordTrace tailWord_6055859 prefixEnd_6055859 115169127513189894722671 := by
  unfold tailWord_6055859
  simp only [CollatzResearch.WordTrace]
  refine ⟨220875323367664576220794631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147250215578443050813863087 220875323367664576220794631)
  ·
    refine ⟨331312985051496864331191947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220875323367664576220794631 331312985051496864331191947)
    ·
      refine ⟨496969477577245296496787921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331312985051496864331191947 496969477577245296496787921)
      ·
        refine ⟨372727108182933972372590941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496969477577245296496787921 372727108182933972372590941)
        ·
          refine ⟨139772665568600239639721603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372727108182933972372590941 139772665568600239639721603)
          ·
            refine ⟨209658998352900359459582405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139772665568600239639721603 209658998352900359459582405)
            ·
              refine ⟨39311062191168817398671701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209658998352900359459582405 39311062191168817398671701)
              ·
                refine ⟨115169127513189894722671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39311062191168817398671701 115169127513189894722671)
                ·
                  rfl

theorem cell23_6055859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 10].length) (baseStart_6055859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055859 prefixEnd_6055859 := by exact prefixLift 6055859
  have htrace : WordTrace (prefixWord ++ tailWord_6055859) baseStart_6055859 baseEnd_6055859 := by
    simpa [prefixWord, tailWord_6055859, baseEnd_6055859] using wordTrace_append hprefix tailTrace_6055859
  have hstable : (prefixWord ++ tailWord_6055859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055859).length < 2 ^ (prefixWord ++ tailWord_6055859).sum := by decide
  have hdescent : baseEnd_6055859 < baseStart_6055859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055866 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_6055866 : Nat := 118140960795 + 6055866 * 2 ^ 59
def prefixEnd_6055866 : Nat := 4983230072969 + 3 ^ 40 * 6055866 * 2
def baseEnd_6055866 : Nat := 3109570037220708630124585

theorem tailTrace_6055866 : CollatzResearch.WordTrace tailWord_6055866 prefixEnd_6055866 3109570037220708630124585 := by
  unfold tailWord_6055866
  simp only [CollatzResearch.WordTrace]
  refine ⟨55218894669659804104074863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147250385785759477610866301 55218894669659804104074863)
  ·
    refine ⟨82828342004489706156112295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55218894669659804104074863 82828342004489706156112295)
    ·
      refine ⟨124242513006734559234168443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82828342004489706156112295 124242513006734559234168443)
      ·
        refine ⟨186363769510101838851252665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124242513006734559234168443 186363769510101838851252665)
        ·
          refine ⟨139772827132576379138439499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186363769510101838851252665 139772827132576379138439499)
          ·
            refine ⟨209659240698864568707659249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139772827132576379138439499 209659240698864568707659249)
            ·
              refine ⟨157244430524148426530744437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209659240698864568707659249 157244430524148426530744437)
              ·
                refine ⟨14741665361638914987257291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157244430524148426530744437 14741665361638914987257291)
                ·
                  refine ⟨22112498042458372480885937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14741665361638914987257291 22112498042458372480885937)
                  ·
                    refine ⟨16584373531843779360664453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22112498042458372480885937 16584373531843779360664453)
                    ·
                      refine ⟨3109570037220708630124585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16584373531843779360664453 3109570037220708630124585)
                      ·
                        rfl

theorem cell23_6055866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_6055866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055866 prefixEnd_6055866 := by exact prefixLift 6055866
  have htrace : WordTrace (prefixWord ++ tailWord_6055866) baseStart_6055866 baseEnd_6055866 := by
    simpa [prefixWord, tailWord_6055866, baseEnd_6055866] using wordTrace_append hprefix tailTrace_6055866
  have hstable : (prefixWord ++ tailWord_6055866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055866).length < 2 ^ (prefixWord ++ tailWord_6055866).sum := by decide
  have hdescent : baseEnd_6055866 < baseStart_6055866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055870 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_6055870 : Nat := 118140960795 + 6055870 * 2 ^ 59
def prefixEnd_6055870 : Nat := 4983230072969 + 3 ^ 40 * 6055870 * 2
def baseEnd_6055870 : Nat := 3109572091143326614474567

theorem tailTrace_6055870 : CollatzResearch.WordTrace tailWord_6055870 prefixEnd_6055870 3109572091143326614474567 := by
  unfold tailWord_6055870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609465571328090637430633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147250483047083150066296709 27609465571328090637430633)
  ·
    refine ⟨20707099178496067978072975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27609465571328090637430633 20707099178496067978072975)
    ·
      refine ⟨31060648767744101967109463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20707099178496067978072975 31060648767744101967109463)
      ·
        refine ⟨46590973151616152950664195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31060648767744101967109463 46590973151616152950664195)
        ·
          refine ⟨69886459727424229425996293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46590973151616152950664195 69886459727424229425996293)
          ·
            refine ⟨13103711198892043017374305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69886459727424229425996293 13103711198892043017374305)
            ·
              refine ⟨9827783399169032263030729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13103711198892043017374305 9827783399169032263030729)
              ·
                refine ⟨7370837549376774197273047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9827783399169032263030729 7370837549376774197273047)
                ·
                  refine ⟨11056256324065161295909571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370837549376774197273047 11056256324065161295909571)
                  ·
                    refine ⟨16584384486097741943864357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11056256324065161295909571 16584384486097741943864357)
                    ·
                      refine ⟨3109572091143326614474567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16584384486097741943864357 3109572091143326614474567)
                      ·
                        rfl

theorem cell23_6055870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_6055870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055870 prefixEnd_6055870 := by exact prefixLift 6055870
  have htrace : WordTrace (prefixWord ++ tailWord_6055870) baseStart_6055870 baseEnd_6055870 := by
    simpa [prefixWord, tailWord_6055870, baseEnd_6055870] using wordTrace_append hprefix tailTrace_6055870
  have hstable : (prefixWord ++ tailWord_6055870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055870).length < 2 ^ (prefixWord ++ tailWord_6055870).sum := by decide
  have hdescent : baseEnd_6055870 < baseStart_6055870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055890 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6055890 : Nat := 118140960795 + 6055890 * 2 ^ 59
def prefixEnd_6055890 : Nat := 4983230072969 + 3 ^ 40 * 6055890 * 2
def baseEnd_6055890 : Nat := 3109582360756416536224475

theorem tailTrace_6055890 : CollatzResearch.WordTrace tailWord_6055890 prefixEnd_6055890 3109582360756416536224475 := by
  unfold tailWord_6055890
  simp only [CollatzResearch.WordTrace]
  refine ⟨55219113507638067128793281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147250969353701512343448749 55219113507638067128793281)
  ·
    refine ⟨41414335130728550346594961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55219113507638067128793281 41414335130728550346594961)
    ·
      refine ⟨31060751348046412759946221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41414335130728550346594961 31060751348046412759946221)
      ·
        refine ⟨11647781755517404784979833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31060751348046412759946221 11647781755517404784979833)
        ·
          refine ⟨8735836316638053588734875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11647781755517404784979833 8735836316638053588734875)
          ·
            refine ⟨13103754474957080383102313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735836316638053588734875 13103754474957080383102313)
            ·
              refine ⟨9827815856217810287326735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13103754474957080383102313 9827815856217810287326735)
              ·
                refine ⟨14741723784326715430990103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9827815856217810287326735 14741723784326715430990103)
                ·
                  refine ⟨22112585676490073146485155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14741723784326715430990103 22112585676490073146485155)
                  ·
                    refine ⟨33168878514735109719727733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22112585676490073146485155 33168878514735109719727733)
                    ·
                      refine ⟨3109582360756416536224475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33168878514735109719727733 3109582360756416536224475)
                      ·
                        rfl

theorem cell23_6055890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6055890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055890 prefixEnd_6055890 := by exact prefixLift 6055890
  have htrace : WordTrace (prefixWord ++ tailWord_6055890) baseStart_6055890 baseEnd_6055890 := by
    simpa [prefixWord, tailWord_6055890, baseEnd_6055890] using wordTrace_append hprefix tailTrace_6055890
  have hstable : (prefixWord ++ tailWord_6055890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055890).length < 2 ^ (prefixWord ++ tailWord_6055890).sum := by decide
  have hdescent : baseEnd_6055890 < baseStart_6055890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055947 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 1, 3, 2]
def baseStart_6055947 : Nat := 118140960795 + 6055947 * 2 ^ 59
def prefixEnd_6055947 : Nat := 4983230072969 + 3 ^ 40 * 6055947 * 2
def baseEnd_6055947 : Nat := 3109611629153722813211713

theorem tailTrace_6055947 : CollatzResearch.WordTrace tailWord_6055947 prefixEnd_6055947 3109611629153722813211713 := by
  unfold tailWord_6055947
  simp only [CollatzResearch.WordTrace]
  refine ⟨220878532991345767249998095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147252355327563844833332063 220878532991345767249998095)
  ·
    refine ⟨331317799487018650874997143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220878532991345767249998095 331317799487018650874997143)
    ·
      refine ⟨496976699230527976312495715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331317799487018650874997143 496976699230527976312495715)
      ·
        refine ⟨745465048845791964468743573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496976699230527976312495715 745465048845791964468743573)
        ·
          refine ⟨34943674164646498334472355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 745465048845791964468743573 34943674164646498334472355)
          ·
            refine ⟨52415511246969747501708533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34943674164646498334472355 52415511246969747501708533)
            ·
              refine ⟨4913954179403413828285175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52415511246969747501708533 4913954179403413828285175)
              ·
                refine ⟨7370931269105120742427763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913954179403413828285175 7370931269105120742427763)
                ·
                  refine ⟨11056396903657681113641645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370931269105120742427763 11056396903657681113641645)
                  ·
                    refine ⟨4146148838871630417615617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11056396903657681113641645 4146148838871630417615617)
                    ·
                      refine ⟨3109611629153722813211713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146148838871630417615617 3109611629153722813211713)
                      ·
                        rfl

theorem cell23_6055947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 3, 2].length) (baseStart_6055947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055947 prefixEnd_6055947 := by exact prefixLift 6055947
  have htrace : WordTrace (prefixWord ++ tailWord_6055947) baseStart_6055947 baseEnd_6055947 := by
    simpa [prefixWord, tailWord_6055947, baseEnd_6055947] using wordTrace_append hprefix tailTrace_6055947
  have hstable : (prefixWord ++ tailWord_6055947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055947).length < 2 ^ (prefixWord ++ tailWord_6055947).sum := by decide
  have hdescent : baseEnd_6055947 < baseStart_6055947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055973 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_6055973 : Nat := 118140960795 + 6055973 * 2 ^ 59
def prefixEnd_6055973 : Nat := 4983230072969 + 3 ^ 40 * 6055973 * 2
def baseEnd_6055973 : Nat := 3109624979650739711486593

theorem tailTrace_6055973 : CollatzResearch.WordTrace tailWord_6055973 prefixEnd_6055973 3109624979650739711486593 := by
  unfold tailWord_6055973
  simp only [CollatzResearch.WordTrace]
  refine ⟨220879481289251573690444573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147252987526167715793629715 220879481289251573690444573)
  ·
    refine ⟨82829805483469340133916715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220879481289251573690444573 82829805483469340133916715)
    ·
      refine ⟨124244708225204010200875073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82829805483469340133916715 124244708225204010200875073)
      ·
        refine ⟨93183531168903007650656305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124244708225204010200875073 93183531168903007650656305)
        ·
          refine ⟨69887648376677255737992229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93183531168903007650656305 69887648376677255737992229)
          ·
            refine ⟨13103934070626985450873543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69887648376677255737992229 13103934070626985450873543)
            ·
              refine ⟨19655901105940478176310315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103934070626985450873543 19655901105940478176310315)
              ·
                refine ⟨29483851658910717264465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19655901105940478176310315 29483851658910717264465473)
                ·
                  refine ⟨22112888744183037948349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29483851658910717264465473 22112888744183037948349105)
                  ·
                    refine ⟨16584666558137278461261829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22112888744183037948349105 16584666558137278461261829)
                    ·
                      refine ⟨3109624979650739711486593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16584666558137278461261829 3109624979650739711486593)
                      ·
                        rfl

theorem cell23_6055973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_6055973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055973 prefixEnd_6055973 := by exact prefixLift 6055973
  have htrace : WordTrace (prefixWord ++ tailWord_6055973) baseStart_6055973 baseEnd_6055973 := by
    simpa [prefixWord, tailWord_6055973, baseEnd_6055973] using wordTrace_append hprefix tailTrace_6055973
  have hstable : (prefixWord ++ tailWord_6055973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055973).length < 2 ^ (prefixWord ++ tailWord_6055973).sum := by decide
  have hdescent : baseEnd_6055973 < baseStart_6055973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6055998 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6055998 : Nat := 118140960795 + 6055998 * 2 ^ 59
def prefixEnd_6055998 : Nat := 4983230072969 + 3 ^ 40 * 6055998 * 2
def baseEnd_6055998 : Nat := 3109637816667102113673979

theorem tailTrace_6055998 : CollatzResearch.WordTrace tailWord_6055998 prefixEnd_6055998 3109637816667102113673979 := by
  unfold tailWord_6055998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27610049139270125370013081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147253595409440668640069765 27610049139270125370013081)
  ·
    refine ⟨20707536854452594027509811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27610049139270125370013081 20707536854452594027509811)
    ·
      refine ⟨31061305281678891041264717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20707536854452594027509811 31061305281678891041264717)
      ·
        refine ⟨11647989480629584140474269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31061305281678891041264717 11647989480629584140474269)
        ·
          refine ⟨4367996055236094052677851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11647989480629584140474269 4367996055236094052677851)
          ·
            refine ⟨6551994082854141079016777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367996055236094052677851 6551994082854141079016777)
            ·
              refine ⟨4913995562140605809262583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6551994082854141079016777 4913995562140605809262583)
              ·
                refine ⟨7370993343210908713893875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913995562140605809262583 7370993343210908713893875)
                ·
                  refine ⟨11056490014816363070840813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7370993343210908713893875 11056490014816363070840813)
                  ·
                    refine ⟨4146183755556136151565305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11056490014816363070840813 4146183755556136151565305)
                    ·
                      refine ⟨3109637816667102113673979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146183755556136151565305 3109637816667102113673979)
                      ·
                        rfl

theorem cell23_6055998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6055998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6055998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6055998 prefixEnd_6055998 := by exact prefixLift 6055998
  have htrace : WordTrace (prefixWord ++ tailWord_6055998) baseStart_6055998 baseEnd_6055998 := by
    simpa [prefixWord, tailWord_6055998, baseEnd_6055998] using wordTrace_append hprefix tailTrace_6055998
  have hstable : (prefixWord ++ tailWord_6055998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6055998).length < 2 ^ (prefixWord ++ tailWord_6055998).sum := by decide
  have hdescent : baseEnd_6055998 < baseStart_6055998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6055998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056000 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 5]
def baseStart_6056000 : Nat := 118140960795 + 6056000 * 2 ^ 59
def prefixEnd_6056000 : Nat := 4983230072969 + 3 ^ 40 * 6056000 * 2
def baseEnd_6056000 : Nat := 345515427069823456205441

theorem tailTrace_6056000 : CollatzResearch.WordTrace tailWord_6056000 prefixEnd_6056000 345515427069823456205441 := by
  unfold tailWord_6056000
  simp only [CollatzResearch.WordTrace]
  refine ⟨110440233030076878650838727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147253644040102504867784969 110440233030076878650838727)
  ·
    refine ⟨165660349545115317976258091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110440233030076878650838727 165660349545115317976258091)
    ·
      refine ⟨248490524317672976964387137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165660349545115317976258091 248490524317672976964387137)
      ·
        refine ⟨186367893238254732723290353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248490524317672976964387137 186367893238254732723290353)
        ·
          refine ⟨139775919928691049542467765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186367893238254732723290353 139775919928691049542467765)
          ·
            refine ⟨13103992493314785894606353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139775919928691049542467765 13103992493314785894606353)
            ·
              refine ⟨9827994369986089420954765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13103992493314785894606353 9827994369986089420954765)
              ·
                refine ⟨3685497888744783532858037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9827994369986089420954765 3685497888744783532858037)
                ·
                  refine ⟨345515427069823456205441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685497888744783532858037 345515427069823456205441)
                  ·
                    rfl

theorem cell23_6056000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 5].length) (baseStart_6056000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056000 prefixEnd_6056000 := by exact prefixLift 6056000
  have htrace : WordTrace (prefixWord ++ tailWord_6056000) baseStart_6056000 baseEnd_6056000 := by
    simpa [prefixWord, tailWord_6056000, baseEnd_6056000] using wordTrace_append hprefix tailTrace_6056000
  have hstable : (prefixWord ++ tailWord_6056000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056000).length < 2 ^ (prefixWord ++ tailWord_6056000).sum := by decide
  have hdescent : baseEnd_6056000 < baseStart_6056000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056003 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 7, 2]
def baseStart_6056003 : Nat := 118140960795 + 6056003 * 2 ^ 59
def prefixEnd_6056003 : Nat := 4983230072969 + 3 ^ 40 * 6056003 * 2
def baseEnd_6056003 : Nat := 3109640384070374594111455

theorem tailTrace_6056003 : CollatzResearch.WordTrace tailWord_6056003 prefixEnd_6056003 3109640384070374594111455 := by
  unfold tailWord_6056003
  simp only [CollatzResearch.WordTrace]
  refine ⟨220880575479142888814036663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147253716986095259209357775 220880575479142888814036663)
  ·
    refine ⟨331320863218714333221054995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220880575479142888814036663 331320863218714333221054995)
    ·
      refine ⟨496981294828071499831582493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331320863218714333221054995 496981294828071499831582493)
      ·
        refine ⟨186367985560526812436843435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 496981294828071499831582493 186367985560526812436843435)
        ·
          refine ⟨279551978340790218655265153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186367985560526812436843435 279551978340790218655265153)
          ·
            refine ⟨209663983755592663991448865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279551978340790218655265153 209663983755592663991448865)
            ·
              refine ⟨157247987816694497993586649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209663983755592663991448865 157247987816694497993586649)
              ·
                refine ⟨117935990862520873495189987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157247987816694497993586649 117935990862520873495189987)
                ·
                  refine ⟨176903986293781310242784981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117935990862520873495189987 176903986293781310242784981)
                  ·
                    refine ⟨4146187178760499458815273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176903986293781310242784981 4146187178760499458815273)
                    ·
                      refine ⟨3109640384070374594111455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146187178760499458815273 3109640384070374594111455)
                      ·
                        rfl

theorem cell23_6056003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_6056003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056003 prefixEnd_6056003 := by exact prefixLift 6056003
  have htrace : WordTrace (prefixWord ++ tailWord_6056003) baseStart_6056003 baseEnd_6056003 := by
    simpa [prefixWord, tailWord_6056003, baseEnd_6056003] using wordTrace_append hprefix tailTrace_6056003
  have hstable : (prefixWord ++ tailWord_6056003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056003).length < 2 ^ (prefixWord ++ tailWord_6056003).sum := by decide
  have hdescent : baseEnd_6056003 < baseStart_6056003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056073 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 6]
def baseStart_6056073 : Nat := 118140960795 + 6056073 * 2 ^ 59
def prefixEnd_6056073 : Nat := 4983230072969 + 3 ^ 40 * 6056073 * 2
def baseEnd_6056073 : Nat := 345519591968465480026237

theorem tailTrace_6056073 : CollatzResearch.WordTrace tailWord_6056073 prefixEnd_6056073 345519591968465480026237 := by
  unfold tailWord_6056073
  simp only [CollatzResearch.WordTrace]
  refine ⟨220883128588889290769084873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147255419059259527179389915 220883128588889290769084873)
  ·
    refine ⟨165662346441666968076813655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220883128588889290769084873 165662346441666968076813655)
    ·
      refine ⟨248493519662500452115220483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165662346441666968076813655 248493519662500452115220483)
      ·
        refine ⟨372740279493750678172830725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248493519662500452115220483 372740279493750678172830725)
        ·
          refine ⟨69888802405078252157405761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372740279493750678172830725 69888802405078252157405761)
          ·
            refine ⟨52416601803808689118054321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69888802405078252157405761 52416601803808689118054321)
            ·
              refine ⟨39312451352856516838540741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52416601803808689118054321 39312451352856516838540741)
              ·
                refine ⟨7371084628660596907226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39312451352856516838540741 7371084628660596907226389)
                ·
                  refine ⟨345519591968465480026237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7371084628660596907226389 345519591968465480026237)
                  ·
                    rfl

theorem cell23_6056073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_6056073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056073 prefixEnd_6056073 := by exact prefixLift 6056073
  have htrace : WordTrace (prefixWord ++ tailWord_6056073) baseStart_6056073 baseEnd_6056073 := by
    simpa [prefixWord, tailWord_6056073, baseEnd_6056073] using wordTrace_append hprefix tailTrace_6056073
  have hstable : (prefixWord ++ tailWord_6056073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056073).length < 2 ^ (prefixWord ++ tailWord_6056073).sum := by decide
  have hdescent : baseEnd_6056073 < baseStart_6056073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056143 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_6056143 : Nat := 118140960795 + 6056143 * 2 ^ 59
def prefixEnd_6056143 : Nat := 4983230072969 + 3 ^ 40 * 6056143 * 2
def baseEnd_6056143 : Nat := 3109712271362004046360811

theorem tailTrace_6056143 : CollatzResearch.WordTrace tailWord_6056143 prefixEnd_6056143 3109712271362004046360811 := by
  unfold tailWord_6056143
  simp only [CollatzResearch.WordTrace]
  refine ⟨220885681698635692724133083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147257121132423795149422055 220885681698635692724133083)
  ·
    refine ⟨331328522547953539086199625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220885681698635692724133083 331328522547953539086199625)
    ·
      refine ⟨248496391910965154314649719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331328522547953539086199625 248496391910965154314649719)
      ·
        refine ⟨372744587866447731471974579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248496391910965154314649719 372744587866447731471974579)
        ·
          refine ⟨559116881799671597207961869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372744587866447731471974579 559116881799671597207961869)
          ·
            refine ⟨209668830674876848952985701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559116881799671597207961869 209668830674876848952985701)
            ·
              refine ⟨39312905751539409178684819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209668830674876848952985701 39312905751539409178684819)
              ·
                refine ⟨58969358627309113768027229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39312905751539409178684819 58969358627309113768027229)
                ·
                  refine ⟨22113509485240917663010211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58969358627309113768027229 22113509485240917663010211)
                  ·
                    refine ⟨33170264227861376494515317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22113509485240917663010211 33170264227861376494515317)
                    ·
                      refine ⟨3109712271362004046360811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33170264227861376494515317 3109712271362004046360811)
                      ·
                        rfl

theorem cell23_6056143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_6056143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056143 prefixEnd_6056143 := by exact prefixLift 6056143
  have htrace : WordTrace (prefixWord ++ tailWord_6056143) baseStart_6056143 baseEnd_6056143 := by
    simpa [prefixWord, tailWord_6056143, baseEnd_6056143] using wordTrace_append hprefix tailTrace_6056143
  have hstable : (prefixWord ++ tailWord_6056143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056143).length < 2 ^ (prefixWord ++ tailWord_6056143).sum := by decide
  have hdescent : baseEnd_6056143 < baseStart_6056143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056153 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_6056153 : Nat := 118140960795 + 6056153 * 2 ^ 59
def prefixEnd_6056153 : Nat := 4983230072969 + 3 ^ 40 * 6056153 * 2
def baseEnd_6056153 : Nat := 3109717406168549007235765

theorem tailTrace_6056153 : CollatzResearch.WordTrace tailWord_6056153 prefixEnd_6056153 3109717406168549007235765 := by
  unfold tailWord_6056153
  simp only [CollatzResearch.WordTrace]
  refine ⟨220886046428599464431997113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147257364285732976287998075 220886046428599464431997113)
  ·
    refine ⟨165664534821449598323997835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220886046428599464431997113 165664534821449598323997835)
    ·
      refine ⟨248496802232174397485996753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165664534821449598323997835 248496802232174397485996753)
      ·
        refine ⟨186372601674130798114497565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248496802232174397485996753 186372601674130798114497565)
        ·
          refine ⟨69889725627799049292936587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186372601674130798114497565 69889725627799049292936587)
          ·
            refine ⟨104834588441698573939404881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69889725627799049292936587 104834588441698573939404881)
            ·
              refine ⟨78625941331273930454553661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104834588441698573939404881 78625941331273930454553661)
              ·
                refine ⟨29484727999227723920457623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78625941331273930454553661 29484727999227723920457623)
                ·
                  refine ⟨44227091998841585880686435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29484727999227723920457623 44227091998841585880686435)
                  ·
                    refine ⟨66340637998262378821029653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44227091998841585880686435 66340637998262378821029653)
                    ·
                      refine ⟨3109717406168549007235765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66340637998262378821029653 3109717406168549007235765)
                      ·
                        rfl

theorem cell23_6056153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_6056153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056153 prefixEnd_6056153 := by exact prefixLift 6056153
  have htrace : WordTrace (prefixWord ++ tailWord_6056153) baseStart_6056153 baseEnd_6056153 := by
    simpa [prefixWord, tailWord_6056153, baseEnd_6056153] using wordTrace_append hprefix tailTrace_6056153
  have hstable : (prefixWord ++ tailWord_6056153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056153).length < 2 ^ (prefixWord ++ tailWord_6056153).sum := by decide
  have hdescent : baseEnd_6056153 < baseStart_6056153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056157 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6056157 : Nat := 118140960795 + 6056157 * 2 ^ 59
def prefixEnd_6056157 : Nat := 4983230072969 + 3 ^ 40 * 6056157 * 2
def baseEnd_6056157 : Nat := 3109719460091166991585747

theorem tailTrace_6056157 : CollatzResearch.WordTrace tailWord_6056157 prefixEnd_6056157 3109719460091166991585747 := by
  unfold tailWord_6056157
  simp only [CollatzResearch.WordTrace]
  refine ⟨220886192320584973115142725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147257461547056648743428483 220886192320584973115142725)
  ·
    refine ⟨41416161060109682459089261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220886192320584973115142725 41416161060109682459089261)
    ·
      refine ⟨15531060397541130922158473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41416161060109682459089261 15531060397541130922158473)
      ·
        refine ⟨11648295298155848191618855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15531060397541130922158473 11648295298155848191618855)
        ·
          refine ⟨17472442947233772287428283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11648295298155848191618855 17472442947233772287428283)
          ·
            refine ⟨26208664420850658431142425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17472442947233772287428283 26208664420850658431142425)
            ·
              refine ⟨19656498315637993823356819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26208664420850658431142425 19656498315637993823356819)
              ·
                refine ⟨29484747473456990735035229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19656498315637993823356819 29484747473456990735035229)
                ·
                  refine ⟨11056780302546371525638211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29484747473456990735035229 11056780302546371525638211)
                  ·
                    refine ⟨16585170453819557288457317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11056780302546371525638211 16585170453819557288457317)
                    ·
                      refine ⟨3109719460091166991585747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16585170453819557288457317 3109719460091166991585747)
                      ·
                        rfl

theorem cell23_6056157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6056157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056157 prefixEnd_6056157 := by exact prefixLift 6056157
  have htrace : WordTrace (prefixWord ++ tailWord_6056157) baseStart_6056157 baseEnd_6056157 := by
    simpa [prefixWord, tailWord_6056157, baseEnd_6056157] using wordTrace_append hprefix tailTrace_6056157
  have hstable : (prefixWord ++ tailWord_6056157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056157).length < 2 ^ (prefixWord ++ tailWord_6056157).sum := by decide
  have hdescent : baseEnd_6056157 < baseStart_6056157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056160 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_6056160 : Nat := 118140960795 + 6056160 * 2 ^ 59
def prefixEnd_6056160 : Nat := 4983230072969 + 3 ^ 40 * 6056160 * 2
def baseEnd_6056160 : Nat := 3109721000533130479848233

theorem tailTrace_6056160 : CollatzResearch.WordTrace tailWord_6056160 prefixEnd_6056160 3109721000533130479848233 := by
  unfold tailWord_6056160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110443150869787052313750967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147257534493049403085001289 110443150869787052313750967)
  ·
    refine ⟨165664726304680578470626451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110443150869787052313750967 165664726304680578470626451)
    ·
      refine ⟨248497089457020867705939677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165664726304680578470626451 248497089457020867705939677)
      ·
        refine ⟨93186408546382825389727379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248497089457020867705939677 93186408546382825389727379)
        ·
          refine ⟨139779612819574238084591069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93186408546382825389727379 139779612819574238084591069)
          ·
            refine ⟨52417354807340339281721651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139779612819574238084591069 52417354807340339281721651)
            ·
              refine ⟨78626032211010508922582477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52417354807340339281721651 78626032211010508922582477)
              ·
                refine ⟨29484762079128940845968429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78626032211010508922582477 29484762079128940845968429)
                ·
                  refine ⟨11056785779673352817238161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29484762079128940845968429 11056785779673352817238161)
                  ·
                    refine ⟨8292589334755014612928621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11056785779673352817238161 8292589334755014612928621)
                    ·
                      refine ⟨3109721000533130479848233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292589334755014612928621 3109721000533130479848233)
                      ·
                        rfl

theorem cell23_6056160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_6056160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056160 prefixEnd_6056160 := by exact prefixLift 6056160
  have htrace : WordTrace (prefixWord ++ tailWord_6056160) baseStart_6056160 baseEnd_6056160 := by
    simpa [prefixWord, tailWord_6056160, baseEnd_6056160] using wordTrace_append hprefix tailTrace_6056160
  have hstable : (prefixWord ++ tailWord_6056160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056160).length < 2 ^ (prefixWord ++ tailWord_6056160).sum := by decide
  have hdescent : baseEnd_6056160 < baseStart_6056160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056170 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6056170 : Nat := 118140960795 + 6056170 * 2 ^ 59
def prefixEnd_6056170 : Nat := 4983230072969 + 3 ^ 40 * 6056170 * 2
def baseEnd_6056170 : Nat := 3109726135339675440723187

theorem tailTrace_6056170 : CollatzResearch.WordTrace tailWord_6056170 prefixEnd_6056170 3109726135339675440723187 := by
  unfold tailWord_6056170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55221666617384469083841491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147257777646358584223577309 55221666617384469083841491)
  ·
    refine ⟨82832499926076703625762237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55221666617384469083841491 82832499926076703625762237)
    ·
      refine ⟨31062187472278763859660839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82832499926076703625762237 31062187472278763859660839)
      ·
        refine ⟨46593281208418145789491259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31062187472278763859660839 46593281208418145789491259)
        ·
          refine ⟨69889921812627218684236889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46593281208418145789491259 69889921812627218684236889)
          ·
            refine ⟨52417441359470414013177667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69889921812627218684236889 52417441359470414013177667)
            ·
              refine ⟨78626162039205621019766501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52417441359470414013177667 78626162039205621019766501)
              ·
                refine ⟨14742405382351053941206219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78626162039205621019766501 14742405382351053941206219)
                ·
                  refine ⟨22113608073526580911809329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14742405382351053941206219 22113608073526580911809329)
                  ·
                    refine ⟨16585206055144935683856997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22113608073526580911809329 16585206055144935683856997)
                    ·
                      refine ⟨3109726135339675440723187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16585206055144935683856997 3109726135339675440723187)
                      ·
                        rfl

theorem cell23_6056170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6056170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056170 prefixEnd_6056170 := by exact prefixLift 6056170
  have htrace : WordTrace (prefixWord ++ tailWord_6056170) baseStart_6056170 baseEnd_6056170 := by
    simpa [prefixWord, tailWord_6056170, baseEnd_6056170] using wordTrace_append hprefix tailTrace_6056170
  have hstable : (prefixWord ++ tailWord_6056170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056170).length < 2 ^ (prefixWord ++ tailWord_6056170).sum := by decide
  have hdescent : baseEnd_6056170 < baseStart_6056170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056207 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_6056207 : Nat := 118140960795 + 6056207 * 2 ^ 59
def prefixEnd_6056207 : Nat := 4983230072969 + 3 ^ 40 * 6056207 * 2
def baseEnd_6056207 : Nat := 3109745134123891795960517

theorem tailTrace_6056207 : CollatzResearch.WordTrace tailWord_6056207 prefixEnd_6056207 3109745134123891795960517 := by
  unfold tailWord_6056207
  simp only [CollatzResearch.WordTrace]
  refine ⟨220888015970403831654462875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147258677313602554436308583 220888015970403831654462875)
  ·
    refine ⟨331332023955605747481694313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220888015970403831654462875 331332023955605747481694313)
    ·
      refine ⟨248499017966704310611270735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331332023955605747481694313 248499017966704310611270735)
      ·
        refine ⟨372748526950056465916906103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248499017966704310611270735 372748526950056465916906103)
        ·
          refine ⟨559122790425084698875359155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372748526950056465916906103 559122790425084698875359155)
          ·
            refine ⟨838684185637627048313038733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559122790425084698875359155 838684185637627048313038733)
            ·
              refine ⟨314506569614110143117389525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838684185637627048313038733 314506569614110143117389525)
              ·
                refine ⟨7371247725330706479313817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 314506569614110143117389525 7371247725330706479313817)
                ·
                  refine ⟨5528435793998029859485363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7371247725330706479313817 5528435793998029859485363)
                  ·
                    refine ⟨8292653690997044789228045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528435793998029859485363 8292653690997044789228045)
                    ·
                      refine ⟨3109745134123891795960517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292653690997044789228045 3109745134123891795960517)
                      ·
                        rfl

theorem cell23_6056207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_6056207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056207 prefixEnd_6056207 := by exact prefixLift 6056207
  have htrace : WordTrace (prefixWord ++ tailWord_6056207) baseStart_6056207 baseEnd_6056207 := by
    simpa [prefixWord, tailWord_6056207, baseEnd_6056207] using wordTrace_append hprefix tailTrace_6056207
  have hstable : (prefixWord ++ tailWord_6056207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056207).length < 2 ^ (prefixWord ++ tailWord_6056207).sum := by decide
  have hdescent : baseEnd_6056207 < baseStart_6056207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056231 : List Nat := [1, 1, 8, 1, 2, 1, 9]
def baseStart_6056231 : Nat := 118140960795 + 6056231 * 2 ^ 59
def prefixEnd_6056231 : Nat := 4983230072969 + 3 ^ 40 * 6056231 * 2
def baseEnd_6056231 : Nat := 38392067378513576568647

theorem tailTrace_6056231 : CollatzResearch.WordTrace tailWord_6056231 prefixEnd_6056231 38392067378513576568647 := by
  unfold tailWord_6056231
  simp only [CollatzResearch.WordTrace]
  refine ⟨220888891322316883753336547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147259260881544589168891031 220888891322316883753336547)
  ·
    refine ⟨331333336983475325630004821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220888891322316883753336547 331333336983475325630004821)
    ·
      refine ⟨3882812542775101472226619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 331333336983475325630004821 3882812542775101472226619)
      ·
        refine ⟨5824218814162652208339929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882812542775101472226619 5824218814162652208339929)
        ·
          refine ⟨4368164110621989156254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5824218814162652208339929 4368164110621989156254947)
          ·
            refine ⟨6552246165932983734382421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368164110621989156254947 6552246165932983734382421)
            ·
              refine ⟨38392067378513576568647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6552246165932983734382421 38392067378513576568647)
              ·
                rfl

theorem cell23_6056231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 9].length) (baseStart_6056231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056231 prefixEnd_6056231 := by exact prefixLift 6056231
  have htrace : WordTrace (prefixWord ++ tailWord_6056231) baseStart_6056231 baseEnd_6056231 := by
    simpa [prefixWord, tailWord_6056231, baseEnd_6056231] using wordTrace_append hprefix tailTrace_6056231
  have hstable : (prefixWord ++ tailWord_6056231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056231).length < 2 ^ (prefixWord ++ tailWord_6056231).sum := by decide
  have hdescent : baseEnd_6056231 < baseStart_6056231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056280 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_6056280 : Nat := 118140960795 + 6056280 * 2 ^ 59
def prefixEnd_6056280 : Nat := 4983230072969 + 3 ^ 40 * 6056280 * 2
def baseEnd_6056280 : Nat := 3109782618211670010347681

theorem tailTrace_6056280 : CollatzResearch.WordTrace tailWord_6056280 prefixEnd_6056280 3109782618211670010347681 := by
  unfold tailWord_6056280
  simp only [CollatzResearch.WordTrace]
  refine ⟨110445339249569682560935147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147260452332759576747913529 110445339249569682560935147)
  ·
    refine ⟨165668008874354523841402721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110445339249569682560935147 165668008874354523841402721)
    ·
      refine ⟨124251006655765892881052041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165668008874354523841402721 124251006655765892881052041)
      ·
        refine ⟨93188254991824419660789031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124251006655765892881052041 93188254991824419660789031)
        ·
          refine ⟨139782382487736629491183547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93188254991824419660789031 139782382487736629491183547)
          ·
            refine ⟨209673573731604944236775321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139782382487736629491183547 209673573731604944236775321)
            ·
              refine ⟨157255180298703708177581491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209673573731604944236775321 157255180298703708177581491)
              ·
                refine ⟨235882770448055562266372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157255180298703708177581491 235882770448055562266372237)
                ·
                  refine ⟨88456038918020835849889589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235882770448055562266372237 88456038918020835849889589)
                  ·
                    refine ⟨8292753648564453360927149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88456038918020835849889589 8292753648564453360927149)
                    ·
                      refine ⟨3109782618211670010347681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292753648564453360927149 3109782618211670010347681)
                      ·
                        rfl

theorem cell23_6056280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_6056280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056280 prefixEnd_6056280 := by exact prefixLift 6056280
  have htrace : WordTrace (prefixWord ++ tailWord_6056280) baseStart_6056280 baseEnd_6056280 := by
    simpa [prefixWord, tailWord_6056280, baseEnd_6056280] using wordTrace_append hprefix tailTrace_6056280
  have hstable : (prefixWord ++ tailWord_6056280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056280).length < 2 ^ (prefixWord ++ tailWord_6056280).sum := by decide
  have hdescent : baseEnd_6056280 < baseStart_6056280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056298 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6056298 : Nat := 118140960795 + 6056298 * 2 ^ 59
def prefixEnd_6056298 : Nat := 4983230072969 + 3 ^ 40 * 6056298 * 2
def baseEnd_6056298 : Nat := 3109791860863450939922599

theorem tailTrace_6056298 : CollatzResearch.WordTrace tailWord_6056298 prefixEnd_6056298 3109791860863450939922599 := by
  unfold tailWord_6056298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55222833753268538549006387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147260890008716102797350365 55222833753268538549006387)
  ·
    refine ⟨82834250629902807823509581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55222833753268538549006387 82834250629902807823509581)
    ·
      refine ⟨31062843986213552933816093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82834250629902807823509581 31062843986213552933816093)
      ·
        refine ⟨11648566494830082350181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31062843986213552933816093 11648566494830082350181035)
        ·
          refine ⟨17472849742245123525271553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11648566494830082350181035 17472849742245123525271553)
          ·
            refine ⟨13104637306683842643953665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17472849742245123525271553 13104637306683842643953665)
            ·
              refine ⟨9828477980012881982965249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13104637306683842643953665 9828477980012881982965249)
              ·
                refine ⟨7371358485009661487223937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9828477980012881982965249 7371358485009661487223937)
                ·
                  refine ⟨5528518863757246115417953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7371358485009661487223937 5528518863757246115417953)
                  ·
                    refine ⟨4146389147817934586563465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5528518863757246115417953 4146389147817934586563465)
                    ·
                      refine ⟨3109791860863450939922599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146389147817934586563465 3109791860863450939922599)
                      ·
                        rfl

theorem cell23_6056298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6056298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056298 prefixEnd_6056298 := by exact prefixLift 6056298
  have htrace : WordTrace (prefixWord ++ tailWord_6056298) baseStart_6056298 baseEnd_6056298 := by
    simpa [prefixWord, tailWord_6056298, baseEnd_6056298] using wordTrace_append hprefix tailTrace_6056298
  have hstable : (prefixWord ++ tailWord_6056298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056298).length < 2 ^ (prefixWord ++ tailWord_6056298).sum := by decide
  have hdescent : baseEnd_6056298 < baseStart_6056298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056304 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 5]
def baseStart_6056304 : Nat := 118140960795 + 6056304 * 2 ^ 59
def prefixEnd_6056304 : Nat := 4983230072969 + 3 ^ 40 * 6056304 * 2
def baseEnd_6056304 : Nat := 345532771305264212938619

theorem tailTrace_6056304 : CollatzResearch.WordTrace tailWord_6056304 prefixEnd_6056304 345532771305264212938619 := by
  unfold tailWord_6056304
  simp only [CollatzResearch.WordTrace]
  refine ⟨110445776925526208610371983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147261035900701611480495977 110445776925526208610371983)
  ·
    refine ⟨165668665388289312915557975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110445776925526208610371983 165668665388289312915557975)
    ·
      refine ⟨248502998082433969373336963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165668665388289312915557975 248502998082433969373336963)
      ·
        refine ⟨372754497123650954060005445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248502998082433969373336963 372754497123650954060005445)
        ·
          refine ⟨69891468210684553886251021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372754497123650954060005445 69891468210684553886251021)
          ·
            refine ⟨26209300579006707707344133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69891468210684553886251021 26209300579006707707344133)
            ·
              refine ⟨4914243858563757695127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26209300579006707707344133 4914243858563757695127025)
              ·
                refine ⟨3685682893922818271345269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914243858563757695127025 3685682893922818271345269)
                ·
                  refine ⟨345532771305264212938619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3685682893922818271345269 345532771305264212938619)
                  ·
                    rfl

theorem cell23_6056304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 5].length) (baseStart_6056304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056304 prefixEnd_6056304 := by exact prefixLift 6056304
  have htrace : WordTrace (prefixWord ++ tailWord_6056304) baseStart_6056304 baseEnd_6056304 := by
    simpa [prefixWord, tailWord_6056304, baseEnd_6056304] using wordTrace_append hprefix tailTrace_6056304
  have hstable : (prefixWord ++ tailWord_6056304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056304).length < 2 ^ (prefixWord ++ tailWord_6056304).sum := by decide
  have hdescent : baseEnd_6056304 < baseStart_6056304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056334 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_6056334 : Nat := 118140960795 + 6056334 * 2 ^ 59
def prefixEnd_6056334 : Nat := 4983230072969 + 3 ^ 40 * 6056334 * 2
def baseEnd_6056334 : Nat := 1036603448722337599690811

theorem tailTrace_6056334 : CollatzResearch.WordTrace tailWord_6056334 prefixEnd_6056334 1036603448722337599690811 := by
  unfold tailWord_6056334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611581005117966543042007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147261765360629154896224037 27611581005117966543042007)
  ·
    refine ⟨41417371507676949814563011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27611581005117966543042007 41417371507676949814563011)
    ·
      refine ⟨62126057261515424721844517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41417371507676949814563011 62126057261515424721844517)
      ·
        refine ⟨11648635736534142135345847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62126057261515424721844517 11648635736534142135345847)
        ·
          refine ⟨17472953604801213203018771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11648635736534142135345847 17472953604801213203018771)
          ·
            refine ⟨26209430407201819804528157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17472953604801213203018771 26209430407201819804528157)
            ·
              refine ⟨9828536402700682426698059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26209430407201819804528157 9828536402700682426698059)
              ·
                refine ⟨14742804604051023640047089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9828536402700682426698059 14742804604051023640047089)
                ·
                  refine ⟨11057103453038267730035317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14742804604051023640047089 11057103453038267730035317)
                  ·
                    refine ⟨1036603448722337599690811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11057103453038267730035317 1036603448722337599690811)
                    ·
                      rfl

theorem cell23_6056334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_6056334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056334 prefixEnd_6056334 := by exact prefixLift 6056334
  have htrace : WordTrace (prefixWord ++ tailWord_6056334) baseStart_6056334 baseEnd_6056334 := by
    simpa [prefixWord, tailWord_6056334, baseEnd_6056334] using wordTrace_append hprefix tailTrace_6056334
  have hstable : (prefixWord ++ tailWord_6056334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056334).length < 2 ^ (prefixWord ++ tailWord_6056334).sum := by decide
  have hdescent : baseEnd_6056334 < baseStart_6056334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056337 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_6056337 : Nat := 118140960795 + 6056337 * 2 ^ 59
def prefixEnd_6056337 : Nat := 4983230072969 + 3 ^ 40 * 6056337 * 2
def baseEnd_6056337 : Nat := 3109811886608976287334919

theorem tailTrace_6056337 : CollatzResearch.WordTrace tailWord_6056337 prefixEnd_6056337 3109811886608976287334919 := by
  unfold tailWord_6056337
  simp only [CollatzResearch.WordTrace]
  refine ⟨220892757459932863856695265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147261838306621909237796843 220892757459932863856695265)
  ·
    refine ⟨165669568094949647892521449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220892757459932863856695265 165669568094949647892521449)
    ·
      refine ⟨124252176071212235919391087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165669568094949647892521449 124252176071212235919391087)
      ·
        refine ⟨186378264106818353879086631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124252176071212235919391087 186378264106818353879086631)
        ·
          refine ⟨279567396160227530818629947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186378264106818353879086631 279567396160227530818629947)
          ·
            refine ⟨419351094240341296227944921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279567396160227530818629947 419351094240341296227944921)
            ·
              refine ⟨314513320680255972170958691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419351094240341296227944921 314513320680255972170958691)
              ·
                refine ⟨471769981020383958256438037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314513320680255972170958691 471769981020383958256438037)
                ·
                  refine ⟨22114217860330498043270533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 471769981020383958256438037 22114217860330498043270533)
                  ·
                    refine ⟨4146415848811968383113225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22114217860330498043270533 4146415848811968383113225)
                    ·
                      refine ⟨3109811886608976287334919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146415848811968383113225 3109811886608976287334919)
                      ·
                        rfl

theorem cell23_6056337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_6056337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056337 prefixEnd_6056337 := by exact prefixLift 6056337
  have htrace : WordTrace (prefixWord ++ tailWord_6056337) baseStart_6056337 baseEnd_6056337 := by
    simpa [prefixWord, tailWord_6056337, baseEnd_6056337] using wordTrace_append hprefix tailTrace_6056337
  have hstable : (prefixWord ++ tailWord_6056337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056337).length < 2 ^ (prefixWord ++ tailWord_6056337).sum := by decide
  have hdescent : baseEnd_6056337 < baseStart_6056337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056354 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6056354 : Nat := 118140960795 + 6056354 * 2 ^ 59
def prefixEnd_6056354 : Nat := 4983230072969 + 3 ^ 40 * 6056354 * 2
def baseEnd_6056354 : Nat := 3109820615780102720822341

theorem tailTrace_6056354 : CollatzResearch.WordTrace tailWord_6056354 prefixEnd_6056354 3109820615780102720822341 := by
  unfold tailWord_6056354
  simp only [CollatzResearch.WordTrace]
  refine ⟨55223344375217818940016029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147262251667247517173376077 55223344375217818940016029)
  ·
    refine ⟨20708754140706682102506011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55223344375217818940016029 20708754140706682102506011)
    ·
      refine ⟨31063131211060023153759017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20708754140706682102506011 31063131211060023153759017)
      ·
        refine ⟨23297348408295017365319263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31063131211060023153759017 23297348408295017365319263)
        ·
          refine ⟨34946022612442526047978895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23297348408295017365319263 34946022612442526047978895)
          ·
            refine ⟨52419033918663789071968343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34946022612442526047978895 52419033918663789071968343)
            ·
              refine ⟨78628550877995683607952515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52419033918663789071968343 78628550877995683607952515)
              ·
                refine ⟨117942826316993525411928773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78628550877995683607952515 117942826316993525411928773)
                ·
                  refine ⟨22114279934436286014736645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117942826316993525411928773 22114279934436286014736645)
                  ·
                    refine ⟨4146427487706803627763121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22114279934436286014736645 4146427487706803627763121)
                    ·
                      refine ⟨3109820615780102720822341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146427487706803627763121 3109820615780102720822341)
                      ·
                        rfl

theorem cell23_6056354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6056354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056354 prefixEnd_6056354 := by exact prefixLift 6056354
  have htrace : WordTrace (prefixWord ++ tailWord_6056354) baseStart_6056354 baseEnd_6056354 := by
    simpa [prefixWord, tailWord_6056354, baseEnd_6056354] using wordTrace_append hprefix tailTrace_6056354
  have hstable : (prefixWord ++ tailWord_6056354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056354).length < 2 ^ (prefixWord ++ tailWord_6056354).sum := by decide
  have hdescent : baseEnd_6056354 < baseStart_6056354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
