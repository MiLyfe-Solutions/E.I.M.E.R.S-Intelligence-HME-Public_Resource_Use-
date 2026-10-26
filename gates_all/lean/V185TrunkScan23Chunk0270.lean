import V185TrunkScan23Chunk0269

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1597057 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_1597057 : Nat := 118140960795 + 1597057 * 2 ^ 59
def prefixEnd_1597057 : Nat := 4983230072969 + 3 ^ 40 * 1597057 * 2
def baseEnd_1597057 : Nat := 820057873627663240842775

theorem tailTrace_1597057 : CollatzResearch.WordTrace tailWord_1597057 prefixEnd_1597057 820057873627663240842775 := by
  unfold tailWord_1597057
  simp only [CollatzResearch.WordTrace]
  refine ⟨58249454175142719465525425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38832969450095146310350283 58249454175142719465525425)
  ·
    refine ⟨43687090631357039599144069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58249454175142719465525425 43687090631357039599144069)
    ·
      refine ⟨8191329493379444924839513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43687090631357039599144069 8191329493379444924839513)
      ·
        refine ⟨6143497120034583693629635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8191329493379444924839513 6143497120034583693629635)
        ·
          refine ⟨9215245680051875540444453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143497120034583693629635 9215245680051875540444453)
          ·
            refine ⟨1727858565009726663833335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9215245680051875540444453 1727858565009726663833335)
            ·
              refine ⟨2591787847514589995750003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727858565009726663833335 2591787847514589995750003)
              ·
                refine ⟨3887681771271884993625005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591787847514589995750003 3887681771271884993625005)
                ·
                  refine ⟨1457880664226956872609377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3887681771271884993625005 1457880664226956872609377)
                  ·
                    refine ⟨1093410498170217654457033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457880664226956872609377 1093410498170217654457033)
                    ·
                      refine ⟨820057873627663240842775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093410498170217654457033 820057873627663240842775)
                      ·
                        rfl

theorem cell23_1597057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_1597057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597057 prefixEnd_1597057 := by exact prefixLift 1597057
  have htrace : WordTrace (prefixWord ++ tailWord_1597057) baseStart_1597057 baseEnd_1597057 := by
    simpa [prefixWord, tailWord_1597057, baseEnd_1597057] using wordTrace_append hprefix tailTrace_1597057
  have hstable : (prefixWord ++ tailWord_1597057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597057).length < 2 ^ (prefixWord ++ tailWord_1597057).sum := by decide
  have hdescent : baseEnd_1597057 < baseStart_1597057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597059 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 7]
def baseStart_1597059 : Nat := 118140960795 + 1597059 * 2 ^ 59
def prefixEnd_1597059 : Nat := 4983230072969 + 3 ^ 40 * 1597059 * 2
def baseEnd_1597059 : Nat := 273352966862990744339255

theorem tailTrace_1597059 : CollatzResearch.WordTrace tailWord_1597059 prefixEnd_1597059 273352966862990744339255 := by
  unfold tailWord_1597059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58249527121135473807098231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38833018080756982538065487 58249527121135473807098231)
  ·
    refine ⟨87374290681703210710647347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58249527121135473807098231 87374290681703210710647347)
    ·
      refine ⟨131061436022554816065971021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87374290681703210710647347 131061436022554816065971021)
      ·
        refine ⟨49148038508458056024739133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131061436022554816065971021 49148038508458056024739133)
        ·
          refine ⟨18430514440671771009277175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49148038508458056024739133 18430514440671771009277175)
          ·
            refine ⟨27645771661007656513915763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18430514440671771009277175 27645771661007656513915763)
            ·
              refine ⟨41468657491511484770873645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27645771661007656513915763 41468657491511484770873645)
              ·
                refine ⟨15550746559316806789077617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41468657491511484770873645 15550746559316806789077617)
                ·
                  refine ⟨11663059919487605091808213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550746559316806789077617 11663059919487605091808213)
                  ·
                    refine ⟨273352966862990744339255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11663059919487605091808213 273352966862990744339255)
                    ·
                      rfl

theorem cell23_1597059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_1597059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597059 prefixEnd_1597059 := by exact prefixLift 1597059
  have htrace : WordTrace (prefixWord ++ tailWord_1597059) baseStart_1597059 baseEnd_1597059 := by
    simpa [prefixWord, tailWord_1597059, baseEnd_1597059] using wordTrace_append hprefix tailTrace_1597059
  have hstable : (prefixWord ++ tailWord_1597059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597059).length < 2 ^ (prefixWord ++ tailWord_1597059).sum := by decide
  have hdescent : baseEnd_1597059 < baseStart_1597059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 4, 2]
def baseStart_1597203 : Nat := 118140960795 + 1597203 * 2 ^ 59
def prefixEnd_1597203 : Nat := 4983230072969 + 3 ^ 40 * 1597203 * 2
def baseEnd_1597203 : Nat := 820132841803219669617103

theorem tailTrace_1597203 : CollatzResearch.WordTrace tailWord_1597203 prefixEnd_1597203 820132841803219669617103 := by
  unfold tailWord_1597203
  simp only [CollatzResearch.WordTrace]
  refine ⟨58254779232613786400340263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38836519488409190933560175 58254779232613786400340263)
  ·
    refine ⟨87382168848920679600510395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58254779232613786400340263 87382168848920679600510395)
    ·
      refine ⟨131073253273381019400765593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87382168848920679600510395 131073253273381019400765593)
      ·
        refine ⟨98304939955035764550574195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131073253273381019400765593 98304939955035764550574195)
        ·
          refine ⟨147457409932553646825861293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98304939955035764550574195 147457409932553646825861293)
          ·
            refine ⟨55296528724707617559697985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147457409932553646825861293 55296528724707617559697985)
            ·
              refine ⟨41472396543530713169773489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55296528724707617559697985 41472396543530713169773489)
              ·
                refine ⟨31104297407648034877330117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41472396543530713169773489 31104297407648034877330117)
                ·
                  refine ⟨5832055763934006539499397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31104297407648034877330117 5832055763934006539499397)
                  ·
                    refine ⟨1093510455737626226156137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832055763934006539499397 1093510455737626226156137)
                    ·
                      refine ⟨820132841803219669617103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093510455737626226156137 820132841803219669617103)
                      ·
                        rfl

theorem cell23_1597203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4, 2].length) (baseStart_1597203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597203 prefixEnd_1597203 := by exact prefixLift 1597203
  have htrace : WordTrace (prefixWord ++ tailWord_1597203) baseStart_1597203 baseEnd_1597203 := by
    simpa [prefixWord, tailWord_1597203, baseEnd_1597203] using wordTrace_append hprefix tailTrace_1597203
  have hstable : (prefixWord ++ tailWord_1597203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597203).length < 2 ^ (prefixWord ++ tailWord_1597203).sum := by decide
  have hdescent : baseEnd_1597203 < baseStart_1597203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597220 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1597220 : Nat := 118140960795 + 1597220 * 2 ^ 59
def prefixEnd_1597220 : Nat := 4983230072969 + 3 ^ 40 * 1597220 * 2
def baseEnd_1597220 : Nat := 820141570974346103104525

theorem tailTrace_1597220 : CollatzResearch.WordTrace tailWord_1597220 prefixEnd_1597220 820141570974346103104525 := by
  unfold tailWord_1597220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127699636776099151854557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38836932849034798869139409 29127699636776099151854557)
  ·
    refine ⟨10922887363791037181945459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29127699636776099151854557 10922887363791037181945459)
    ·
      refine ⟨16384331045686555772918189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922887363791037181945459 16384331045686555772918189)
      ·
        refine ⟨6144124142132458414844321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16384331045686555772918189 6144124142132458414844321)
        ·
          refine ⟨4608093106599343811133241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6144124142132458414844321 4608093106599343811133241)
          ·
            refine ⟨3456069829949507858349931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608093106599343811133241 3456069829949507858349931)
            ·
              refine ⟨5184104744924261787524897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456069829949507858349931 5184104744924261787524897)
              ·
                refine ⟨3888078558693196340643673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184104744924261787524897 3888078558693196340643673)
                ·
                  refine ⟨2916058919019897255482755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3888078558693196340643673 2916058919019897255482755)
                  ·
                    refine ⟨4374088378529845883224133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2916058919019897255482755 4374088378529845883224133)
                    ·
                      refine ⟨820141570974346103104525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4374088378529845883224133 820141570974346103104525)
                      ·
                        rfl

theorem cell23_1597220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1597220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597220 prefixEnd_1597220 := by exact prefixLift 1597220
  have htrace : WordTrace (prefixWord ++ tailWord_1597220) baseStart_1597220 baseEnd_1597220 := by
    simpa [prefixWord, tailWord_1597220, baseEnd_1597220] using wordTrace_append hprefix tailTrace_1597220
  have hstable : (prefixWord ++ tailWord_1597220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597220).length < 2 ^ (prefixWord ++ tailWord_1597220).sum := by decide
  have hdescent : baseEnd_1597220 < baseStart_1597220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597254 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1597254 : Nat := 118140960795 + 1597254 * 2 ^ 59
def prefixEnd_1597254 : Nat := 4983230072969 + 3 ^ 40 * 1597254 * 2
def baseEnd_1597254 : Nat := 820159029316598970079369

theorem tailTrace_1597254 : CollatzResearch.WordTrace tailWord_1597254 prefixEnd_1597254 820159029316598970079369 := by
  unfold tailWord_1597254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820519979857156940951463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38837759570286014740297877 1820519979857156940951463)
  ·
    refine ⟨2730779969785735411427195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820519979857156940951463 2730779969785735411427195)
    ·
      refine ⟨4096169954678603117140793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730779969785735411427195 4096169954678603117140793)
      ·
        refine ⟨3072127466008952337855595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096169954678603117140793 3072127466008952337855595)
        ·
          refine ⟨4608191199013428506783393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072127466008952337855595 4608191199013428506783393)
          ·
            refine ⟨3456143399260071380087545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608191199013428506783393 3456143399260071380087545)
            ·
              refine ⟨2592107549445053535065659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456143399260071380087545 2592107549445053535065659)
              ·
                refine ⟨3888161324167580302598489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592107549445053535065659 3888161324167580302598489)
                ·
                  refine ⟨2916120993125685226948867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3888161324167580302598489 2916120993125685226948867)
                  ·
                    refine ⟨4374181489688527840423301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2916120993125685226948867 4374181489688527840423301)
                    ·
                      refine ⟨820159029316598970079369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4374181489688527840423301 820159029316598970079369)
                      ·
                        rfl

theorem cell23_1597254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1597254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597254 prefixEnd_1597254 := by exact prefixLift 1597254
  have htrace : WordTrace (prefixWord ++ tailWord_1597254) baseStart_1597254 baseEnd_1597254 := by
    simpa [prefixWord, tailWord_1597254, baseEnd_1597254] using wordTrace_append hprefix tailTrace_1597254
  have hstable : (prefixWord ++ tailWord_1597254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597254).length < 2 ^ (prefixWord ++ tailWord_1597254).sum := by decide
  have hdescent : baseEnd_1597254 < baseStart_1597254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597303 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 8, 4]
def baseStart_1597303 : Nat := 118140960795 + 1597303 * 2 ^ 59
def prefixEnd_1597303 : Nat := 4983230072969 + 3 ^ 40 * 1597303 * 2
def baseEnd_1597303 : Nat := 273394729956223092788881

theorem tailTrace_1597303 : CollatzResearch.WordTrace tailWord_1597303 prefixEnd_1597303 273394729956223092788881 := by
  unfold tailWord_1597303
  simp only [CollatzResearch.WordTrace]
  refine ⟨58258426532251503478980563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38838951021501002319320375 58258426532251503478980563)
  ·
    refine ⟨87387639798377255218470845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58258426532251503478980563 87387639798377255218470845)
    ·
      refine ⟨32770364924391470706926567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87387639798377255218470845 32770364924391470706926567)
      ·
        refine ⟨49155547386587206060389851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32770364924391470706926567 49155547386587206060389851)
        ·
          refine ⟨73733321079880809090584777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49155547386587206060389851 73733321079880809090584777)
          ·
            refine ⟨55299990809910606817938583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73733321079880809090584777 55299990809910606817938583)
            ·
              refine ⟨82949986214865910226907875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55299990809910606817938583 82949986214865910226907875)
              ·
                refine ⟨124424979322298865340361813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82949986214865910226907875 124424979322298865340361813)
                ·
                  refine ⟨1458105226433189828207365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 124424979322298865340361813 1458105226433189828207365)
                  ·
                    refine ⟨273394729956223092788881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458105226433189828207365 273394729956223092788881)
                    ·
                      rfl

theorem cell23_1597303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_1597303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597303 prefixEnd_1597303 := by exact prefixLift 1597303
  have htrace : WordTrace (prefixWord ++ tailWord_1597303) baseStart_1597303 baseEnd_1597303 := by
    simpa [prefixWord, tailWord_1597303, baseEnd_1597303] using wordTrace_append hprefix tailTrace_1597303
  have hstable : (prefixWord ++ tailWord_1597303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597303).length < 2 ^ (prefixWord ++ tailWord_1597303).sum := by decide
  have hdescent : baseEnd_1597303 < baseStart_1597303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597383 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1597383 : Nat := 118140960795 + 1597383 * 2 ^ 59
def prefixEnd_1597383 : Nat := 4983230072969 + 3 ^ 40 * 1597383 * 2
def baseEnd_1597383 : Nat := 820225268321028965366275

theorem tailTrace_1597383 : CollatzResearch.WordTrace tailWord_1597383 prefixEnd_1597383 820225268321028965366275 := by
  unfold tailWord_1597383
  simp only [CollatzResearch.WordTrace]
  refine ⟨58261344371961677141892803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38840896247974451427928535 58261344371961677141892803)
  ·
    refine ⟨87392016557942515712839205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58261344371961677141892803 87392016557942515712839205)
    ·
      refine ⟨16386003104614221696157351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87392016557942515712839205 16386003104614221696157351)
      ·
        refine ⟨24579004656921332544236027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16386003104614221696157351 24579004656921332544236027)
        ·
          refine ⟨36868506985381998816354041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24579004656921332544236027 36868506985381998816354041)
          ·
            refine ⟨27651380239036499112265531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36868506985381998816354041 27651380239036499112265531)
            ·
              refine ⟨41477070358554748668398297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27651380239036499112265531 41477070358554748668398297)
              ·
                refine ⟨31107802768916061501298723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41477070358554748668398297 31107802768916061501298723)
                ·
                  refine ⟨46661704153374092251948085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31107802768916061501298723 46661704153374092251948085)
                  ·
                    refine ⟨4374534764378821148620133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46661704153374092251948085 4374534764378821148620133)
                    ·
                      refine ⟨820225268321028965366275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4374534764378821148620133 820225268321028965366275)
                      ·
                        rfl

theorem cell23_1597383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1597383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597383 prefixEnd_1597383 := by exact prefixLift 1597383
  have htrace : WordTrace (prefixWord ++ tailWord_1597383) baseStart_1597383 baseEnd_1597383 := by
    simpa [prefixWord, tailWord_1597383, baseEnd_1597383] using wordTrace_append hprefix tailTrace_1597383
  have hstable : (prefixWord ++ tailWord_1597383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597383).length < 2 ^ (prefixWord ++ tailWord_1597383).sum := by decide
  have hdescent : baseEnd_1597383 < baseStart_1597383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597387 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 1, 3, 2]
def baseStart_1597387 : Nat := 118140960795 + 1597387 * 2 ^ 59
def prefixEnd_1597387 : Nat := 4983230072969 + 3 ^ 40 * 1597387 * 2
def baseEnd_1597387 : Nat := 820227322243646949716257

theorem tailTrace_1597387 : CollatzResearch.WordTrace tailWord_1597387 prefixEnd_1597387 820227322243646949716257 := by
  unfold tailWord_1597387
  simp only [CollatzResearch.WordTrace]
  refine ⟨58261490263947185825038415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38840993509298123883358943 58261490263947185825038415)
  ·
    refine ⟨87392235395920778737557623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58261490263947185825038415 87392235395920778737557623)
    ·
      refine ⟨131088353093881168106336435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87392235395920778737557623 131088353093881168106336435)
      ·
        refine ⟨196632529640821752159504653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131088353093881168106336435 196632529640821752159504653)
        ·
          refine ⟨73737198615308157059814245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196632529640821752159504653 73737198615308157059814245)
          ·
            refine ⟨13825724740370279448715171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73737198615308157059814245 13825724740370279448715171)
            ·
              refine ⟨20738587110555419173072757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825724740370279448715171 20738587110555419173072757)
              ·
                refine ⟨1944242541614570547475571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20738587110555419173072757 1944242541614570547475571)
                ·
                  refine ⟨2916363812421855821213357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944242541614570547475571 2916363812421855821213357)
                  ·
                    refine ⟨1093636429658195932955009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916363812421855821213357 1093636429658195932955009)
                    ·
                      refine ⟨820227322243646949716257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093636429658195932955009 820227322243646949716257)
                      ·
                        rfl

theorem cell23_1597387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3, 2].length) (baseStart_1597387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597387 prefixEnd_1597387 := by exact prefixLift 1597387
  have htrace : WordTrace (prefixWord ++ tailWord_1597387) baseStart_1597387 baseEnd_1597387 := by
    simpa [prefixWord, tailWord_1597387, baseEnd_1597387] using wordTrace_append hprefix tailTrace_1597387
  have hstable : (prefixWord ++ tailWord_1597387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597387).length < 2 ^ (prefixWord ++ tailWord_1597387).sum := by decide
  have hdescent : baseEnd_1597387 < baseStart_1597387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597393 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1597393 : Nat := 118140960795 + 1597393 * 2 ^ 59
def prefixEnd_1597393 : Nat := 4983230072969 + 3 ^ 40 * 1597393 * 2
def baseEnd_1597393 : Nat := 273410134375857975413743

theorem tailTrace_1597393 : CollatzResearch.WordTrace tailWord_1597393 prefixEnd_1597393 273410134375857975413743 := by
  unfold tailWord_1597393
  simp only [CollatzResearch.WordTrace]
  refine ⟨58261709101925448849756833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38841139401283632566504555 58261709101925448849756833)
  ·
    refine ⟨43696281826444086637317625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58261709101925448849756833 43696281826444086637317625)
    ·
      refine ⟨32772211369833064977988219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43696281826444086637317625 32772211369833064977988219)
      ·
        refine ⟨49158317054749597466982329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32772211369833064977988219 49158317054749597466982329)
        ·
          refine ⟨36868737791062198100236747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49158317054749597466982329 36868737791062198100236747)
          ·
            refine ⟨55303106686593297150355121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36868737791062198100236747 55303106686593297150355121)
            ·
              refine ⟨41477330014944972862766341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55303106686593297150355121 41477330014944972862766341)
              ·
                refine ⟨7776999377802182411768689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41477330014944972862766341 7776999377802182411768689)
                ·
                  refine ⟨5832749533351636808826517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7776999377802182411768689 5832749533351636808826517)
                  ·
                    refine ⟨273410134375857975413743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5832749533351636808826517 273410134375857975413743)
                    ·
                      rfl

theorem cell23_1597393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1597393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597393 prefixEnd_1597393 := by exact prefixLift 1597393
  have htrace : WordTrace (prefixWord ++ tailWord_1597393) baseStart_1597393 baseEnd_1597393 := by
    simpa [prefixWord, tailWord_1597393, baseEnd_1597393] using wordTrace_append hprefix tailTrace_1597393
  have hstable : (prefixWord ++ tailWord_1597393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597393).length < 2 ^ (prefixWord ++ tailWord_1597393).sum := by decide
  have hdescent : baseEnd_1597393 < baseStart_1597393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597411 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1597411 : Nat := 118140960795 + 1597411 * 2 ^ 59
def prefixEnd_1597411 : Nat := 4983230072969 + 3 ^ 40 * 1597411 * 2
def baseEnd_1597411 : Nat := 820239645779354855816147

theorem tailTrace_1597411 : CollatzResearch.WordTrace tailWord_1597411 prefixEnd_1597411 820239645779354855816147 := by
  unfold tailWord_1597411
  simp only [CollatzResearch.WordTrace]
  refine ⟨58262365615860237923912087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38841577077240158615941391 58262365615860237923912087)
  ·
    refine ⟨87393548423790356885868131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58262365615860237923912087 87393548423790356885868131)
    ·
      refine ⟨131090322635685535328802197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87393548423790356885868131 131090322635685535328802197)
      ·
        refine ⟨6144858873547759468537603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131090322635685535328802197 6144858873547759468537603)
        ·
          refine ⟨9217288310321639202806405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144858873547759468537603 9217288310321639202806405)
          ·
            refine ⟨1728241558185307350526201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9217288310321639202806405 1728241558185307350526201)
            ·
              refine ⟨1296181168638980512894651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728241558185307350526201 1296181168638980512894651)
              ·
                refine ⟨1944271752958470769341977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296181168638980512894651 1944271752958470769341977)
                ·
                  refine ⟨1458203814718853077006483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1944271752958470769341977 1458203814718853077006483)
                  ·
                    refine ⟨2187305722078279615509725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1458203814718853077006483 2187305722078279615509725)
                    ·
                      refine ⟨820239645779354855816147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2187305722078279615509725 820239645779354855816147)
                      ·
                        rfl

theorem cell23_1597411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1597411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597411 prefixEnd_1597411 := by exact prefixLift 1597411
  have htrace : WordTrace (prefixWord ++ tailWord_1597411) baseStart_1597411 baseEnd_1597411 := by
    simpa [prefixWord, tailWord_1597411, baseEnd_1597411] using wordTrace_append hprefix tailTrace_1597411
  have hstable : (prefixWord ++ tailWord_1597411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597411).length < 2 ^ (prefixWord ++ tailWord_1597411).sum := by decide
  have hdescent : baseEnd_1597411 < baseStart_1597411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597421 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1597421 : Nat := 118140960795 + 1597421 * 2 ^ 59
def prefixEnd_1597421 : Nat := 4983230072969 + 3 ^ 40 * 1597421 * 2
def baseEnd_1597421 : Nat := 820244780585899816691101

theorem tailTrace_1597421 : CollatzResearch.WordTrace tailWord_1597421 prefixEnd_1597421 820244780585899816691101 := by
  unfold tailWord_1597421
  simp only [CollatzResearch.WordTrace]
  refine ⟨58262730345824009631776117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38841820230549339754517411 58262730345824009631776117)
  ·
    refine ⟨5462130969921000902979011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58262730345824009631776117 5462130969921000902979011)
    ·
      refine ⟨8193196454881501354468517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462130969921000902979011 8193196454881501354468517)
      ·
        refine ⟨1536224335290281503962847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8193196454881501354468517 1536224335290281503962847)
        ·
          refine ⟨2304336502935422255944271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536224335290281503962847 2304336502935422255944271)
          ·
            refine ⟨3456504754403133383916407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304336502935422255944271 3456504754403133383916407)
            ·
              refine ⟨5184757131604700075874611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456504754403133383916407 5184757131604700075874611)
              ·
                refine ⟨7777135697407050113811917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184757131604700075874611 7777135697407050113811917)
                ·
                  refine ⟨2916425886527643792679469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7777135697407050113811917 2916425886527643792679469)
                  ·
                    refine ⟨1093659707447866422254801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916425886527643792679469 1093659707447866422254801)
                    ·
                      refine ⟨820244780585899816691101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093659707447866422254801 820244780585899816691101)
                      ·
                        rfl

theorem cell23_1597421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1597421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597421 prefixEnd_1597421 := by exact prefixLift 1597421
  have htrace : WordTrace (prefixWord ++ tailWord_1597421) baseStart_1597421 baseEnd_1597421 := by
    simpa [prefixWord, tailWord_1597421, baseEnd_1597421] using wordTrace_append hprefix tailTrace_1597421
  have hstable : (prefixWord ++ tailWord_1597421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597421).length < 2 ^ (prefixWord ++ tailWord_1597421).sum := by decide
  have hdescent : baseEnd_1597421 < baseStart_1597421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597423 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 9]
def baseStart_1597423 : Nat := 118140960795 + 1597423 * 2 ^ 59
def prefixEnd_1597423 : Nat := 4983230072969 + 3 ^ 40 * 1597423 * 2
def baseEnd_1597423 : Nat := 91138423060800978762899

theorem tailTrace_1597423 : CollatzResearch.WordTrace tailWord_1597423 prefixEnd_1597423 91138423060800978762899 := by
  unfold tailWord_1597423
  simp only [CollatzResearch.WordTrace]
  refine ⟨58262803291816763973348923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38841868861211175982232615 58262803291816763973348923)
  ·
    refine ⟨87394204937725145960023385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58262803291816763973348923 87394204937725145960023385)
    ·
      refine ⟨65545653703293859470017539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87394204937725145960023385 65545653703293859470017539)
      ·
        refine ⟨98318480554940789205026309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65545653703293859470017539 98318480554940789205026309)
        ·
          refine ⟨18434715104051397975942433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98318480554940789205026309 18434715104051397975942433)
          ·
            refine ⟨13826036328038548481956825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18434715104051397975942433 13826036328038548481956825)
            ·
              refine ⟨10369527246028911361467619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13826036328038548481956825 10369527246028911361467619)
              ·
                refine ⟨15554290869043367042201429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10369527246028911361467619 15554290869043367042201429)
                ·
                  refine ⟨91138423060800978762899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15554290869043367042201429 91138423060800978762899)
                  ·
                    rfl

theorem cell23_1597423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 9].length) (baseStart_1597423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597423 prefixEnd_1597423 := by exact prefixLift 1597423
  have htrace : WordTrace (prefixWord ++ tailWord_1597423) baseStart_1597423 baseEnd_1597423 := by
    simpa [prefixWord, tailWord_1597423, baseEnd_1597423] using wordTrace_append hprefix tailTrace_1597423
  have hstable : (prefixWord ++ tailWord_1597423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597423).length < 2 ^ (prefixWord ++ tailWord_1597423).sum := by decide
  have hdescent : baseEnd_1597423 < baseStart_1597423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597438 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1597438 : Nat := 118140960795 + 1597438 * 2 ^ 59
def prefixEnd_1597438 : Nat := 4983230072969 + 3 ^ 40 * 1597438 * 2
def baseEnd_1597438 : Nat := 820253509757026250178523

theorem tailTrace_1597438 : CollatzResearch.WordTrace tailWord_1597438 prefixEnd_1597438 820253509757026250178523 := by
  unfold tailWord_1597438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282918798345302691893121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38842233591174947690096645 7282918798345302691893121)
  ·
    refine ⟨5462189098758977018919841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7282918798345302691893121 5462189098758977018919841)
    ·
      refine ⟨4096641824069232764189881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5462189098758977018919841 4096641824069232764189881)
      ·
        refine ⟨3072481368051924573142411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096641824069232764189881 3072481368051924573142411)
        ·
          refine ⟨4608722052077886859713617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072481368051924573142411 4608722052077886859713617)
          ·
            refine ⟨3456541539058415144785213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608722052077886859713617 3456541539058415144785213)
            ·
              refine ⟨1296203077146905679294455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3456541539058415144785213 1296203077146905679294455)
              ·
                refine ⟨1944304615720358518941683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296203077146905679294455 1944304615720358518941683)
                ·
                  refine ⟨2916456923580537778412525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944304615720358518941683 2916456923580537778412525)
                  ·
                    refine ⟨1093671346342701666904697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916456923580537778412525 1093671346342701666904697)
                    ·
                      refine ⟨820253509757026250178523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093671346342701666904697 820253509757026250178523)
                      ·
                        rfl

theorem cell23_1597438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1597438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597438 prefixEnd_1597438 := by exact prefixLift 1597438
  have htrace : WordTrace (prefixWord ++ tailWord_1597438) baseStart_1597438 baseEnd_1597438 := by
    simpa [prefixWord, tailWord_1597438, baseEnd_1597438] using wordTrace_append hprefix tailTrace_1597438
  have hstable : (prefixWord ++ tailWord_1597438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597438).length < 2 ^ (prefixWord ++ tailWord_1597438).sum := by decide
  have hdescent : baseEnd_1597438 < baseStart_1597438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597446 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1597446 : Nat := 118140960795 + 1597446 * 2 ^ 59
def prefixEnd_1597446 : Nat := 4983230072969 + 3 ^ 40 * 1597446 * 2
def baseEnd_1597446 : Nat := 820257617602262218878487

theorem tailTrace_1597446 : CollatzResearch.WordTrace tailWord_1597446 prefixEnd_1597446 820257617602262218878487 := by
  unfold tailWord_1597446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820738817835419965669881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38842428113822292600957461 1820738817835419965669881)
  ·
    refine ⟨1365554113376564974252411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1820738817835419965669881 1365554113376564974252411)
    ·
      refine ⟨2048331170064847461378617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365554113376564974252411 2048331170064847461378617)
      ·
        refine ⟨1536248377548635596033963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048331170064847461378617 1536248377548635596033963)
        ·
          refine ⟨2304372566322953394050945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536248377548635596033963 2304372566322953394050945)
          ·
            refine ⟨1728279424742215045538209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304372566322953394050945 1728279424742215045538209)
            ·
              refine ⟨1296209568556661284153657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728279424742215045538209 1296209568556661284153657)
              ·
                refine ⟨972157176417495963115243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296209568556661284153657 972157176417495963115243)
                ·
                  refine ⟨1458235764626243944672865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972157176417495963115243 1458235764626243944672865)
                  ·
                    refine ⟨1093676823469682958504649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1458235764626243944672865 1093676823469682958504649)
                    ·
                      refine ⟨820257617602262218878487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093676823469682958504649 820257617602262218878487)
                      ·
                        rfl

theorem cell23_1597446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1597446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597446 prefixEnd_1597446 := by exact prefixLift 1597446
  have htrace : WordTrace (prefixWord ++ tailWord_1597446) baseStart_1597446 baseEnd_1597446 := by
    simpa [prefixWord, tailWord_1597446, baseEnd_1597446] using wordTrace_append hprefix tailTrace_1597446
  have hstable : (prefixWord ++ tailWord_1597446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597446).length < 2 ^ (prefixWord ++ tailWord_1597446).sum := by decide
  have hdescent : baseEnd_1597446 < baseStart_1597446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597483 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 10]
def baseStart_1597483 : Nat := 118140960795 + 1597483 * 2 ^ 59
def prefixEnd_1597483 : Nat := 4983230072969 + 3 ^ 40 * 1597483 * 2
def baseEnd_1597483 : Nat := 273425538795492858038605

theorem tailTrace_1597483 : CollatzResearch.WordTrace tailWord_1597483 prefixEnd_1597483 273425538795492858038605 := by
  unfold tailWord_1597483
  simp only [CollatzResearch.WordTrace]
  refine ⟨58264991671599394220533103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38843327781066262813688735 58264991671599394220533103)
  ·
    refine ⟨87397487507399091330799655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58264991671599394220533103 87397487507399091330799655)
    ·
      refine ⟨131096231261098636996199483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87397487507399091330799655 131096231261098636996199483)
      ·
        refine ⟨196644346891647955494299225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131096231261098636996199483 196644346891647955494299225)
        ·
          refine ⟨147483260168735966620724419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196644346891647955494299225 147483260168735966620724419)
          ·
            refine ⟨221224890253103949931086629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147483260168735966620724419 221224890253103949931086629)
            ·
              refine ⟨41479666922456990612078743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221224890253103949931086629 41479666922456990612078743)
              ·
                refine ⟨62219500383685485918118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41479666922456990612078743 62219500383685485918118115)
                ·
                  refine ⟨93329250575528228877177173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62219500383685485918118115 93329250575528228877177173)
                  ·
                    refine ⟨273425538795492858038605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 93329250575528228877177173 273425538795492858038605)
                    ·
                      rfl

theorem cell23_1597483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_1597483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597483 prefixEnd_1597483 := by exact prefixLift 1597483
  have htrace : WordTrace (prefixWord ++ tailWord_1597483) baseStart_1597483 baseEnd_1597483 := by
    simpa [prefixWord, tailWord_1597483, baseEnd_1597483] using wordTrace_append hprefix tailTrace_1597483
  have hstable : (prefixWord ++ tailWord_1597483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597483).length < 2 ^ (prefixWord ++ tailWord_1597483).sum := by decide
  have hdescent : baseEnd_1597483 < baseStart_1597483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597551 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 1, 4]
def baseStart_1597551 : Nat := 118140960795 + 1597551 * 2 ^ 59
def prefixEnd_1597551 : Nat := 4983230072969 + 3 ^ 40 * 1597551 * 2
def baseEnd_1597551 : Nat := 273437177690328102688501

theorem tailTrace_1597551 : CollatzResearch.WordTrace tailWord_1597551 prefixEnd_1597551 273437177690328102688501 := by
  unfold tailWord_1597551
  simp only [CollatzResearch.WordTrace]
  refine ⟨58267471835353041834008507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38844981223568694556005671 58267471835353041834008507)
  ·
    refine ⟨87401207753029562751012761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58267471835353041834008507 87401207753029562751012761)
    ·
      refine ⟨65550905814772172063259571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87401207753029562751012761 65550905814772172063259571)
      ·
        refine ⟨98326358722158258094889357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65550905814772172063259571 98326358722158258094889357)
        ·
          refine ⟨36872384520809346785583509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98326358722158258094889357 36872384520809346785583509)
          ·
            refine ⟨1728393024412938130574227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36872384520809346785583509 1728393024412938130574227)
            ·
              refine ⟨2592589536619407195861341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728393024412938130574227 2592589536619407195861341)
              ·
                refine ⟨972221076232277698448003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2592589536619407195861341 972221076232277698448003)
                ·
                  refine ⟨1458331614348416547672005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972221076232277698448003 1458331614348416547672005)
                  ·
                    refine ⟨273437177690328102688501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458331614348416547672005 273437177690328102688501)
                    ·
                      rfl

theorem cell23_1597551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_1597551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597551 prefixEnd_1597551 := by exact prefixLift 1597551
  have htrace : WordTrace (prefixWord ++ tailWord_1597551) baseStart_1597551 baseEnd_1597551 := by
    simpa [prefixWord, tailWord_1597551, baseEnd_1597551] using wordTrace_append hprefix tailTrace_1597551
  have hstable : (prefixWord ++ tailWord_1597551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597551).length < 2 ^ (prefixWord ++ tailWord_1597551).sum := by decide
  have hdescent : baseEnd_1597551 < baseStart_1597551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597560 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_1597560 : Nat := 118140960795 + 1597560 * 2 ^ 59
def prefixEnd_1597560 : Nat := 4983230072969 + 3 ^ 40 * 1597560 * 2
def baseEnd_1597560 : Nat := 273438718132291590950987

theorem tailTrace_1597560 : CollatzResearch.WordTrace tailWord_1597560 prefixEnd_1597560 273438718132291590950987 := by
  unfold tailWord_1597560
  simp only [CollatzResearch.WordTrace]
  refine ⟨29133900046160218185543067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38845200061546957580724089 29133900046160218185543067)
  ·
    refine ⟨43700850069240327278314601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29133900046160218185543067 43700850069240327278314601)
    ·
      refine ⟨32775637551930245458735951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43700850069240327278314601 32775637551930245458735951)
      ·
        refine ⟨49163456327895368188103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32775637551930245458735951 49163456327895368188103927)
        ·
          refine ⟨73745184491843052282155891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49163456327895368188103927 73745184491843052282155891)
          ·
            refine ⟨110617776737764578423233837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73745184491843052282155891 110617776737764578423233837)
            ·
              refine ⟨41481666276661716908712689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110617776737764578423233837 41481666276661716908712689)
              ·
                refine ⟨31111249707496287681534517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41481666276661716908712689 31111249707496287681534517)
                ·
                  refine ⟨2916679660077776970143861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31111249707496287681534517 2916679660077776970143861)
                  ·
                    refine ⟨273438718132291590950987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2916679660077776970143861 273438718132291590950987)
                    ·
                      rfl

theorem cell23_1597560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_1597560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597560 prefixEnd_1597560 := by exact prefixLift 1597560
  have htrace : WordTrace (prefixWord ++ tailWord_1597560) baseStart_1597560 baseEnd_1597560 := by
    simpa [prefixWord, tailWord_1597560, baseEnd_1597560] using wordTrace_append hprefix tailTrace_1597560
  have hstable : (prefixWord ++ tailWord_1597560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597560).length < 2 ^ (prefixWord ++ tailWord_1597560).sum := by decide
  have hdescent : baseEnd_1597560 < baseStart_1597560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597580 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1597580 : Nat := 118140960795 + 1597580 * 2 ^ 59
def prefixEnd_1597580 : Nat := 4983230072969 + 3 ^ 40 * 1597580 * 2
def baseEnd_1597580 : Nat := 820326424009964694602869

theorem tailTrace_1597580 : CollatzResearch.WordTrace tailWord_1597580 prefixEnd_1597580 820326424009964694602869 := by
  unfold tailWord_1597580
  simp only [CollatzResearch.WordTrace]
  refine ⟨29134264776123989893407097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38845686368165319857876129 29134264776123989893407097)
  ·
    refine ⟨21850698582092992420055323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29134264776123989893407097 21850698582092992420055323)
    ·
      refine ⟨32776047873139488630082985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21850698582092992420055323 32776047873139488630082985)
      ·
        refine ⟨24582035904854616472562239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32776047873139488630082985 24582035904854616472562239)
        ·
          refine ⟨36873053857281924708843359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24582035904854616472562239 36873053857281924708843359)
          ·
            refine ⟨55309580785922887063265039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36873053857281924708843359 55309580785922887063265039)
            ·
              refine ⟨82964371178884330594897559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55309580785922887063265039 82964371178884330594897559)
              ·
                refine ⟨124446556768326495892346339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82964371178884330594897559 124446556768326495892346339)
                ·
                  refine ⟨186669835152489743838519509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124446556768326495892346339 186669835152489743838519509)
                  ·
                    refine ⟨4375074261386478371215301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186669835152489743838519509 4375074261386478371215301)
                    ·
                      refine ⟨820326424009964694602869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4375074261386478371215301 820326424009964694602869)
                      ·
                        rfl

theorem cell23_1597580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1597580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597580 prefixEnd_1597580 := by exact prefixLift 1597580
  have htrace : WordTrace (prefixWord ++ tailWord_1597580) baseStart_1597580 baseEnd_1597580 := by
    simpa [prefixWord, tailWord_1597580, baseEnd_1597580] using wordTrace_append hprefix tailTrace_1597580
  have hstable : (prefixWord ++ tailWord_1597580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597580).length < 2 ^ (prefixWord ++ tailWord_1597580).sum := by decide
  have hdescent : baseEnd_1597580 < baseStart_1597580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597594 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_1597594 : Nat := 118140960795 + 1597594 * 2 ^ 59
def prefixEnd_1597594 : Nat := 4983230072969 + 3 ^ 40 * 1597594 * 2
def baseEnd_1597594 : Nat := 273444537579709213275935

theorem tailTrace_1597594 : CollatzResearch.WordTrace tailWord_1597594 prefixEnd_1597594 273444537579709213275935 := by
  unfold tailWord_1597594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567260043549315044455959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38846026782798173451882557 14567260043549315044455959)
  ·
    refine ⟨21850890065323972566683939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14567260043549315044455959 21850890065323972566683939)
    ·
      refine ⟨32776335097985958850025909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21850890065323972566683939 32776335097985958850025909)
      ·
        refine ⟨3072781415436183642189929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32776335097985958850025909 3072781415436183642189929)
        ·
          refine ⟨2304586061577137731642447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3072781415436183642189929 2304586061577137731642447)
          ·
            refine ⟨3456879092365706597463671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304586061577137731642447 3456879092365706597463671)
            ·
              refine ⟨5185318638548559896195507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456879092365706597463671 5185318638548559896195507)
              ·
                refine ⟨7777977957822839844293261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185318638548559896195507 7777977957822839844293261)
                ·
                  refine ⟨2916741734183564941609973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7777977957822839844293261 2916741734183564941609973)
                  ·
                    refine ⟨273444537579709213275935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2916741734183564941609973 273444537579709213275935)
                    ·
                      rfl

theorem cell23_1597594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_1597594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597594 prefixEnd_1597594 := by exact prefixLift 1597594
  have htrace : WordTrace (prefixWord ++ tailWord_1597594) baseStart_1597594 baseEnd_1597594 := by
    simpa [prefixWord, tailWord_1597594, baseEnd_1597594] using wordTrace_append hprefix tailTrace_1597594
  have hstable : (prefixWord ++ tailWord_1597594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597594).length < 2 ^ (prefixWord ++ tailWord_1597594).sum := by decide
  have hdescent : baseEnd_1597594 < baseStart_1597594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597601 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1597601 : Nat := 118140960795 + 1597601 * 2 ^ 59
def prefixEnd_1597601 : Nat := 4983230072969 + 3 ^ 40 * 1597601 * 2
def baseEnd_1597601 : Nat := 820337207103709112440273

theorem tailTrace_1597601 : CollatzResearch.WordTrace tailWord_1597601 prefixEnd_1597601 820337207103709112440273 := by
  unfold tailWord_1597601
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269295485171900373328657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38846196990114600248885771 58269295485171900373328657)
  ·
    refine ⟨43701971613878925279996493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58269295485171900373328657 43701971613878925279996493)
    ·
      refine ⟨16388239355204596979998685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43701971613878925279996493 16388239355204596979998685)
      ·
        refine ⟨6145589758201723867499507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16388239355204596979998685 6145589758201723867499507)
        ·
          refine ⟨9218384637302585801249261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145589758201723867499507 9218384637302585801249261)
          ·
            refine ⟨3456894238988469675468473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9218384637302585801249261 3456894238988469675468473)
            ·
              refine ⟨2592670679241352256601355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456894238988469675468473 2592670679241352256601355)
              ·
                refine ⟨3889006018862028384902033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592670679241352256601355 3889006018862028384902033)
                ·
                  refine ⟨2916754514146521288676525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3889006018862028384902033 2916754514146521288676525)
                  ·
                    refine ⟨1093782942804945483253697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916754514146521288676525 1093782942804945483253697)
                    ·
                      refine ⟨820337207103709112440273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093782942804945483253697 820337207103709112440273)
                      ·
                        rfl

theorem cell23_1597601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1597601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597601 prefixEnd_1597601 := by exact prefixLift 1597601
  have htrace : WordTrace (prefixWord ++ tailWord_1597601) baseStart_1597601 baseEnd_1597601 := by
    simpa [prefixWord, tailWord_1597601, baseEnd_1597601] using wordTrace_append hprefix tailTrace_1597601
  have hstable : (prefixWord ++ tailWord_1597601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597601).length < 2 ^ (prefixWord ++ tailWord_1597601).sum := by decide
  have hdescent : baseEnd_1597601 < baseStart_1597601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597624 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_1597624 : Nat := 118140960795 + 1597624 * 2 ^ 59
def prefixEnd_1597624 : Nat := 4983230072969 + 3 ^ 40 * 1597624 * 2
def baseEnd_1597624 : Nat := 273449672386254174150889

theorem tailTrace_1597624 : CollatzResearch.WordTrace tailWord_1597624 prefixEnd_1597624 273449672386254174150889 := by
  unfold tailWord_1597624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29135067182044287650707963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38846756242725716867610617 29135067182044287650707963)
  ·
    refine ⟨43702600773066431476061945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29135067182044287650707963 43702600773066431476061945)
    ·
      refine ⟨32776950579799823607046459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43702600773066431476061945 32776950579799823607046459)
      ·
        refine ⟨49165425869699735410569689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32776950579799823607046459 49165425869699735410569689)
        ·
          refine ⟨36874069402274801557927267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49165425869699735410569689 36874069402274801557927267)
          ·
            refine ⟨55311104103412202336890901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36874069402274801557927267 55311104103412202336890901)
            ·
              refine ⟨2592708004847446984541761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55311104103412202336890901 2592708004847446984541761)
              ·
                refine ⟨1944531003635585238406321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592708004847446984541761 1944531003635585238406321)
                ·
                  refine ⟨1458398252726688928804741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1944531003635585238406321 1458398252726688928804741)
                  ·
                    refine ⟨273449672386254174150889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458398252726688928804741 273449672386254174150889)
                    ·
                      rfl

theorem cell23_1597624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_1597624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597624 prefixEnd_1597624 := by exact prefixLift 1597624
  have htrace : WordTrace (prefixWord ++ tailWord_1597624) baseStart_1597624 baseEnd_1597624 := by
    simpa [prefixWord, tailWord_1597624, baseEnd_1597624] using wordTrace_append hprefix tailTrace_1597624
  have hstable : (prefixWord ++ tailWord_1597624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597624).length < 2 ^ (prefixWord ++ tailWord_1597624).sum := by decide
  have hdescent : baseEnd_1597624 < baseStart_1597624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597664 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_1597664 : Nat := 118140960795 + 1597664 * 2 ^ 59
def prefixEnd_1597664 : Nat := 4983230072969 + 3 ^ 40 * 1597664 * 2
def baseEnd_1597664 : Nat := 820369556384942365952483

theorem tailTrace_1597664 : CollatzResearch.WordTrace tailWord_1597664 prefixEnd_1597664 820369556384942365952483 := by
  unfold tailWord_1597664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29135796641971831066436023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38847728855962441421914697 29135796641971831066436023)
  ·
    refine ⟨43703694962957746599654035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29135796641971831066436023 43703694962957746599654035)
    ·
      refine ⟨65555542444436619899481053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43703694962957746599654035 65555542444436619899481053)
      ·
        refine ⟨24583328416663732462305395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65555542444436619899481053 24583328416663732462305395)
        ·
          refine ⟨36874992624995598693458093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24583328416663732462305395 36874992624995598693458093)
          ·
            refine ⟨13828122234373349510046785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36874992624995598693458093 13828122234373349510046785)
            ·
              refine ⟨10371091675780012132535089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828122234373349510046785 10371091675780012132535089)
              ·
                refine ⟨7778318756835009099401317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10371091675780012132535089 7778318756835009099401317)
                ·
                  refine ⟨1458434766906564206137747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7778318756835009099401317 1458434766906564206137747)
                  ·
                    refine ⟨2187652150359846309206621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1458434766906564206137747 2187652150359846309206621)
                    ·
                      refine ⟨820369556384942365952483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2187652150359846309206621 820369556384942365952483)
                      ·
                        rfl

theorem cell23_1597664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_1597664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597664 prefixEnd_1597664 := by exact prefixLift 1597664
  have htrace : WordTrace (prefixWord ++ tailWord_1597664) baseStart_1597664 baseEnd_1597664 := by
    simpa [prefixWord, tailWord_1597664, baseEnd_1597664] using wordTrace_append hprefix tailTrace_1597664
  have hstable : (prefixWord ++ tailWord_1597664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597664).length < 2 ^ (prefixWord ++ tailWord_1597664).sum := by decide
  have hdescent : baseEnd_1597664 < baseStart_1597664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597681 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_1597681 : Nat := 118140960795 + 1597681 * 2 ^ 59
def prefixEnd_1597681 : Nat := 4983230072969 + 3 ^ 40 * 1597681 * 2
def baseEnd_1597681 : Nat := 820378285556068799439905

theorem tailTrace_1597681 : CollatzResearch.WordTrace tailWord_1597681 prefixEnd_1597681 820378285556068799439905 := by
  unfold tailWord_1597681
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272213324882074036240897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38848142216588049357493931 58272213324882074036240897)
  ·
    refine ⟨43704159993661555527180673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58272213324882074036240897 43704159993661555527180673)
    ·
      refine ⟨32778119995246166645385505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43704159993661555527180673 32778119995246166645385505)
      ·
        refine ⟨24583589996434624984039129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32778119995246166645385505 24583589996434624984039129)
        ·
          refine ⟨18437692497325968738029347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24583589996434624984039129 18437692497325968738029347)
          ·
            refine ⟨27656538745988953107044021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437692497325968738029347 27656538745988953107044021)
            ·
              refine ⟨2592800507436464353785377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27656538745988953107044021 2592800507436464353785377)
              ·
                refine ⟨1944600380577348265339033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592800507436464353785377 1944600380577348265339033)
                ·
                  refine ⟨1458450285433011199004275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1944600380577348265339033 1458450285433011199004275)
                  ·
                    refine ⟨2187675428149516798506413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1458450285433011199004275 2187675428149516798506413)
                    ·
                      refine ⟨820378285556068799439905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2187675428149516798506413 820378285556068799439905)
                      ·
                        rfl

theorem cell23_1597681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_1597681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597681 prefixEnd_1597681 := by exact prefixLift 1597681
  have htrace : WordTrace (prefixWord ++ tailWord_1597681) baseStart_1597681 baseEnd_1597681 := by
    simpa [prefixWord, tailWord_1597681, baseEnd_1597681] using wordTrace_append hprefix tailTrace_1597681
  have hstable : (prefixWord ++ tailWord_1597681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597681).length < 2 ^ (prefixWord ++ tailWord_1597681).sum := by decide
  have hdescent : baseEnd_1597681 < baseStart_1597681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597697 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1597697 : Nat := 118140960795 + 1597697 * 2 ^ 59
def prefixEnd_1597697 : Nat := 4983230072969 + 3 ^ 40 * 1597697 * 2
def baseEnd_1597697 : Nat := 273462167082180245613277

theorem tailTrace_1597697 : CollatzResearch.WordTrace tailWord_1597697 prefixEnd_1597697 273462167082180245613277 := by
  unfold tailWord_1597697
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272796892824108768823345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38848531261882739179215563 58272796892824108768823345)
  ·
    refine ⟨43704597669618081576617509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58272796892824108768823345 43704597669618081576617509)
    ·
      refine ⟨8194612063053390295615783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43704597669618081576617509 8194612063053390295615783)
      ·
        refine ⟨12291918094580085443423675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194612063053390295615783 12291918094580085443423675)
        ·
          refine ⟨18437877141870128165135513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291918094580085443423675 18437877141870128165135513)
          ·
            refine ⟨13828407856402596123851635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18437877141870128165135513 13828407856402596123851635)
            ·
              refine ⟨20742611784603894185777453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13828407856402596123851635 20742611784603894185777453)
              ·
                refine ⟨7778479419226460319666545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20742611784603894185777453 7778479419226460319666545)
                ·
                  refine ⟨5833859564419845239749909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778479419226460319666545 5833859564419845239749909)
                  ·
                    refine ⟨273462167082180245613277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5833859564419845239749909 273462167082180245613277)
                    ·
                      rfl

theorem cell23_1597697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1597697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597697 prefixEnd_1597697 := by exact prefixLift 1597697
  have htrace : WordTrace (prefixWord ++ tailWord_1597697) baseStart_1597697 baseEnd_1597697 := by
    simpa [prefixWord, tailWord_1597697, baseEnd_1597697] using wordTrace_append hprefix tailTrace_1597697
  have hstable : (prefixWord ++ tailWord_1597697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597697).length < 2 ^ (prefixWord ++ tailWord_1597697).sum := by decide
  have hdescent : baseEnd_1597697 < baseStart_1597697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597698 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1597698 : Nat := 118140960795 + 1597698 * 2 ^ 59
def prefixEnd_1597698 : Nat := 4983230072969 + 3 ^ 40 * 1597698 * 2
def baseEnd_1597698 : Nat := 820387014727195232927327

theorem tailTrace_1597698 : CollatzResearch.WordTrace tailWord_1597698 prefixEnd_1597698 820387014727195232927327 := by
  unfold tailWord_1597698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568208341455121484902437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38848555577213657293073165 14568208341455121484902437)
  ·
    refine ⟨2731539064022835278419207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14568208341455121484902437 2731539064022835278419207)
    ·
      refine ⟨4097308596034252917628811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731539064022835278419207 4097308596034252917628811)
      ·
        refine ⟨6145962894051379376443217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097308596034252917628811 6145962894051379376443217)
        ·
          refine ⟨4609472170538534532332413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145962894051379376443217 4609472170538534532332413)
          ·
            refine ⟨1728552063951950449624655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4609472170538534532332413 1728552063951950449624655)
            ·
              refine ⟨2592828095927925674436983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728552063951950449624655 2592828095927925674436983)
              ·
                refine ⟨3889242143891888511655475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592828095927925674436983 3889242143891888511655475)
                ·
                  refine ⟨5833863215837832767483213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889242143891888511655475 5833863215837832767483213)
                  ·
                    refine ⟨2187698705939187287806205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5833863215837832767483213 2187698705939187287806205)
                    ·
                      refine ⟨820387014727195232927327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2187698705939187287806205 820387014727195232927327)
                      ·
                        rfl

theorem cell23_1597698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1597698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597698 prefixEnd_1597698 := by exact prefixLift 1597698
  have htrace : WordTrace (prefixWord ++ tailWord_1597698) baseStart_1597698 baseEnd_1597698 := by
    simpa [prefixWord, tailWord_1597698, baseEnd_1597698] using wordTrace_append hprefix tailTrace_1597698
  have hstable : (prefixWord ++ tailWord_1597698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597698).length < 2 ^ (prefixWord ++ tailWord_1597698).sum := by decide
  have hdescent : baseEnd_1597698 < baseStart_1597698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597707 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_1597707 : Nat := 118140960795 + 1597707 * 2 ^ 59
def prefixEnd_1597707 : Nat := 4983230072969 + 3 ^ 40 * 1597707 * 2
def baseEnd_1597707 : Nat := 820391636053085697714785

theorem tailTrace_1597707 : CollatzResearch.WordTrace tailWord_1597707 prefixEnd_1597707 820391636053085697714785 := by
  unfold tailWord_1597707
  simp only [CollatzResearch.WordTrace]
  refine ⟨58273161622787880476687375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38848774415191920317791583 58273161622787880476687375)
  ·
    refine ⟨87409742434181820715031063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58273161622787880476687375 87409742434181820715031063)
    ·
      refine ⟨131114613651272731072546595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87409742434181820715031063 131114613651272731072546595)
      ·
        refine ⟨196671920476909096608819893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131114613651272731072546595 196671920476909096608819893)
        ·
          refine ⟨18437992544710227807076865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196671920476909096608819893 18437992544710227807076865)
          ·
            refine ⟨13828494408532670855307649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18437992544710227807076865 13828494408532670855307649)
            ·
              refine ⟨10371370806399503141480737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828494408532670855307649 10371370806399503141480737)
              ·
                refine ⟨7778528104799627356110553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10371370806399503141480737 7778528104799627356110553)
                ·
                  refine ⟨5833896078599720517082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778528104799627356110553 5833896078599720517082915)
                  ·
                    refine ⟨8750844117899580775624373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5833896078599720517082915 8750844117899580775624373)
                    ·
                      refine ⟨820391636053085697714785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8750844117899580775624373 820391636053085697714785)
                      ·
                        rfl

theorem cell23_1597707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_1597707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597707 prefixEnd_1597707 := by exact prefixLift 1597707
  have htrace : WordTrace (prefixWord ++ tailWord_1597707) baseStart_1597707 baseEnd_1597707 := by
    simpa [prefixWord, tailWord_1597707, baseEnd_1597707] using wordTrace_append hprefix tailTrace_1597707
  have hstable : (prefixWord ++ tailWord_1597707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597707).length < 2 ^ (prefixWord ++ tailWord_1597707).sum := by decide
  have hdescent : baseEnd_1597707 < baseStart_1597707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597717 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_1597717 : Nat := 118140960795 + 1597717 * 2 ^ 59
def prefixEnd_1597717 : Nat := 4983230072969 + 3 ^ 40 * 1597717 * 2
def baseEnd_1597717 : Nat := 820396770859630658589739

theorem tailTrace_1597717 : CollatzResearch.WordTrace tailWord_1597717 prefixEnd_1597717 820396770859630658589739 := by
  unfold tailWord_1597717
  simp only [CollatzResearch.WordTrace]
  refine ⟨58273526352751652184551405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38849017568501101456367603 58273526352751652184551405)
  ·
    refine ⟨21852572382281869569206777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58273526352751652184551405 21852572382281869569206777)
    ·
      refine ⟨16389429286711402176905083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21852572382281869569206777 16389429286711402176905083)
      ·
        refine ⟨24584143930067103265357625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389429286711402176905083 24584143930067103265357625)
        ·
          refine ⟨18438107947550327449018219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24584143930067103265357625 18438107947550327449018219)
          ·
            refine ⟨27657161921325491173527329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18438107947550327449018219 27657161921325491173527329)
            ·
              refine ⟨20742871440994118380145497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27657161921325491173527329 20742871440994118380145497)
              ·
                refine ⟨15557153580745588785109123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20742871440994118380145497 15557153580745588785109123)
                ·
                  refine ⟨23335730371118383177663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15557153580745588785109123 23335730371118383177663685)
                  ·
                    refine ⟨4375449444584696845811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23335730371118383177663685 4375449444584696845811941)
                    ·
                      refine ⟨820396770859630658589739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4375449444584696845811941 820396770859630658589739)
                      ·
                        rfl

theorem cell23_1597717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_1597717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597717 prefixEnd_1597717 := by exact prefixLift 1597717
  have htrace : WordTrace (prefixWord ++ tailWord_1597717) baseStart_1597717 baseEnd_1597717 := by
    simpa [prefixWord, tailWord_1597717, baseEnd_1597717] using wordTrace_append hprefix tailTrace_1597717
  have hstable : (prefixWord ++ tailWord_1597717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597717).length < 2 ^ (prefixWord ++ tailWord_1597717).sum := by decide
  have hdescent : baseEnd_1597717 < baseStart_1597717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597767 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1597767 : Nat := 118140960795 + 1597767 * 2 ^ 59
def prefixEnd_1597767 : Nat := 4983230072969 + 3 ^ 40 * 1597767 * 2
def baseEnd_1597767 : Nat := 820422444892355462964509

theorem tailTrace_1597767 : CollatzResearch.WordTrace tailWord_1597767 prefixEnd_1597767 820422444892355462964509 := by
  unfold tailWord_1597767
  simp only [CollatzResearch.WordTrace]
  refine ⟨58275350002570510723871555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38850233335047007149247703 58275350002570510723871555)
  ·
    refine ⟨87413025003855766085807333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58275350002570510723871555 87413025003855766085807333)
    ·
      refine ⟨16389942188222956141088875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87413025003855766085807333 16389942188222956141088875)
      ·
        refine ⟨24584913282334434211633313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389942188222956141088875 24584913282334434211633313)
        ·
          refine ⟨18438684961750825658724985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24584913282334434211633313 18438684961750825658724985)
          ·
            refine ⟨13829013721313119244043739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18438684961750825658724985 13829013721313119244043739)
            ·
              refine ⟨20743520581969678866065609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829013721313119244043739 20743520581969678866065609)
              ·
                refine ⟨15557640436477259149549207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20743520581969678866065609 15557640436477259149549207)
                ·
                  refine ⟨23336460654715888724323811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15557640436477259149549207 23336460654715888724323811)
                  ·
                    refine ⟨35004690982073833086485717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23336460654715888724323811 35004690982073833086485717)
                    ·
                      refine ⟨820422444892355462964509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35004690982073833086485717 820422444892355462964509)
                      ·
                        rfl

theorem cell23_1597767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1597767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597767 prefixEnd_1597767 := by exact prefixLift 1597767
  have htrace : WordTrace (prefixWord ++ tailWord_1597767) baseStart_1597767 baseEnd_1597767 := by
    simpa [prefixWord, tailWord_1597767, baseEnd_1597767] using wordTrace_append hprefix tailTrace_1597767
  have hstable : (prefixWord ++ tailWord_1597767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597767).length < 2 ^ (prefixWord ++ tailWord_1597767).sum := by decide
  have hdescent : baseEnd_1597767 < baseStart_1597767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597807 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1597807 : Nat := 118140960795 + 1597807 * 2 ^ 59
def prefixEnd_1597807 : Nat := 4983230072969 + 3 ^ 40 * 1597807 * 2
def baseEnd_1597807 : Nat := 820442984118535306464325

theorem tailTrace_1597807 : CollatzResearch.WordTrace tailWord_1597807 prefixEnd_1597807 820442984118535306464325 := by
  unfold tailWord_1597807
  simp only [CollatzResearch.WordTrace]
  refine ⟨58276808922425597555327675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38851205948283731703551783 58276808922425597555327675)
  ·
    refine ⟨87415213383638396332991513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58276808922425597555327675 87415213383638396332991513)
    ·
      refine ⟨65561410037728797249743635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87415213383638396332991513 65561410037728797249743635)
      ·
        refine ⟨98342115056593195874615453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65561410037728797249743635 98342115056593195874615453)
        ·
          refine ⟨36878293146222448452980795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98342115056593195874615453 36878293146222448452980795)
          ·
            refine ⟨55317439719333672679471193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36878293146222448452980795 55317439719333672679471193)
            ·
              refine ⟨41488079789500254509603395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55317439719333672679471193 41488079789500254509603395)
              ·
                refine ⟨62232119684250381764405093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41488079789500254509603395 62232119684250381764405093)
                ·
                  refine ⟨11668522440796946580825955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62232119684250381764405093 11668522440796946580825955)
                  ·
                    refine ⟨17502783661195419871238933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11668522440796946580825955 17502783661195419871238933)
                    ·
                      refine ⟨820442984118535306464325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17502783661195419871238933 820442984118535306464325)
                      ·
                        rfl

theorem cell23_1597807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1597807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597807 prefixEnd_1597807 := by exact prefixLift 1597807
  have htrace : WordTrace (prefixWord ++ tailWord_1597807) baseStart_1597807 baseEnd_1597807 := by
    simpa [prefixWord, tailWord_1597807, baseEnd_1597807] using wordTrace_append hprefix tailTrace_1597807
  have hstable : (prefixWord ++ tailWord_1597807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597807).length < 2 ^ (prefixWord ++ tailWord_1597807).sum := by decide
  have hdescent : baseEnd_1597807 < baseStart_1597807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597817 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 10]
def baseStart_1597817 : Nat := 118140960795 + 1597817 * 2 ^ 59
def prefixEnd_1597817 : Nat := 4983230072969 + 3 ^ 40 * 1597817 * 2
def baseEnd_1597817 : Nat := 91160902102786696371031

theorem tailTrace_1597817 : CollatzResearch.WordTrace tailWord_1597817 prefixEnd_1597817 91160902102786696371031 := by
  unfold tailWord_1597817
  simp only [CollatzResearch.WordTrace]
  refine ⟨58277173652389369263191705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38851449101592912842127803 58277173652389369263191705)
  ·
    refine ⟨43707880239292026947393779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58277173652389369263191705 43707880239292026947393779)
    ·
      refine ⟨65561820358938040421090669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43707880239292026947393779 65561820358938040421090669)
      ·
        refine ⟨24585682634601765157909001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65561820358938040421090669 24585682634601765157909001)
        ·
          refine ⟨18439261975951323868431751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24585682634601765157909001 18439261975951323868431751)
          ·
            refine ⟨27658892963926985802647627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439261975951323868431751 27658892963926985802647627)
            ·
              refine ⟨41488339445890478703971441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27658892963926985802647627 41488339445890478703971441)
              ·
                refine ⟨31116254584417859027978581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41488339445890478703971441 31116254584417859027978581)
                ·
                  refine ⟨91160902102786696371031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31116254584417859027978581 91160902102786696371031)
                  ·
                    rfl

theorem cell23_1597817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_1597817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597817 prefixEnd_1597817 := by exact prefixLift 1597817
  have htrace : WordTrace (prefixWord ++ tailWord_1597817) baseStart_1597817 baseEnd_1597817 := by
    simpa [prefixWord, tailWord_1597817, baseEnd_1597817] using wordTrace_append hprefix tailTrace_1597817
  have hstable : (prefixWord ++ tailWord_1597817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597817).length < 2 ^ (prefixWord ++ tailWord_1597817).sum := by decide
  have hdescent : baseEnd_1597817 < baseStart_1597817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597821 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1597821 : Nat := 118140960795 + 1597821 * 2 ^ 59
def prefixEnd_1597821 : Nat := 4983230072969 + 3 ^ 40 * 1597821 * 2
def baseEnd_1597821 : Nat := 273483390949232750563087

theorem tailTrace_1597821 : CollatzResearch.WordTrace tailWord_1597821 prefixEnd_1597821 273483390949232750563087 := by
  unfold tailWord_1597821
  simp only [CollatzResearch.WordTrace]
  refine ⟨58277319544374877946337317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38851546362916585297558211 58277319544374877946337317)
  ·
    refine ⟨10926997414570289614938247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58277319544374877946337317 10926997414570289614938247)
    ·
      refine ⟨16390496121855434422407371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10926997414570289614938247 16390496121855434422407371)
      ·
        refine ⟨24585744182783151633611057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390496121855434422407371 24585744182783151633611057)
        ·
          refine ⟨18439308137087363725208293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24585744182783151633611057 18439308137087363725208293)
          ·
            refine ⟨3457370275703880698476555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18439308137087363725208293 3457370275703880698476555)
            ·
              refine ⟨5186055413555821047714833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457370275703880698476555 5186055413555821047714833)
              ·
                refine ⟨3889541560166865785786125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186055413555821047714833 3889541560166865785786125)
                ·
                  refine ⟨1458578085062574669669797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3889541560166865785786125 1458578085062574669669797)
                  ·
                    refine ⟨273483390949232750563087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458578085062574669669797 273483390949232750563087)
                    ·
                      rfl

theorem cell23_1597821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1597821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597821 prefixEnd_1597821 := by exact prefixLift 1597821
  have htrace : WordTrace (prefixWord ++ tailWord_1597821) baseStart_1597821 baseEnd_1597821 := by
    simpa [prefixWord, tailWord_1597821, baseEnd_1597821] using wordTrace_append hprefix tailTrace_1597821
  have hstable : (prefixWord ++ tailWord_1597821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597821).length < 2 ^ (prefixWord ++ tailWord_1597821).sum := by decide
  have hdescent : baseEnd_1597821 < baseStart_1597821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597881 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_1597881 : Nat := 118140960795 + 1597881 * 2 ^ 59
def prefixEnd_1597881 : Nat := 4983230072969 + 3 ^ 40 * 1597881 * 2
def baseEnd_1597881 : Nat := 273493660562322672312995

theorem tailTrace_1597881 : CollatzResearch.WordTrace tailWord_1597881 prefixEnd_1597881 273493660562322672312995 := by
  unfold tailWord_1597881
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279507924157508193521497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38853005282771672129014331 58279507924157508193521497)
  ·
    refine ⟨43709630943118131145141123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58279507924157508193521497 43709630943118131145141123)
    ·
      refine ⟨65564446414677196717711685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43709630943118131145141123 65564446414677196717711685)
      ·
        refine ⟨12293333702751974384570941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65564446414677196717711685 12293333702751974384570941)
        ·
          refine ⟨4610000138531990394214103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12293333702751974384570941 4610000138531990394214103)
          ·
            refine ⟨6915000207797985591321155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610000138531990394214103 6915000207797985591321155)
            ·
              refine ⟨10372500311696978386981733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915000207797985591321155 10372500311696978386981733)
              ·
                refine ⟨1944843808443183447559075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10372500311696978386981733 1944843808443183447559075)
                ·
                  refine ⟨2917265712664775171338613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944843808443183447559075 2917265712664775171338613)
                  ·
                    refine ⟨273493660562322672312995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2917265712664775171338613 273493660562322672312995)
                    ·
                      rfl

theorem cell23_1597881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_1597881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597881 prefixEnd_1597881 := by exact prefixLift 1597881
  have htrace : WordTrace (prefixWord ++ tailWord_1597881) baseStart_1597881 baseEnd_1597881 := by
    simpa [prefixWord, tailWord_1597881, baseEnd_1597881] using wordTrace_append hprefix tailTrace_1597881
  have hstable : (prefixWord ++ tailWord_1597881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597881).length < 2 ^ (prefixWord ++ tailWord_1597881).sum := by decide
  have hdescent : baseEnd_1597881 < baseStart_1597881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597895 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_1597895 : Nat := 118140960795 + 1597895 * 2 ^ 59
def prefixEnd_1597895 : Nat := 4983230072969 + 3 ^ 40 * 1597895 * 2
def baseEnd_1597895 : Nat := 820488170416130962163921

theorem tailTrace_1597895 : CollatzResearch.WordTrace tailWord_1597895 prefixEnd_1597895 820488170416130962163921 := by
  unfold tailWord_1597895
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280018546106788584531139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38853345697404525723020759 58280018546106788584531139)
  ·
    refine ⟨87420027819160182876796709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58280018546106788584531139 87420027819160182876796709)
    ·
      refine ⟨16391255216092534289399383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87420027819160182876796709 16391255216092534289399383)
      ·
        refine ⟨24586882824138801434099075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16391255216092534289399383 24586882824138801434099075)
        ·
          refine ⟨36880324236208202151148613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24586882824138801434099075 36880324236208202151148613)
          ·
            refine ⟨6915060794289037903340365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36880324236208202151148613 6915060794289037903340365)
            ·
              refine ⟨2593147797858389213752637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6915060794289037903340365 2593147797858389213752637)
              ·
                refine ⟨972430424196895955157239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593147797858389213752637 972430424196895955157239)
                ·
                  refine ⟨1458645636295343932735859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972430424196895955157239 1458645636295343932735859)
                  ·
                    refine ⟨2187968454443015899103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1458645636295343932735859 2187968454443015899103789)
                    ·
                      refine ⟨820488170416130962163921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2187968454443015899103789 820488170416130962163921)
                      ·
                        rfl

theorem cell23_1597895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_1597895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597895 prefixEnd_1597895 := by exact prefixLift 1597895
  have htrace : WordTrace (prefixWord ++ tailWord_1597895) baseStart_1597895 baseEnd_1597895 := by
    simpa [prefixWord, tailWord_1597895, baseEnd_1597895] using wordTrace_append hprefix tailTrace_1597895
  have hstable : (prefixWord ++ tailWord_1597895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597895).length < 2 ^ (prefixWord ++ tailWord_1597895).sum := by decide
  have hdescent : baseEnd_1597895 < baseStart_1597895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597914 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1597914 : Nat := 118140960795 + 1597914 * 2 ^ 59
def prefixEnd_1597914 : Nat := 4983230072969 + 3 ^ 40 * 1597914 * 2
def baseEnd_1597914 : Nat := 820497926548566387826333

theorem tailTrace_1597914 : CollatzResearch.WordTrace tailWord_1597914 prefixEnd_1597914 820497926548566387826333 := by
  unfold tailWord_1597914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570177883259488707368199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38853807688691969886315197 14570177883259488707368199)
  ·
    refine ⟨21855266824889233061052299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570177883259488707368199 21855266824889233061052299)
    ·
      refine ⟨32782900237333849591578449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855266824889233061052299 32782900237333849591578449)
      ·
        refine ⟨24587175178000387193683837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32782900237333849591578449 24587175178000387193683837)
        ·
          refine ⟨9220190691750145197631439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24587175178000387193683837 9220190691750145197631439)
          ·
            refine ⟨13830286037625217796447159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220190691750145197631439 13830286037625217796447159)
            ·
              refine ⟨20745429056437826694670739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13830286037625217796447159 20745429056437826694670739)
              ·
                refine ⟨31118143584656740042006109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745429056437826694670739 31118143584656740042006109)
                ·
                  refine ⟨11669303844246277515752291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31118143584656740042006109 11669303844246277515752291)
                  ·
                    refine ⟨17503955766369416273628437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11669303844246277515752291 17503955766369416273628437)
                    ·
                      refine ⟨820497926548566387826333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17503955766369416273628437 820497926548566387826333)
                      ·
                        rfl

theorem cell23_1597914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1597914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597914 prefixEnd_1597914 := by exact prefixLift 1597914
  have htrace : WordTrace (prefixWord ++ tailWord_1597914) baseStart_1597914 baseEnd_1597914 := by
    simpa [prefixWord, tailWord_1597914, baseEnd_1597914] using wordTrace_append hprefix tailTrace_1597914
  have hstable : (prefixWord ++ tailWord_1597914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597914).length < 2 ^ (prefixWord ++ tailWord_1597914).sum := by decide
  have hdescent : baseEnd_1597914 < baseStart_1597914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597921 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1597921 : Nat := 118140960795 + 1597921 * 2 ^ 59
def prefixEnd_1597921 : Nat := 4983230072969 + 3 ^ 40 * 1597921 * 2
def baseEnd_1597921 : Nat := 820501520913147860438801

theorem tailTrace_1597921 : CollatzResearch.WordTrace tailWord_1597921 prefixEnd_1597921 820501520913147860438801 := by
  unfold tailWord_1597921
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280966844012595024977617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38853977896008396683318411 58280966844012595024977617)
  ·
    refine ⟨43710725133009446268733213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58280966844012595024977617 43710725133009446268733213)
    ·
      refine ⟨16391521924878542350774955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43710725133009446268733213 16391521924878542350774955)
      ·
        refine ⟨24587282887317813526162433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16391521924878542350774955 24587282887317813526162433)
        ·
          refine ⟨18440462165488360144621825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24587282887317813526162433 18440462165488360144621825)
          ·
            refine ⟨13830346624116270108466369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18440462165488360144621825 13830346624116270108466369)
            ·
              refine ⟨10372759968087202581349777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830346624116270108466369 10372759968087202581349777)
              ·
                refine ⟨7779569976065401936012333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10372759968087202581349777 7779569976065401936012333)
                ·
                  refine ⟨2917338741024525726004625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7779569976065401936012333 2917338741024525726004625)
                  ·
                    refine ⟨2188004055768394294503469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917338741024525726004625 2188004055768394294503469)
                    ·
                      refine ⟨820501520913147860438801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188004055768394294503469 820501520913147860438801)
                      ·
                        rfl

theorem cell23_1597921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1597921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597921 prefixEnd_1597921 := by exact prefixLift 1597921
  have htrace : WordTrace (prefixWord ++ tailWord_1597921) baseStart_1597921 baseEnd_1597921 := by
    simpa [prefixWord, tailWord_1597921, baseEnd_1597921] using wordTrace_append hprefix tailTrace_1597921
  have hstable : (prefixWord ++ tailWord_1597921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597921).length < 2 ^ (prefixWord ++ tailWord_1597921).sum := by decide
  have hdescent : baseEnd_1597921 < baseStart_1597921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597928 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1597928 : Nat := 118140960795 + 1597928 * 2 ^ 59
def prefixEnd_1597928 : Nat := 4983230072969 + 3 ^ 40 * 1597928 * 2
def baseEnd_1597928 : Nat := 273501705092576444350423

theorem tailTrace_1597928 : CollatzResearch.WordTrace tailWord_1597928 prefixEnd_1597928 273501705092576444350423 := by
  unfold tailWord_1597928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29140611077493617610241219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38854148103324823480321625 29140611077493617610241219)
  ·
    refine ⟨43710916616240426415361829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29140611077493617610241219 43710916616240426415361829)
    ·
      refine ⟨8195796865545079952880343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43710916616240426415361829 8195796865545079952880343)
      ·
        refine ⟨12293695298317619929320515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195796865545079952880343 12293695298317619929320515)
        ·
          refine ⟨18440542947476429893980773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12293695298317619929320515 18440542947476429893980773)
          ·
            refine ⟨3457601802651830605121395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18440542947476429893980773 3457601802651830605121395)
            ·
              refine ⟨5186402703977745907682093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457601802651830605121395 5186402703977745907682093)
              ·
                refine ⟨1944901013991654715380785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186402703977745907682093 1944901013991654715380785)
                ·
                  refine ⟨1458675760493741036535589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1944901013991654715380785 1458675760493741036535589)
                  ·
                    refine ⟨273501705092576444350423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458675760493741036535589 273501705092576444350423)
                    ·
                      rfl

theorem cell23_1597928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1597928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597928 prefixEnd_1597928 := by exact prefixLift 1597928
  have htrace : WordTrace (prefixWord ++ tailWord_1597928) baseStart_1597928 baseEnd_1597928 := by
    simpa [prefixWord, tailWord_1597928, baseEnd_1597928] using wordTrace_append hprefix tailTrace_1597928
  have hstable : (prefixWord ++ tailWord_1597928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597928).length < 2 ^ (prefixWord ++ tailWord_1597928).sum := by decide
  have hdescent : baseEnd_1597928 < baseStart_1597928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597951 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1597951 : Nat := 118140960795 + 1597951 * 2 ^ 59
def prefixEnd_1597951 : Nat := 4983230072969 + 3 ^ 40 * 1597951 * 2
def baseEnd_1597951 : Nat := 820516925332782743063663

theorem tailTrace_1597951 : CollatzResearch.WordTrace tailWord_1597951 prefixEnd_1597951 820516925332782743063663 := by
  unfold tailWord_1597951
  simp only [CollatzResearch.WordTrace]
  refine ⟨58282061033903910148569707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38854707355935940099046471 58282061033903910148569707)
  ·
    refine ⟨87423091550855865222854561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58282061033903910148569707 87423091550855865222854561)
    ·
      refine ⟨65567318663141898917140921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87423091550855865222854561 65567318663141898917140921)
      ·
        refine ⟨49175488997356424187855691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65567318663141898917140921 49175488997356424187855691)
        ·
          refine ⟨73763233496034636281783537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49175488997356424187855691 73763233496034636281783537)
          ·
            refine ⟨55322425122025977211337653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73763233496034636281783537 55322425122025977211337653)
            ·
              refine ⟨5186477355189935363562905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55322425122025977211337653 5186477355189935363562905)
              ·
                refine ⟨3889858016392451522672179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186477355189935363562905 3889858016392451522672179)
                ·
                  refine ⟨5834787024588677284008269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889858016392451522672179 5834787024588677284008269)
                  ·
                    refine ⟨2188045134220753981503101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5834787024588677284008269 2188045134220753981503101)
                    ·
                      refine ⟨820516925332782743063663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188045134220753981503101 820516925332782743063663)
                      ·
                        rfl

theorem cell23_1597951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1597951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597951 prefixEnd_1597951 := by exact prefixLift 1597951
  have htrace : WordTrace (prefixWord ++ tailWord_1597951) baseStart_1597951 baseEnd_1597951 := by
    simpa [prefixWord, tailWord_1597951, baseEnd_1597951] using wordTrace_append hprefix tailTrace_1597951
  have hstable : (prefixWord ++ tailWord_1597951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597951).length < 2 ^ (prefixWord ++ tailWord_1597951).sum := by decide
  have hdescent : baseEnd_1597951 < baseStart_1597951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597975 : List Nat := [1, 1, 3, 6, 2, 1, 1, 8]
def baseStart_1597975 : Nat := 118140960795 + 1597975 * 2 ^ 59
def prefixEnd_1597975 : Nat := 4983230072969 + 3 ^ 40 * 1597975 * 2
def baseEnd_1597975 : Nat := 30389972180314468487539

theorem tailTrace_1597975 : CollatzResearch.WordTrace tailWord_1597975 prefixEnd_1597975 30389972180314468487539 := by
  unfold tailWord_1597975
  simp only [CollatzResearch.WordTrace]
  refine ⟨58282936385816962247443379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38855290923877974831628919 58282936385816962247443379)
  ·
    refine ⟨87424404578725443371165069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58282936385816962247443379 87424404578725443371165069)
    ·
      refine ⟨32784151717022041264186901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87424404578725443371165069 32784151717022041264186901)
      ·
        refine ⟨1536757111735408184258761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32784151717022041264186901 1536757111735408184258761)
        ·
          refine ⟨1152567833801556138194071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536757111735408184258761 1152567833801556138194071)
          ·
            refine ⟨1728851750702334207291107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152567833801556138194071 1728851750702334207291107)
            ·
              refine ⟨2593277626053501310936661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728851750702334207291107 2593277626053501310936661)
              ·
                refine ⟨30389972180314468487539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2593277626053501310936661 30389972180314468487539)
                ·
                  rfl

theorem cell23_1597975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 8].length) (baseStart_1597975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597975 prefixEnd_1597975 := by exact prefixLift 1597975
  have htrace : WordTrace (prefixWord ++ tailWord_1597975) baseStart_1597975 baseEnd_1597975 := by
    simpa [prefixWord, tailWord_1597975, baseEnd_1597975] using wordTrace_append hprefix tailTrace_1597975
  have hstable : (prefixWord ++ tailWord_1597975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597975).length < 2 ^ (prefixWord ++ tailWord_1597975).sum := by decide
  have hdescent : baseEnd_1597975 < baseStart_1597975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597978 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_1597978 : Nat := 118140960795 + 1597978 * 2 ^ 59
def prefixEnd_1597978 : Nat := 4983230072969 + 3 ^ 40 * 1597978 * 2
def baseEnd_1597978 : Nat := 820530789310454137426039

theorem tailTrace_1597978 : CollatzResearch.WordTrace tailWord_1597978 prefixEnd_1597978 820530789310454137426039 := by
  unfold tailWord_1597978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570761451201523439950647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38855363869870729173201725 14570761451201523439950647)
  ·
    refine ⟨21856142176802285159925971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570761451201523439950647 21856142176802285159925971)
    ·
      refine ⟨32784213265203427739888957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21856142176802285159925971 32784213265203427739888957)
      ·
        refine ⟨12294079974451285402458359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32784213265203427739888957 12294079974451285402458359)
        ·
          refine ⟨18441119961676928103687539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12294079974451285402458359 18441119961676928103687539)
          ·
            refine ⟨27661679942515392155531309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18441119961676928103687539 27661679942515392155531309)
            ·
              refine ⟨10373129978443272058324241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27661679942515392155531309 10373129978443272058324241)
              ·
                refine ⟨7779847483832454043743181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373129978443272058324241 7779847483832454043743181)
                ·
                  refine ⟨2917442806437170266403693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7779847483832454043743181 2917442806437170266403693)
                  ·
                    refine ⟨1094041052413938849901385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917442806437170266403693 1094041052413938849901385)
                    ·
                      refine ⟨820530789310454137426039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094041052413938849901385 820530789310454137426039)
                      ·
                        rfl

theorem cell23_1597978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_1597978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597978 prefixEnd_1597978 := by exact prefixLift 1597978
  have htrace : WordTrace (prefixWord ++ tailWord_1597978) baseStart_1597978 baseEnd_1597978 := by
    simpa [prefixWord, tailWord_1597978, baseEnd_1597978] using wordTrace_append hprefix tailTrace_1597978
  have hstable : (prefixWord ++ tailWord_1597978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597978).length < 2 ^ (prefixWord ++ tailWord_1597978).sum := by decide
  have hdescent : baseEnd_1597978 < baseStart_1597978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598008 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_1598008 : Nat := 118140960795 + 1598008 * 2 ^ 59
def prefixEnd_1598008 : Nat := 4983230072969 + 3 ^ 40 * 1598008 * 2
def baseEnd_1598008 : Nat := 820546193730089020050901

theorem tailTrace_1598008 : CollatzResearch.WordTrace tailWord_1598008 prefixEnd_1598008 820546193730089020050901 := by
  unfold tailWord_1598008
  simp only [CollatzResearch.WordTrace]
  refine ⟨29142069997348704441697339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38856093329798272588929785 29142069997348704441697339)
  ·
    refine ⟨43713104996023056662546009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29142069997348704441697339 43713104996023056662546009)
    ·
      refine ⟨32784828747017292496909507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43713104996023056662546009 32784828747017292496909507)
      ·
        refine ⟨49177243120525938745364261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32784828747017292496909507 49177243120525938745364261)
        ·
          refine ⟨9220733085098613514755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49177243120525938745364261 9220733085098613514755799)
          ·
            refine ⟨13831099627647920272133699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220733085098613514755799 13831099627647920272133699)
            ·
              refine ⟨20746649441471880408200549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13831099627647920272133699 20746649441471880408200549)
              ·
                refine ⟨3889996770275977576537603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20746649441471880408200549 3889996770275977576537603)
                ·
                  refine ⟨5834995155413966364806405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889996770275977576537603 5834995155413966364806405)
                  ·
                    refine ⟨1094061591640118693401201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834995155413966364806405 1094061591640118693401201)
                    ·
                      refine ⟨820546193730089020050901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094061591640118693401201 820546193730089020050901)
                      ·
                        rfl

theorem cell23_1598008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_1598008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598008 prefixEnd_1598008 := by exact prefixLift 1598008
  have htrace : WordTrace (prefixWord ++ tailWord_1598008) baseStart_1598008 baseEnd_1598008 := by
    simpa [prefixWord, tailWord_1598008, baseEnd_1598008] using wordTrace_append hprefix tailTrace_1598008
  have hstable : (prefixWord ++ tailWord_1598008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598008).length < 2 ^ (prefixWord ++ tailWord_1598008).sum := by decide
  have hdescent : baseEnd_1598008 < baseStart_1598008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598012 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_1598012 : Nat := 118140960795 + 1598012 * 2 ^ 59
def prefixEnd_1598012 : Nat := 4983230072969 + 3 ^ 40 * 1598012 * 2
def baseEnd_1598012 : Nat := 820548247652707004400883

theorem tailTrace_1598012 : CollatzResearch.WordTrace tailWord_1598012 prefixEnd_1598012 820548247652707004400883 := by
  unfold tailWord_1598012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29142142943341458783270145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38856190591121945044360193 29142142943341458783270145)
  ·
    refine ⟨21856607207506094087452609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29142142943341458783270145 21856607207506094087452609)
    ·
      refine ⟨16392455405629570565589457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21856607207506094087452609 16392455405629570565589457)
      ·
        refine ⟨12294341554222177924192093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16392455405629570565589457 12294341554222177924192093)
        ·
          refine ⟨4610378082833316721572035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12294341554222177924192093 4610378082833316721572035)
          ·
            refine ⟨6915567124249975082358053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610378082833316721572035 6915567124249975082358053)
            ·
              refine ⟨1296668835796870327942135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6915567124249975082358053 1296668835796870327942135)
              ·
                refine ⟨1945003253695305491913203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296668835796870327942135 1945003253695305491913203)
                ·
                  refine ⟨2917504880542958237869805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945003253695305491913203 2917504880542958237869805)
                  ·
                    refine ⟨1094064330203609339201177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917504880542958237869805 1094064330203609339201177)
                    ·
                      refine ⟨820548247652707004400883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094064330203609339201177 820548247652707004400883)
                      ·
                        rfl

theorem cell23_1598012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_1598012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598012 prefixEnd_1598012 := by exact prefixLift 1598012
  have htrace : WordTrace (prefixWord ++ tailWord_1598012) baseStart_1598012 baseEnd_1598012 := by
    simpa [prefixWord, tailWord_1598012, baseEnd_1598012] using wordTrace_append hprefix tailTrace_1598012
  have hstable : (prefixWord ++ tailWord_1598012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598012).length < 2 ^ (prefixWord ++ tailWord_1598012).sum := by decide
  have hdescent : baseEnd_1598012 < baseStart_1598012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598021 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1598021 : Nat := 118140960795 + 1598021 * 2 ^ 59
def prefixEnd_1598021 : Nat := 4983230072969 + 3 ^ 40 * 1598021 * 2
def baseEnd_1598021 : Nat := 820552868978597469188341

theorem tailTrace_1598021 : CollatzResearch.WordTrace tailWord_1598021 prefixEnd_1598021 820552868978597469188341 := by
  unfold tailWord_1598021
  simp only [CollatzResearch.WordTrace]
  refine ⟨58284614143650312103617917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38856409429100208069078611 58284614143650312103617917)
  ·
    refine ⟨21856730303868867038856719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58284614143650312103617917 21856730303868867038856719)
    ·
      refine ⟨32785095455803300558285079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21856730303868867038856719 32785095455803300558285079)
      ·
        refine ⟨49177643183704950837427619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32785095455803300558285079 49177643183704950837427619)
        ·
          refine ⟨73766464775557426256141429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49177643183704950837427619 73766464775557426256141429)
          ·
            refine ⟨6915606072708508711513259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73766464775557426256141429 6915606072708508711513259)
            ·
              refine ⟨10373409109062763067269889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915606072708508711513259 10373409109062763067269889)
              ·
                refine ⟨7780056831797072300452417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373409109062763067269889 7780056831797072300452417)
                ·
                  refine ⟨5835042623847804225339313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780056831797072300452417 5835042623847804225339313)
                  ·
                    refine ⟨4376281967885853169004485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835042623847804225339313 4376281967885853169004485)
                    ·
                      refine ⟨820552868978597469188341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4376281967885853169004485 820552868978597469188341)
                      ·
                        rfl

theorem cell23_1598021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1598021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598021 prefixEnd_1598021 := by exact prefixLift 1598021
  have htrace : WordTrace (prefixWord ++ tailWord_1598021) baseStart_1598021 baseEnd_1598021 := by
    simpa [prefixWord, tailWord_1598021, baseEnd_1598021] using wordTrace_append hprefix tailTrace_1598021
  have hstable : (prefixWord ++ tailWord_1598021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598021).length < 2 ^ (prefixWord ++ tailWord_1598021).sum := by decide
  have hdescent : baseEnd_1598021 < baseStart_1598021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598138 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_1598138 : Nat := 118140960795 + 1598138 * 2 ^ 59
def prefixEnd_1598138 : Nat := 4983230072969 + 3 ^ 40 * 1598138 * 2
def baseEnd_1598138 : Nat := 91179216246130390158367

theorem tailTrace_1598138 : CollatzResearch.WordTrace tailWord_1598138 prefixEnd_1598138 91179216246130390158367 := by
  unfold tailWord_1598138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572220371056610271406767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38859254322817627390418045 14572220371056610271406767)
  ·
    refine ⟨21858330556584915407110151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14572220371056610271406767 21858330556584915407110151)
    ·
      refine ⟨32787495834877373110665227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21858330556584915407110151 32787495834877373110665227)
      ·
        refine ⟨49181243752316059665997841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787495834877373110665227 49181243752316059665997841)
        ·
          refine ⟨36885932814237044749498381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49181243752316059665997841 36885932814237044749498381)
          ·
            refine ⟨13832224805338891781061893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36885932814237044749498381 13832224805338891781061893)
            ·
              refine ⟨2593542151001042208949105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13832224805338891781061893 2593542151001042208949105)
              ·
                refine ⟨1945156613250781656711829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593542151001042208949105 1945156613250781656711829)
                ·
                  refine ⟨91179216246130390158367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1945156613250781656711829 91179216246130390158367)
                  ·
                    rfl

theorem cell23_1598138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_1598138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598138 prefixEnd_1598138 := by exact prefixLift 1598138
  have htrace : WordTrace (prefixWord ++ tailWord_1598138) baseStart_1598138 baseEnd_1598138 := by
    simpa [prefixWord, tailWord_1598138, baseEnd_1598138] using wordTrace_append hprefix tailTrace_1598138
  have hstable : (prefixWord ++ tailWord_1598138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598138).length < 2 ^ (prefixWord ++ tailWord_1598138).sum := by decide
  have hdescent : baseEnd_1598138 < baseStart_1598138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598142 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1598142 : Nat := 118140960795 + 1598142 * 2 ^ 59
def prefixEnd_1598142 : Nat := 4983230072969 + 3 ^ 40 * 1598142 * 2
def baseEnd_1598142 : Nat := 273538333379263831925095

theorem tailTrace_1598142 : CollatzResearch.WordTrace tailWord_1598142 prefixEnd_1598142 273538333379263831925095 := by
  unfold tailWord_1598142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286128422026493721096585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38859351584141299845848453 7286128422026493721096585)
  ·
    refine ⟨5464596316519870290822439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7286128422026493721096585 5464596316519870290822439)
    ·
      refine ⟨8196894474779805436233659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5464596316519870290822439 8196894474779805436233659)
      ·
        refine ⟨12295341712169708154350489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196894474779805436233659 12295341712169708154350489)
        ·
          refine ⟨9221506284127281115762867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12295341712169708154350489 9221506284127281115762867)
          ·
            refine ⟨13832259426190921673644301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9221506284127281115762867 13832259426190921673644301)
            ·
              refine ⟨5187097284821595627616613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13832259426190921673644301 5187097284821595627616613)
              ·
                refine ⟨972580740904049180178115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5187097284821595627616613 972580740904049180178115)
                ·
                  refine ⟨1458871111356073770267173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972580740904049180178115 1458871111356073770267173)
                  ·
                    refine ⟨273538333379263831925095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458871111356073770267173 273538333379263831925095)
                    ·
                      rfl

theorem cell23_1598142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1598142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598142 prefixEnd_1598142 := by exact prefixLift 1598142
  have htrace : WordTrace (prefixWord ++ tailWord_1598142) baseStart_1598142 baseEnd_1598142 := by
    simpa [prefixWord, tailWord_1598142, baseEnd_1598142] using wordTrace_append hprefix tailTrace_1598142
  have hstable : (prefixWord ++ tailWord_1598142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598142).length < 2 ^ (prefixWord ++ tailWord_1598142).sum := by decide
  have hdescent : baseEnd_1598142 < baseStart_1598142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598161 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1598161 : Nat := 118140960795 + 1598161 * 2 ^ 59
def prefixEnd_1598161 : Nat := 4983230072969 + 3 ^ 40 * 1598161 * 2
def baseEnd_1598161 : Nat := 820624756270226921437697

theorem tailTrace_1598161 : CollatzResearch.WordTrace tailWord_1598161 prefixEnd_1598161 820624756270226921437697 := by
  unfold tailWord_1598161
  simp only [CollatzResearch.WordTrace]
  refine ⟨58289720363143116013714337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38859813575428744009142891 58289720363143116013714337)
  ·
    refine ⟨43717290272357337010285753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58289720363143116013714337 43717290272357337010285753)
    ·
      refine ⟨32787967704268002757714315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43717290272357337010285753 32787967704268002757714315)
      ·
        refine ⟨49181951556402004136571473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787967704268002757714315 49181951556402004136571473)
        ·
          refine ⟨36886463667301503102428605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49181951556402004136571473 36886463667301503102428605)
          ·
            refine ⟨13832423875238063663410727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36886463667301503102428605 13832423875238063663410727)
            ·
              refine ⟨20748635812857095495116091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13832423875238063663410727 20748635812857095495116091)
              ·
                refine ⟨31122953719285643242674137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20748635812857095495116091 31122953719285643242674137)
                ·
                  refine ⟨23342215289464232432005603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31122953719285643242674137 23342215289464232432005603)
                  ·
                    refine ⟨35013322934196348648008405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23342215289464232432005603 35013322934196348648008405)
                    ·
                      refine ⟨820624756270226921437697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35013322934196348648008405 820624756270226921437697)
                      ·
                        rfl

theorem cell23_1598161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1598161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598161 prefixEnd_1598161 := by exact prefixLift 1598161
  have htrace : WordTrace (prefixWord ++ tailWord_1598161) baseStart_1598161 baseEnd_1598161 := by
    simpa [prefixWord, tailWord_1598161, baseEnd_1598161] using wordTrace_append hprefix tailTrace_1598161
  have hstable : (prefixWord ++ tailWord_1598161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598161).length < 2 ^ (prefixWord ++ tailWord_1598161).sum := by decide
  have hdescent : baseEnd_1598161 < baseStart_1598161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598168 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_1598168 : Nat := 118140960795 + 1598168 * 2 ^ 59
def prefixEnd_1598168 : Nat := 4983230072969 + 3 ^ 40 * 1598168 * 2
def baseEnd_1598168 : Nat := 273542783544936131350055

theorem tailTrace_1598168 : CollatzResearch.WordTrace tailWord_1598168 prefixEnd_1598168 273542783544936131350055 := by
  unfold tailWord_1598168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144987837058878104609579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38859983782745170806146105 29144987837058878104609579)
  ·
    refine ⟨43717481755588317156914369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29144987837058878104609579 43717481755588317156914369)
    ·
      refine ⟨32788111316691237867685777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43717481755588317156914369 32788111316691237867685777)
      ·
        refine ⟨24591083487518428400764333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32788111316691237867685777 24591083487518428400764333)
        ·
          refine ⟨9221656307819410650286625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24591083487518428400764333 9221656307819410650286625)
          ·
            refine ⟨6916242230864557987714969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9221656307819410650286625 6916242230864557987714969)
            ·
              refine ⟨5187181673148418490786227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916242230864557987714969 5187181673148418490786227)
              ·
                refine ⟨7780772509722627736179341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187181673148418490786227 7780772509722627736179341)
                ·
                  refine ⟨2917789691145985401067253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7780772509722627736179341 2917789691145985401067253)
                  ·
                    refine ⟨273542783544936131350055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2917789691145985401067253 273542783544936131350055)
                    ·
                      rfl

theorem cell23_1598168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_1598168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598168 prefixEnd_1598168 := by exact prefixLift 1598168
  have htrace : WordTrace (prefixWord ++ tailWord_1598168) baseStart_1598168 baseEnd_1598168 := by
    simpa [prefixWord, tailWord_1598168, baseEnd_1598168] using wordTrace_append hprefix tailTrace_1598168
  have hstable : (prefixWord ++ tailWord_1598168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598168).length < 2 ^ (prefixWord ++ tailWord_1598168).sum := by decide
  have hdescent : baseEnd_1598168 < baseStart_1598168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598171 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_1598171 : Nat := 118140960795 + 1598171 * 2 ^ 59
def prefixEnd_1598171 : Nat := 4983230072969 + 3 ^ 40 * 1598171 * 2
def baseEnd_1598171 : Nat := 820629891076771882312651

theorem tailTrace_1598171 : CollatzResearch.WordTrace tailWord_1598171 prefixEnd_1598171 820629891076771882312651 := by
  unfold tailWord_1598171
  simp only [CollatzResearch.WordTrace]
  refine ⟨58290085093106887721578367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38860056728737925147718911 58290085093106887721578367)
  ·
    refine ⟨87435127639660331582367551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58290085093106887721578367 87435127639660331582367551)
    ·
      refine ⟨131152691459490497373551327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87435127639660331582367551 131152691459490497373551327)
      ·
        refine ⟨196729037189235746060326991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131152691459490497373551327 196729037189235746060326991)
        ·
          refine ⟨295093555783853619090490487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196729037189235746060326991 295093555783853619090490487)
          ·
            refine ⟨442640333675780428635735731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295093555783853619090490487 442640333675780428635735731)
            ·
              refine ⟨663960500513670642953603597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442640333675780428635735731 663960500513670642953603597)
              ·
                refine ⟨248985187692626491107601349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663960500513670642953603597 248985187692626491107601349)
                ·
                  refine ⟨46684722692367467082675253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248985187692626491107601349 46684722692367467082675253)
                  ·
                    refine ⟨4376692752409450039000805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46684722692367467082675253 4376692752409450039000805)
                    ·
                      refine ⟨820629891076771882312651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4376692752409450039000805 820629891076771882312651)
                      ·
                        rfl

theorem cell23_1598171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_1598171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598171 prefixEnd_1598171 := by exact prefixLift 1598171
  have htrace : WordTrace (prefixWord ++ tailWord_1598171) baseStart_1598171 baseEnd_1598171 := by
    simpa [prefixWord, tailWord_1598171, baseEnd_1598171] using wordTrace_append hprefix tailTrace_1598171
  have hstable : (prefixWord ++ tailWord_1598171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598171).length < 2 ^ (prefixWord ++ tailWord_1598171).sum := by decide
  have hdescent : baseEnd_1598171 < baseStart_1598171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598175 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 5, 2]
def baseStart_1598175 : Nat := 118140960795 + 1598175 * 2 ^ 59
def prefixEnd_1598175 : Nat := 4983230072969 + 3 ^ 40 * 1598175 * 2
def baseEnd_1598175 : Nat := 820631944999389866662633

theorem tailTrace_1598175 : CollatzResearch.WordTrace tailWord_1598175 prefixEnd_1598175 820631944999389866662633 := by
  unfold tailWord_1598175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58290230985092396404723979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38860153990061597603149319 58290230985092396404723979)
  ·
    refine ⟨87435346477638594607085969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58290230985092396404723979 87435346477638594607085969)
    ·
      refine ⟨65576509858228945955314477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87435346477638594607085969 65576509858228945955314477)
      ·
        refine ⟨24591191196835854733242929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65576509858228945955314477 24591191196835854733242929)
        ·
          refine ⟨18443393397626891049932197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24591191196835854733242929 18443393397626891049932197)
          ·
            refine ⟨3458136262055042071862287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18443393397626891049932197 3458136262055042071862287)
            ·
              refine ⟨5187204393082563107793431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458136262055042071862287 5187204393082563107793431)
              ·
                refine ⟨7780806589623844661690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187204393082563107793431 7780806589623844661690147)
                ·
                  refine ⟨11671209884435766992535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780806589623844661690147 11671209884435766992535221)
                  ·
                    refine ⟨1094175926665853155550177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11671209884435766992535221 1094175926665853155550177)
                    ·
                      refine ⟨820631944999389866662633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094175926665853155550177 820631944999389866662633)
                      ·
                        rfl

theorem cell23_1598175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_1598175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598175 prefixEnd_1598175 := by exact prefixLift 1598175
  have htrace : WordTrace (prefixWord ++ tailWord_1598175) baseStart_1598175 baseEnd_1598175 := by
    simpa [prefixWord, tailWord_1598175, baseEnd_1598175] using wordTrace_append hprefix tailTrace_1598175
  have hstable : (prefixWord ++ tailWord_1598175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598175).length < 2 ^ (prefixWord ++ tailWord_1598175).sum := by decide
  have hdescent : baseEnd_1598175 < baseStart_1598175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598185 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_1598185 : Nat := 118140960795 + 1598185 * 2 ^ 59
def prefixEnd_1598185 : Nat := 4983230072969 + 3 ^ 40 * 1598185 * 2
def baseEnd_1598185 : Nat := 273545693268644942512529

theorem tailTrace_1598185 : CollatzResearch.WordTrace tailWord_1598185 prefixEnd_1598185 273545693268644942512529 := by
  unfold tailWord_1598185
  simp only [CollatzResearch.WordTrace]
  refine ⟨58290595715056168112588009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38860397143370778741725339 58290595715056168112588009)
  ·
    refine ⟨43717946786292126084441007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58290595715056168112588009 43717946786292126084441007)
    ·
      refine ⟨65576920179438189126661511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43717946786292126084441007 65576920179438189126661511)
      ·
        refine ⟨98365380269157283689992267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65576920179438189126661511 98365380269157283689992267)
        ·
          refine ⟨147548070403735925534988401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98365380269157283689992267 147548070403735925534988401)
          ·
            refine ⟨110661052802801944151241301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147548070403735925534988401 110661052802801944151241301)
            ·
              refine ⟨1296809212532835283022359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 110661052802801944151241301 1296809212532835283022359)
              ·
                refine ⟨1945213818799252924533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296809212532835283022359 1945213818799252924533539)
                ·
                  refine ⟨2917820728198879386800309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945213818799252924533539 2917820728198879386800309)
                  ·
                    refine ⟨273545693268644942512529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2917820728198879386800309 273545693268644942512529)
                    ·
                      rfl

theorem cell23_1598185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_1598185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598185 prefixEnd_1598185 := by exact prefixLift 1598185
  have htrace : WordTrace (prefixWord ++ tailWord_1598185) baseStart_1598185 baseEnd_1598185 := by
    simpa [prefixWord, tailWord_1598185, baseEnd_1598185] using wordTrace_append hprefix tailTrace_1598185
  have hstable : (prefixWord ++ tailWord_1598185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598185).length < 2 ^ (prefixWord ++ tailWord_1598185).sum := by decide
  have hdescent : baseEnd_1598185 < baseStart_1598185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598211 : List Nat := [1, 1, 1, 3, 2, 2, 1, 12]
def baseStart_1598211 : Nat := 118140960795 + 1598211 * 2 ^ 59
def prefixEnd_1598211 : Nat := 4983230072969 + 3 ^ 40 * 1598211 * 2
def baseEnd_1598211 : Nat := 30394460381590804659721

theorem tailTrace_1598211 : CollatzResearch.WordTrace tailWord_1598211 prefixEnd_1598211 30394460381590804659721 := by
  unfold tailWord_1598211
  simp only [CollatzResearch.WordTrace]
  refine ⟨58291544012961974553034487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38861029341974649702022991 58291544012961974553034487)
  ·
    refine ⟨87437316019442961829551731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58291544012961974553034487 87437316019442961829551731)
    ·
      refine ⟨131155974029164442744327597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87437316019442961829551731 131155974029164442744327597)
      ·
        refine ⟨49183490260936666029122849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131155974029164442744327597 49183490260936666029122849)
        ·
          refine ⟨36887617695702499521842137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49183490260936666029122849 36887617695702499521842137)
          ·
            refine ⟨27665713271776874641381603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36887617695702499521842137 27665713271776874641381603)
            ·
              refine ⟨41498569907665311962072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27665713271776874641381603 41498569907665311962072405)
              ·
                refine ⟨30394460381590804659721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 41498569907665311962072405 30394460381590804659721)
                ·
                  rfl

theorem cell23_1598211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 12].length) (baseStart_1598211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598211 prefixEnd_1598211 := by exact prefixLift 1598211
  have htrace : WordTrace (prefixWord ++ tailWord_1598211) baseStart_1598211 baseEnd_1598211 := by
    simpa [prefixWord, tailWord_1598211, baseEnd_1598211] using wordTrace_append hprefix tailTrace_1598211
  have hstable : (prefixWord ++ tailWord_1598211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598211).length < 2 ^ (prefixWord ++ tailWord_1598211).sum := by decide
  have hdescent : baseEnd_1598211 < baseStart_1598211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598215 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1598215 : Nat := 118140960795 + 1598215 * 2 ^ 59
def prefixEnd_1598215 : Nat := 4983230072969 + 3 ^ 40 * 1598215 * 2
def baseEnd_1598215 : Nat := 273550828075189903387483

theorem tailTrace_1598215 : CollatzResearch.WordTrace tailWord_1598215 prefixEnd_1598215 273550828075189903387483 := by
  unfold tailWord_1598215
  simp only [CollatzResearch.WordTrace]
  refine ⟨58291689904947483236180099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38861126603298322157453399 58291689904947483236180099)
  ·
    refine ⟨87437534857421224854270149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58291689904947483236180099 87437534857421224854270149)
    ·
      refine ⟨16394537785766479660175653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87437534857421224854270149 16394537785766479660175653)
      ·
        refine ⟨3073975834831214936282935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16394537785766479660175653 3073975834831214936282935)
        ·
          refine ⟨4610963752246822404424403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073975834831214936282935 4610963752246822404424403)
          ·
            refine ⟨6916445628370233606636605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610963752246822404424403 6916445628370233606636605)
            ·
              refine ⟨2593667110638837602488727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6916445628370233606636605 2593667110638837602488727)
              ·
                refine ⟨3890500665958256403733091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593667110638837602488727 3890500665958256403733091)
                ·
                  refine ⟨5835750998937384605599637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890500665958256403733091 5835750998937384605599637)
                  ·
                    refine ⟨273550828075189903387483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5835750998937384605599637 273550828075189903387483)
                    ·
                      rfl

theorem cell23_1598215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1598215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598215 prefixEnd_1598215 := by exact prefixLift 1598215
  have htrace : WordTrace (prefixWord ++ tailWord_1598215) baseStart_1598215 baseEnd_1598215 := by
    simpa [prefixWord, tailWord_1598215, baseEnd_1598215] using wordTrace_append hprefix tailTrace_1598215
  have hstable : (prefixWord ++ tailWord_1598215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598215).length < 2 ^ (prefixWord ++ tailWord_1598215).sum := by decide
  have hdescent : baseEnd_1598215 < baseStart_1598215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598218 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1598218 : Nat := 118140960795 + 1598218 * 2 ^ 59
def prefixEnd_1598218 : Nat := 4983230072969 + 3 ^ 40 * 1598218 * 2
def baseEnd_1598218 : Nat := 820654024667533198424935

theorem tailTrace_1598218 : CollatzResearch.WordTrace tailWord_1598218 prefixEnd_1598218 820654024667533198424935 := by
  unfold tailWord_1598218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572949830984153687134827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38861199549291076499026205 14572949830984153687134827)
  ·
    refine ⟨21859424746476230530702241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14572949830984153687134827 21859424746476230530702241)
    ·
      refine ⟨16394568559857172898026681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21859424746476230530702241 16394568559857172898026681)
      ·
        refine ⟨12295926419892879673520011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16394568559857172898026681 12295926419892879673520011)
        ·
          refine ⟨18443889629839319510280017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295926419892879673520011 18443889629839319510280017)
          ·
            refine ⟨13832917222379489632710013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18443889629839319510280017 13832917222379489632710013)
            ·
              refine ⟨5187343958392308612266255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13832917222379489632710013 5187343958392308612266255)
              ·
                refine ⟨7781015937588462918399383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187343958392308612266255 7781015937588462918399383)
                ·
                  refine ⟨11671523906382694377599075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7781015937588462918399383 11671523906382694377599075)
                  ·
                    refine ⟨17507285859574041566398613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11671523906382694377599075 17507285859574041566398613)
                    ·
                      refine ⟨820654024667533198424935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17507285859574041566398613 820654024667533198424935)
                      ·
                        rfl

theorem cell23_1598218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1598218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598218 prefixEnd_1598218 := by exact prefixLift 1598218
  have htrace : WordTrace (prefixWord ++ tailWord_1598218) baseStart_1598218 baseEnd_1598218 := by
    simpa [prefixWord, tailWord_1598218, baseEnd_1598218] using wordTrace_append hprefix tailTrace_1598218
  have hstable : (prefixWord ++ tailWord_1598218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598218).length < 2 ^ (prefixWord ++ tailWord_1598218).sum := by decide
  have hdescent : baseEnd_1598218 < baseStart_1598218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598225 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_1598225 : Nat := 118140960795 + 1598225 * 2 ^ 59
def prefixEnd_1598225 : Nat := 4983230072969 + 3 ^ 40 * 1598225 * 2
def baseEnd_1598225 : Nat := 820657619032114671037403

theorem tailTrace_1598225 : CollatzResearch.WordTrace tailWord_1598225 prefixEnd_1598225 820657619032114671037403 := by
  unfold tailWord_1598225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58292054634911254944044129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38861369756607503296029419 58292054634911254944044129)
  ·
    refine ⟨43719040976183441208033097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58292054634911254944044129 43719040976183441208033097)
    ·
      refine ⟨32789280732137580906024823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43719040976183441208033097 32789280732137580906024823)
      ·
        refine ⟨49183921098206371359037235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32789280732137580906024823 49183921098206371359037235)
        ·
          refine ⟨73775881647309557038555853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49183921098206371359037235 73775881647309557038555853)
          ·
            refine ⟨27665955617741083889458445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73775881647309557038555853 27665955617741083889458445)
            ·
              refine ⟨10374733356652906458546917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27665955617741083889458445 10374733356652906458546917)
              ·
                refine ⟨1945262504372419960977547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10374733356652906458546917 1945262504372419960977547)
                ·
                  refine ⟨2917893756558629941466321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945262504372419960977547 2917893756558629941466321)
                  ·
                    refine ⟨2188420317418972456099741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917893756558629941466321 2188420317418972456099741)
                    ·
                      refine ⟨820657619032114671037403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188420317418972456099741 820657619032114671037403)
                      ·
                        rfl

theorem cell23_1598225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_1598225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598225 prefixEnd_1598225 := by exact prefixLift 1598225
  have htrace : WordTrace (prefixWord ++ tailWord_1598225) baseStart_1598225 baseEnd_1598225 := by
    simpa [prefixWord, tailWord_1598225, baseEnd_1598225] using wordTrace_append hprefix tailTrace_1598225
  have hstable : (prefixWord ++ tailWord_1598225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598225).length < 2 ^ (prefixWord ++ tailWord_1598225).sum := by decide
  have hdescent : baseEnd_1598225 < baseStart_1598225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598242 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1598242 : Nat := 118140960795 + 1598242 * 2 ^ 59
def prefixEnd_1598242 : Nat := 4983230072969 + 3 ^ 40 * 1598242 * 2
def baseEnd_1598242 : Nat := 820666348203241104524825

theorem tailTrace_1598242 : CollatzResearch.WordTrace tailWord_1598242 prefixEnd_1598242 820666348203241104524825 := by
  unfold tailWord_1598242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573168668962416711853245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38861783117233111231608653 14573168668962416711853245)
  ·
    refine ⟨5464938250860906266944967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14573168668962416711853245 5464938250860906266944967)
    ·
      refine ⟨8197407376291359400417451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5464938250860906266944967 8197407376291359400417451)
      ·
        refine ⟨12296111064437039100626177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197407376291359400417451 12296111064437039100626177)
        ·
          refine ⟨9222083298327779325469633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12296111064437039100626177 9222083298327779325469633)
          ·
            refine ⟨6916562473745834494102225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9222083298327779325469633 6916562473745834494102225)
            ·
              refine ⟨5187421855309375870576669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916562473745834494102225 5187421855309375870576669)
              ·
                refine ⟨1945283195741015951466251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187421855309375870576669 1945283195741015951466251)
                ·
                  refine ⟨2917924793611523927199377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945283195741015951466251 2917924793611523927199377)
                  ·
                    refine ⟨2188443595208642945399533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2917924793611523927199377 2188443595208642945399533)
                    ·
                      refine ⟨820666348203241104524825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188443595208642945399533 820666348203241104524825)
                      ·
                        rfl

theorem cell23_1598242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1598242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598242 prefixEnd_1598242 := by exact prefixLift 1598242
  have htrace : WordTrace (prefixWord ++ tailWord_1598242) baseStart_1598242 baseEnd_1598242 := by
    simpa [prefixWord, tailWord_1598242, baseEnd_1598242] using wordTrace_append hprefix tailTrace_1598242
  have hstable : (prefixWord ++ tailWord_1598242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598242).length < 2 ^ (prefixWord ++ tailWord_1598242).sum := by decide
  have hdescent : baseEnd_1598242 < baseStart_1598242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598258 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1598258 : Nat := 118140960795 + 1598258 * 2 ^ 59
def prefixEnd_1598258 : Nat := 4983230072969 + 3 ^ 40 * 1598258 * 2
def baseEnd_1598258 : Nat := 273558187964571013974917

theorem tailTrace_1598258 : CollatzResearch.WordTrace tailWord_1598258 prefixEnd_1598258 273558187964571013974917 := by
  unfold tailWord_1598258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573314560947925394998857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38862172162527801053330285 14573314560947925394998857)
  ·
    refine ⟨10929985920710944046249143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14573314560947925394998857 10929985920710944046249143)
    ·
      refine ⟨16394978881066416069373715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929985920710944046249143 16394978881066416069373715)
      ·
        refine ⟨24592468321599624104060573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16394978881066416069373715 24592468321599624104060573)
        ·
          refine ⟨9222175620599859039022715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24592468321599624104060573 9222175620599859039022715)
          ·
            refine ⟨13833263430899788558534073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222175620599859039022715 13833263430899788558534073)
            ·
              refine ⟨10374947573174841418900555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13833263430899788558534073 10374947573174841418900555)
              ·
                refine ⟨15562421359762262128350833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10374947573174841418900555 15562421359762262128350833)
                ·
                  refine ⟨11671816019821696596263125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15562421359762262128350833 11671816019821696596263125)
                  ·
                    refine ⟨273558187964571013974917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11671816019821696596263125 273558187964571013974917)
                    ·
                      rfl

theorem cell23_1598258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1598258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598258 prefixEnd_1598258 := by exact prefixLift 1598258
  have htrace : WordTrace (prefixWord ++ tailWord_1598258) baseStart_1598258 baseEnd_1598258 := by
    simpa [prefixWord, tailWord_1598258, baseEnd_1598258] using wordTrace_append hprefix tailTrace_1598258
  have hstable : (prefixWord ++ tailWord_1598258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598258).length < 2 ^ (prefixWord ++ tailWord_1598258).sum := by decide
  have hdescent : baseEnd_1598258 < baseStart_1598258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598262 : List Nat := [5, 1, 2, 2, 2, 1, 2, 8]
def baseStart_1598262 : Nat := 118140960795 + 1598262 * 2 ^ 59
def prefixEnd_1598262 : Nat := 4983230072969 + 3 ^ 40 * 1598262 * 2
def baseEnd_1598262 : Nat := 30395430289493741713879

theorem tailTrace_1598262 : CollatzResearch.WordTrace tailWord_1598262 prefixEnd_1598262 30395430289493741713879 := by
  unfold tailWord_1598262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643337758486075641446315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38862269423851473508760693 3643337758486075641446315)
  ·
    refine ⟨5465006637729113462169473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3643337758486075641446315 5465006637729113462169473)
    ·
      refine ⟨4098754978296835096627105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5465006637729113462169473 4098754978296835096627105)
      ·
        refine ⟨3074066233722626322470329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4098754978296835096627105 3074066233722626322470329)
        ·
          refine ⟨2305549675291969741852747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074066233722626322470329 2305549675291969741852747)
          ·
            refine ⟨3458324512937954612779121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305549675291969741852747 3458324512937954612779121)
            ·
              refine ⟨2593743384703465959584341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458324512937954612779121 2593743384703465959584341)
              ·
                refine ⟨30395430289493741713879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2593743384703465959584341 30395430289493741713879)
                ·
                  rfl

theorem cell23_1598262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_1598262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598262 prefixEnd_1598262 := by exact prefixLift 1598262
  have htrace : WordTrace (prefixWord ++ tailWord_1598262) baseStart_1598262 baseEnd_1598262 := by
    simpa [prefixWord, tailWord_1598262, baseEnd_1598262] using wordTrace_append hprefix tailTrace_1598262
  have hstable : (prefixWord ++ tailWord_1598262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598262).length < 2 ^ (prefixWord ++ tailWord_1598262).sum := by decide
  have hdescent : baseEnd_1598262 < baseStart_1598262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598266 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_1598266 : Nat := 118140960795 + 1598266 * 2 ^ 59
def prefixEnd_1598266 : Nat := 4983230072969 + 3 ^ 40 * 1598266 * 2
def baseEnd_1598266 : Nat := 273559557246316336874905

theorem tailTrace_1598266 : CollatzResearch.WordTrace tailWord_1598266 prefixEnd_1598266 273559557246316336874905 := by
  unfold tailWord_1598266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573387506940679736571663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38862366685175145964191101 14573387506940679736571663)
  ·
    refine ⟨21860081260411019604857495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14573387506940679736571663 21860081260411019604857495)
    ·
      refine ⟨32790121890616529407286243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21860081260411019604857495 32790121890616529407286243)
      ·
        refine ⟨49185182835924794110929365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32790121890616529407286243 49185182835924794110929365)
        ·
          refine ⟨1152777722716987361974907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49185182835924794110929365 1152777722716987361974907)
          ·
            refine ⟨1729166584075481042962361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152777722716987361974907 1729166584075481042962361)
            ·
              refine ⟨1296874938056610782221771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729166584075481042962361 1296874938056610782221771)
              ·
                refine ⟨1945312407084916173332657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296874938056610782221771 1945312407084916173332657)
                ·
                  refine ⟨1458984305313687129999493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945312407084916173332657 1458984305313687129999493)
                  ·
                    refine ⟨273559557246316336874905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458984305313687129999493 273559557246316336874905)
                    ·
                      rfl

theorem cell23_1598266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_1598266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598266 prefixEnd_1598266 := by exact prefixLift 1598266
  have htrace : WordTrace (prefixWord ++ tailWord_1598266) baseStart_1598266 baseEnd_1598266 := by
    simpa [prefixWord, tailWord_1598266, baseEnd_1598266] using wordTrace_append hprefix tailTrace_1598266
  have hstable : (prefixWord ++ tailWord_1598266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598266).length < 2 ^ (prefixWord ++ tailWord_1598266).sum := by decide
  have hdescent : baseEnd_1598266 < baseStart_1598266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598282 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_1598282 : Nat := 118140960795 + 1598282 * 2 ^ 59
def prefixEnd_1598282 : Nat := 4983230072969 + 3 ^ 40 * 1598282 * 2
def baseEnd_1598282 : Nat := 820686887429420948024641

theorem tailTrace_1598282 : CollatzResearch.WordTrace tailWord_1598282 prefixEnd_1598282 820686887429420948024641 := by
  unfold tailWord_1598282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573533398926188419717275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38862755730469835785912733 14573533398926188419717275)
  ·
    refine ⟨21860300098389282629575913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14573533398926188419717275 21860300098389282629575913)
    ·
      refine ⟨16395225073791961972181935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21860300098389282629575913 16395225073791961972181935)
      ·
        refine ⟨24592837610687942958272903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16395225073791961972181935 24592837610687942958272903)
        ·
          refine ⟨36889256416031914437409355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24592837610687942958272903 36889256416031914437409355)
          ·
            refine ⟨55333884624047871656114033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36889256416031914437409355 55333884624047871656114033)
            ·
              refine ⟨41500413468035903742085525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55333884624047871656114033 41500413468035903742085525)
              ·
                refine ⟨1945331881314182987910259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41500413468035903742085525 1945331881314182987910259)
                ·
                  refine ⟨2917997821971274481865389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945331881314182987910259 2917997821971274481865389)
                  ·
                    refine ⟨1094249183239227930699521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917997821971274481865389 1094249183239227930699521)
                    ·
                      refine ⟨820686887429420948024641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094249183239227930699521 820686887429420948024641)
                      ·
                        rfl

theorem cell23_1598282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_1598282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598282 prefixEnd_1598282 := by exact prefixLift 1598282
  have htrace : WordTrace (prefixWord ++ tailWord_1598282) baseStart_1598282 baseEnd_1598282 := by
    simpa [prefixWord, tailWord_1598282, baseEnd_1598282] using wordTrace_append hprefix tailTrace_1598282
  have hstable : (prefixWord ++ tailWord_1598282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598282).length < 2 ^ (prefixWord ++ tailWord_1598282).sum := by decide
  have hdescent : baseEnd_1598282 < baseStart_1598282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598306 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1598306 : Nat := 118140960795 + 1598306 * 2 ^ 59
def prefixEnd_1598306 : Nat := 4983230072969 + 3 ^ 40 * 1598306 * 2
def baseEnd_1598306 : Nat := 820699210965128854124531

theorem tailTrace_1598306 : CollatzResearch.WordTrace tailWord_1598306 prefixEnd_1598306 820699210965128854124531 := by
  unfold tailWord_1598306
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573752236904451444435693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38863339298411870518495181 14573752236904451444435693)
  ·
    refine ⟨5465157088839169291663385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14573752236904451444435693 5465157088839169291663385)
    ·
      refine ⟨4098867816629376968747539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5465157088839169291663385 4098867816629376968747539)
      ·
        refine ⟨6148301724944065453121309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098867816629376968747539 6148301724944065453121309)
        ·
          refine ⟨2305613146854024544920491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6148301724944065453121309 2305613146854024544920491)
          ·
            refine ⟨3458419720281036817380737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305613146854024544920491 3458419720281036817380737)
            ·
              refine ⟨2593814790210777613035553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458419720281036817380737 2593814790210777613035553)
              ·
                refine ⟨1945361092658083209776665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593814790210777613035553 1945361092658083209776665)
                ·
                  refine ⟨1459020819493562407332499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945361092658083209776665 1459020819493562407332499)
                  ·
                    refine ⟨2188531229240343610998749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459020819493562407332499 2188531229240343610998749)
                    ·
                      refine ⟨820699210965128854124531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188531229240343610998749 820699210965128854124531)
                      ·
                        rfl

theorem cell23_1598306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1598306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598306 prefixEnd_1598306 := by exact prefixLift 1598306
  have htrace : WordTrace (prefixWord ++ tailWord_1598306) baseStart_1598306 baseEnd_1598306 := by
    simpa [prefixWord, tailWord_1598306, baseEnd_1598306] using wordTrace_append hprefix tailTrace_1598306
  have hstable : (prefixWord ++ tailWord_1598306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598306).length < 2 ^ (prefixWord ++ tailWord_1598306).sum := by decide
  have hdescent : baseEnd_1598306 < baseStart_1598306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598325 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1598325 : Nat := 118140960795 + 1598325 * 2 ^ 59
def prefixEnd_1598325 : Nat := 4983230072969 + 3 ^ 40 * 1598325 * 2
def baseEnd_1598325 : Nat := 820708967097564279786943

theorem tailTrace_1598325 : CollatzResearch.WordTrace tailWord_1598325 prefixEnd_1598325 820708967097564279786943 := by
  unfold tailWord_1598325
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295701934548972022684429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38863801289699314681789619 58295701934548972022684429)
  ·
    refine ⟨21860888225455864508506661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58295701934548972022684429 21860888225455864508506661)
    ·
      refine ⟨4098916542272974595344999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21860888225455864508506661 4098916542272974595344999)
      ·
        refine ⟨6148374813409461893017499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098916542272974595344999 6148374813409461893017499)
        ·
          refine ⟨9222562220114192839526249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148374813409461893017499 9222562220114192839526249)
          ·
            refine ⟨6916921665085644629644687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9222562220114192839526249 6916921665085644629644687)
            ·
              refine ⟨10375382497628466944467031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916921665085644629644687 10375382497628466944467031)
              ·
                refine ⟨15563073746442700416700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375382497628466944467031 15563073746442700416700547)
                ·
                  refine ⟨23344610619664050625050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15563073746442700416700547 23344610619664050625050821)
                  ·
                    refine ⟨4377114491187009492197029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23344610619664050625050821 4377114491187009492197029)
                    ·
                      refine ⟨820708967097564279786943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4377114491187009492197029 820708967097564279786943)
                      ·
                        rfl

theorem cell23_1598325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1598325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598325 prefixEnd_1598325 := by exact prefixLift 1598325
  have htrace : WordTrace (prefixWord ++ tailWord_1598325) baseStart_1598325 baseEnd_1598325 := by
    simpa [prefixWord, tailWord_1598325, baseEnd_1598325] using wordTrace_append hprefix tailTrace_1598325
  have hstable : (prefixWord ++ tailWord_1598325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598325).length < 2 ^ (prefixWord ++ tailWord_1598325).sum := by decide
  have hdescent : baseEnd_1598325 < baseStart_1598325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598329 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 2, 2, 2]
def baseStart_1598329 : Nat := 118140960795 + 1598329 * 2 ^ 59
def prefixEnd_1598329 : Nat := 4983230072969 + 3 ^ 40 * 1598329 * 2
def baseEnd_1598329 : Nat := 820711021020182264136925

theorem tailTrace_1598329 : CollatzResearch.WordTrace tailWord_1598329 prefixEnd_1598329 820711021020182264136925 := by
  unfold tailWord_1598329
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295847826534480705830041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38863898551022987137220027 58295847826534480705830041)
  ·
    refine ⟨43721885869900860529372531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58295847826534480705830041 43721885869900860529372531)
    ·
      refine ⟨65582828804851290794058797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721885869900860529372531 65582828804851290794058797)
      ·
        refine ⟨24593560801819234047772049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65582828804851290794058797 24593560801819234047772049)
        ·
          refine ⟨18445170601364425535829037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24593560801819234047772049 18445170601364425535829037)
          ·
            refine ⟨6916938975511659575935889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18445170601364425535829037 6916938975511659575935889)
            ·
              refine ⟨5187704231633744681951917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916938975511659575935889 5187704231633744681951917)
              ·
                refine ⟨1945389086862654255731969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187704231633744681951917 1945389086862654255731969)
                ·
                  refine ⟨1459041815146990691798977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945389086862654255731969 1459041815146990691798977)
                  ·
                    refine ⟨1094281361360243018849233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1459041815146990691798977 1094281361360243018849233)
                    ·
                      refine ⟨820711021020182264136925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094281361360243018849233 820711021020182264136925)
                      ·
                        rfl

theorem cell23_1598329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_1598329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598329 prefixEnd_1598329 := by exact prefixLift 1598329
  have htrace : WordTrace (prefixWord ++ tailWord_1598329) baseStart_1598329 baseEnd_1598329 := by
    simpa [prefixWord, tailWord_1598329, baseEnd_1598329] using wordTrace_append hprefix tailTrace_1598329
  have hstable : (prefixWord ++ tailWord_1598329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598329).length < 2 ^ (prefixWord ++ tailWord_1598329).sum := by decide
  have hdescent : baseEnd_1598329 < baseStart_1598329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598355 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 7, 2]
def baseStart_1598355 : Nat := 118140960795 + 1598355 * 2 ^ 59
def prefixEnd_1598355 : Nat := 4983230072969 + 3 ^ 40 * 1598355 * 2
def baseEnd_1598355 : Nat := 820724371517199162411805

theorem tailTrace_1598355 : CollatzResearch.WordTrace tailWord_1598355 prefixEnd_1598355 820724371517199162411805 := by
  unfold tailWord_1598355
  simp only [CollatzResearch.WordTrace]
  refine ⟨58296796124440287146276519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38864530749626858097517679 58296796124440287146276519)
  ·
    refine ⟨87445194186660430719414779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58296796124440287146276519 87445194186660430719414779)
    ·
      refine ⟨131167791279990646079122169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87445194186660430719414779 131167791279990646079122169)
      ·
        refine ⟨98375843459992984559341627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131167791279990646079122169 98375843459992984559341627)
        ·
          refine ⟨147563765189989476839012441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98375843459992984559341627 147563765189989476839012441)
          ·
            refine ⟨110672823892492107629259331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147563765189989476839012441 110672823892492107629259331)
            ·
              refine ⟨166009235838738161443888997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110672823892492107629259331 166009235838738161443888997)
              ·
                refine ⟨31126731719763405270729187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166009235838738161443888997 31126731719763405270729187)
                ·
                  refine ⟨46690097579645107906093781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31126731719763405270729187 46690097579645107906093781)
                  ·
                    refine ⟨1094299162022932216549073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46690097579645107906093781 1094299162022932216549073)
                    ·
                      refine ⟨820724371517199162411805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094299162022932216549073 820724371517199162411805)
                      ·
                        rfl

theorem cell23_1598355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7, 2].length) (baseStart_1598355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598355 prefixEnd_1598355 := by exact prefixLift 1598355
  have htrace : WordTrace (prefixWord ++ tailWord_1598355) baseStart_1598355 baseEnd_1598355 := by
    simpa [prefixWord, tailWord_1598355, baseEnd_1598355] using wordTrace_append hprefix tailTrace_1598355
  have hstable : (prefixWord ++ tailWord_1598355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598355).length < 2 ^ (prefixWord ++ tailWord_1598355).sum := by decide
  have hdescent : baseEnd_1598355 < baseStart_1598355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598365 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1598365 : Nat := 118140960795 + 1598365 * 2 ^ 59
def prefixEnd_1598365 : Nat := 4983230072969 + 3 ^ 40 * 1598365 * 2
def baseEnd_1598365 : Nat := 273576502107914707762253

theorem tailTrace_1598365 : CollatzResearch.WordTrace tailWord_1598365 prefixEnd_1598365 273576502107914707762253 := by
  unfold tailWord_1598365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58297160854404058854140549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38864773902936039236093699 58297160854404058854140549)
  ·
    refine ⟨10930717660200761035151353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58297160854404058854140549 10930717660200761035151353)
    ·
      refine ⟨8198038245150570776363515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10930717660200761035151353 8198038245150570776363515)
      ·
        refine ⟨12297057367725856164545273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198038245150570776363515 12297057367725856164545273)
        ·
          refine ⟨9222793025794392123408955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12297057367725856164545273 9222793025794392123408955)
          ·
            refine ⟨13834189538691588185113433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222793025794392123408955 13834189538691588185113433)
            ·
              refine ⟨10375642154018691138835075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13834189538691588185113433 10375642154018691138835075)
              ·
                refine ⟨15563463231028036708252613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375642154018691138835075 15563463231028036708252613)
                ·
                  refine ⟨2918149355817756882797365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15563463231028036708252613 2918149355817756882797365)
                  ·
                    refine ⟨273576502107914707762253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2918149355817756882797365 273576502107914707762253)
                    ·
                      rfl

theorem cell23_1598365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1598365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598365 prefixEnd_1598365 := by exact prefixLift 1598365
  have htrace : WordTrace (prefixWord ++ tailWord_1598365) baseStart_1598365 baseEnd_1598365 := by
    simpa [prefixWord, tailWord_1598365, baseEnd_1598365] using wordTrace_append hprefix tailTrace_1598365
  have hstable : (prefixWord ++ tailWord_1598365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598365).length < 2 ^ (prefixWord ++ tailWord_1598365).sum := by decide
  have hdescent : baseEnd_1598365 < baseStart_1598365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598425 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 8]
def baseStart_1598425 : Nat := 118140960795 + 1598425 * 2 ^ 59
def prefixEnd_1598425 : Nat := 4983230072969 + 3 ^ 40 * 1598425 * 2
def baseEnd_1598425 : Nat := 91195590573668209837387

theorem tailTrace_1598425 : CollatzResearch.WordTrace tailWord_1598425 prefixEnd_1598425 91195590573668209837387 := by
  unfold tailWord_1598425
  simp only [CollatzResearch.WordTrace]
  refine ⟨58299349234186689101324729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38866232822791126067549819 58299349234186689101324729)
  ·
    refine ⟨43724511925640016825993547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58299349234186689101324729 43724511925640016825993547)
    ·
      refine ⟨65586767888460025238990321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43724511925640016825993547 65586767888460025238990321)
      ·
        refine ⟨49190075916345018929242741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65586767888460025238990321 49190075916345018929242741)
        ·
          refine ⟨4611569617157345524616507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49190075916345018929242741 4611569617157345524616507)
          ·
            refine ⟨6917354425736018286924761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611569617157345524616507 6917354425736018286924761)
            ·
              refine ⟨5188015819302013715193571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917354425736018286924761 5188015819302013715193571)
              ·
                refine ⟨7782023728953020572790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188015819302013715193571 7782023728953020572790357)
                ·
                  refine ⟨91195590573668209837387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7782023728953020572790357 91195590573668209837387)
                  ·
                    rfl

theorem cell23_1598425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_1598425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598425 prefixEnd_1598425 := by exact prefixLift 1598425
  have htrace : WordTrace (prefixWord ++ tailWord_1598425) baseStart_1598425 baseEnd_1598425 := by
    simpa [prefixWord, tailWord_1598425, baseEnd_1598425] using wordTrace_append hprefix tailTrace_1598425
  have hstable : (prefixWord ++ tailWord_1598425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598425).length < 2 ^ (prefixWord ++ tailWord_1598425).sum := by decide
  have hdescent : baseEnd_1598425 < baseStart_1598425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598429 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1598429 : Nat := 118140960795 + 1598429 * 2 ^ 59
def prefixEnd_1598429 : Nat := 4983230072969 + 3 ^ 40 * 1598429 * 2
def baseEnd_1598429 : Nat := 273587456361877290962155

theorem tailTrace_1598429 : CollatzResearch.WordTrace tailWord_1598429 prefixEnd_1598429 273587456361877290962155 := by
  unfold tailWord_1598429
  simp only [CollatzResearch.WordTrace]
  refine ⟨58299495126172197784470341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38866330084114798522980227 58299495126172197784470341)
  ·
    refine ⟨10931155336157287084588189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58299495126172197784470341 10931155336157287084588189)
    ·
      refine ⟨4099183251058982656720571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10931155336157287084588189 4099183251058982656720571)
      ·
        refine ⟨6148774876588473985080857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099183251058982656720571 6148774876588473985080857)
        ·
          refine ⟨4611581157441355488810643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6148774876588473985080857 4611581157441355488810643)
          ·
            refine ⟨6917371736162033233215965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611581157441355488810643 6917371736162033233215965)
            ·
              refine ⟨2594014401060762462455987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6917371736162033233215965 2594014401060762462455987)
              ·
                refine ⟨3891021601591143693683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594014401060762462455987 3891021601591143693683981)
                ·
                  refine ⟨1459133100596678885131493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3891021601591143693683981 1459133100596678885131493)
                  ·
                    refine ⟨273587456361877290962155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459133100596678885131493 273587456361877290962155)
                    ·
                      rfl

theorem cell23_1598429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1598429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598429 prefixEnd_1598429 := by exact prefixLift 1598429
  have htrace : WordTrace (prefixWord ++ tailWord_1598429) baseStart_1598429 baseEnd_1598429 := by
    simpa [prefixWord, tailWord_1598429, baseEnd_1598429] using wordTrace_append hprefix tailTrace_1598429
  have hstable : (prefixWord ++ tailWord_1598429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598429).length < 2 ^ (prefixWord ++ tailWord_1598429).sum := by decide
  have hdescent : baseEnd_1598429 < baseStart_1598429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598442 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_1598442 : Nat := 118140960795 + 1598442 * 2 ^ 59
def prefixEnd_1598442 : Nat := 4983230072969 + 3 ^ 40 * 1598442 * 2
def baseEnd_1598442 : Nat := 91196560481571146891545

theorem tailTrace_1598442 : CollatzResearch.WordTrace tailWord_1598442 prefixEnd_1598442 91196560481571146891545 := by
  unfold tailWord_1598442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574992318781275251173395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38866646183416734003129053 14574992318781275251173395)
  ·
    refine ⟨21862488478171912876760093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14574992318781275251173395 21862488478171912876760093)
    ·
      refine ⟨8198433179314467328785035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21862488478171912876760093 8198433179314467328785035)
      ·
        refine ⟨12297649768971700993177553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198433179314467328785035 12297649768971700993177553)
        ·
          refine ⟨9223237326728775744883165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12297649768971700993177553 9223237326728775744883165)
          ·
            refine ⟨3458713997523290904331187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9223237326728775744883165 3458713997523290904331187)
            ·
              refine ⟨5188070996284936356496781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458713997523290904331187 5188070996284936356496781)
              ·
                refine ⟨1945526623606851133686293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188070996284936356496781 1945526623606851133686293)
                ·
                  refine ⟨91196560481571146891545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1945526623606851133686293 91196560481571146891545)
                  ·
                    rfl

theorem cell23_1598442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_1598442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598442 prefixEnd_1598442 := by exact prefixLift 1598442
  have htrace : WordTrace (prefixWord ++ tailWord_1598442) baseStart_1598442 baseEnd_1598442 := by
    simpa [prefixWord, tailWord_1598442, baseEnd_1598442] using wordTrace_append hprefix tailTrace_1598442
  have hstable : (prefixWord ++ tailWord_1598442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598442).length < 2 ^ (prefixWord ++ tailWord_1598442).sum := by decide
  have hdescent : baseEnd_1598442 < baseStart_1598442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598512 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_1598512 : Nat := 118140960795 + 1598512 * 2 ^ 59
def prefixEnd_1598512 : Nat := 4983230072969 + 3 ^ 40 * 1598512 * 2
def baseEnd_1598512 : Nat := 820804987979955048148583

theorem tailTrace_1598512 : CollatzResearch.WordTrace tailWord_1598512 prefixEnd_1598512 820804987979955048148583 := by
  unfold tailWord_1598512
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151261192435751479870895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38868348256581001973161193 29151261192435751479870895)
  ·
    refine ⟨43726891788653627219806343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29151261192435751479870895 43726891788653627219806343)
    ·
      refine ⟨65590337682980440829709515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43726891788653627219806343 65590337682980440829709515)
      ·
        refine ⟨98385506524470661244564273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65590337682980440829709515 98385506524470661244564273)
        ·
          refine ⟨73789129893352995933423205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98385506524470661244564273 73789129893352995933423205)
          ·
            refine ⟨13835461855003686737516851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73789129893352995933423205 13835461855003686737516851)
            ·
              refine ⟨20753192782505530106275277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13835461855003686737516851 20753192782505530106275277)
              ·
                refine ⟨7782447293439573789853229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20753192782505530106275277 7782447293439573789853229)
                ·
                  refine ⟨2918417735039840171194961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7782447293439573789853229 2918417735039840171194961)
                  ·
                    refine ⟨2188813301279880128396221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2918417735039840171194961 2188813301279880128396221)
                    ·
                      refine ⟨820804987979955048148583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188813301279880128396221 820804987979955048148583)
                      ·
                        rfl

theorem cell23_1598512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_1598512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598512 prefixEnd_1598512 := by exact prefixLift 1598512
  have htrace : WordTrace (prefixWord ++ tailWord_1598512) baseStart_1598512 baseEnd_1598512 := by
    simpa [prefixWord, tailWord_1598512, baseEnd_1598512] using wordTrace_append hprefix tailTrace_1598512
  have hstable : (prefixWord ++ tailWord_1598512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598512).length < 2 ^ (prefixWord ++ tailWord_1598512).sum := by decide
  have hdescent : baseEnd_1598512 < baseStart_1598512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598522 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_1598522 : Nat := 118140960795 + 1598522 * 2 ^ 59
def prefixEnd_1598522 : Nat := 4983230072969 + 3 ^ 40 * 1598522 * 2
def baseEnd_1598522 : Nat := 820810122786500009023537

theorem tailTrace_1598522 : CollatzResearch.WordTrace tailWord_1598522 prefixEnd_1598522 820810122786500009023537 := by
  unfold tailWord_1598522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575721778708818666901455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38868591409890183111737213 14575721778708818666901455)
  ·
    refine ⟨21863582668063228000352183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14575721778708818666901455 21863582668063228000352183)
    ·
      refine ⟨32795374002094842000528275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863582668063228000352183 32795374002094842000528275)
      ·
        refine ⟨49193061003142263000792413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32795374002094842000528275 49193061003142263000792413)
        ·
          refine ⟨18447397876178348625297155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49193061003142263000792413 18447397876178348625297155)
          ·
            refine ⟨27671096814267522937945733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447397876178348625297155 27671096814267522937945733)
            ·
              refine ⟨5188330652675160550864825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27671096814267522937945733 5188330652675160550864825)
              ·
                refine ⟨3891247989506370413148619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188330652675160550864825 3891247989506370413148619)
                ·
                  refine ⟨5836871984259555619722929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891247989506370413148619 5836871984259555619722929)
                  ·
                    refine ⟨4377653988194666714792197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5836871984259555619722929 4377653988194666714792197)
                    ·
                      refine ⟨820810122786500009023537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4377653988194666714792197 820810122786500009023537)
                      ·
                        rfl

theorem cell23_1598522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_1598522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598522 prefixEnd_1598522 := by exact prefixLift 1598522
  have htrace : WordTrace (prefixWord ++ tailWord_1598522) baseStart_1598522 baseEnd_1598522 := by
    simpa [prefixWord, tailWord_1598522, baseEnd_1598522] using wordTrace_append hprefix tailTrace_1598522
  have hstable : (prefixWord ++ tailWord_1598522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598522).length < 2 ^ (prefixWord ++ tailWord_1598522).sum := by decide
  have hdescent : baseEnd_1598522 < baseStart_1598522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598526 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1598526 : Nat := 118140960795 + 1598526 * 2 ^ 59
def prefixEnd_1598526 : Nat := 4983230072969 + 3 ^ 40 * 1598526 * 2
def baseEnd_1598526 : Nat := 820812176709117993373519

theorem tailTrace_1598526 : CollatzResearch.WordTrace tailWord_1598526 prefixEnd_1598526 820812176709117993373519 := by
  unfold tailWord_1598526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7287879125852597918843929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38868688671213855567167621 7287879125852597918843929)
  ·
    refine ⟨5465909344389448439132947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7287879125852597918843929 5465909344389448439132947)
    ·
      refine ⟨8198864016584172658699421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465909344389448439132947 8198864016584172658699421)
      ·
        refine ⟨3074574006219064747012283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8198864016584172658699421 3074574006219064747012283)
        ·
          refine ⟨4611861009328597120518425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074574006219064747012283 4611861009328597120518425)
          ·
            refine ⟨3458895756996447840388819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611861009328597120518425 3458895756996447840388819)
            ·
              refine ⟨5188343635494671760583229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458895756996447840388819 5188343635494671760583229)
              ·
                refine ⟨1945628863310501910218711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188343635494671760583229 1945628863310501910218711)
                ·
                  refine ⟨2918443294965752865328067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945628863310501910218711 2918443294965752865328067)
                  ·
                    refine ⟨4377664942448629297992101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918443294965752865328067 4377664942448629297992101)
                    ·
                      refine ⟨820812176709117993373519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4377664942448629297992101 820812176709117993373519)
                      ·
                        rfl

theorem cell23_1598526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1598526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598526 prefixEnd_1598526 := by exact prefixLift 1598526
  have htrace : WordTrace (prefixWord ++ tailWord_1598526) baseStart_1598526 baseEnd_1598526 := by
    simpa [prefixWord, tailWord_1598526, baseEnd_1598526] using wordTrace_append hprefix tailTrace_1598526
  have hstable : (prefixWord ++ tailWord_1598526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598526).length < 2 ^ (prefixWord ++ tailWord_1598526).sum := by decide
  have hdescent : baseEnd_1598526 < baseStart_1598526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598545 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1598545 : Nat := 118140960795 + 1598545 * 2 ^ 59
def prefixEnd_1598545 : Nat := 4983230072969 + 3 ^ 40 * 1598545 * 2
def baseEnd_1598545 : Nat := 273607310947184473011977

theorem tailTrace_1598545 : CollatzResearch.WordTrace tailWord_1598545 prefixEnd_1598545 273607310947184473011977 := by
  unfold tailWord_1598545
  simp only [CollatzResearch.WordTrace]
  refine ⟨58303725993751949595693089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38869150662501299730462059 58303725993751949595693089)
  ·
    refine ⟨43727794495313962196769817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58303725993751949595693089 43727794495313962196769817)
    ·
      refine ⟨32795845871485471647577363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43727794495313962196769817 32795845871485471647577363)
      ·
        refine ⟨49193768807228207471366045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32795845871485471647577363 49193768807228207471366045)
        ·
          refine ⟨18447663302710577801762267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49193768807228207471366045 18447663302710577801762267)
          ·
            refine ⟨27671494954065866702643401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447663302710577801762267 27671494954065866702643401)
            ·
              refine ⟨20753621215549400026982551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27671494954065866702643401 20753621215549400026982551)
              ·
                refine ⟨31130431823324100040473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20753621215549400026982551 31130431823324100040473827)
                ·
                  refine ⟨46695647734986150060710741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31130431823324100040473827 46695647734986150060710741)
                  ·
                    refine ⟨273607310947184473011977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46695647734986150060710741 273607310947184473011977)
                    ·
                      rfl

theorem cell23_1598545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1598545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598545 prefixEnd_1598545 := by exact prefixLift 1598545
  have htrace : WordTrace (prefixWord ++ tailWord_1598545) baseStart_1598545 baseEnd_1598545 := by
    simpa [prefixWord, tailWord_1598545, baseEnd_1598545] using wordTrace_append hprefix tailTrace_1598545
  have hstable : (prefixWord ++ tailWord_1598545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598545).length < 2 ^ (prefixWord ++ tailWord_1598545).sum := by decide
  have hdescent : baseEnd_1598545 < baseStart_1598545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598602 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1598602 : Nat := 118140960795 + 1598602 * 2 ^ 59
def prefixEnd_1598602 : Nat := 4983230072969 + 3 ^ 40 * 1598602 * 2
def baseEnd_1598602 : Nat := 820851201238859696023169

theorem tailTrace_1598602 : CollatzResearch.WordTrace tailWord_1598602 prefixEnd_1598602 820851201238859696023169 := by
  unfold tailWord_1598602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576451238636362082629515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38870536636363632220345373 14576451238636362082629515)
  ·
    refine ⟨21864676857954543123944273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576451238636362082629515 21864676857954543123944273)
    ·
      refine ⟨16398507643465907342958205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21864676857954543123944273 16398507643465907342958205)
      ·
        refine ⟨6149440366299715253609327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16398507643465907342958205 6149440366299715253609327)
        ·
          refine ⟨9224160549449572880413991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149440366299715253609327 9224160549449572880413991)
          ·
            refine ⟨13836240824174359320620987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224160549449572880413991 13836240824174359320620987)
            ·
              refine ⟨20754361236261538980931481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13836240824174359320620987 20754361236261538980931481)
              ·
                refine ⟨15565770927196154235698611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20754361236261538980931481 15565770927196154235698611)
                ·
                  refine ⟨23348656390794231353547917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15565770927196154235698611 23348656390794231353547917)
                  ·
                    refine ⟨8755746146547836757580469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23348656390794231353547917 8755746146547836757580469)
                    ·
                      refine ⟨820851201238859696023169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8755746146547836757580469 820851201238859696023169)
                      ·
                        rfl

theorem cell23_1598602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1598602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598602 prefixEnd_1598602 := by exact prefixLift 1598602
  have htrace : WordTrace (prefixWord ++ tailWord_1598602) baseStart_1598602 baseEnd_1598602 := by
    simpa [prefixWord, tailWord_1598602, baseEnd_1598602] using wordTrace_append hprefix tailTrace_1598602
  have hstable : (prefixWord ++ tailWord_1598602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598602).length < 2 ^ (prefixWord ++ tailWord_1598602).sum := by decide
  have hdescent : baseEnd_1598602 < baseStart_1598602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598610 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1598610 : Nat := 118140960795 + 1598610 * 2 ^ 59
def prefixEnd_1598610 : Nat := 4983230072969 + 3 ^ 40 * 1598610 * 2
def baseEnd_1598610 : Nat := 820855309084095664723133

theorem tailTrace_1598610 : CollatzResearch.WordTrace tailWord_1598610 prefixEnd_1598610 820855309084095664723133 := by
  unfold tailWord_1598610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576524184629116424202321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38870731159010977131206189 14576524184629116424202321)
  ·
    refine ⟨10932393138471837318151741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14576524184629116424202321 10932393138471837318151741)
    ·
      refine ⟨4099647426926938994306903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10932393138471837318151741 4099647426926938994306903)
      ·
        refine ⟨6149471140390408491460355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099647426926938994306903 6149471140390408491460355)
        ·
          refine ⟨9224206710585612737190533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149471140390408491460355 9224206710585612737190533)
          ·
            refine ⟨1729538758234802388223225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9224206710585612737190533 1729538758234802388223225)
            ·
              refine ⟨1297154068676101791167419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729538758234802388223225 1297154068676101791167419)
              ·
                refine ⟨1945731103014152686751129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297154068676101791167419 1945731103014152686751129)
                ·
                  refine ⟨1459298327260614515063347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945731103014152686751129 1459298327260614515063347)
                  ·
                    refine ⟨2188947490890921772595021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459298327260614515063347 2188947490890921772595021)
                    ·
                      refine ⟨820855309084095664723133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2188947490890921772595021 820855309084095664723133)
                      ·
                        rfl

theorem cell23_1598610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1598610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598610 prefixEnd_1598610 := by exact prefixLift 1598610
  have htrace : WordTrace (prefixWord ++ tailWord_1598610) baseStart_1598610 baseEnd_1598610 := by
    simpa [prefixWord, tailWord_1598610, baseEnd_1598610] using wordTrace_append hprefix tailTrace_1598610
  have hstable : (prefixWord ++ tailWord_1598610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598610).length < 2 ^ (prefixWord ++ tailWord_1598610).sum := by decide
  have hdescent : baseEnd_1598610 < baseStart_1598610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598656 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 5]
def baseStart_1598656 : Nat := 118140960795 + 1598656 * 2 ^ 59
def prefixEnd_1598656 : Nat := 4983230072969 + 3 ^ 40 * 1598656 * 2
def baseEnd_1598656 : Nat := 91208769910466942749769

theorem tailTrace_1598656 : CollatzResearch.WordTrace tailWord_1598656 prefixEnd_1598656 91208769910466942749769 := by
  unfold tailWord_1598656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153887248174907776491911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38871849664233210368655881 29153887248174907776491911)
  ·
    refine ⟨43730830872262361664737867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29153887248174907776491911 43730830872262361664737867)
    ·
      refine ⟨65596246308393542497106801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43730830872262361664737867 65596246308393542497106801)
      ·
        refine ⟨49197184731295156872830101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65596246308393542497106801 49197184731295156872830101)
        ·
          refine ⟨2306118034279460478413911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49197184731295156872830101 2306118034279460478413911)
          ·
            refine ⟨3459177051419190717620867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306118034279460478413911 3459177051419190717620867)
            ·
              refine ⟨5188765577128786076431301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459177051419190717620867 5188765577128786076431301)
              ·
                refine ⟨972893545711647389330869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5188765577128786076431301 972893545711647389330869)
                ·
                  refine ⟨91208769910466942749769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972893545711647389330869 91208769910466942749769)
                  ·
                    rfl

theorem cell23_1598656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 5].length) (baseStart_1598656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598656 prefixEnd_1598656 := by exact prefixLift 1598656
  have htrace : WordTrace (prefixWord ++ tailWord_1598656) baseStart_1598656 baseEnd_1598656 := by
    simpa [prefixWord, tailWord_1598656, baseEnd_1598656] using wordTrace_append hprefix tailTrace_1598656
  have hstable : (prefixWord ++ tailWord_1598656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598656).length < 2 ^ (prefixWord ++ tailWord_1598656).sum := by decide
  have hdescent : baseEnd_1598656 < baseStart_1598656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598689 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1598689 : Nat := 118140960795 + 1598689 * 2 ^ 59
def prefixEnd_1598689 : Nat := 4983230072969 + 3 ^ 40 * 1598689 * 2
def baseEnd_1598689 : Nat := 820895874055800855635269

theorem tailTrace_1598689 : CollatzResearch.WordTrace tailWord_1598689 prefixEnd_1598689 820895874055800855635269 := by
  unfold tailWord_1598689
  simp only [CollatzResearch.WordTrace]
  refine ⟨58308978105230262188935121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38872652070153508125956747 58308978105230262188935121)
  ·
    refine ⟨43731733578922696641701341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58308978105230262188935121 43731733578922696641701341)
    ·
      refine ⟨16399400092096011240638003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43731733578922696641701341 16399400092096011240638003)
      ·
        refine ⟨24599100138144016860957005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399400092096011240638003 24599100138144016860957005)
        ·
          refine ⟨9224662551804006322858877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24599100138144016860957005 9224662551804006322858877)
          ·
            refine ⟨3459248456926502371072079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9224662551804006322858877 3459248456926502371072079)
            ·
              refine ⟨5188872685389753556608119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459248456926502371072079 5188872685389753556608119)
              ·
                refine ⟨7783309028084630334912179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188872685389753556608119 7783309028084630334912179)
                ·
                  refine ⟨11674963542126945502368269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783309028084630334912179 11674963542126945502368269)
                  ·
                    refine ⟨4378111328297604563388101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11674963542126945502368269 4378111328297604563388101)
                    ·
                      refine ⟨820895874055800855635269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4378111328297604563388101 820895874055800855635269)
                      ·
                        rfl

theorem cell23_1598689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1598689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598689 prefixEnd_1598689 := by exact prefixLift 1598689
  have htrace : WordTrace (prefixWord ++ tailWord_1598689) baseStart_1598689 baseEnd_1598689 := by
    simpa [prefixWord, tailWord_1598689, baseEnd_1598689] using wordTrace_append hprefix tailTrace_1598689
  have hstable : (prefixWord ++ tailWord_1598689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598689).length < 2 ^ (prefixWord ++ tailWord_1598689).sum := by decide
  have hdescent : baseEnd_1598689 < baseStart_1598689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598773 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1598773 : Nat := 118140960795 + 1598773 * 2 ^ 59
def prefixEnd_1598773 : Nat := 4983230072969 + 3 ^ 40 * 1598773 * 2
def baseEnd_1598773 : Nat := 820939006430778526984883

theorem tailTrace_1598773 : CollatzResearch.WordTrace tailWord_1598773 prefixEnd_1598773 820939006430778526984883 := by
  unfold tailWord_1598773
  simp only [CollatzResearch.WordTrace]
  refine ⟨58312041836925944534992973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38874694557950629689995315 58312041836925944534992973)
  ·
    refine ⟨21867015688847229200622365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58312041836925944534992973 21867015688847229200622365)
    ·
      refine ⟨8200130883317710950233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21867015688847229200622365 8200130883317710950233387)
      ·
        refine ⟨12300196324976566425350081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8200130883317710950233387 12300196324976566425350081)
        ·
          refine ⟨9225147243732424819012561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12300196324976566425350081 9225147243732424819012561)
          ·
            refine ⟨6918860432799318614259421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9225147243732424819012561 6918860432799318614259421)
            ·
              refine ⟨2594572662299744480347283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6918860432799318614259421 2594572662299744480347283)
              ·
                refine ⟨3891858993449616720520925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594572662299744480347283 3891858993449616720520925)
                ·
                  refine ⟨1459447122543606270195347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3891858993449616720520925 1459447122543606270195347)
                  ·
                    refine ⟨2189170683815409405293021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459447122543606270195347 2189170683815409405293021)
                    ·
                      refine ⟨820939006430778526984883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189170683815409405293021 820939006430778526984883)
                      ·
                        rfl

theorem cell23_1598773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1598773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598773 prefixEnd_1598773 := by exact prefixLift 1598773
  have htrace : WordTrace (prefixWord ++ tailWord_1598773) baseStart_1598773 baseEnd_1598773 := by
    simpa [prefixWord, tailWord_1598773, baseEnd_1598773] using wordTrace_append hprefix tailTrace_1598773
  have hstable : (prefixWord ++ tailWord_1598773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598773).length < 2 ^ (prefixWord ++ tailWord_1598773).sum := by decide
  have hdescent : baseEnd_1598773 < baseStart_1598773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598796 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1598796 : Nat := 118140960795 + 1598796 * 2 ^ 59
def prefixEnd_1598796 : Nat := 4983230072969 + 3 ^ 40 * 1598796 * 2
def baseEnd_1598796 : Nat := 820950816485831936997277

theorem tailTrace_1598796 : CollatzResearch.WordTrace tailWord_1598796 prefixEnd_1598796 820950816485831936997277 := by
  unfold tailWord_1598796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156440357921309731540121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38875253810561746308720161 29156440357921309731540121)
  ·
    refine ⟨21867330268440982298655091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29156440357921309731540121 21867330268440982298655091)
    ·
      refine ⟨32800995402661473447982637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21867330268440982298655091 32800995402661473447982637)
      ·
        refine ⟨12300373275998052542993489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32800995402661473447982637 12300373275998052542993489)
        ·
          refine ⟨9225279956998539407245117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12300373275998052542993489 9225279956998539407245117)
          ·
            refine ⟨3459479983874452277716919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9225279956998539407245117 3459479983874452277716919)
            ·
              refine ⟨5189219975811678416575379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459479983874452277716919 5189219975811678416575379)
              ·
                refine ⟨7783829963717517624863069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189219975811678416575379 7783829963717517624863069)
                ·
                  refine ⟨2918936236394069109323651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7783829963717517624863069 2918936236394069109323651)
                  ·
                    refine ⟨4378404354591103663985477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918936236394069109323651 4378404354591103663985477)
                    ·
                      refine ⟨820950816485831936997277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4378404354591103663985477 820950816485831936997277)
                      ·
                        rfl

theorem cell23_1598796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1598796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598796 prefixEnd_1598796 := by exact prefixLift 1598796
  have htrace : WordTrace (prefixWord ++ tailWord_1598796) baseStart_1598796 baseEnd_1598796 := by
    simpa [prefixWord, tailWord_1598796, baseEnd_1598796] using wordTrace_append hprefix tailTrace_1598796
  have hstable : (prefixWord ++ tailWord_1598796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598796).length < 2 ^ (prefixWord ++ tailWord_1598796).sum := by decide
  have hdescent : baseEnd_1598796 < baseStart_1598796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598809 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1598809 : Nat := 118140960795 + 1598809 * 2 ^ 59
def prefixEnd_1598809 : Nat := 4983230072969 + 3 ^ 40 * 1598809 * 2
def baseEnd_1598809 : Nat := 820957491734340386134717

theorem tailTrace_1598809 : CollatzResearch.WordTrace tailWord_1598809 prefixEnd_1598809 820957491734340386134717 := by
  unfold tailWord_1598809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58313354864795522683303481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38875569909863681788868987 58313354864795522683303481)
  ·
    refine ⟨43735016148596642012477611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58313354864795522683303481 43735016148596642012477611)
    ·
      refine ⟨65602524222894963018716417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43735016148596642012477611 65602524222894963018716417)
      ·
        refine ⟨49201893167171222264037313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65602524222894963018716417 49201893167171222264037313)
        ·
          refine ⟨36901419875378416698027985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49201893167171222264037313 36901419875378416698027985)
          ·
            refine ⟨27676064906533812523520989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36901419875378416698027985 27676064906533812523520989)
            ·
              refine ⟨10378524339950179696320371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27676064906533812523520989 10378524339950179696320371)
              ·
                refine ⟨15567786509925269544480557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378524339950179696320371 15567786509925269544480557)
                ·
                  refine ⟨5837919941221976079180209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15567786509925269544480557 5837919941221976079180209)
                  ·
                    refine ⟨4378439955916482059385157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5837919941221976079180209 4378439955916482059385157)
                    ·
                      refine ⟨820957491734340386134717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4378439955916482059385157 820957491734340386134717)
                      ·
                        rfl

theorem cell23_1598809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1598809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598809 prefixEnd_1598809 := by exact prefixLift 1598809
  have htrace : WordTrace (prefixWord ++ tailWord_1598809) baseStart_1598809 baseEnd_1598809 := by
    simpa [prefixWord, tailWord_1598809, baseEnd_1598809] using wordTrace_append hprefix tailTrace_1598809
  have hstable : (prefixWord ++ tailWord_1598809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598809).length < 2 ^ (prefixWord ++ tailWord_1598809).sum := by decide
  have hdescent : baseEnd_1598809 < baseStart_1598809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598816 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1598816 : Nat := 118140960795 + 1598816 * 2 ^ 59
def prefixEnd_1598816 : Nat := 4983230072969 + 3 ^ 40 * 1598816 * 2
def baseEnd_1598816 : Nat := 820961086098921858747185

theorem tailTrace_1598816 : CollatzResearch.WordTrace tailWord_1598816 prefixEnd_1598816 820961086098921858747185 := by
  unfold tailWord_1598816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156805087885081439404151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38875740117180108585872201 29156805087885081439404151)
  ·
    refine ⟨43735207631827622159106227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29156805087885081439404151 43735207631827622159106227)
    ·
      refine ⟨65602811447741433238659341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43735207631827622159106227 65602811447741433238659341)
      ·
        refine ⟨24601054292903037464497253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65602811447741433238659341 24601054292903037464497253)
        ·
          refine ⟨4612697679919319524593235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24601054292903037464497253 4612697679919319524593235)
          ·
            refine ⟨6919046519878979286889853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612697679919319524593235 6919046519878979286889853)
            ·
              refine ⟨2594642444954617232583695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6919046519878979286889853 2594642444954617232583695)
              ·
                refine ⟨3891963667431925848875543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594642444954617232583695 3891963667431925848875543)
                ·
                  refine ⟨5837945501147888773313315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891963667431925848875543 5837945501147888773313315)
                  ·
                    refine ⟨8756918251721833159969973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837945501147888773313315 8756918251721833159969973)
                    ·
                      refine ⟨820961086098921858747185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8756918251721833159969973 820961086098921858747185)
                      ·
                        rfl

theorem cell23_1598816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1598816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598816 prefixEnd_1598816 := by exact prefixLift 1598816
  have htrace : WordTrace (prefixWord ++ tailWord_1598816) baseStart_1598816 baseEnd_1598816 := by
    simpa [prefixWord, tailWord_1598816, baseEnd_1598816] using wordTrace_append hprefix tailTrace_1598816
  have hstable : (prefixWord ++ tailWord_1598816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598816).length < 2 ^ (prefixWord ++ tailWord_1598816).sum := by decide
  have hdescent : baseEnd_1598816 < baseStart_1598816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598824 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1598824 : Nat := 118140960795 + 1598824 * 2 ^ 59
def prefixEnd_1598824 : Nat := 4983230072969 + 3 ^ 40 * 1598824 * 2
def baseEnd_1598824 : Nat := 820965193944157827447149

theorem tailTrace_1598824 : CollatzResearch.WordTrace tailWord_1598824 prefixEnd_1598824 820965193944157827447149 := by
  unfold tailWord_1598824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156950979870590122549763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38875934639827453496733017 29156950979870590122549763)
  ·
    refine ⟨43735426469805885183824645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29156950979870590122549763 43735426469805885183824645)
    ·
      refine ⟨8200392463088603471967121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43735426469805885183824645 8200392463088603471967121)
      ·
        refine ⟨6150294347316452603975341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8200392463088603471967121 6150294347316452603975341)
        ·
          refine ⟨2306360380243669726490753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6150294347316452603975341 2306360380243669726490753)
          ·
            refine ⟨1729770285182752294868065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306360380243669726490753 1729770285182752294868065)
            ·
              refine ⟨1297327713887064221151049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729770285182752294868065 1297327713887064221151049)
              ·
                refine ⟨972995785415298165863287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297327713887064221151049 972995785415298165863287)
                ·
                  refine ⟨1459493678122947248794931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972995785415298165863287 1459493678122947248794931)
                  ·
                    refine ⟨2189240517184420873192397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459493678122947248794931 2189240517184420873192397)
                    ·
                      refine ⟨820965193944157827447149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189240517184420873192397 820965193944157827447149)
                      ·
                        rfl

theorem cell23_1598824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1598824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598824 prefixEnd_1598824 := by exact prefixLift 1598824
  have htrace : WordTrace (prefixWord ++ tailWord_1598824) baseStart_1598824 baseEnd_1598824 := by
    simpa [prefixWord, tailWord_1598824, baseEnd_1598824] using wordTrace_append hprefix tailTrace_1598824
  have hstable : (prefixWord ++ tailWord_1598824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598824).length < 2 ^ (prefixWord ++ tailWord_1598824).sum := by decide
  have hdescent : baseEnd_1598824 < baseStart_1598824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598850 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1598850 : Nat := 118140960795 + 1598850 * 2 ^ 59
def prefixEnd_1598850 : Nat := 4983230072969 + 3 ^ 40 * 1598850 * 2
def baseEnd_1598850 : Nat := 820978544441174725722029

theorem tailTrace_1598850 : CollatzResearch.WordTrace tailWord_1598850 prefixEnd_1598850 820978544441174725722029 := by
  unfold tailWord_1598850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578712564411746671386501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38876566838431324457030669 14578712564411746671386501)
  ·
    refine ⟨2733508605827202500884969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14578712564411746671386501 2733508605827202500884969)
    ·
      refine ⟨2050131454370401875663727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733508605827202500884969 2050131454370401875663727)
      ·
        refine ⟨3075197181555602813495591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050131454370401875663727 3075197181555602813495591)
        ·
          refine ⟨4612795772333404220243387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075197181555602813495591 4612795772333404220243387)
          ·
            refine ⟨6919193658500106330365081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612795772333404220243387 6919193658500106330365081)
            ·
              refine ⟨5189395243875079747773811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919193658500106330365081 5189395243875079747773811)
              ·
                refine ⟨7784092865812619621660717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189395243875079747773811 7784092865812619621660717)
                ·
                  refine ⟨2919034824679732358122769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7784092865812619621660717 2919034824679732358122769)
                  ·
                    refine ⟨2189276118509799268592077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919034824679732358122769 2189276118509799268592077)
                    ·
                      refine ⟨820978544441174725722029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189276118509799268592077 820978544441174725722029)
                      ·
                        rfl

theorem cell23_1598850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1598850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598850 prefixEnd_1598850 := by exact prefixLift 1598850
  have htrace : WordTrace (prefixWord ++ tailWord_1598850) baseStart_1598850 baseEnd_1598850 := by
    simpa [prefixWord, tailWord_1598850, baseEnd_1598850] using wordTrace_append hprefix tailTrace_1598850
  have hstable : (prefixWord ++ tailWord_1598850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598850).length < 2 ^ (prefixWord ++ tailWord_1598850).sum := by decide
  have hdescent : baseEnd_1598850 < baseStart_1598850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598859 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_1598859 : Nat := 118140960795 + 1598859 * 2 ^ 59
def prefixEnd_1598859 : Nat := 4983230072969 + 3 ^ 40 * 1598859 * 2
def baseEnd_1598859 : Nat := 820983165767065190509487

theorem tailTrace_1598859 : CollatzResearch.WordTrace tailWord_1598859 prefixEnd_1598859 820983165767065190509487 := by
  unfold tailWord_1598859
  simp only [CollatzResearch.WordTrace]
  refine ⟨58315178514614381222623631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38876785676409587481749087 58315178514614381222623631)
  ·
    refine ⟨87472767771921571833935447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58315178514614381222623631 87472767771921571833935447)
    ·
      refine ⟨131209151657882357750903171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87472767771921571833935447 131209151657882357750903171)
      ·
        refine ⟨196813727486823536626354757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131209151657882357750903171 196813727486823536626354757)
        ·
          refine ⟨36902573903779413117441517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196813727486823536626354757 36902573903779413117441517)
          ·
            refine ⟨13838465213917279919040569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36902573903779413117441517 13838465213917279919040569)
            ·
              refine ⟨10378848910437959939280427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13838465213917279919040569 10378848910437959939280427)
              ·
                refine ⟨15568273365656939908920641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378848910437959939280427 15568273365656939908920641)
                ·
                  refine ⟨11676205024242704931690481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15568273365656939908920641 11676205024242704931690481)
                  ·
                    refine ⟨8757153768182028698767861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11676205024242704931690481 8757153768182028698767861)
                    ·
                      refine ⟨820983165767065190509487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8757153768182028698767861 820983165767065190509487)
                      ·
                        rfl

theorem cell23_1598859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_1598859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598859 prefixEnd_1598859 := by exact prefixLift 1598859
  have htrace : WordTrace (prefixWord ++ tailWord_1598859) baseStart_1598859 baseEnd_1598859 := by
    simpa [prefixWord, tailWord_1598859, baseEnd_1598859] using wordTrace_append hprefix tailTrace_1598859
  have hstable : (prefixWord ++ tailWord_1598859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598859).length < 2 ^ (prefixWord ++ tailWord_1598859).sum := by decide
  have hdescent : baseEnd_1598859 < baseStart_1598859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598889 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_1598889 : Nat := 118140960795 + 1598889 * 2 ^ 59
def prefixEnd_1598889 : Nat := 4983230072969 + 3 ^ 40 * 1598889 * 2
def baseEnd_1598889 : Nat := 820998570186700073134349

theorem tailTrace_1598889 : CollatzResearch.WordTrace tailWord_1598889 prefixEnd_1598889 820998570186700073134349 := by
  unfold tailWord_1598889
  simp only [CollatzResearch.WordTrace]
  refine ⟨58316272704505696346215721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38877515136337130897477147 58316272704505696346215721)
  ·
    refine ⟨43737204528379272259661791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58316272704505696346215721 43737204528379272259661791)
    ·
      refine ⟨65605806792568908389492687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43737204528379272259661791 65605806792568908389492687)
      ·
        refine ⟨98408710188853362584239031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65605806792568908389492687 98408710188853362584239031)
        ·
          refine ⟨147613065283280043876358547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98408710188853362584239031 147613065283280043876358547)
          ·
            refine ⟨221419597924920065814537821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147613065283280043876358547 221419597924920065814537821)
            ·
              refine ⟨83032349221845024680451683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221419597924920065814537821 83032349221845024680451683)
              ·
                refine ⟨124548523832767537020677525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83032349221845024680451683 124548523832767537020677525)
                ·
                  refine ⟨5838212054660978297844259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124548523832767537020677525 5838212054660978297844259)
                  ·
                    refine ⟨8757318081991467446766389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838212054660978297844259 8757318081991467446766389)
                    ·
                      refine ⟨820998570186700073134349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8757318081991467446766389 820998570186700073134349)
                      ·
                        rfl

theorem cell23_1598889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_1598889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598889 prefixEnd_1598889 := by exact prefixLift 1598889
  have htrace : WordTrace (prefixWord ++ tailWord_1598889) baseStart_1598889 baseEnd_1598889 := by
    simpa [prefixWord, tailWord_1598889, baseEnd_1598889] using wordTrace_append hprefix tailTrace_1598889
  have hstable : (prefixWord ++ tailWord_1598889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598889).length < 2 ^ (prefixWord ++ tailWord_1598889).sum := by decide
  have hdescent : baseEnd_1598889 < baseStart_1598889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598929 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1598929 : Nat := 118140960795 + 1598929 * 2 ^ 59
def prefixEnd_1598929 : Nat := 4983230072969 + 3 ^ 40 * 1598929 * 2
def baseEnd_1598929 : Nat := 821019109412879916634165

theorem tailTrace_1598929 : CollatzResearch.WordTrace tailWord_1598929 prefixEnd_1598929 821019109412879916634165 := by
  unfold tailWord_1598929
  simp only [CollatzResearch.WordTrace]
  refine ⟨58317731624360783177671841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38878487749573855451781227 58317731624360783177671841)
  ·
    refine ⟨43738298718270587383253881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58317731624360783177671841 43738298718270587383253881)
    ·
      refine ⟨32803724038702940537440411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43738298718270587383253881 32803724038702940537440411)
      ·
        refine ⟨49205586058054410806160617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32803724038702940537440411 49205586058054410806160617)
        ·
          refine ⟨36904189543540808104620463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49205586058054410806160617 36904189543540808104620463)
          ·
            refine ⟨55356284315311212156930695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36904189543540808104620463 55356284315311212156930695)
            ·
              refine ⟨83034426472966818235396043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55356284315311212156930695 83034426472966818235396043)
              ·
                refine ⟨124551639709450227353094065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83034426472966818235396043 124551639709450227353094065)
                ·
                  refine ⟨93413729782087670514820549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124551639709450227353094065 93413729782087670514820549)
                  ·
                    refine ⟨17515074334141438221528853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93413729782087670514820549 17515074334141438221528853)
                    ·
                      refine ⟨821019109412879916634165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17515074334141438221528853 821019109412879916634165)
                      ·
                        rfl

theorem cell23_1598929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1598929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598929 prefixEnd_1598929 := by exact prefixLift 1598929
  have htrace : WordTrace (prefixWord ++ tailWord_1598929) baseStart_1598929 baseEnd_1598929 := by
    simpa [prefixWord, tailWord_1598929, baseEnd_1598929] using wordTrace_append hprefix tailTrace_1598929
  have hstable : (prefixWord ++ tailWord_1598929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598929).length < 2 ^ (prefixWord ++ tailWord_1598929).sum := by decide
  have hdescent : baseEnd_1598929 < baseStart_1598929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598936 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1598936 : Nat := 118140960795 + 1598936 * 2 ^ 59
def prefixEnd_1598936 : Nat := 4983230072969 + 3 ^ 40 * 1598936 * 2
def baseEnd_1598936 : Nat := 821022703777461389246633

theorem tailTrace_1598936 : CollatzResearch.WordTrace tailWord_1598936 prefixEnd_1598936 821022703777461389246633 := by
  unfold tailWord_1598936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158993467667711686588331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38878657956890282248784441 29158993467667711686588331)
  ·
    refine ⟨43738490201501567529882497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29158993467667711686588331 43738490201501567529882497)
    ·
      refine ⟨32803867651126175647411873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43738490201501567529882497 32803867651126175647411873)
      ·
        refine ⟨24602900738344631735558905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32803867651126175647411873 24602900738344631735558905)
        ·
          refine ⟨18452175553758473801669179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24602900738344631735558905 18452175553758473801669179)
          ·
            refine ⟨27678263330637710702503769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18452175553758473801669179 27678263330637710702503769)
            ·
              refine ⟨20758697497978283026877827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27678263330637710702503769 20758697497978283026877827)
              ·
                refine ⟨31138046246967424540316741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758697497978283026877827 31138046246967424540316741)
                ·
                  refine ⟨5838383671306392101309389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31138046246967424540316741 5838383671306392101309389)
                  ·
                    refine ⟨2189393876739897037991021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5838383671306392101309389 2189393876739897037991021)
                    ·
                      refine ⟨821022703777461389246633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189393876739897037991021 821022703777461389246633)
                      ·
                        rfl

theorem cell23_1598936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1598936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598936 prefixEnd_1598936 := by exact prefixLift 1598936
  have htrace : WordTrace (prefixWord ++ tailWord_1598936) baseStart_1598936 baseEnd_1598936 := by
    simpa [prefixWord, tailWord_1598936, baseEnd_1598936] using wordTrace_append hprefix tailTrace_1598936
  have hstable : (prefixWord ++ tailWord_1598936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598936).length < 2 ^ (prefixWord ++ tailWord_1598936).sum := by decide
  have hdescent : baseEnd_1598936 < baseStart_1598936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598973 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1598973 : Nat := 118140960795 + 1598973 * 2 ^ 59
def prefixEnd_1598973 : Nat := 4983230072969 + 3 ^ 40 * 1598973 * 2
def baseEnd_1598973 : Nat := 273680567520559248161321

theorem tailTrace_1598973 : CollatzResearch.WordTrace tailWord_1598973 prefixEnd_1598973 273680567520559248161321 := by
  unfold tailWord_1598973
  simp only [CollatzResearch.WordTrace]
  refine ⟨58319336436201378692273573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38879557624134252461515715 58319336436201378692273573)
  ·
    refine ⟨10934875581787758504801295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58319336436201378692273573 10934875581787758504801295)
    ·
      refine ⟨16402313372681637757201943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934875581787758504801295 16402313372681637757201943)
      ·
        refine ⟨24603470059022456635802915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16402313372681637757201943 24603470059022456635802915)
        ·
          refine ⟨36905205088533684953704373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24603470059022456635802915 36905205088533684953704373)
          ·
            refine ⟨3459862977050032964409785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36905205088533684953704373 3459862977050032964409785)
            ·
              refine ⟨2594897232787524723307339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459862977050032964409785 2594897232787524723307339)
              ·
                refine ⟨3892345849181287084961009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594897232787524723307339 3892345849181287084961009)
                ·
                  refine ⟨2919259386885965313720757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892345849181287084961009 2919259386885965313720757)
                  ·
                    refine ⟨273680567520559248161321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2919259386885965313720757 273680567520559248161321)
                    ·
                      rfl

theorem cell23_1598973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1598973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598973 prefixEnd_1598973 := by exact prefixLift 1598973
  have htrace : WordTrace (prefixWord ++ tailWord_1598973) baseStart_1598973 baseEnd_1598973 := by
    simpa [prefixWord, tailWord_1598973, baseEnd_1598973] using wordTrace_append hprefix tailTrace_1598973
  have hstable : (prefixWord ++ tailWord_1598973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598973).length < 2 ^ (prefixWord ++ tailWord_1598973).sum := by decide
  have hdescent : baseEnd_1598973 < baseStart_1598973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598993 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_1598993 : Nat := 118140960795 + 1598993 * 2 ^ 59
def prefixEnd_1598993 : Nat := 4983230072969 + 3 ^ 40 * 1598993 * 2
def baseEnd_1598993 : Nat := 821051972174767666233871

theorem tailTrace_1598993 : CollatzResearch.WordTrace tailWord_1598993 prefixEnd_1598993 821051972174767666233871 := by
  unfold tailWord_1598993
  simp only [CollatzResearch.WordTrace]
  refine ⟨58320065896128922108001633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38880043930752614738667755 58320065896128922108001633)
  ·
    refine ⟨43740049422096691581001225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58320065896128922108001633 43740049422096691581001225)
    ·
      refine ⟨32805037066572518685750919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43740049422096691581001225 32805037066572518685750919)
      ·
        refine ⟨49207555599858778028626379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32805037066572518685750919 49207555599858778028626379)
        ·
          refine ⟨73811333399788167042939569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49207555599858778028626379 73811333399788167042939569)
          ·
            refine ⟨55358500049841125282204677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73811333399788167042939569 55358500049841125282204677)
            ·
              refine ⟨10379718759345210990413377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55358500049841125282204677 10379718759345210990413377)
              ·
                refine ⟨7784789069508908242810033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10379718759345210990413377 7784789069508908242810033)
                ·
                  refine ⟨5838591802131681182107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7784789069508908242810033 5838591802131681182107525)
                  ·
                    refine ⟨1094735962899690221645161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838591802131681182107525 1094735962899690221645161)
                    ·
                      refine ⟨821051972174767666233871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094735962899690221645161 821051972174767666233871)
                      ·
                        rfl

theorem cell23_1598993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_1598993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1598993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1598993 prefixEnd_1598993 := by exact prefixLift 1598993
  have htrace : WordTrace (prefixWord ++ tailWord_1598993) baseStart_1598993 baseEnd_1598993 := by
    simpa [prefixWord, tailWord_1598993, baseEnd_1598993] using wordTrace_append hprefix tailTrace_1598993
  have hstable : (prefixWord ++ tailWord_1598993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598993).length < 2 ^ (prefixWord ++ tailWord_1598993).sum := by decide
  have hdescent : baseEnd_1598993 < baseStart_1598993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599080 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1599080 : Nat := 118140960795 + 1599080 * 2 ^ 59
def prefixEnd_1599080 : Nat := 4983230072969 + 3 ^ 40 * 1599080 * 2
def baseEnd_1599080 : Nat := 273698881663902941948657

theorem tailTrace_1599080 : CollatzResearch.WordTrace tailWord_1599080 prefixEnd_1599080 273698881663902941948657 := by
  unfold tailWord_1599080
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161619523406867983209347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38882159364542490644279129 29161619523406867983209347)
  ·
    refine ⟨43742429285110301974814021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29161619523406867983209347 43742429285110301974814021)
    ·
      refine ⟨8201705490958181620277629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43742429285110301974814021 8201705490958181620277629)
      ·
        refine ⟨3075639559109318107604111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8201705490958181620277629 3075639559109318107604111)
        ·
          refine ⟨4613459338663977161406167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075639559109318107604111 4613459338663977161406167)
          ·
            refine ⟨6920189007995965742109251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613459338663977161406167 6920189007995965742109251)
            ·
              refine ⟨10380283511993948613163877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920189007995965742109251 10380283511993948613163877)
              ·
                refine ⟨1946303158498865364968227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10380283511993948613163877 1946303158498865364968227)
                ·
                  refine ⟨2919454737748298047452341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946303158498865364968227 2919454737748298047452341)
                  ·
                    refine ⟨273698881663902941948657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2919454737748298047452341 273698881663902941948657)
                    ·
                      rfl

theorem cell23_1599080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1599080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599080 prefixEnd_1599080 := by exact prefixLift 1599080
  have htrace : WordTrace (prefixWord ++ tailWord_1599080) baseStart_1599080 baseEnd_1599080 := by
    simpa [prefixWord, tailWord_1599080, baseEnd_1599080] using wordTrace_append hprefix tailTrace_1599080
  have hstable : (prefixWord ++ tailWord_1599080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599080).length < 2 ^ (prefixWord ++ tailWord_1599080).sum := by decide
  have hdescent : baseEnd_1599080 < baseStart_1599080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599096 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1599096 : Nat := 118140960795 + 1599096 * 2 ^ 59
def prefixEnd_1599096 : Nat := 4983230072969 + 3 ^ 40 * 1599096 * 2
def baseEnd_1599096 : Nat := 821104860682180763245897

theorem tailTrace_1599096 : CollatzResearch.WordTrace tailWord_1599096 prefixEnd_1599096 821104860682180763245897 := by
  unfold tailWord_1599096
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161911307377885349500571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38882548409837180466000761 29161911307377885349500571)
  ·
    refine ⟨43742866961066828024250857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29161911307377885349500571 43742866961066828024250857)
    ·
      refine ⟨32807150220800121018188143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43742866961066828024250857 32807150220800121018188143)
      ·
        refine ⟨49210725331200181527282215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32807150220800121018188143 49210725331200181527282215)
        ·
          refine ⟨73816087996800272290923323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49210725331200181527282215 73816087996800272290923323)
          ·
            refine ⟨110724131995200408436384985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73816087996800272290923323 110724131995200408436384985)
            ·
              refine ⟨83043098996400306327288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110724131995200408436384985 83043098996400306327288739)
              ·
                refine ⟨124564648494600459490933109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83043098996400306327288739 124564648494600459490933109)
                ·
                  refine ⟨11677935796368793077274979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124564648494600459490933109 11677935796368793077274979)
                  ·
                    refine ⟨17516903694553189615912469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11677935796368793077274979 17516903694553189615912469)
                    ·
                      refine ⟨821104860682180763245897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17516903694553189615912469 821104860682180763245897)
                      ·
                        rfl

theorem cell23_1599096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1599096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599096 prefixEnd_1599096 := by exact prefixLift 1599096
  have htrace : WordTrace (prefixWord ++ tailWord_1599096) baseStart_1599096 baseEnd_1599096 := by
    simpa [prefixWord, tailWord_1599096, baseEnd_1599096] using wordTrace_append hprefix tailTrace_1599096
  have hstable : (prefixWord ++ tailWord_1599096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599096).length < 2 ^ (prefixWord ++ tailWord_1599096).sum := by decide
  have hdescent : baseEnd_1599096 < baseStart_1599096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599127 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 2, 4]
def baseStart_1599127 : Nat := 118140960795 + 1599127 * 2 ^ 59
def prefixEnd_1599127 : Nat := 4983230072969 + 3 ^ 40 * 1599127 * 2
def baseEnd_1599127 : Nat := 273706926194156713986085

theorem tailTrace_1599127 : CollatzResearch.WordTrace tailWord_1599127 prefixEnd_1599127 273706926194156713986085 := by
  unfold tailWord_1599127
  simp only [CollatzResearch.WordTrace]
  refine ⟨58324953277643462993379635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38883302185095641995586423 58324953277643462993379635)
  ·
    refine ⟨87487429916465194490069453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58324953277643462993379635 87487429916465194490069453)
    ·
      refine ⟨32807786218674447933776045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87487429916465194490069453 32807786218674447933776045)
      ·
        refine ⟨12302919832002917975166017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32807786218674447933776045 12302919832002917975166017)
        ·
          refine ⟨9227189874002188481374513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12302919832002917975166017 9227189874002188481374513)
          ·
            refine ⟨6920392405501641361030885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9227189874002188481374513 6920392405501641361030885)
            ·
              refine ⟨1297573576031557755193291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6920392405501641361030885 1297573576031557755193291)
              ·
                refine ⟨1946360364047336632789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297573576031557755193291 1946360364047336632789937)
                ·
                  refine ⟨1459770273035502474592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946360364047336632789937 1459770273035502474592453)
                  ·
                    refine ⟨273706926194156713986085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459770273035502474592453 273706926194156713986085)
                    ·
                      rfl

theorem cell23_1599127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_1599127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599127 prefixEnd_1599127 := by exact prefixLift 1599127
  have htrace : WordTrace (prefixWord ++ tailWord_1599127) baseStart_1599127 baseEnd_1599127 := by
    simpa [prefixWord, tailWord_1599127, baseEnd_1599127] using wordTrace_append hprefix tailTrace_1599127
  have hstable : (prefixWord ++ tailWord_1599127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599127).length < 2 ^ (prefixWord ++ tailWord_1599127).sum := by decide
  have hdescent : baseEnd_1599127 < baseStart_1599127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599134 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1599134 : Nat := 118140960795 + 1599134 * 2 ^ 59
def prefixEnd_1599134 : Nat := 4983230072969 + 3 ^ 40 * 1599134 * 2
def baseEnd_1599134 : Nat := 821124372947051614570723

theorem tailTrace_1599134 : CollatzResearch.WordTrace tailWord_1599134 prefixEnd_1599134 821124372947051614570723 := by
  unfold tailWord_1599134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290651073577262898610557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38883472392412068792589637 7290651073577262898610557)
  ·
    refine ⟨2733994152591473586978959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7290651073577262898610557 2733994152591473586978959)
    ·
      refine ⟨4100991228887210380468439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733994152591473586978959 4100991228887210380468439)
      ·
        refine ⟨6151486843330815570702659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100991228887210380468439 6151486843330815570702659)
        ·
          refine ⟨9227230264996223356053989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151486843330815570702659 9227230264996223356053989)
          ·
            refine ⟨1730105674686791879260123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9227230264996223356053989 1730105674686791879260123)
            ·
              refine ⟨2595158512030187818890185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730105674686791879260123 2595158512030187818890185)
              ·
                refine ⟨1946368884022640864167639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595158512030187818890185 1946368884022640864167639)
                ·
                  refine ⟨2919553326033961296251459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946368884022640864167639 2919553326033961296251459)
                  ·
                    refine ⟨4379329989050941944377189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2919553326033961296251459 4379329989050941944377189)
                    ·
                      refine ⟨821124372947051614570723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4379329989050941944377189 821124372947051614570723)
                      ·
                        rfl

theorem cell23_1599134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1599134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599134 prefixEnd_1599134 := by exact prefixLift 1599134
  have htrace : WordTrace (prefixWord ++ tailWord_1599134) baseStart_1599134 baseEnd_1599134 := by
    simpa [prefixWord, tailWord_1599134, baseEnd_1599134] using wordTrace_append hprefix tailTrace_1599134
  have hstable : (prefixWord ++ tailWord_1599134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599134).length < 2 ^ (prefixWord ++ tailWord_1599134).sum := by decide
  have hdescent : baseEnd_1599134 < baseStart_1599134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599137 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1599137 : Nat := 118140960795 + 1599137 * 2 ^ 59
def prefixEnd_1599137 : Nat := 4983230072969 + 3 ^ 40 * 1599137 * 2
def baseEnd_1599137 : Nat := 821125913389015102833209

theorem tailTrace_1599137 : CollatzResearch.WordTrace tailWord_1599137 prefixEnd_1599137 821125913389015102833209 := by
  unfold tailWord_1599137
  simp only [CollatzResearch.WordTrace]
  refine ⟨58325318007607234701243665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38883545338404823134162443 58325318007607234701243665)
  ·
    refine ⟨43743988505705426025932749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58325318007607234701243665 43743988505705426025932749)
    ·
      refine ⟨16403995689639534759724781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43743988505705426025932749 16403995689639534759724781)
      ·
        refine ⟨6151498383614825534896793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16403995689639534759724781 6151498383614825534896793)
        ·
          refine ⟨4613623787711119151172595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151498383614825534896793 4613623787711119151172595)
          ·
            refine ⟨6920435681566678726758893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613623787711119151172595 6920435681566678726758893)
            ·
              refine ⟨2595163380587504522534585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6920435681566678726758893 2595163380587504522534585)
              ·
                refine ⟨1946372535440628391900939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595163380587504522534585 1946372535440628391900939)
                ·
                  refine ⟨2919558803160942587851409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946372535440628391900939 2919558803160942587851409)
                  ·
                    refine ⟨2189669102370706940888557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919558803160942587851409 2189669102370706940888557)
                    ·
                      refine ⟨821125913389015102833209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189669102370706940888557 821125913389015102833209)
                      ·
                        rfl

theorem cell23_1599137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1599137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599137 prefixEnd_1599137 := by exact prefixLift 1599137
  have htrace : WordTrace (prefixWord ++ tailWord_1599137) baseStart_1599137 baseEnd_1599137 := by
    simpa [prefixWord, tailWord_1599137, baseEnd_1599137] using wordTrace_append hprefix tailTrace_1599137
  have hstable : (prefixWord ++ tailWord_1599137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599137).length < 2 ^ (prefixWord ++ tailWord_1599137).sum := by decide
  have hdescent : baseEnd_1599137 < baseStart_1599137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599144 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1599144 : Nat := 118140960795 + 1599144 * 2 ^ 59
def prefixEnd_1599144 : Nat := 4983230072969 + 3 ^ 40 * 1599144 * 2
def baseEnd_1599144 : Nat := 273709835917865525148559

theorem tailTrace_1599144 : CollatzResearch.WordTrace tailWord_1599144 prefixEnd_1599144 273709835917865525148559 := by
  unfold tailWord_1599144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162786659290937448374243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38883715545721249931165657 29162786659290937448374243)
  ·
    refine ⟨43744179988936406172561365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162786659290937448374243 43744179988936406172561365)
    ·
      refine ⟨1025254218490697019669407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43744179988936406172561365 1025254218490697019669407)
      ·
        refine ⟨1537881327736045529504111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025254218490697019669407 1537881327736045529504111)
        ·
          refine ⟨2306821991604068294256167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537881327736045529504111 2306821991604068294256167)
          ·
            refine ⟨3460232987406102441384251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306821991604068294256167 3460232987406102441384251)
            ·
              refine ⟨5190349481109153662076377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460232987406102441384251 5190349481109153662076377)
              ·
                refine ⟨3892762110831865246557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190349481109153662076377 3892762110831865246557283)
                ·
                  refine ⟨5839143166247797869835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892762110831865246557283 5839143166247797869835925)
                  ·
                    refine ⟨273709835917865525148559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5839143166247797869835925 273709835917865525148559)
                    ·
                      rfl

theorem cell23_1599144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1599144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599144 prefixEnd_1599144 := by exact prefixLift 1599144
  have htrace : WordTrace (prefixWord ++ tailWord_1599144) baseStart_1599144 baseEnd_1599144 := by
    simpa [prefixWord, tailWord_1599144, baseEnd_1599144] using wordTrace_append hprefix tailTrace_1599144
  have hstable : (prefixWord ++ tailWord_1599144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599144).length < 2 ^ (prefixWord ++ tailWord_1599144).sum := by decide
  have hdescent : baseEnd_1599144 < baseStart_1599144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599167 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_1599167 : Nat := 118140960795 + 1599167 * 2 ^ 59
def prefixEnd_1599167 : Nat := 4983230072969 + 3 ^ 40 * 1599167 * 2
def baseEnd_1599167 : Nat := 821141317808649985458071

theorem tailTrace_1599167 : CollatzResearch.WordTrace tailWord_1599167 prefixEnd_1599167 821141317808649985458071 := by
  unfold tailWord_1599167
  simp only [CollatzResearch.WordTrace]
  refine ⟨58326412197498549824835755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38884274798332366549890503 58326412197498549824835755)
  ·
    refine ⟨87489618296247824737253633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58326412197498549824835755 87489618296247824737253633)
    ·
      refine ⟨65617213722185868552940225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87489618296247824737253633 65617213722185868552940225)
      ·
        refine ⟨49212910291639401414705169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65617213722185868552940225 49212910291639401414705169)
        ·
          refine ⟨36909682718729551061028877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49212910291639401414705169 36909682718729551061028877)
          ·
            refine ⟨13841131019523581647885829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36909682718729551061028877 13841131019523581647885829)
            ·
              refine ⟨2595212066160671558978593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13841131019523581647885829 2595212066160671558978593)
              ·
                refine ⟨1946409049620503669233945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595212066160671558978593 1946409049620503669233945)
                ·
                  refine ⟨1459806787215377751925459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946409049620503669233945 1459806787215377751925459)
                  ·
                    refine ⟨2189710180823066627888189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459806787215377751925459 2189710180823066627888189)
                    ·
                      refine ⟨821141317808649985458071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189710180823066627888189 821141317808649985458071)
                      ·
                        rfl

theorem cell23_1599167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_1599167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599167 prefixEnd_1599167 := by exact prefixLift 1599167
  have htrace : WordTrace (prefixWord ++ tailWord_1599167) baseStart_1599167 baseEnd_1599167 := by
    simpa [prefixWord, tailWord_1599167, baseEnd_1599167] using wordTrace_append hprefix tailTrace_1599167
  have hstable : (prefixWord ++ tailWord_1599167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599167).length < 2 ^ (prefixWord ++ tailWord_1599167).sum := by decide
  have hdescent : baseEnd_1599167 < baseStart_1599167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599174 : List Nat := [6, 1, 2, 1, 1, 3, 1, 8]
def baseStart_1599174 : Nat := 118140960795 + 1599174 * 2 ^ 59
def prefixEnd_1599174 : Nat := 4983230072969 + 3 ^ 40 * 1599174 * 2
def baseEnd_1599174 : Nat := 30412774524934498447057

theorem tailTrace_1599174 : CollatzResearch.WordTrace tailWord_1599174 prefixEnd_1599174 30412774524934498447057 := by
  unfold tailWord_1599174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822708359639787188135643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38884445005648793346893717 1822708359639787188135643)
  ·
    refine ⟨2734062539459680782203465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822708359639787188135643 2734062539459680782203465)
    ·
      refine ⟨2050546904594760586652599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2734062539459680782203465 2050546904594760586652599)
      ·
        refine ⟨3075820356892140879978899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050546904594760586652599 3075820356892140879978899)
        ·
          refine ⟨4613730535338211319968349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075820356892140879978899 4613730535338211319968349)
          ·
            refine ⟨1730148950751829244988131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4613730535338211319968349 1730148950751829244988131)
            ·
              refine ⟨2595223426127743867482197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730148950751829244988131 2595223426127743867482197)
              ·
                refine ⟨30412774524934498447057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2595223426127743867482197 30412774524934498447057)
                ·
                  rfl

theorem cell23_1599174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_1599174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599174 prefixEnd_1599174 := by exact prefixLift 1599174
  have htrace : WordTrace (prefixWord ++ tailWord_1599174) baseStart_1599174 baseEnd_1599174 := by
    simpa [prefixWord, tailWord_1599174, baseEnd_1599174] using wordTrace_append hprefix tailTrace_1599174
  have hstable : (prefixWord ++ tailWord_1599174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599174).length < 2 ^ (prefixWord ++ tailWord_1599174).sum := by decide
  have hdescent : baseEnd_1599174 < baseStart_1599174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599240 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1599240 : Nat := 118140960795 + 1599240 * 2 ^ 59
def prefixEnd_1599240 : Nat := 4983230072969 + 3 ^ 40 * 1599240 * 2
def baseEnd_1599240 : Nat := 821178801896428199845235

theorem tailTrace_1599240 : CollatzResearch.WordTrace tailWord_1599240 prefixEnd_1599240 821178801896428199845235 := by
  unfold tailWord_1599240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164537363117041646121587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38886049817489388861495449 29164537363117041646121587)
  ·
    refine ⟨43746806044675562469182381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29164537363117041646121587 43746806044675562469182381)
    ·
      refine ⟨16405052266753335925943393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43746806044675562469182381 16405052266753335925943393)
      ·
        refine ⟨12303789200065001944457545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16405052266753335925943393 12303789200065001944457545)
        ·
          refine ⟨9227841900048751458343159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303789200065001944457545 9227841900048751458343159)
          ·
            refine ⟨13841762850073127187514739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227841900048751458343159 13841762850073127187514739)
            ·
              refine ⟨20762644275109690781272109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841762850073127187514739 20762644275109690781272109)
              ·
                refine ⟨7785991603166134042977041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20762644275109690781272109 7785991603166134042977041)
                ·
                  refine ⟨5839493702374600532232781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785991603166134042977041 5839493702374600532232781)
                  ·
                    refine ⟨2189810138390475199587293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5839493702374600532232781 2189810138390475199587293)
                    ·
                      refine ⟨821178801896428199845235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189810138390475199587293 821178801896428199845235)
                      ·
                        rfl

theorem cell23_1599240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1599240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599240 prefixEnd_1599240 := by exact prefixLift 1599240
  have htrace : WordTrace (prefixWord ++ tailWord_1599240) baseStart_1599240 baseEnd_1599240 := by
    simpa [prefixWord, tailWord_1599240, baseEnd_1599240] using wordTrace_append hprefix tailTrace_1599240
  have hstable : (prefixWord ++ tailWord_1599240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599240).length < 2 ^ (prefixWord ++ tailWord_1599240).sum := by decide
  have hdescent : baseEnd_1599240 < baseStart_1599240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599243 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 7]
def baseStart_1599243 : Nat := 118140960795 + 1599243 * 2 ^ 59
def prefixEnd_1599243 : Nat := 4983230072969 + 3 ^ 40 * 1599243 * 2
def baseEnd_1599243 : Nat := 273726780779463896035907

theorem tailTrace_1599243 : CollatzResearch.WordTrace tailWord_1599243 prefixEnd_1599243 273726780779463896035907 := by
  unfold tailWord_1599243
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329184145223214804602383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38886122763482143203068255 58329184145223214804602383)
  ·
    refine ⟨87493776217834822206903575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58329184145223214804602383 87493776217834822206903575)
    ·
      refine ⟨131240664326752233310355363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87493776217834822206903575 131240664326752233310355363)
      ·
        refine ⟨196860996490128349965533045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131240664326752233310355363 196860996490128349965533045)
        ·
          refine ⟨18455718420949532809268723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196860996490128349965533045 18455718420949532809268723)
          ·
            refine ⟨27683577631424299213903085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18455718420949532809268723 27683577631424299213903085)
            ·
              refine ⟨10381341611784112205213657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27683577631424299213903085 10381341611784112205213657)
              ·
                refine ⟨7786006208838084153910243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381341611784112205213657 7786006208838084153910243)
                ·
                  refine ⟨11679009313257126230865365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786006208838084153910243 11679009313257126230865365)
                  ·
                    refine ⟨273726780779463896035907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11679009313257126230865365 273726780779463896035907)
                    ·
                      rfl

theorem cell23_1599243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_1599243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599243 prefixEnd_1599243 := by exact prefixLift 1599243
  have htrace : WordTrace (prefixWord ++ tailWord_1599243) baseStart_1599243 baseEnd_1599243 := by
    simpa [prefixWord, tailWord_1599243, baseEnd_1599243] using wordTrace_append hprefix tailTrace_1599243
  have hstable : (prefixWord ++ tailWord_1599243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599243).length < 2 ^ (prefixWord ++ tailWord_1599243).sum := by decide
  have hdescent : baseEnd_1599243 < baseStart_1599243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599260 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1599260 : Nat := 118140960795 + 1599260 * 2 ^ 59
def prefixEnd_1599260 : Nat := 4983230072969 + 3 ^ 40 * 1599260 * 2
def baseEnd_1599260 : Nat := 273729690503172707198381

theorem tailTrace_1599260 : CollatzResearch.WordTrace tailWord_1599260 prefixEnd_1599260 273729690503172707198381 := by
  unfold tailWord_1599260
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164902093080813353985617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38886536124107751138647489 29164902093080813353985617)
  ·
    refine ⟨21873676569810610015489213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29164902093080813353985617 21873676569810610015489213)
    ·
      refine ⟨8202628713678978755808455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21873676569810610015489213 8202628713678978755808455)
      ·
        refine ⟨12303943070518468133712683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8202628713678978755808455 12303943070518468133712683)
        ·
          refine ⟨18455914605777702200569025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12303943070518468133712683 18455914605777702200569025)
          ·
            refine ⟨13841935954333276650426769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18455914605777702200569025 13841935954333276650426769)
            ·
              refine ⟨10381451965749957487820077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13841935954333276650426769 10381451965749957487820077)
              ·
                refine ⟨3893044487156234057932529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10381451965749957487820077 3893044487156234057932529)
                ·
                  refine ⟨2919783365367175543449397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893044487156234057932529 2919783365367175543449397)
                  ·
                    refine ⟨273729690503172707198381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2919783365367175543449397 273729690503172707198381)
                    ·
                      rfl

theorem cell23_1599260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1599260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599260 prefixEnd_1599260 := by exact prefixLift 1599260
  have htrace : WordTrace (prefixWord ++ tailWord_1599260) baseStart_1599260 baseEnd_1599260 := by
    simpa [prefixWord, tailWord_1599260, baseEnd_1599260] using wordTrace_append hprefix tailTrace_1599260
  have hstable : (prefixWord ++ tailWord_1599260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599260).length < 2 ^ (prefixWord ++ tailWord_1599260).sum := by decide
  have hdescent : baseEnd_1599260 < baseStart_1599260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599317 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1599317 : Nat := 118140960795 + 1599317 * 2 ^ 59
def prefixEnd_1599317 : Nat := 4983230072969 + 3 ^ 40 * 1599317 * 2
def baseEnd_1599317 : Nat := 821218339906824398582381

theorem tailTrace_1599317 : CollatzResearch.WordTrace tailWord_1599317 prefixEnd_1599317 821218339906824398582381 := by
  unfold tailWord_1599317
  simp only [CollatzResearch.WordTrace]
  refine ⟨58331883146955125442796205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38887922097970083628530803 58331883146955125442796205)
  ·
    refine ⟨21874456180108172041048577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58331883146955125442796205 21874456180108172041048577)
    ·
      refine ⟨16405842135081129030786433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21874456180108172041048577 16405842135081129030786433)
      ·
        refine ⟨12304381601310846773089825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16405842135081129030786433 12304381601310846773089825)
        ·
          refine ⟨9228286200983135079817369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12304381601310846773089825 9228286200983135079817369)
          ·
            refine ⟨6921214650737351309863027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9228286200983135079817369 6921214650737351309863027)
            ·
              refine ⟨10381821976106026964794541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921214650737351309863027 10381821976106026964794541)
              ·
                refine ⟨3893183241039760111797953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10381821976106026964794541 3893183241039760111797953)
                ·
                  refine ⟨2919887430779820083848465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893183241039760111797953 2919887430779820083848465)
                  ·
                    refine ⟨2189915573084865062886349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919887430779820083848465 2189915573084865062886349)
                    ·
                      refine ⟨821218339906824398582381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189915573084865062886349 821218339906824398582381)
                      ·
                        rfl

theorem cell23_1599317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1599317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599317 prefixEnd_1599317 := by exact prefixLift 1599317
  have htrace : WordTrace (prefixWord ++ tailWord_1599317) baseStart_1599317 baseEnd_1599317 := by
    simpa [prefixWord, tailWord_1599317, baseEnd_1599317] using wordTrace_append hprefix tailTrace_1599317
  have hstable : (prefixWord ++ tailWord_1599317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599317).length < 2 ^ (prefixWord ++ tailWord_1599317).sum := by decide
  have hdescent : baseEnd_1599317 < baseStart_1599317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599341 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1599341 : Nat := 118140960795 + 1599341 * 2 ^ 59
def prefixEnd_1599341 : Nat := 4983230072969 + 3 ^ 40 * 1599341 * 2
def baseEnd_1599341 : Nat := 273743554480844101560757

theorem tailTrace_1599341 : CollatzResearch.WordTrace tailWord_1599341 prefixEnd_1599341 273743554480844101560757 := by
  unfold tailWord_1599341
  simp only [CollatzResearch.WordTrace]
  refine ⟨58332758498868177541669877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38888505665912118361113251 58332758498868177541669877)
  ·
    refine ⟨5468696109268891644531551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58332758498868177541669877 5468696109268891644531551)
    ·
      refine ⟨8203044163903337466797327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5468696109268891644531551 8203044163903337466797327)
      ·
        refine ⟨12304566245855006200195991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203044163903337466797327 12304566245855006200195991)
        ·
          refine ⟨18456849368782509300293987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12304566245855006200195991 18456849368782509300293987)
          ·
            refine ⟨27685274053173763950440981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18456849368782509300293987 27685274053173763950440981)
            ·
              refine ⟨1297747221242520185176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27685274053173763950440981 1297747221242520185176921)
              ·
                refine ⟨973310415931890138882691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297747221242520185176921 973310415931890138882691)
                ·
                  refine ⟨1459965623897835208324037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973310415931890138882691 1459965623897835208324037)
                  ·
                    refine ⟨273743554480844101560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459965623897835208324037 273743554480844101560757)
                    ·
                      rfl

theorem cell23_1599341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1599341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599341 prefixEnd_1599341 := by exact prefixLift 1599341
  have htrace : WordTrace (prefixWord ++ tailWord_1599341) baseStart_1599341 baseEnd_1599341 := by
    simpa [prefixWord, tailWord_1599341, baseEnd_1599341] using wordTrace_append hprefix tailTrace_1599341
  have hstable : (prefixWord ++ tailWord_1599341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599341).length < 2 ^ (prefixWord ++ tailWord_1599341).sum := by decide
  have hdescent : baseEnd_1599341 < baseStart_1599341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599347 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 3]
def baseStart_1599347 : Nat := 118140960795 + 1599347 * 2 ^ 59
def prefixEnd_1599347 : Nat := 4983230072969 + 3 ^ 40 * 1599347 * 2
def baseEnd_1599347 : Nat := 821233744326459281207243

theorem tailTrace_1599347 : CollatzResearch.WordTrace tailWord_1599347 prefixEnd_1599347 821233744326459281207243 := by
  unfold tailWord_1599347
  simp only [CollatzResearch.WordTrace]
  refine ⟨58332977336846440566388295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38888651557897627044258863 58332977336846440566388295)
  ·
    refine ⟨87499466005269660849582443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58332977336846440566388295 87499466005269660849582443)
    ·
      refine ⟨131249199007904491274373665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87499466005269660849582443 131249199007904491274373665)
      ·
        refine ⟨98436899255928368455780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131249199007904491274373665 98436899255928368455780249)
        ·
          refine ⟨73827674441946276341835187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98436899255928368455780249 73827674441946276341835187)
          ·
            refine ⟨110741511662919414512752781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73827674441946276341835187 110741511662919414512752781)
            ·
              refine ⟨41528066873594780442282293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110741511662919414512752781 41528066873594780442282293)
              ·
                refine ⟨3893256269399510666463965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41528066873594780442282293 3893256269399510666463965)
                ·
                  refine ⟨1459971101024816499923987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3893256269399510666463965 1459971101024816499923987)
                  ·
                    refine ⟨2189956651537224749885981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459971101024816499923987 2189956651537224749885981)
                    ·
                      refine ⟨821233744326459281207243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2189956651537224749885981 821233744326459281207243)
                      ·
                        rfl

theorem cell23_1599347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_1599347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599347 prefixEnd_1599347 := by exact prefixLift 1599347
  have htrace : WordTrace (prefixWord ++ tailWord_1599347) baseStart_1599347 baseEnd_1599347 := by
    simpa [prefixWord, tailWord_1599347, baseEnd_1599347] using wordTrace_append hprefix tailTrace_1599347
  have hstable : (prefixWord ++ tailWord_1599347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599347).length < 2 ^ (prefixWord ++ tailWord_1599347).sum := by decide
  have hdescent : baseEnd_1599347 < baseStart_1599347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599357 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_1599357 : Nat := 118140960795 + 1599357 * 2 ^ 59
def prefixEnd_1599357 : Nat := 4983230072969 + 3 ^ 40 * 1599357 * 2
def baseEnd_1599357 : Nat := 821238879133004242082197

theorem tailTrace_1599357 : CollatzResearch.WordTrace tailWord_1599357 prefixEnd_1599357 821238879133004242082197 := by
  unfold tailWord_1599357
  simp only [CollatzResearch.WordTrace]
  refine ⟨58333342066810212274252325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38888894711206808182834883 58333342066810212274252325)
  ·
    refine ⟨10937501637526914801422311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58333342066810212274252325 10937501637526914801422311)
    ·
      refine ⟨16406252456290372202133467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10937501637526914801422311 16406252456290372202133467)
      ·
        refine ⟨24609378684435558303200201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16406252456290372202133467 24609378684435558303200201)
        ·
          refine ⟨18457034013326668727400151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24609378684435558303200201 18457034013326668727400151)
          ·
            refine ⟨27685551019990003091100227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18457034013326668727400151 27685551019990003091100227)
            ·
              refine ⟨41528326529985004636650341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685551019990003091100227 41528326529985004636650341)
              ·
                refine ⟨7786561224372188369371939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41528326529985004636650341 7786561224372188369371939)
                ·
                  refine ⟨11679841836558282554057909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786561224372188369371939 11679841836558282554057909)
                  ·
                    refine ⟨1094985172177338989442929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11679841836558282554057909 1094985172177338989442929)
                    ·
                      refine ⟨821238879133004242082197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1094985172177338989442929 821238879133004242082197)
                      ·
                        rfl

theorem cell23_1599357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_1599357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599357 prefixEnd_1599357 := by exact prefixLift 1599357
  have htrace : WordTrace (prefixWord ++ tailWord_1599357) baseStart_1599357 baseEnd_1599357 := by
    simpa [prefixWord, tailWord_1599357, baseEnd_1599357] using wordTrace_append hprefix tailTrace_1599357
  have hstable : (prefixWord ++ tailWord_1599357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599357).length < 2 ^ (prefixWord ++ tailWord_1599357).sum := by decide
  have hdescent : baseEnd_1599357 < baseStart_1599357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599381 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_1599381 : Nat := 118140960795 + 1599381 * 2 ^ 59
def prefixEnd_1599381 : Nat := 4983230072969 + 3 ^ 40 * 1599381 * 2
def baseEnd_1599381 : Nat := 821251202668712148182087

theorem tailTrace_1599381 : CollatzResearch.WordTrace tailWord_1599381 prefixEnd_1599381 821251202668712148182087 := by
  unfold tailWord_1599381
  simp only [CollatzResearch.WordTrace]
  refine ⟨58334217418723264373125997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38889478279148842915417331 58334217418723264373125997)
  ·
    refine ⟨21875331532021224139922249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58334217418723264373125997 21875331532021224139922249)
    ·
      refine ⟨16406498649015918104941687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21875331532021224139922249 16406498649015918104941687)
      ·
        refine ⟨24609747973523877157412531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16406498649015918104941687 24609747973523877157412531)
        ·
          refine ⟨36914621960285815736118797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24609747973523877157412531 36914621960285815736118797)
          ·
            refine ⟨13842983235107180901044549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36914621960285815736118797 13842983235107180901044549)
            ·
              refine ⟨2595559356582596418945853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13842983235107180901044549 2595559356582596418945853)
              ·
                refine ⟨973334758718473657104695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595559356582596418945853 973334758718473657104695)
                ·
                  refine ⟨1460002138077710485657043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973334758718473657104695 1460002138077710485657043)
                  ·
                    refine ⟨2190003207116565728485565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460002138077710485657043 2190003207116565728485565)
                    ·
                      refine ⟨821251202668712148182087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190003207116565728485565 821251202668712148182087)
                      ·
                        rfl

theorem cell23_1599381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_1599381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599381 prefixEnd_1599381 := by exact prefixLift 1599381
  have htrace : WordTrace (prefixWord ++ tailWord_1599381) baseStart_1599381 baseEnd_1599381 := by
    simpa [prefixWord, tailWord_1599381, baseEnd_1599381] using wordTrace_append hprefix tailTrace_1599381
  have hstable : (prefixWord ++ tailWord_1599381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599381).length < 2 ^ (prefixWord ++ tailWord_1599381).sum := by decide
  have hdescent : baseEnd_1599381 < baseStart_1599381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599421 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1599421 : Nat := 118140960795 + 1599421 * 2 ^ 59
def prefixEnd_1599421 : Nat := 4983230072969 + 3 ^ 40 * 1599421 * 2
def baseEnd_1599421 : Nat := 821271741894891991681903

theorem tailTrace_1599421 : CollatzResearch.WordTrace tailWord_1599421 prefixEnd_1599421 821271741894891991681903 := by
  unfold tailWord_1599421
  simp only [CollatzResearch.WordTrace]
  refine ⟨58335676338578351204582117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38890450892385567469721411 58335676338578351204582117)
  ·
    refine ⟨10937939313483440850859147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58335676338578351204582117 10937939313483440850859147)
    ·
      refine ⟨16406908970225161276288721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10937939313483440850859147 16406908970225161276288721)
      ·
        refine ⟨12305181727668870957216541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16406908970225161276288721 12305181727668870957216541)
        ·
          refine ⟨4614443147875826608956203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12305181727668870957216541 4614443147875826608956203)
          ·
            refine ⟨6921664721813739913434305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614443147875826608956203 6921664721813739913434305)
            ·
              refine ⟨5191248541360304935075729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921664721813739913434305 5191248541360304935075729)
              ·
                refine ⟨3893436406020228701306797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191248541360304935075729 3893436406020228701306797)
                ·
                  refine ⟨1460038652257585762990049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3893436406020228701306797 1460038652257585762990049)
                  ·
                    refine ⟨1095028989193189322242537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460038652257585762990049 1095028989193189322242537)
                    ·
                      refine ⟨821271741894891991681903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095028989193189322242537 821271741894891991681903)
                      ·
                        rfl

theorem cell23_1599421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1599421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599421 prefixEnd_1599421 := by exact prefixLift 1599421
  have htrace : WordTrace (prefixWord ++ tailWord_1599421) baseStart_1599421 baseEnd_1599421 := by
    simpa [prefixWord, tailWord_1599421, baseEnd_1599421] using wordTrace_append hprefix tailTrace_1599421
  have hstable : (prefixWord ++ tailWord_1599421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599421).length < 2 ^ (prefixWord ++ tailWord_1599421).sum := by decide
  have hdescent : baseEnd_1599421 < baseStart_1599421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599424 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_1599424 : Nat := 118140960795 + 1599424 * 2 ^ 59
def prefixEnd_1599424 : Nat := 4983230072969 + 3 ^ 40 * 1599424 * 2
def baseEnd_1599424 : Nat := 821273282336855479944389

theorem tailTrace_1599424 : CollatzResearch.WordTrace tailWord_1599424 prefixEnd_1599424 821273282336855479944389 := by
  unfold tailWord_1599424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29167892878783741358470663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38890523838378321811294217 29167892878783741358470663)
  ·
    refine ⟨43751839318175612037705995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29167892878783741358470663 43751839318175612037705995)
    ·
      refine ⟨65627758977263418056558993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43751839318175612037705995 65627758977263418056558993)
      ·
        refine ⟨49220819232947563542419245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65627758977263418056558993 49220819232947563542419245)
        ·
          refine ⟨18457807212355336328407217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49220819232947563542419245 18457807212355336328407217)
          ·
            refine ⟨13843355409266502246305413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18457807212355336328407217 13843355409266502246305413)
            ·
              refine ⟨2595629139237469171182265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13843355409266502246305413 2595629139237469171182265)
              ·
                refine ⟨1946721854428101878386699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595629139237469171182265 1946721854428101878386699)
                ·
                  refine ⟨2920082781642152817580049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946721854428101878386699 2920082781642152817580049)
                  ·
                    refine ⟨2190062086231614613185037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2920082781642152817580049 2190062086231614613185037)
                    ·
                      refine ⟨821273282336855479944389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190062086231614613185037 821273282336855479944389)
                      ·
                        rfl

theorem cell23_1599424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_1599424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599424 prefixEnd_1599424 := by exact prefixLift 1599424
  have htrace : WordTrace (prefixWord ++ tailWord_1599424) baseStart_1599424 baseEnd_1599424 := by
    simpa [prefixWord, tailWord_1599424, baseEnd_1599424] using wordTrace_append hprefix tailTrace_1599424
  have hstable : (prefixWord ++ tailWord_1599424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599424).length < 2 ^ (prefixWord ++ tailWord_1599424).sum := by decide
  have hdescent : baseEnd_1599424 < baseStart_1599424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599455 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 1, 2, 2]
def baseStart_1599455 : Nat := 118140960795 + 1599455 * 2 ^ 59
def prefixEnd_1599455 : Nat := 4983230072969 + 3 ^ 40 * 1599455 * 2
def baseEnd_1599455 : Nat := 821289200237144858656747

theorem tailTrace_1599455 : CollatzResearch.WordTrace tailWord_1599455 prefixEnd_1599455 821289200237144858656747 := by
  unfold tailWord_1599455
  simp only [CollatzResearch.WordTrace]
  refine ⟨58336916420455175011319819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38891277613636783340879879 58336916420455175011319819)
  ·
    refine ⟨87505374630682762516979729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58336916420455175011319819 87505374630682762516979729)
    ·
      refine ⟨65629030973012071887734797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87505374630682762516979729 65629030973012071887734797)
      ·
        refine ⟨24610886614879526957900549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65629030973012071887734797 24610886614879526957900549)
        ·
          refine ⟨4614541240289911304606353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24610886614879526957900549 4614541240289911304606353)
          ·
            refine ⟨3460905930217433478454765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4614541240289911304606353 3460905930217433478454765)
            ·
              refine ⟨1297839723831537554420537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3460905930217433478454765 1297839723831537554420537)
              ·
                refine ⟨973379792873653165815403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297839723831537554420537 973379792873653165815403)
                ·
                  refine ⟨1460069689310479748723105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973379792873653165815403 1460069689310479748723105)
                  ·
                    refine ⟨1095052266982859811542329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460069689310479748723105 1095052266982859811542329)
                    ·
                      refine ⟨821289200237144858656747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095052266982859811542329 821289200237144858656747)
                      ·
                        rfl

theorem cell23_1599455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_1599455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599455 prefixEnd_1599455 := by exact prefixLift 1599455
  have htrace : WordTrace (prefixWord ++ tailWord_1599455) baseStart_1599455 baseEnd_1599455 := by
    simpa [prefixWord, tailWord_1599455, baseEnd_1599455] using wordTrace_append hprefix tailTrace_1599455
  have hstable : (prefixWord ++ tailWord_1599455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599455).length < 2 ^ (prefixWord ++ tailWord_1599455).sum := by decide
  have hdescent : baseEnd_1599455 < baseStart_1599455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1599464 : Nat := 118140960795 + 1599464 * 2 ^ 59
def prefixEnd_1599464 : Nat := 4983230072969 + 3 ^ 40 * 1599464 * 2
def baseEnd_1599464 : Nat := 821293821563035323444205

theorem tailTrace_1599464 : CollatzResearch.WordTrace tailWord_1599464 prefixEnd_1599464 821293821563035323444205 := by
  unfold tailWord_1599464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29168622338711284774198723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38891496451615046365598297 29168622338711284774198723)
  ·
    refine ⟨43752933508066927161298085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29168622338711284774198723 43752933508066927161298085)
    ·
      refine ⟨8203675032762548842743391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43752933508066927161298085 8203675032762548842743391)
      ·
        refine ⟨12305512549143823264115087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203675032762548842743391 12305512549143823264115087)
        ·
          refine ⟨18458268823715734896172631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305512549143823264115087 18458268823715734896172631)
          ·
            refine ⟨27687403235573602344258947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18458268823715734896172631 27687403235573602344258947)
            ·
              refine ⟨41531104853360403516388421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27687403235573602344258947 41531104853360403516388421)
              ·
                refine ⟨7787082160005075659322829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41531104853360403516388421 7787082160005075659322829)
                ·
                  refine ⟨2920155810001903372246061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7787082160005075659322829 2920155810001903372246061)
                  ·
                    refine ⟨1095058428750713764592273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920155810001903372246061 1095058428750713764592273)
                    ·
                      refine ⟨821293821563035323444205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095058428750713764592273 821293821563035323444205)
                      ·
                        rfl

theorem cell23_1599464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1599464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599464 prefixEnd_1599464 := by exact prefixLift 1599464
  have htrace : WordTrace (prefixWord ++ tailWord_1599464) baseStart_1599464 baseEnd_1599464 := by
    simpa [prefixWord, tailWord_1599464, baseEnd_1599464] using wordTrace_append hprefix tailTrace_1599464
  have hstable : (prefixWord ++ tailWord_1599464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599464).length < 2 ^ (prefixWord ++ tailWord_1599464).sum := by decide
  have hdescent : baseEnd_1599464 < baseStart_1599464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599481 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 1, 3, 2]
def baseStart_1599481 : Nat := 118140960795 + 1599481 * 2 ^ 59
def prefixEnd_1599481 : Nat := 4983230072969 + 3 ^ 40 * 1599481 * 2
def baseEnd_1599481 : Nat := 821302550734161756931627

theorem tailTrace_1599481 : CollatzResearch.WordTrace tailWord_1599481 prefixEnd_1599481 821302550734161756931627 := by
  unfold tailWord_1599481
  simp only [CollatzResearch.WordTrace]
  refine ⟨58337864718360981451766297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38891909812240654301177531 58337864718360981451766297)
  ·
    refine ⟨43753398538770736088824723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58337864718360981451766297 43753398538770736088824723)
    ·
      refine ⟨65630097808156104133237085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43753398538770736088824723 65630097808156104133237085)
      ·
        refine ⟨24611286678058539049963907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65630097808156104133237085 24611286678058539049963907)
        ·
          refine ⟨36916930017087808574945861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24611286678058539049963907 36916930017087808574945861)
          ·
            refine ⟨6921924378203964107802349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36916930017087808574945861 6921924378203964107802349)
            ·
              refine ⟨2595721641826486540425881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6921924378203964107802349 2595721641826486540425881)
              ·
                refine ⟨1946791231369864905319411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595721641826486540425881 1946791231369864905319411)
                ·
                  refine ⟨2920186847054797357979117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946791231369864905319411 2920186847054797357979117)
                  ·
                    refine ⟨1095070067645549009242169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920186847054797357979117 1095070067645549009242169)
                    ·
                      refine ⟨821302550734161756931627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095070067645549009242169 821302550734161756931627)
                      ·
                        rfl

theorem cell23_1599481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_1599481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599481 prefixEnd_1599481 := by exact prefixLift 1599481
  have htrace : WordTrace (prefixWord ++ tailWord_1599481) baseStart_1599481 baseEnd_1599481 := by
    simpa [prefixWord, tailWord_1599481, baseEnd_1599481] using wordTrace_append hprefix tailTrace_1599481
  have hstable : (prefixWord ++ tailWord_1599481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599481).length < 2 ^ (prefixWord ++ tailWord_1599481).sum := by decide
  have hdescent : baseEnd_1599481 < baseStart_1599481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599534 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_1599534 : Nat := 118140960795 + 1599534 * 2 ^ 59
def prefixEnd_1599534 : Nat := 4983230072969 + 3 ^ 40 * 1599534 * 2
def baseEnd_1599534 : Nat := 91258862800983338840987

theorem tailTrace_1599534 : CollatzResearch.WordTrace tailWord_1599534 prefixEnd_1599534 91258862800983338840987 := by
  unfold tailWord_1599534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292474723396121437930707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38893198524779314335630437 7292474723396121437930707)
  ·
    refine ⟨10938712085094182156896061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7292474723396121437930707 10938712085094182156896061)
    ·
      refine ⟨4102017031910318308836023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10938712085094182156896061 4102017031910318308836023)
      ·
        refine ⟨6153025547865477463254035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102017031910318308836023 6153025547865477463254035)
        ·
          refine ⟨9229538321798216194881053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153025547865477463254035 9229538321798216194881053)
          ·
            refine ⟨3461076870674331073080395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9229538321798216194881053 3461076870674331073080395)
            ·
              refine ⟨5191615306011496609620593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461076870674331073080395 5191615306011496609620593)
              ·
                refine ⟨3893711479508622457215445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191615306011496609620593 3893711479508622457215445)
                ·
                  refine ⟨91258862800983338840987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3893711479508622457215445 91258862800983338840987)
                  ·
                    rfl

theorem cell23_1599534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_1599534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599534 prefixEnd_1599534 := by exact prefixLift 1599534
  have htrace : WordTrace (prefixWord ++ tailWord_1599534) baseStart_1599534 baseEnd_1599534 := by
    simpa [prefixWord, tailWord_1599534, baseEnd_1599534] using wordTrace_append hprefix tailTrace_1599534
  have hstable : (prefixWord ++ tailWord_1599534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599534).length < 2 ^ (prefixWord ++ tailWord_1599534).sum := by decide
  have hdescent : baseEnd_1599534 < baseStart_1599534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599607 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 8]
def baseStart_1599607 : Nat := 118140960795 + 1599607 * 2 ^ 59
def prefixEnd_1599607 : Nat := 4983230072969 + 3 ^ 40 * 1599607 * 2
def baseEnd_1599607 : Nat := 91263027699625362661783

theorem tailTrace_1599607 : CollatzResearch.WordTrace tailWord_1599607 prefixEnd_1599607 91263027699625362661783 := by
  unfold tailWord_1599607
  simp only [CollatzResearch.WordTrace]
  refine ⟨58342460315904504970853075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38894973543936336647235383 58342460315904504970853075)
  ·
    refine ⟨87513690473856757456279613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58342460315904504970853075 87513690473856757456279613)
    ·
      refine ⟨32817633927696284046104855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87513690473856757456279613 32817633927696284046104855)
      ·
        refine ⟨49226450891544426069157283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32817633927696284046104855 49226450891544426069157283)
        ·
          refine ⟨73839676337316639103735925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49226450891544426069157283 73839676337316639103735925)
          ·
            refine ⟨6922469656623434915975243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73839676337316639103735925 6922469656623434915975243)
            ·
              refine ⟨10383704484935152373962865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922469656623434915975243 10383704484935152373962865)
              ·
                refine ⟨7787778363701364280472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10383704484935152373962865 7787778363701364280472149)
                ·
                  refine ⟨91263027699625362661783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7787778363701364280472149 91263027699625362661783)
                  ·
                    rfl

theorem cell23_1599607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 8].length) (baseStart_1599607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599607 prefixEnd_1599607 := by exact prefixLift 1599607
  have htrace : WordTrace (prefixWord ++ tailWord_1599607) baseStart_1599607 baseEnd_1599607 := by
    simpa [prefixWord, tailWord_1599607, baseEnd_1599607] using wordTrace_append hprefix tailTrace_1599607
  have hstable : (prefixWord ++ tailWord_1599607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599607).length < 2 ^ (prefixWord ++ tailWord_1599607).sum := by decide
  have hdescent : baseEnd_1599607 < baseStart_1599607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599621 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_1599621 : Nat := 118140960795 + 1599621 * 2 ^ 59
def prefixEnd_1599621 : Nat := 4983230072969 + 3 ^ 40 * 1599621 * 2
def baseEnd_1599621 : Nat := 821374438025791209180983

theorem tailTrace_1599621 : CollatzResearch.WordTrace tailWord_1599621 prefixEnd_1599621 821374438025791209180983 := by
  unfold tailWord_1599621
  simp only [CollatzResearch.WordTrace]
  refine ⟨58342970937853785361862717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38895313958569190241241811 58342970937853785361862717)
  ·
    refine ⟨21878614101695169510698519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58342970937853785361862717 21878614101695169510698519)
    ·
      refine ⟨32817921152542754266047779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21878614101695169510698519 32817921152542754266047779)
      ·
        refine ⟨49226881728814131399071669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32817921152542754266047779 49226881728814131399071669)
        ·
          refine ⟨4615020162076324818662969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49226881728814131399071669 4615020162076324818662969)
          ·
            refine ⟨3461265121557243613997227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615020162076324818662969 3461265121557243613997227)
            ·
              refine ⟨5191897682335865420995841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461265121557243613997227 5191897682335865420995841)
              ·
                refine ⟨3893923261751899065746881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191897682335865420995841 3893923261751899065746881)
                ·
                  refine ⟨2920442446313924299310161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893923261751899065746881 2920442446313924299310161)
                  ·
                    refine ⟨2190331834735443224482621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2920442446313924299310161 2190331834735443224482621)
                    ·
                      refine ⟨821374438025791209180983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190331834735443224482621 821374438025791209180983)
                      ·
                        rfl

theorem cell23_1599621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_1599621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599621 prefixEnd_1599621 := by exact prefixLift 1599621
  have htrace : WordTrace (prefixWord ++ tailWord_1599621) baseStart_1599621 baseEnd_1599621 := by
    simpa [prefixWord, tailWord_1599621, baseEnd_1599621] using wordTrace_append hprefix tailTrace_1599621
  have hstable : (prefixWord ++ tailWord_1599621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599621).length < 2 ^ (prefixWord ++ tailWord_1599621).sum := by decide
  have hdescent : baseEnd_1599621 < baseStart_1599621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599624 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 8]
def baseStart_1599624 : Nat := 118140960795 + 1599624 * 2 ^ 59
def prefixEnd_1599624 : Nat := 4983230072969 + 3 ^ 40 * 1599624 * 2
def baseEnd_1599624 : Nat := 91263997607528299715941

theorem tailTrace_1599624 : CollatzResearch.WordTrace tailWord_1599624 prefixEnd_1599624 91263997607528299715941 := by
  unfold tailWord_1599624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29171540178421458437110963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38895386904561944582814617 29171540178421458437110963)
  ·
    refine ⟨43757310267632187655666445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29171540178421458437110963 43757310267632187655666445)
    ·
      refine ⟨16408991350362070370874917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43757310267632187655666445 16408991350362070370874917)
      ·
        refine ⟨3076685878192888194539047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16408991350362070370874917 3076685878192888194539047)
        ·
          refine ⟨4615028817289332291808571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076685878192888194539047 4615028817289332291808571)
          ·
            refine ⟨6922543225933998437712857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615028817289332291808571 6922543225933998437712857)
            ·
              refine ⟨5191907419450498828284643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6922543225933998437712857 5191907419450498828284643)
              ·
                refine ⟨7787861129175748242426965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191907419450498828284643 7787861129175748242426965)
                ·
                  refine ⟨91263997607528299715941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7787861129175748242426965 91263997607528299715941)
                  ·
                    rfl

theorem cell23_1599624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_1599624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599624 prefixEnd_1599624 := by exact prefixLift 1599624
  have htrace : WordTrace (prefixWord ++ tailWord_1599624) baseStart_1599624 baseEnd_1599624 := by
    simpa [prefixWord, tailWord_1599624, baseEnd_1599624] using wordTrace_append hprefix tailTrace_1599624
  have hstable : (prefixWord ++ tailWord_1599624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599624).length < 2 ^ (prefixWord ++ tailWord_1599624).sum := by decide
  have hdescent : baseEnd_1599624 < baseStart_1599624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599685 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_1599685 : Nat := 118140960795 + 1599685 * 2 ^ 59
def prefixEnd_1599685 : Nat := 4983230072969 + 3 ^ 40 * 1599685 * 2
def baseEnd_1599685 : Nat := 821407300787678958780689

theorem tailTrace_1599685 : CollatzResearch.WordTrace tailWord_1599685 prefixEnd_1599685 821407300787678958780689 := by
  unfold tailWord_1599685
  simp only [CollatzResearch.WordTrace]
  refine ⟨58345305209621924292192509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38896870139747949528128339 58345305209621924292192509)
  ·
    refine ⟨21879489453608221609572191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58345305209621924292192509 21879489453608221609572191)
    ·
      refine ⟨32819234180412332414358287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21879489453608221609572191 32819234180412332414358287)
      ·
        refine ⟨49228851270618498621537431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32819234180412332414358287 49228851270618498621537431)
        ·
          refine ⟨73843276905927747932306147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49228851270618498621537431 73843276905927747932306147)
          ·
            refine ⟨110764915358891621898459221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73843276905927747932306147 110764915358891621898459221)
            ·
              refine ⟨1298026351862011194122569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 110764915358891621898459221 1298026351862011194122569)
              ·
                refine ⟨973519763896508395591927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298026351862011194122569 973519763896508395591927)
                ·
                  refine ⟨1460279645844762593387891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973519763896508395591927 1460279645844762593387891)
                  ·
                    refine ⟨2190419468767143890081837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460279645844762593387891 2190419468767143890081837)
                    ·
                      refine ⟨821407300787678958780689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190419468767143890081837 821407300787678958780689)
                      ·
                        rfl

theorem cell23_1599685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_1599685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599685 prefixEnd_1599685 := by exact prefixLift 1599685
  have htrace : WordTrace (prefixWord ++ tailWord_1599685) baseStart_1599685 baseEnd_1599685 := by
    simpa [prefixWord, tailWord_1599685, baseEnd_1599685] using wordTrace_append hprefix tailTrace_1599685
  have hstable : (prefixWord ++ tailWord_1599685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599685).length < 2 ^ (prefixWord ++ tailWord_1599685).sum := by decide
  have hdescent : baseEnd_1599685 < baseStart_1599685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599711 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1599711 : Nat := 118140960795 + 1599711 * 2 ^ 59
def prefixEnd_1599711 : Nat := 4983230072969 + 3 ^ 40 * 1599711 * 2
def baseEnd_1599711 : Nat := 821420651284695857055569

theorem tailTrace_1599711 : CollatzResearch.WordTrace tailWord_1599711 prefixEnd_1599711 821420651284695857055569 := by
  unfold tailWord_1599711
  simp only [CollatzResearch.WordTrace]
  refine ⟨58346253507527730732638987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38897502338351820488425991 58346253507527730732638987)
  ·
    refine ⟨87519380261291596098958481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58346253507527730732638987 87519380261291596098958481)
    ·
      refine ⟨65639535195968697074218861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87519380261291596098958481 65639535195968697074218861)
      ·
        refine ⟨24614825698488261402832073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65639535195968697074218861 24614825698488261402832073)
        ·
          refine ⟨18461119273866196052124055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24614825698488261402832073 18461119273866196052124055)
          ·
            refine ⟨27691678910799294078186083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18461119273866196052124055 27691678910799294078186083)
            ·
              refine ⟨41537518366198941117279125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27691678910799294078186083 41537518366198941117279125)
              ·
                refine ⟨1947071173415575364872459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41537518366198941117279125 1947071173415575364872459)
                ·
                  refine ⟨2920606760123363047308689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947071173415575364872459 2920606760123363047308689)
                  ·
                    refine ⟨2190455070092522285481517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2920606760123363047308689 2190455070092522285481517)
                    ·
                      refine ⟨821420651284695857055569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190455070092522285481517 821420651284695857055569)
                      ·
                        rfl

theorem cell23_1599711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1599711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599711 prefixEnd_1599711 := by exact prefixLift 1599711
  have htrace : WordTrace (prefixWord ++ tailWord_1599711) baseStart_1599711 baseEnd_1599711 := by
    simpa [prefixWord, tailWord_1599711, baseEnd_1599711] using wordTrace_append hprefix tailTrace_1599711
  have hstable : (prefixWord ++ tailWord_1599711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599711).length < 2 ^ (prefixWord ++ tailWord_1599711).sum := by decide
  have hdescent : baseEnd_1599711 < baseStart_1599711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599742 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1599742 : Nat := 118140960795 + 1599742 * 2 ^ 59
def prefixEnd_1599742 : Nat := 4983230072969 + 3 ^ 40 * 1599742 * 2
def baseEnd_1599742 : Nat := 821436569184985235767927

theorem tailTrace_1599742 : CollatzResearch.WordTrace tailWord_1599742 prefixEnd_1599742 821436569184985235767927 := by
  unfold tailWord_1599742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293423021301927878377185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38898256113610282018011653 7293423021301927878377185)
  ·
    refine ⟨5470067265976445908782889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7293423021301927878377185 5470067265976445908782889)
    ·
      refine ⟨4102550449482334431587167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470067265976445908782889 4102550449482334431587167)
      ·
        refine ⟨6153825674223501647380751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102550449482334431587167 6153825674223501647380751)
        ·
          refine ⟨9230738511335252471071127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153825674223501647380751 9230738511335252471071127)
          ·
            refine ⟨13846107767002878706606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230738511335252471071127 13846107767002878706606691)
            ·
              refine ⟨20769161650504318059910037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846107767002878706606691 20769161650504318059910037)
              ·
                refine ⟨973554452367389909058283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20769161650504318059910037 973554452367389909058283)
                ·
                  refine ⟨1460331678551084863587425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973554452367389909058283 1460331678551084863587425)
                  ·
                    refine ⟨1095248758913313647690569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460331678551084863587425 1095248758913313647690569)
                    ·
                      refine ⟨821436569184985235767927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095248758913313647690569 821436569184985235767927)
                      ·
                        rfl

theorem cell23_1599742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1599742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599742 prefixEnd_1599742 := by exact prefixLift 1599742
  have htrace : WordTrace (prefixWord ++ tailWord_1599742) baseStart_1599742 baseEnd_1599742 := by
    simpa [prefixWord, tailWord_1599742, baseEnd_1599742] using wordTrace_append hprefix tailTrace_1599742
  have hstable : (prefixWord ++ tailWord_1599742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599742).length < 2 ^ (prefixWord ++ tailWord_1599742).sum := by decide
  have hdescent : baseEnd_1599742 < baseStart_1599742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599809 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1599809 : Nat := 118140960795 + 1599809 * 2 ^ 59
def prefixEnd_1599809 : Nat := 4983230072969 + 3 ^ 40 * 1599809 * 2
def baseEnd_1599809 : Nat := 821470972388836473630119

theorem tailTrace_1599809 : CollatzResearch.WordTrace tailWord_1599809 prefixEnd_1599809 821470972388836473630119 := by
  unfold tailWord_1599809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58349827861172693469706481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38899885240781795646470987 58349827861172693469706481)
  ·
    refine ⟨43762370895879520102279861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58349827861172693469706481 43762370895879520102279861)
    ·
      refine ⟨4102722271488705009588737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43762370895879520102279861 4102722271488705009588737)
      ·
        refine ⟨3077041703616528757191553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102722271488705009588737 3077041703616528757191553)
        ·
          refine ⟨2307781277712396567893665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3077041703616528757191553 2307781277712396567893665)
          ·
            refine ⟨1730835958284297425920249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307781277712396567893665 1730835958284297425920249)
            ·
              refine ⟨1298126968713223069440187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730835958284297425920249 1298126968713223069440187)
              ·
                refine ⟨1947190453069834604160281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298126968713223069440187 1947190453069834604160281)
                ·
                  refine ⟨1460392839802375953120211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947190453069834604160281 1460392839802375953120211)
                  ·
                    refine ⟨2190589259703563929680317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460392839802375953120211 2190589259703563929680317)
                    ·
                      refine ⟨821470972388836473630119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190589259703563929680317 821470972388836473630119)
                      ·
                        rfl

theorem cell23_1599809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1599809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599809 prefixEnd_1599809 := by exact prefixLift 1599809
  have htrace : WordTrace (prefixWord ++ tailWord_1599809) baseStart_1599809 baseEnd_1599809 := by
    simpa [prefixWord, tailWord_1599809, baseEnd_1599809] using wordTrace_append hprefix tailTrace_1599809
  have hstable : (prefixWord ++ tailWord_1599809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599809).length < 2 ^ (prefixWord ++ tailWord_1599809).sum := by decide
  have hdescent : baseEnd_1599809 < baseStart_1599809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599815 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_1599815 : Nat := 118140960795 + 1599815 * 2 ^ 59
def prefixEnd_1599815 : Nat := 4983230072969 + 3 ^ 40 * 1599815 * 2
def baseEnd_1599815 : Nat := 821474053272763450155091

theorem tailTrace_1599815 : CollatzResearch.WordTrace tailWord_1599815 prefixEnd_1599815 821474053272763450155091 := by
  unfold tailWord_1599815
  simp only [CollatzResearch.WordTrace]
  refine ⟨58350046699150956494424899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38900031132767304329616599 58350046699150956494424899)
  ·
    refine ⟨87525070048726434741637349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58350046699150956494424899 87525070048726434741637349)
    ·
      refine ⟨16410950634136206514057003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87525070048726434741637349 16410950634136206514057003)
      ·
        refine ⟨24616425951204309771085505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16410950634136206514057003 24616425951204309771085505)
        ·
          refine ⟨18462319463403232328314129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24616425951204309771085505 18462319463403232328314129)
          ·
            refine ⟨13846739597552424246235597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18462319463403232328314129 13846739597552424246235597)
            ·
              refine ⟨5192527349082159092338349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13846739597552424246235597 5192527349082159092338349)
              ·
                refine ⟨1947197755905809659626881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5192527349082159092338349 1947197755905809659626881)
                ·
                  refine ⟨1460398316929357244720161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947197755905809659626881 1460398316929357244720161)
                  ·
                    refine ⟨1095298737697017933540121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460398316929357244720161 1095298737697017933540121)
                    ·
                      refine ⟨821474053272763450155091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095298737697017933540121 821474053272763450155091)
                      ·
                        rfl

theorem cell23_1599815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_1599815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599815 prefixEnd_1599815 := by exact prefixLift 1599815
  have htrace : WordTrace (prefixWord ++ tailWord_1599815) baseStart_1599815 baseEnd_1599815 := by
    simpa [prefixWord, tailWord_1599815, baseEnd_1599815] using wordTrace_append hprefix tailTrace_1599815
  have hstable : (prefixWord ++ tailWord_1599815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599815).length < 2 ^ (prefixWord ++ tailWord_1599815).sum := by decide
  have hdescent : baseEnd_1599815 < baseStart_1599815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599858 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_1599858 : Nat := 118140960795 + 1599858 * 2 ^ 59
def prefixEnd_1599858 : Nat := 4983230072969 + 3 ^ 40 * 1599858 * 2
def baseEnd_1599858 : Nat := 821496132940906781917393

theorem tailTrace_1599858 : CollatzResearch.WordTrace tailWord_1599858 prefixEnd_1599858 821496132940906781917393 := by
  unfold tailWord_1599858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587903759498793709560057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38901076691996783225493485 14587903759498793709560057)
  ·
    refine ⟨10940927819624095282170043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14587903759498793709560057 10940927819624095282170043)
    ·
      refine ⟨16411391729436142923255065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10940927819624095282170043 16411391729436142923255065)
      ·
        refine ⟨12308543797077107192441299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16411391729436142923255065 12308543797077107192441299)
        ·
          refine ⟨18462815695615660788661949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12308543797077107192441299 18462815695615660788661949)
          ·
            refine ⟨6923555885855872795748231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18462815695615660788661949 6923555885855872795748231)
            ·
              refine ⟨10385333828783809193622347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6923555885855872795748231 10385333828783809193622347)
              ·
                refine ⟨15578000743175713790433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10385333828783809193622347 15578000743175713790433521)
                ·
                  refine ⟨11683500557381785342825141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15578000743175713790433521 11683500557381785342825141)
                  ·
                    refine ⟨1095328177254542375889857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11683500557381785342825141 1095328177254542375889857)
                    ·
                      refine ⟨821496132940906781917393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095328177254542375889857 821496132940906781917393)
                      ·
                        rfl

theorem cell23_1599858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_1599858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599858 prefixEnd_1599858 := by exact prefixLift 1599858
  have htrace : WordTrace (prefixWord ++ tailWord_1599858) baseStart_1599858 baseEnd_1599858 := by
    simpa [prefixWord, tailWord_1599858, baseEnd_1599858] using wordTrace_append hprefix tailTrace_1599858
  have hstable : (prefixWord ++ tailWord_1599858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599858).length < 2 ^ (prefixWord ++ tailWord_1599858).sum := by decide
  have hdescent : baseEnd_1599858 < baseStart_1599858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599908 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_1599908 : Nat := 118140960795 + 1599908 * 2 ^ 59
def prefixEnd_1599908 : Nat := 4983230072969 + 3 ^ 40 * 1599908 * 2
def baseEnd_1599908 : Nat := 821521806973631586292163

theorem tailTrace_1599908 : CollatzResearch.WordTrace tailWord_1599908 prefixEnd_1599908 821521806973631586292163 := by
  unfold tailWord_1599908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29176719343907016688780189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38902292458542688918373585 29176719343907016688780189)
  ·
    refine ⟨10941269753965131258292571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29176719343907016688780189 10941269753965131258292571)
    ·
      refine ⟨16411904630947696887438857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10941269753965131258292571 16411904630947696887438857)
      ·
        refine ⟨12308928473210772665579143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16411904630947696887438857 12308928473210772665579143)
        ·
          refine ⟨18463392709816158998368715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12308928473210772665579143 18463392709816158998368715)
          ·
            refine ⟨27695089064724238497553073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18463392709816158998368715 27695089064724238497553073)
            ·
              refine ⟨20771316798543178873164805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27695089064724238497553073 20771316798543178873164805)
              ·
                refine ⟨3894621899726846038718401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20771316798543178873164805 3894621899726846038718401)
                ·
                  refine ⟨2920966424795134529038801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894621899726846038718401 2920966424795134529038801)
                  ·
                    refine ⟨2190724818596350896779101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2920966424795134529038801 2190724818596350896779101)
                    ·
                      refine ⟨821521806973631586292163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190724818596350896779101 821521806973631586292163)
                      ·
                        rfl

theorem cell23_1599908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_1599908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1599908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1599908 prefixEnd_1599908 := by exact prefixLift 1599908
  have htrace : WordTrace (prefixWord ++ tailWord_1599908) baseStart_1599908 baseEnd_1599908 := by
    simpa [prefixWord, tailWord_1599908, baseEnd_1599908] using wordTrace_append hprefix tailTrace_1599908
  have hstable : (prefixWord ++ tailWord_1599908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599908).length < 2 ^ (prefixWord ++ tailWord_1599908).sum := by decide
  have hdescent : baseEnd_1599908 < baseStart_1599908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600012 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_1600012 : Nat := 118140960795 + 1600012 * 2 ^ 59
def prefixEnd_1600012 : Nat := 4983230072969 + 3 ^ 40 * 1600012 * 2
def baseEnd_1600012 : Nat := 821575208961699179391685

theorem tailTrace_1600012 : CollatzResearch.WordTrace tailWord_1600012 prefixEnd_1600012 821575208961699179391685 := by
  unfold tailWord_1600012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29178615939718629569673145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38904821252958172759564193 29178615939718629569673145)
  ·
    refine ⟨21883961954788972177254859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29178615939718629569673145 21883961954788972177254859)
    ·
      refine ⟨32825942932183458265882289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21883961954788972177254859 32825942932183458265882289)
      ·
        refine ⟨24619457199137593699411717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32825942932183458265882289 24619457199137593699411717)
        ·
          refine ⟨4616148224838298818639697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24619457199137593699411717 4616148224838298818639697)
          ·
            refine ⟨3462111168628724113979773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616148224838298818639697 3462111168628724113979773)
            ·
              refine ⟨1298291688235771542742415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3462111168628724113979773 1298291688235771542742415)
              ·
                refine ⟨1947437532353657314113623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298291688235771542742415 1947437532353657314113623)
                ·
                  refine ⟨2921156298530485971170435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947437532353657314113623 2921156298530485971170435)
                  ·
                    refine ⟨4381734447795728956755653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921156298530485971170435 4381734447795728956755653)
                    ·
                      refine ⟨821575208961699179391685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4381734447795728956755653 821575208961699179391685)
                      ·
                        rfl

theorem cell23_1600012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_1600012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600012 prefixEnd_1600012 := by exact prefixLift 1600012
  have htrace : WordTrace (prefixWord ++ tailWord_1600012) baseStart_1600012 baseEnd_1600012 := by
    simpa [prefixWord, tailWord_1600012, baseEnd_1600012] using wordTrace_append hprefix tailTrace_1600012
  have hstable : (prefixWord ++ tailWord_1600012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600012).length < 2 ^ (prefixWord ++ tailWord_1600012).sum := by decide
  have hdescent : baseEnd_1600012 < baseStart_1600012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600023 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1600023 : Nat := 118140960795 + 1600023 * 2 ^ 59
def prefixEnd_1600023 : Nat := 4983230072969 + 3 ^ 40 * 1600023 * 2
def baseEnd_1600023 : Nat := 821580857248898636354135

theorem tailTrace_1600023 : CollatzResearch.WordTrace tailWord_1600023 prefixEnd_1600023 821580857248898636354135 := by
  unfold tailWord_1600023
  simp only [CollatzResearch.WordTrace]
  refine ⟨58357633082397408017996723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38905088721598272011997815 58357633082397408017996723)
  ·
    refine ⟨87536449623596112026995085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58357633082397408017996723 87536449623596112026995085)
    ·
      refine ⟨32826168608848542010123157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87536449623596112026995085 32826168608848542010123157)
      ·
        refine ⟨1538726653539775406724523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32826168608848542010123157 1538726653539775406724523)
        ·
          refine ⟨2308089980309663110086785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538726653539775406724523 2308089980309663110086785)
          ·
            refine ⟨1731067485232247332565089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308089980309663110086785 1731067485232247332565089)
            ·
              refine ⟨1298300613924185499423817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731067485232247332565089 1298300613924185499423817)
              ·
                refine ⟨973725460443139124567863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298300613924185499423817 973725460443139124567863)
                ·
                  refine ⟨1460588190664708686851795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973725460443139124567863 1460588190664708686851795)
                  ·
                    refine ⟨2190882285997063030277693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460588190664708686851795 2190882285997063030277693)
                    ·
                      refine ⟨821580857248898636354135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190882285997063030277693 821580857248898636354135)
                      ·
                        rfl

theorem cell23_1600023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1600023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600023 prefixEnd_1600023 := by exact prefixLift 1600023
  have htrace : WordTrace (prefixWord ++ tailWord_1600023) baseStart_1600023 baseEnd_1600023 := by
    simpa [prefixWord, tailWord_1600023, baseEnd_1600023] using wordTrace_append hprefix tailTrace_1600023
  have hstable : (prefixWord ++ tailWord_1600023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600023).length < 2 ^ (prefixWord ++ tailWord_1600023).sum := by decide
  have hdescent : baseEnd_1600023 < baseStart_1600023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600055 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_1600055 : Nat := 118140960795 + 1600055 * 2 ^ 59
def prefixEnd_1600055 : Nat := 4983230072969 + 3 ^ 40 * 1600055 * 2
def baseEnd_1600055 : Nat := 821597288629842511153987

theorem tailTrace_1600055 : CollatzResearch.WordTrace tailWord_1600055 prefixEnd_1600055 821597288629842511153987 := by
  unfold tailWord_1600055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58358800218281477483161619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38905866812187651655441079 58358800218281477483161619)
  ·
    refine ⟨87538200327422216224742429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58358800218281477483161619 87538200327422216224742429)
    ·
      refine ⟨32826825122783331084278411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87538200327422216224742429 32826825122783331084278411)
      ·
        refine ⟨49240237684174996626417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32826825122783331084278411 49240237684174996626417617)
        ·
          refine ⟨36930178263131247469813213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49240237684174996626417617 36930178263131247469813213)
          ·
            refine ⟨13848816848674217801179955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36930178263131247469813213 13848816848674217801179955)
            ·
              refine ⟨20773225273011326701769933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848816848674217801179955 20773225273011326701769933)
              ·
                refine ⟨7789959477379247513163725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20773225273011326701769933 7789959477379247513163725)
                ·
                  refine ⟨2921234804017217817436397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7789959477379247513163725 2921234804017217817436397)
                  ·
                    refine ⟨1095463051506456681538649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921234804017217817436397 1095463051506456681538649)
                    ·
                      refine ⟨821597288629842511153987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095463051506456681538649 821597288629842511153987)
                      ·
                        rfl

theorem cell23_1600055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_1600055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600055 prefixEnd_1600055 := by exact prefixLift 1600055
  have htrace : WordTrace (prefixWord ++ tailWord_1600055) baseStart_1600055 baseEnd_1600055 := by
    simpa [prefixWord, tailWord_1600055, baseEnd_1600055] using wordTrace_append hprefix tailTrace_1600055
  have hstable : (prefixWord ++ tailWord_1600055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600055).length < 2 ^ (prefixWord ++ tailWord_1600055).sum := by decide
  have hdescent : baseEnd_1600055 < baseStart_1600055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600078 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1600078 : Nat := 118140960795 + 1600078 * 2 ^ 59
def prefixEnd_1600078 : Nat := 4983230072969 + 3 ^ 40 * 1600078 * 2
def baseEnd_1600078 : Nat := 273869699561631973722127

theorem tailTrace_1600078 : CollatzResearch.WordTrace tailWord_1600078 prefixEnd_1600078 273869699561631973722127 := by
  unfold tailWord_1600078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294954887149769051406111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38906426064798768274165925 7294954887149769051406111)
  ·
    refine ⟨10942432330724653577109167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294954887149769051406111 10942432330724653577109167)
    ·
      refine ⟨16413648496086980365663751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10942432330724653577109167 16413648496086980365663751)
      ·
        refine ⟨24620472744130470548495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16413648496086980365663751 24620472744130470548495627)
        ·
          refine ⟨36930709116195705822743441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620472744130470548495627 36930709116195705822743441)
          ·
            refine ⟨27698031837146779367057581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36930709116195705822743441 27698031837146779367057581)
            ·
              refine ⟨10386761938930042262646593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27698031837146779367057581 10386761938930042262646593)
              ·
                refine ⟨7790071454197531696984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10386761938930042262646593 7790071454197531696984945)
                ·
                  refine ⟨5842553590648148772738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790071454197531696984945 5842553590648148772738709)
                  ·
                    refine ⟨273869699561631973722127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5842553590648148772738709 273869699561631973722127)
                    ·
                      rfl

theorem cell23_1600078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1600078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600078 prefixEnd_1600078 := by exact prefixLift 1600078
  have htrace : WordTrace (prefixWord ++ tailWord_1600078) baseStart_1600078 baseEnd_1600078 := by
    simpa [prefixWord, tailWord_1600078, baseEnd_1600078] using wordTrace_append hprefix tailTrace_1600078
  have hstable : (prefixWord ++ tailWord_1600078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600078).length < 2 ^ (prefixWord ++ tailWord_1600078).sum := by decide
  have hdescent : baseEnd_1600078 < baseStart_1600078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600085 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1600085 : Nat := 118140960795 + 1600085 * 2 ^ 59
def prefixEnd_1600085 : Nat := 4983230072969 + 3 ^ 40 * 1600085 * 2
def baseEnd_1600085 : Nat := 821612693049477393778849

theorem tailTrace_1600085 : CollatzResearch.WordTrace tailWord_1600085 prefixEnd_1600085 821612693049477393778849 := by
  unfold tailWord_1600085
  simp only [CollatzResearch.WordTrace]
  refine ⟨58359894408172792606753709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38906596272115195071169139 58359894408172792606753709)
  ·
    refine ⟨21884960403064797227532641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58359894408172792606753709 21884960403064797227532641)
    ·
      refine ⟨16413720302298597920649481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21884960403064797227532641 16413720302298597920649481)
      ·
        refine ⟨12310290226723948440487111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16413720302298597920649481 12310290226723948440487111)
        ·
          refine ⟨18465435340085922660730667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310290226723948440487111 18465435340085922660730667)
          ·
            refine ⟨27698153010128883991096001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465435340085922660730667 27698153010128883991096001)
            ·
              refine ⟨20773614757596662993322001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27698153010128883991096001 20773614757596662993322001)
              ·
                refine ⟨15580211068197497244991501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20773614757596662993322001 15580211068197497244991501)
                ·
                  refine ⟨5842579150574061466871813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15580211068197497244991501 5842579150574061466871813)
                  ·
                    refine ⟨1095483590732636525038465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842579150574061466871813 1095483590732636525038465)
                    ·
                      refine ⟨821612693049477393778849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095483590732636525038465 821612693049477393778849)
                      ·
                        rfl

theorem cell23_1600085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1600085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600085 prefixEnd_1600085 := by exact prefixLift 1600085
  have htrace : WordTrace (prefixWord ++ tailWord_1600085) baseStart_1600085 baseEnd_1600085 := by
    simpa [prefixWord, tailWord_1600085, baseEnd_1600085] using wordTrace_append hprefix tailTrace_1600085
  have hstable : (prefixWord ++ tailWord_1600085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600085).length < 2 ^ (prefixWord ++ tailWord_1600085).sum := by decide
  have hdescent : baseEnd_1600085 < baseStart_1600085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600088 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1600088 : Nat := 118140960795 + 1600088 * 2 ^ 59
def prefixEnd_1600088 : Nat := 4983230072969 + 3 ^ 40 * 1600088 * 2
def baseEnd_1600088 : Nat := 821614233491440882041335

theorem tailTrace_1600088 : CollatzResearch.WordTrace tailWord_1600088 prefixEnd_1600088 821614233491440882041335 := by
  unfold tailWord_1600088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180001913580962059556459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38906669218107949412741945 29180001913580962059556459)
  ·
    refine ⟨43770002870371443089334689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29180001913580962059556459 43770002870371443089334689)
    ·
      refine ⟨32827502152778582317001017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43770002870371443089334689 32827502152778582317001017)
      ·
        refine ⟨24620626614583936737750763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32827502152778582317001017 24620626614583936737750763)
        ·
          refine ⟨36930939921875905106626145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620626614583936737750763 36930939921875905106626145)
          ·
            refine ⟨27698204941406928829969609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36930939921875905106626145 27698204941406928829969609)
            ·
              refine ⟨20773653706055196622477207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27698204941406928829969609 20773653706055196622477207)
              ·
                refine ⟨31160480559082794933715811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20773653706055196622477207 31160480559082794933715811)
                ·
                  refine ⟨46740720838624192400573717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31160480559082794933715811 46740720838624192400573717)
                  ·
                    refine ⟨2190971289310509018776893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46740720838624192400573717 2190971289310509018776893)
                    ·
                      refine ⟨821614233491440882041335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2190971289310509018776893 821614233491440882041335)
                      ·
                        rfl

theorem cell23_1600088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1600088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600088 prefixEnd_1600088 := by exact prefixLift 1600088
  have htrace : WordTrace (prefixWord ++ tailWord_1600088) baseStart_1600088 baseEnd_1600088 := by
    simpa [prefixWord, tailWord_1600088, baseEnd_1600088] using wordTrace_append hprefix tailTrace_1600088
  have hstable : (prefixWord ++ tailWord_1600088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600088).length < 2 ^ (prefixWord ++ tailWord_1600088).sum := by decide
  have hdescent : baseEnd_1600088 < baseStart_1600088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600108 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 7]
def baseStart_1600108 : Nat := 118140960795 + 1600108 * 2 ^ 59
def prefixEnd_1600108 : Nat := 4983230072969 + 3 ^ 40 * 1600108 * 2
def baseEnd_1600108 : Nat := 91291611456058978199027

theorem tailTrace_1600108 : CollatzResearch.WordTrace tailWord_1600108 prefixEnd_1600108 91291611456058978199027 := by
  unfold tailWord_1600108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180366643544733767420489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38907155524726311689893985 29180366643544733767420489)
  ·
    refine ⟨21885274982658550325565367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29180366643544733767420489 21885274982658550325565367)
    ·
      refine ⟨32827912473987825488348051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885274982658550325565367 32827912473987825488348051)
      ·
        refine ⟨49241868710981738232522077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32827912473987825488348051 49241868710981738232522077)
        ·
          refine ⟨18465700766618151837195779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49241868710981738232522077 18465700766618151837195779)
          ·
            refine ⟨27698551149927227755793669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465700766618151837195779 27698551149927227755793669)
            ·
              refine ⟨5193478340611355204211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27698551149927227755793669 5193478340611355204211313)
              ·
                refine ⟨3895108755458516403158485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5193478340611355204211313 3895108755458516403158485)
                ·
                  refine ⟨91291611456058978199027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3895108755458516403158485 91291611456058978199027)
                  ·
                    rfl

theorem cell23_1600108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_1600108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600108 prefixEnd_1600108 := by exact prefixLift 1600108
  have htrace : WordTrace (prefixWord ++ tailWord_1600108) baseStart_1600108 baseEnd_1600108 := by
    simpa [prefixWord, tailWord_1600108, baseEnd_1600108] using wordTrace_append hprefix tailTrace_1600108
  have hstable : (prefixWord ++ tailWord_1600108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600108).length < 2 ^ (prefixWord ++ tailWord_1600108).sum := by decide
  have hdescent : baseEnd_1600108 < baseStart_1600108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600175 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_1600175 : Nat := 118140960795 + 1600175 * 2 ^ 59
def prefixEnd_1600175 : Nat := 4983230072969 + 3 ^ 40 * 1600175 * 2
def baseEnd_1600175 : Nat := 821658906308382041653435

theorem tailTrace_1600175 : CollatzResearch.WordTrace tailWord_1600175 prefixEnd_1600175 821658906308382041653435 := by
  unfold tailWord_1600175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363176977846737977529979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38908784651897825318353319 58363176977846737977529979)
  ·
    refine ⟨87544765466770106966294969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58363176977846737977529979 87544765466770106966294969)
    ·
      refine ⟨65658574100077580224721227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87544765466770106966294969 65658574100077580224721227)
      ·
        refine ⟨98487861150116370337081841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65658574100077580224721227 98487861150116370337081841)
        ·
          refine ⟨73865895862587277752811381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98487861150116370337081841 73865895862587277752811381)
          ·
            refine ⟨6924927737117557289326067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73865895862587277752811381 6924927737117557289326067)
            ·
              refine ⟨10387391605676335933989101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924927737117557289326067 10387391605676335933989101)
              ·
                refine ⟨3895271852128625975245913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10387391605676335933989101 3895271852128625975245913)
                ·
                  refine ⟨2921453889096469481434435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3895271852128625975245913 2921453889096469481434435)
                  ·
                    refine ⟨4382180833644704222151653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921453889096469481434435 4382180833644704222151653)
                    ·
                      refine ⟨821658906308382041653435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4382180833644704222151653 821658906308382041653435)
                      ·
                        rfl

theorem cell23_1600175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_1600175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600175 prefixEnd_1600175 := by exact prefixLift 1600175
  have htrace : WordTrace (prefixWord ++ tailWord_1600175) baseStart_1600175 baseEnd_1600175 := by
    simpa [prefixWord, tailWord_1600175, baseEnd_1600175] using wordTrace_append hprefix tailTrace_1600175
  have hstable : (prefixWord ++ tailWord_1600175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600175).length < 2 ^ (prefixWord ++ tailWord_1600175).sum := by decide
  have hdescent : baseEnd_1600175 < baseStart_1600175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600193 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 5]
def baseStart_1600193 : Nat := 118140960795 + 1600193 * 2 ^ 59
def prefixEnd_1600193 : Nat := 4983230072969 + 3 ^ 40 * 1600193 * 2
def baseEnd_1600193 : Nat := 91296460995573663469817

theorem tailTrace_1600193 : CollatzResearch.WordTrace tailWord_1600193 prefixEnd_1600193 91296460995573663469817 := by
  unfold tailWord_1600193
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363833491781527051685233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38909222327854351367790155 58363833491781527051685233)
  ·
    refine ⟨43772875118836145288763925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58363833491781527051685233 43772875118836145288763925)
    ·
      refine ⟨2051853521195444310410809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43772875118836145288763925 2051853521195444310410809)
      ·
        refine ⟨1538890140896583232808107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051853521195444310410809 1538890140896583232808107)
        ·
          refine ⟨2308335211344874849212161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538890140896583232808107 2308335211344874849212161)
          ·
            refine ⟨1731251408508656136909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308335211344874849212161 1731251408508656136909121)
            ·
              refine ⟨1298438556381492102681841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731251408508656136909121 1298438556381492102681841)
              ·
                refine ⟨973828917286119077011381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298438556381492102681841 973828917286119077011381)
                ·
                  refine ⟨91296460995573663469817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 973828917286119077011381 91296460995573663469817)
                  ·
                    rfl

theorem cell23_1600193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 5].length) (baseStart_1600193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600193 prefixEnd_1600193 := by exact prefixLift 1600193
  have htrace : WordTrace (prefixWord ++ tailWord_1600193) baseStart_1600193 baseEnd_1600193 := by
    simpa [prefixWord, tailWord_1600193, baseEnd_1600193] using wordTrace_append hprefix tailTrace_1600193
  have hstable : (prefixWord ++ tailWord_1600193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600193).length < 2 ^ (prefixWord ++ tailWord_1600193).sum := by decide
  have hdescent : baseEnd_1600193 < baseStart_1600193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600215 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 6]
def baseStart_1600215 : Nat := 118140960795 + 1600215 * 2 ^ 59
def prefixEnd_1600215 : Nat := 4983230072969 + 3 ^ 40 * 1600215 * 2
def baseEnd_1600215 : Nat := 91297716170506876128139

theorem tailTrace_1600215 : CollatzResearch.WordTrace tailWord_1600215 prefixEnd_1600215 91297716170506876128139 := by
  unfold tailWord_1600215
  simp only [CollatzResearch.WordTrace]
  refine ⟨58364635897701824808986099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38909757265134549872657399 58364635897701824808986099)
  ·
    refine ⟨87546953846552737213479149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58364635897701824808986099 87546953846552737213479149)
    ·
      refine ⟨32830107692457276455054681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87546953846552737213479149 32830107692457276455054681)
      ·
        refine ⟨24622580769342957341291011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32830107692457276455054681 24622580769342957341291011)
        ·
          refine ⟨36933871154014436011936517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24622580769342957341291011 36933871154014436011936517)
          ·
            refine ⟨6925100841377706752238097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36933871154014436011936517 6925100841377706752238097)
            ·
              refine ⟨5193825631033280064178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925100841377706752238097 5193825631033280064178573)
              ·
                refine ⟨1947684611637480024066965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193825631033280064178573 1947684611637480024066965)
                ·
                  refine ⟨91297716170506876128139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1947684611637480024066965 91297716170506876128139)
                  ·
                    rfl

theorem cell23_1600215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 6].length) (baseStart_1600215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600215 prefixEnd_1600215 := by exact prefixLift 1600215
  have htrace : WordTrace (prefixWord ++ tailWord_1600215) baseStart_1600215 baseEnd_1600215 := by
    simpa [prefixWord, tailWord_1600215, baseEnd_1600215] using wordTrace_append hprefix tailTrace_1600215
  have hstable : (prefixWord ++ tailWord_1600215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600215).length < 2 ^ (prefixWord ++ tailWord_1600215).sum := by decide
  have hdescent : baseEnd_1600215 < baseStart_1600215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600229 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1600229 : Nat := 118140960795 + 1600229 * 2 ^ 59
def prefixEnd_1600229 : Nat := 4983230072969 + 3 ^ 40 * 1600229 * 2
def baseEnd_1600229 : Nat := 821686634263724830378187

theorem tailTrace_1600229 : CollatzResearch.WordTrace tailWord_1600229 prefixEnd_1600229 821686634263724830378187 := by
  unfold tailWord_1600229
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365146519651105199995741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38910097679767403466663827 58365146519651105199995741)
  ·
    refine ⟨21886929944869164449998403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58365146519651105199995741 21886929944869164449998403)
    ·
      refine ⟨32830394917303746674997605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21886929944869164449998403 32830394917303746674997605)
      ·
        refine ⟨6155699046994452501562051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32830394917303746674997605 6155699046994452501562051)
        ·
          refine ⟨9233548570491678752343077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155699046994452501562051 9233548570491678752343077)
          ·
            refine ⟨1731290356967189766064327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9233548570491678752343077 1731290356967189766064327)
            ·
              refine ⟨2596935535450784649096491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731290356967189766064327 2596935535450784649096491)
              ·
                refine ⟨3895403303176176973644737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596935535450784649096491 3895403303176176973644737)
                ·
                  refine ⟨2921552477382132730233553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3895403303176176973644737 2921552477382132730233553)
                  ·
                    refine ⟨2191164358036599547675165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921552477382132730233553 2191164358036599547675165)
                    ·
                      refine ⟨821686634263724830378187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2191164358036599547675165 821686634263724830378187)
                      ·
                        rfl

theorem cell23_1600229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1600229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600229 prefixEnd_1600229 := by exact prefixLift 1600229
  have htrace : WordTrace (prefixWord ++ tailWord_1600229) baseStart_1600229 baseEnd_1600229 := by
    simpa [prefixWord, tailWord_1600229, baseEnd_1600229] using wordTrace_append hprefix tailTrace_1600229
  have hstable : (prefixWord ++ tailWord_1600229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600229).length < 2 ^ (prefixWord ++ tailWord_1600229).sum := by decide
  have hdescent : baseEnd_1600229 < baseStart_1600229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600265 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_1600265 : Nat := 118140960795 + 1600265 * 2 ^ 59
def prefixEnd_1600265 : Nat := 4983230072969 + 3 ^ 40 * 1600265 * 2
def baseEnd_1600265 : Nat := 821705119567286689528021

theorem tailTrace_1600265 : CollatzResearch.WordTrace tailWord_1600265 prefixEnd_1600265 821705119567286689528021 := by
  unfold tailWord_1600265
  simp only [CollatzResearch.WordTrace]
  refine ⟨58366459547520683348306249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38910973031680455565537499 58366459547520683348306249)
  ·
    refine ⟨43774844660640512511229687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58366459547520683348306249 43774844660640512511229687)
    ·
      refine ⟨65662266990960768766844531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43774844660640512511229687 65662266990960768766844531)
      ·
        refine ⟨98493400486441153150266797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65662266990960768766844531 98493400486441153150266797)
        ·
          refine ⟨36935025182415432431350049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98493400486441153150266797 36935025182415432431350049)
          ·
            refine ⟨27701268886811574323512537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36935025182415432431350049 27701268886811574323512537)
            ·
              refine ⟨20775951665108680742634403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27701268886811574323512537 20775951665108680742634403)
              ·
                refine ⟨31163927497663021113951605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20775951665108680742634403 31163927497663021113951605)
                ·
                  refine ⟨2921618202905908229432963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31163927497663021113951605 2921618202905908229432963)
                  ·
                    refine ⟨4382427304358862344149445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921618202905908229432963 4382427304358862344149445)
                    ·
                      refine ⟨821705119567286689528021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4382427304358862344149445 821705119567286689528021)
                      ·
                        rfl

theorem cell23_1600265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_1600265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600265 prefixEnd_1600265 := by exact prefixLift 1600265
  have htrace : WordTrace (prefixWord ++ tailWord_1600265) baseStart_1600265 baseEnd_1600265 := by
    simpa [prefixWord, tailWord_1600265, baseEnd_1600265] using wordTrace_append hprefix tailTrace_1600265
  have hstable : (prefixWord ++ tailWord_1600265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600265).length < 2 ^ (prefixWord ++ tailWord_1600265).sum := by decide
  have hdescent : baseEnd_1600265 < baseStart_1600265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600279 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 1, 5]
def baseStart_1600279 : Nat := 118140960795 + 1600279 * 2 ^ 59
def prefixEnd_1600279 : Nat := 4983230072969 + 3 ^ 40 * 1600279 * 2
def baseEnd_1600279 : Nat := 273904102765483211584319

theorem tailTrace_1600279 : CollatzResearch.WordTrace tailWord_1600279 prefixEnd_1600279 273904102765483211584319 := by
  unfold tailWord_1600279
  simp only [CollatzResearch.WordTrace]
  refine ⟨58366970169469963739315891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38911313446313309159543927 58366970169469963739315891)
  ·
    refine ⟨87550455254204945608973837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58366970169469963739315891 87550455254204945608973837)
    ·
      refine ⟨32831420720326854603365189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87550455254204945608973837 32831420720326854603365189)
      ·
        refine ⟨6155891385061285238130973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32831420720326854603365189 6155891385061285238130973)
        ·
          refine ⟨2308459269397981964299115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6155891385061285238130973 2308459269397981964299115)
          ·
            refine ⟨3462688904096972946448673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308459269397981964299115 3462688904096972946448673)
            ·
              refine ⟨2597016678072729709836505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462688904096972946448673 2597016678072729709836505)
              ·
                refine ⟨1947762508554547282377379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597016678072729709836505 1947762508554547282377379)
                ·
                  refine ⟨2921643762831820923566069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947762508554547282377379 2921643762831820923566069)
                  ·
                    refine ⟨273904102765483211584319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2921643762831820923566069 273904102765483211584319)
                    ·
                      rfl

theorem cell23_1600279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_1600279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600279 prefixEnd_1600279 := by exact prefixLift 1600279
  have htrace : WordTrace (prefixWord ++ tailWord_1600279) baseStart_1600279 baseEnd_1600279 := by
    simpa [prefixWord, tailWord_1600279, baseEnd_1600279] using wordTrace_append hprefix tailTrace_1600279
  have hstable : (prefixWord ++ tailWord_1600279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600279).length < 2 ^ (prefixWord ++ tailWord_1600279).sum := by decide
  have hdescent : baseEnd_1600279 < baseStart_1600279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600282 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_1600282 : Nat := 118140960795 + 1600282 * 2 ^ 59
def prefixEnd_1600282 : Nat := 4983230072969 + 3 ^ 40 * 1600282 * 2
def baseEnd_1600282 : Nat := 821713848738413123015443

theorem tailTrace_1600282 : CollatzResearch.WordTrace tailWord_1600282 prefixEnd_1600282 821713848738413123015443 := by
  unfold tailWord_1600282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591769897114773812918775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38911386392306063501116733 14591769897114773812918775)
  ·
    refine ⟨21887654845672160719378163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14591769897114773812918775 21887654845672160719378163)
    ·
      refine ⟨32831482268508241079067245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21887654845672160719378163 32831482268508241079067245)
      ·
        refine ⟨12311805850690590404650217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32831482268508241079067245 12311805850690590404650217)
        ·
          refine ⟨9233854388017942803487663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12311805850690590404650217 9233854388017942803487663)
          ·
            refine ⟨13850781582026914205231495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9233854388017942803487663 13850781582026914205231495)
            ·
              refine ⟨20776172373040371307847243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13850781582026914205231495 20776172373040371307847243)
              ·
                refine ⟨31164258559560556961770865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20776172373040371307847243 31164258559560556961770865)
                ·
                  refine ⟨23373193919670417721328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31164258559560556961770865 23373193919670417721328149)
                  ·
                    refine ⟨1095618464984550830687257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23373193919670417721328149 1095618464984550830687257)
                    ·
                      refine ⟨821713848738413123015443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095618464984550830687257 821713848738413123015443)
                      ·
                        rfl

theorem cell23_1600282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_1600282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600282 prefixEnd_1600282 := by exact prefixLift 1600282
  have htrace : WordTrace (prefixWord ++ tailWord_1600282) baseStart_1600282 baseEnd_1600282 := by
    simpa [prefixWord, tailWord_1600282, baseEnd_1600282] using wordTrace_append hprefix tailTrace_1600282
  have hstable : (prefixWord ++ tailWord_1600282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600282).length < 2 ^ (prefixWord ++ tailWord_1600282).sum := by decide
  have hdescent : baseEnd_1600282 < baseStart_1600282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600310 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1600310 : Nat := 118140960795 + 1600310 * 2 ^ 59
def prefixEnd_1600310 : Nat := 4983230072969 + 3 ^ 40 * 1600310 * 2
def baseEnd_1600310 : Nat := 821728226196739013465315

theorem tailTrace_1600310 : CollatzResearch.WordTrace tailWord_1600310 prefixEnd_1600310 821728226196739013465315 := by
  unfold tailWord_1600310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648006302022353502105899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38912067221571770689129589 3648006302022353502105899)
  ·
    refine ⟨5472009453033530253158849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648006302022353502105899 5472009453033530253158849)
    ·
      refine ⟨4104007089775147689869137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472009453033530253158849 4104007089775147689869137)
      ·
        refine ⟨3078005317331360767401853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4104007089775147689869137 3078005317331360767401853)
        ·
          refine ⟨1154251993999260287775695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3078005317331360767401853 1154251993999260287775695)
          ·
            refine ⟨1731377990998890431663543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154251993999260287775695 1731377990998890431663543)
            ·
              refine ⟨2597066986498335647495315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731377990998890431663543 2597066986498335647495315)
              ·
                refine ⟨3895600479747503471242973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597066986498335647495315 3895600479747503471242973)
                ·
                  refine ⟨1460850179905313801716115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3895600479747503471242973 1460850179905313801716115)
                  ·
                    refine ⟨2191275269857970702574173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460850179905313801716115 2191275269857970702574173)
                    ·
                      refine ⟨821728226196739013465315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2191275269857970702574173 821728226196739013465315)
                      ·
                        rfl

theorem cell23_1600310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1600310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600310 prefixEnd_1600310 := by exact prefixLift 1600310
  have htrace : WordTrace (prefixWord ++ tailWord_1600310) baseStart_1600310 baseEnd_1600310 := by
    simpa [prefixWord, tailWord_1600310, baseEnd_1600310] using wordTrace_append hprefix tailTrace_1600310
  have hstable : (prefixWord ++ tailWord_1600310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600310).length < 2 ^ (prefixWord ++ tailWord_1600310).sum := by decide
  have hdescent : baseEnd_1600310 < baseStart_1600310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600333 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1600333 : Nat := 118140960795 + 1600333 * 2 ^ 59
def prefixEnd_1600333 : Nat := 4983230072969 + 3 ^ 40 * 1600333 * 2
def baseEnd_1600333 : Nat := 821740036251792423477709

theorem tailTrace_1600333 : CollatzResearch.WordTrace tailWord_1600333 prefixEnd_1600333 821740036251792423477709 := by
  unfold tailWord_1600333
  simp only [CollatzResearch.WordTrace]
  refine ⟨58368939711274330961781653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38912626474182887307854435 58368939711274330961781653)
  ·
    refine ⟨2736044048965984263833515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58368939711274330961781653 2736044048965984263833515)
    ·
      refine ⟨4104066073448976395750273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736044048965984263833515 4104066073448976395750273)
      ·
        refine ⟨3078049555086732296812705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4104066073448976395750273 3078049555086732296812705)
        ·
          refine ⟨2308537166315049222609529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078049555086732296812705 2308537166315049222609529)
          ·
            refine ⟨1731402874736286916957147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308537166315049222609529 1731402874736286916957147)
            ·
              refine ⟨2597104312104430375435721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731402874736286916957147 2597104312104430375435721)
              ·
                refine ⟨1947828234078322781576791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597104312104430375435721 1947828234078322781576791)
                ·
                  refine ⟨2921742351117484172365187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947828234078322781576791 2921742351117484172365187)
                  ·
                    refine ⟨4382613526676226258547781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921742351117484172365187 4382613526676226258547781)
                    ·
                      refine ⟨821740036251792423477709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4382613526676226258547781 821740036251792423477709)
                      ·
                        rfl

theorem cell23_1600333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1600333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600333 prefixEnd_1600333 := by exact prefixLift 1600333
  have htrace : WordTrace (prefixWord ++ tailWord_1600333) baseStart_1600333 baseEnd_1600333 := by
    simpa [prefixWord, tailWord_1600333, baseEnd_1600333] using wordTrace_append hprefix tailTrace_1600333
  have hstable : (prefixWord ++ tailWord_1600333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600333).length < 2 ^ (prefixWord ++ tailWord_1600333).sum := by decide
  have hdescent : baseEnd_1600333 < baseStart_1600333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600375 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1600375 : Nat := 118140960795 + 1600375 * 2 ^ 59
def prefixEnd_1600375 : Nat := 4983230072969 + 3 ^ 40 * 1600375 * 2
def baseEnd_1600375 : Nat := 821761602439281259152515

theorem tailTrace_1600375 : CollatzResearch.WordTrace tailWord_1600375 prefixEnd_1600375 821761602439281259152515 := by
  unfold tailWord_1600375
  simp only [CollatzResearch.WordTrace]
  refine ⟨58370471577122172134810579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38913647718081448089873719 58370471577122172134810579)
  ·
    refine ⟨87555707365683258202215869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58370471577122172134810579 87555707365683258202215869)
    ·
      refine ⟨32833390262131221825830951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87555707365683258202215869 32833390262131221825830951)
      ·
        refine ⟨49250085393196832738746427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32833390262131221825830951 49250085393196832738746427)
        ·
          refine ⟨73875128089795249108119641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49250085393196832738746427 73875128089795249108119641)
          ·
            refine ⟨55406346067346436831089731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73875128089795249108119641 55406346067346436831089731)
            ·
              refine ⟨83109519101019655246634597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55406346067346436831089731 83109519101019655246634597)
              ·
                refine ⟨15583034831441185358743987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83109519101019655246634597 15583034831441185358743987)
                ·
                  refine ⟨23374552247161778038115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15583034831441185358743987 23374552247161778038115981)
                  ·
                    refine ⟨8765457092685666764293493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23374552247161778038115981 8765457092685666764293493)
                    ·
                      refine ⟨821761602439281259152515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8765457092685666764293493 821761602439281259152515)
                      ·
                        rfl

theorem cell23_1600375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1600375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600375 prefixEnd_1600375 := by exact prefixLift 1600375
  have htrace : WordTrace (prefixWord ++ tailWord_1600375) baseStart_1600375 baseEnd_1600375 := by
    simpa [prefixWord, tailWord_1600375, baseEnd_1600375] using wordTrace_append hprefix tailTrace_1600375
  have hstable : (prefixWord ++ tailWord_1600375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600375).length < 2 ^ (prefixWord ++ tailWord_1600375).sum := by decide
  have hdescent : baseEnd_1600375 < baseStart_1600375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600389 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_1600389 : Nat := 118140960795 + 1600389 * 2 ^ 59
def prefixEnd_1600389 : Nat := 4983230072969 + 3 ^ 40 * 1600389 * 2
def baseEnd_1600389 : Nat := 821768791168444204377451

theorem tailTrace_1600389 : CollatzResearch.WordTrace tailWord_1600389 prefixEnd_1600389 821768791168444204377451 := by
  unfold tailWord_1600389
  simp only [CollatzResearch.WordTrace]
  refine ⟨58370982199071452525820221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38913988132714301683880147 58370982199071452525820221)
  ·
    refine ⟨21889118324651794697182583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58370982199071452525820221 21889118324651794697182583)
    ·
      refine ⟨32833677486977692045773875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21889118324651794697182583 32833677486977692045773875)
      ·
        refine ⟨49250516230466538068660813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32833677486977692045773875 49250516230466538068660813)
        ·
          refine ⟨18468943586424951775747805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49250516230466538068660813 18468943586424951775747805)
          ·
            refine ⟨6925853844909356915905427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18468943586424951775747805 6925853844909356915905427)
            ·
              refine ⟨10388780767364035373858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925853844909356915905427 10388780767364035373858141)
              ·
                refine ⟨3895792787761513265196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10388780767364035373858141 3895792787761513265196803)
                ·
                  refine ⟨5843689181642269897795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895792787761513265196803 5843689181642269897795205)
                  ·
                    refine ⟨1095691721557925605836601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843689181642269897795205 1095691721557925605836601)
                    ·
                      refine ⟨821768791168444204377451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095691721557925605836601 821768791168444204377451)
                      ·
                        rfl

theorem cell23_1600389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_1600389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600389 prefixEnd_1600389 := by exact prefixLift 1600389
  have htrace : WordTrace (prefixWord ++ tailWord_1600389) baseStart_1600389 baseEnd_1600389 := by
    simpa [prefixWord, tailWord_1600389, baseEnd_1600389] using wordTrace_append hprefix tailTrace_1600389
  have hstable : (prefixWord ++ tailWord_1600389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600389).length < 2 ^ (prefixWord ++ tailWord_1600389).sum := by decide
  have hdescent : baseEnd_1600389 < baseStart_1600389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600395 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 9]
def baseStart_1600395 : Nat := 118140960795 + 1600395 * 2 ^ 59
def prefixEnd_1600395 : Nat := 4983230072969 + 3 ^ 40 * 1600395 * 2
def baseEnd_1600395 : Nat := 91307985783596797878047

theorem tailTrace_1600395 : CollatzResearch.WordTrace tailWord_1600395 prefixEnd_1600395 91307985783596797878047 := by
  unfold tailWord_1600395
  simp only [CollatzResearch.WordTrace]
  refine ⟨58371201037049715550538639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38914134024699810367025759 58371201037049715550538639)
  ·
    refine ⟨87556801555574573325807959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58371201037049715550538639 87556801555574573325807959)
    ·
      refine ⟨131335202333361859988711939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87556801555574573325807959 131335202333361859988711939)
      ·
        refine ⟨197002803500042789983067909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131335202333361859988711939 197002803500042789983067909)
        ·
          refine ⟨36938025656258023121825233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197002803500042789983067909 36938025656258023121825233)
          ·
            refine ⟨27703519242193517341368925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36938025656258023121825233 27703519242193517341368925)
            ·
              refine ⟨10388819715822569003013347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27703519242193517341368925 10388819715822569003013347)
              ·
                refine ⟨15583229573733853504520021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388819715822569003013347 15583229573733853504520021)
                ·
                  refine ⟨91307985783596797878047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15583229573733853504520021 91307985783596797878047)
                  ·
                    rfl

theorem cell23_1600395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_1600395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600395 prefixEnd_1600395 := by exact prefixLift 1600395
  have htrace : WordTrace (prefixWord ++ tailWord_1600395) baseStart_1600395 baseEnd_1600395 := by
    simpa [prefixWord, tailWord_1600395, baseEnd_1600395] using wordTrace_append hprefix tailTrace_1600395
  have hstable : (prefixWord ++ tailWord_1600395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600395).length < 2 ^ (prefixWord ++ tailWord_1600395).sum := by decide
  have hdescent : baseEnd_1600395 < baseStart_1600395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600410 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1600410 : Nat := 118140960795 + 1600410 * 2 ^ 59
def prefixEnd_1600410 : Nat := 4983230072969 + 3 ^ 40 * 1600410 * 2
def baseEnd_1600410 : Nat := 821779574262188622214855

theorem tailTrace_1600410 : CollatzResearch.WordTrace tailWord_1600410 prefixEnd_1600410 821779574262188622214855 := by
  unfold tailWord_1600410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592937032998843278083671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38914498754663582074889789 14592937032998843278083671)
  ·
    refine ⟨21889405549498264917125507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14592937032998843278083671 21889405549498264917125507)
    ·
      refine ⟨32834108324247397375688261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21889405549498264917125507 32834108324247397375688261)
      ·
        refine ⟨6156395310796387007941549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32834108324247397375688261 6156395310796387007941549)
        ·
          refine ⟨2308648241548645127978081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156395310796387007941549 2308648241548645127978081)
          ·
            refine ⟨1731486181161483845983561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308648241548645127978081 1731486181161483845983561)
            ·
              refine ⟨1298614635871112884487671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731486181161483845983561 1298614635871112884487671)
              ·
                refine ⟨1947921953806669326731507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298614635871112884487671 1947921953806669326731507)
                ·
                  refine ⟨2921882930710003990097261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947921953806669326731507 2921882930710003990097261)
                  ·
                    refine ⟨1095706099016251496286473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921882930710003990097261 1095706099016251496286473)
                    ·
                      refine ⟨821779574262188622214855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095706099016251496286473 821779574262188622214855)
                      ·
                        rfl

theorem cell23_1600410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1600410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600410 prefixEnd_1600410 := by exact prefixLift 1600410
  have htrace : WordTrace (prefixWord ++ tailWord_1600410) baseStart_1600410 baseEnd_1600410 := by
    simpa [prefixWord, tailWord_1600410, baseEnd_1600410] using wordTrace_append hprefix tailTrace_1600410
  have hstable : (prefixWord ++ tailWord_1600410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600410).length < 2 ^ (prefixWord ++ tailWord_1600410).sum := by decide
  have hdescent : baseEnd_1600410 < baseStart_1600410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600423 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1600423 : Nat := 118140960795 + 1600423 * 2 ^ 59
def prefixEnd_1600423 : Nat := 4983230072969 + 3 ^ 40 * 1600423 * 2
def baseEnd_1600423 : Nat := 821786249510697071352295

theorem tailTrace_1600423 : CollatzResearch.WordTrace tailWord_1600423 prefixEnd_1600423 821786249510697071352295 := by
  unfold tailWord_1600423
  simp only [CollatzResearch.WordTrace]
  refine ⟨58372222280948276332557923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38914814853965517555038615 58372222280948276332557923)
  ·
    refine ⟨87558333421422414498836885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58372222280948276332557923 87558333421422414498836885)
    ·
      refine ⟨4104296879129175679632979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87558333421422414498836885 4104296879129175679632979)
      ·
        refine ⟨6156445318693763519449469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104296879129175679632979 6156445318693763519449469)
        ·
          refine ⟨2308666994510161319793551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156445318693763519449469 2308666994510161319793551)
          ·
            refine ⟨3463000491765241979690327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308666994510161319793551 3463000491765241979690327)
            ·
              refine ⟨5194500737647862969535491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463000491765241979690327 5194500737647862969535491)
              ·
                refine ⟨7791751106471794454303237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194500737647862969535491 7791751106471794454303237)
                ·
                  refine ⟨1460953332463461460181857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7791751106471794454303237 1460953332463461460181857)
                  ·
                    refine ⟨1095714999347596095136393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460953332463461460181857 1095714999347596095136393)
                    ·
                      refine ⟨821786249510697071352295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095714999347596095136393 821786249510697071352295)
                      ·
                        rfl

theorem cell23_1600423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1600423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600423 prefixEnd_1600423 := by exact prefixLift 1600423
  have htrace : WordTrace (prefixWord ++ tailWord_1600423) baseStart_1600423 baseEnd_1600423 := by
    simpa [prefixWord, tailWord_1600423, baseEnd_1600423] using wordTrace_append hprefix tailTrace_1600423
  have hstable : (prefixWord ++ tailWord_1600423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600423).length < 2 ^ (prefixWord ++ tailWord_1600423).sum := by decide
  have hdescent : baseEnd_1600423 < baseStart_1600423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600436 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1600436 : Nat := 118140960795 + 1600436 * 2 ^ 59
def prefixEnd_1600436 : Nat := 4983230072969 + 3 ^ 40 * 1600436 * 2
def baseEnd_1600436 : Nat := 821792924759205520489735

theorem tailTrace_1600436 : CollatzResearch.WordTrace tailWord_1600436 prefixEnd_1600436 821792924759205520489735 := by
  unfold tailWord_1600436
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186348214950589776390581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38915130953267453035187441 29186348214950589776390581)
  ·
    refine ⟨2736220145151617791536617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29186348214950589776390581 2736220145151617791536617)
    ·
      refine ⟨2052165108863713343652463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2736220145151617791536617 2052165108863713343652463)
      ·
        refine ⟨3078247663295570015478695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052165108863713343652463 3078247663295570015478695)
        ·
          refine ⟨4617371494943355023218043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078247663295570015478695 4617371494943355023218043)
          ·
            refine ⟨6926057242415032534827065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617371494943355023218043 6926057242415032534827065)
            ·
              refine ⟨5194542931811274401120299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926057242415032534827065 5194542931811274401120299)
              ·
                refine ⟨7791814397716911601680449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194542931811274401120299 7791814397716911601680449)
                ·
                  refine ⟨5843860798287683701260337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791814397716911601680449 5843860798287683701260337)
                  ·
                    refine ⟨4382895598715762775945253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843860798287683701260337 4382895598715762775945253)
                    ·
                      refine ⟨821792924759205520489735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4382895598715762775945253 821792924759205520489735)
                      ·
                        rfl

theorem cell23_1600436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1600436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600436 prefixEnd_1600436 := by exact prefixLift 1600436
  have htrace : WordTrace (prefixWord ++ tailWord_1600436) baseStart_1600436 baseEnd_1600436 := by
    simpa [prefixWord, tailWord_1600436, baseEnd_1600436] using wordTrace_append hprefix tailTrace_1600436
  have hstable : (prefixWord ++ tailWord_1600436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600436).length < 2 ^ (prefixWord ++ tailWord_1600436).sum := by decide
  have hdescent : baseEnd_1600436 < baseStart_1600436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600566 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1600566 : Nat := 118140960795 + 1600566 * 2 ^ 59
def prefixEnd_1600566 : Nat := 4983230072969 + 3 ^ 40 * 1600566 * 2
def baseEnd_1600566 : Nat := 273953225748096670621379

theorem tailTrace_1600566 : CollatzResearch.WordTrace tailWord_1600566 prefixEnd_1600566 273953225748096670621379 := by
  unfold tailWord_1600566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648589869964388234688347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38918291946286807836675701 3648589869964388234688347)
  ·
    refine ⟨5472884804946582352032521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648589869964388234688347 5472884804946582352032521)
    ·
      refine ⟨4104663603709936764024391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472884804946582352032521 4104663603709936764024391)
      ·
        refine ⟨6156995405564905146036587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104663603709936764024391 6156995405564905146036587)
        ·
          refine ⟨9235493108347357719054881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156995405564905146036587 9235493108347357719054881)
          ·
            refine ⟨6926619831260518289291161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235493108347357719054881 6926619831260518289291161)
            ·
              refine ⟨5194964873445388716968371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926619831260518289291161 5194964873445388716968371)
              ·
                refine ⟨7792447310168083075452557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194964873445388716968371 7792447310168083075452557)
                ·
                  refine ⟨2922167741313031153294709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7792447310168083075452557 2922167741313031153294709)
                  ·
                    refine ⟨273953225748096670621379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2922167741313031153294709 273953225748096670621379)
                    ·
                      rfl

theorem cell23_1600566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1600566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600566 prefixEnd_1600566 := by exact prefixLift 1600566
  have htrace : WordTrace (prefixWord ++ tailWord_1600566) baseStart_1600566 baseEnd_1600566 := by
    simpa [prefixWord, tailWord_1600566, baseEnd_1600566] using wordTrace_append hprefix tailTrace_1600566
  have hstable : (prefixWord ++ tailWord_1600566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600566).length < 2 ^ (prefixWord ++ tailWord_1600566).sum := by decide
  have hdescent : baseEnd_1600566 < baseStart_1600566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600573 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1600573 : Nat := 118140960795 + 1600573 * 2 ^ 59
def prefixEnd_1600573 : Nat := 4983230072969 + 3 ^ 40 * 1600573 * 2
def baseEnd_1600573 : Nat := 821863271608871484476605

theorem tailTrace_1600573 : CollatzResearch.WordTrace tailWord_1600573 prefixEnd_1600573 821863271608871484476605 := by
  unfold tailWord_1600573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58377693230404851950518373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38918462153603234633678915 58377693230404851950518373)
  ·
    refine ⟨10945817480700909740722195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58377693230404851950518373 10945817480700909740722195)
    ·
      refine ⟨16418726221051364611083293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945817480700909740722195 16418726221051364611083293)
      ·
        refine ⟨6157022332894261729156235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16418726221051364611083293 6157022332894261729156235)
        ·
          refine ⟨9235533499341392593734353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157022332894261729156235 9235533499341392593734353)
          ·
            refine ⟨6926650124506044445300765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235533499341392593734353 6926650124506044445300765)
            ·
              refine ⟨2597493796689766666987787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6926650124506044445300765 2597493796689766666987787)
              ·
                refine ⟨3896240695034650000481681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597493796689766666987787 3896240695034650000481681)
                ·
                  refine ⟨2922180521275987500361261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896240695034650000481681 2922180521275987500361261)
                  ·
                    refine ⟨1095817695478495312635473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922180521275987500361261 1095817695478495312635473)
                    ·
                      refine ⟨821863271608871484476605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095817695478495312635473 821863271608871484476605)
                      ·
                        rfl

theorem cell23_1600573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1600573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600573 prefixEnd_1600573 := by exact prefixLift 1600573
  have htrace : WordTrace (prefixWord ++ tailWord_1600573) baseStart_1600573 baseEnd_1600573 := by
    simpa [prefixWord, tailWord_1600573, baseEnd_1600573] using wordTrace_append hprefix tailTrace_1600573
  have hstable : (prefixWord ++ tailWord_1600573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600573).length < 2 ^ (prefixWord ++ tailWord_1600573).sum := by decide
  have hdescent : baseEnd_1600573 < baseStart_1600573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600579 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 4, 4]
def baseStart_1600579 : Nat := 118140960795 + 1600579 * 2 ^ 59
def prefixEnd_1600579 : Nat := 4983230072969 + 3 ^ 40 * 1600579 * 2
def baseEnd_1600579 : Nat := 273955450830932820333859

theorem tailTrace_1600579 : CollatzResearch.WordTrace tailWord_1600579 prefixEnd_1600579 273955450830932820333859 := by
  unfold tailWord_1600579
  simp only [CollatzResearch.WordTrace]
  refine ⟨58377912068383114975236791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38918608045588743316824527 58377912068383114975236791)
  ·
    refine ⟨87566868102574672462855187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58377912068383114975236791 87566868102574672462855187)
    ·
      refine ⟨131350302153862008694282781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87566868102574672462855187 131350302153862008694282781)
      ·
        refine ⟨49256363307698253260356043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131350302153862008694282781 49256363307698253260356043)
        ·
          refine ⟨73884544961547379890534065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49256363307698253260356043 73884544961547379890534065)
          ·
            refine ⟨55413408721160534917900549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73884544961547379890534065 55413408721160534917900549)
            ·
              refine ⟨10390014135217600297106353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55413408721160534917900549 10390014135217600297106353)
              ·
                refine ⟨7792510601413200222829765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390014135217600297106353 7792510601413200222829765)
                ·
                  refine ⟨1461095737764975041780581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7792510601413200222829765 1461095737764975041780581)
                  ·
                    refine ⟨273955450830932820333859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461095737764975041780581 273955450830932820333859)
                    ·
                      rfl

theorem cell23_1600579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 4].length) (baseStart_1600579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600579 prefixEnd_1600579 := by exact prefixLift 1600579
  have htrace : WordTrace (prefixWord ++ tailWord_1600579) baseStart_1600579 baseEnd_1600579 := by
    simpa [prefixWord, tailWord_1600579, baseEnd_1600579] using wordTrace_append hprefix tailTrace_1600579
  have hstable : (prefixWord ++ tailWord_1600579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600579).length < 2 ^ (prefixWord ++ tailWord_1600579).sum := by decide
  have hdescent : baseEnd_1600579 < baseStart_1600579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600583 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 1, 5]
def baseStart_1600583 : Nat := 118140960795 + 1600583 * 2 ^ 59
def prefixEnd_1600583 : Nat := 4983230072969 + 3 ^ 40 * 1600583 * 2
def baseEnd_1600583 : Nat := 273956135471805481783853

theorem tailTrace_1600583 : CollatzResearch.WordTrace tailWord_1600583 prefixEnd_1600583 273956135471805481783853 := by
  unfold tailWord_1600583
  simp only [CollatzResearch.WordTrace]
  refine ⟨58378057960368623658382403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38918705306912415772254935 58378057960368623658382403)
  ·
    refine ⟨87567086940552935487573605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58378057960368623658382403 87567086940552935487573605)
    ·
      refine ⟨16418828801353675403920051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87567086940552935487573605 16418828801353675403920051)
      ·
        refine ⟨24628243202030513105880077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16418828801353675403920051 24628243202030513105880077)
        ·
          refine ⟨9235591200761442414705029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24628243202030513105880077 9235591200761442414705029)
          ·
            refine ⟨1731673350142770452757193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9235591200761442414705029 1731673350142770452757193)
            ·
              refine ⟨1298755012607077839567895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731673350142770452757193 1298755012607077839567895)
              ·
                refine ⟨1948132518910616759351843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298755012607077839567895 1948132518910616759351843)
                ·
                  refine ⟨2922198778365925139027765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948132518910616759351843 2922198778365925139027765)
                  ·
                    refine ⟨273956135471805481783853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2922198778365925139027765 273956135471805481783853)
                    ·
                      rfl

theorem cell23_1600583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_1600583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600583 prefixEnd_1600583 := by exact prefixLift 1600583
  have htrace : WordTrace (prefixWord ++ tailWord_1600583) baseStart_1600583 baseEnd_1600583 := by
    simpa [prefixWord, tailWord_1600583, baseEnd_1600583] using wordTrace_append hprefix tailTrace_1600583
  have hstable : (prefixWord ++ tailWord_1600583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600583).length < 2 ^ (prefixWord ++ tailWord_1600583).sum := by decide
  have hdescent : baseEnd_1600583 < baseStart_1600583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600613 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1600613 : Nat := 118140960795 + 1600613 * 2 ^ 59
def prefixEnd_1600613 : Nat := 4983230072969 + 3 ^ 40 * 1600613 * 2
def baseEnd_1600613 : Nat := 273961270278350442658807

theorem tailTrace_1600613 : CollatzResearch.WordTrace tailWord_1600613 prefixEnd_1600613 273961270278350442658807 := by
  unfold tailWord_1600613
  simp only [CollatzResearch.WordTrace]
  refine ⟨58379152150259938781974493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38919434766839959187982995 58379152150259938781974493)
  ·
    refine ⟨21892182056347477043240435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58379152150259938781974493 21892182056347477043240435)
    ·
      refine ⟨32838273084521215564860653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21892182056347477043240435 32838273084521215564860653)
      ·
        refine ⟨12314352406695455836822745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32838273084521215564860653 12314352406695455836822745)
        ·
          refine ⟨9235764305021591877617059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314352406695455836822745 9235764305021591877617059)
          ·
            refine ⟨13853646457532387816425589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235764305021591877617059 13853646457532387816425589)
            ·
              refine ⟨1298779355393661357789899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13853646457532387816425589 1298779355393661357789899)
              ·
                refine ⟨1948169033090492036684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298779355393661357789899 1948169033090492036684849)
                ·
                  refine ⟨1461126774817869027513637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948169033090492036684849 1461126774817869027513637)
                  ·
                    refine ⟨273961270278350442658807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461126774817869027513637 273961270278350442658807)
                    ·
                      rfl

theorem cell23_1600613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1600613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600613 prefixEnd_1600613 := by exact prefixLift 1600613
  have htrace : WordTrace (prefixWord ++ tailWord_1600613) baseStart_1600613 baseEnd_1600613 := by
    simpa [prefixWord, tailWord_1600613, baseEnd_1600613] using wordTrace_append hprefix tailTrace_1600613
  have hstable : (prefixWord ++ tailWord_1600613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600613).length < 2 ^ (prefixWord ++ tailWord_1600613).sum := by decide
  have hdescent : baseEnd_1600613 < baseStart_1600613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600636 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_1600636 : Nat := 118140960795 + 1600636 * 2 ^ 59
def prefixEnd_1600636 : Nat := 4983230072969 + 3 ^ 40 * 1600636 * 2
def baseEnd_1600636 : Nat := 821895620890104737988815

theorem tailTrace_1600636 : CollatzResearch.WordTrace tailWord_1600636 prefixEnd_1600636 821895620890104737988815 := by
  unfold tailWord_1600636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189995514588306855030881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38919994019451075806707841 29189995514588306855030881)
  ·
    refine ⟨21892496635941230141273161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29189995514588306855030881 21892496635941230141273161)
    ·
      refine ⟨16419372476955922605954871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21892496635941230141273161 16419372476955922605954871)
      ·
        refine ⟨24629058715433883908932307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16419372476955922605954871 24629058715433883908932307)
        ·
          refine ⟨36943588073150825863398461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24629058715433883908932307 36943588073150825863398461)
          ·
            refine ⟨13853845527431559698774423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36943588073150825863398461 13853845527431559698774423)
            ·
              refine ⟨20780768291147339548161635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853845527431559698774423 20780768291147339548161635)
              ·
                refine ⟨31171152436721009322242453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20780768291147339548161635 31171152436721009322242453)
                ·
                  refine ⟨1461147770471297311980115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31171152436721009322242453 1461147770471297311980115)
                  ·
                    refine ⟨2191721655706945967970173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461147770471297311980115 2191721655706945967970173)
                    ·
                      refine ⟨821895620890104737988815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2191721655706945967970173 821895620890104737988815)
                      ·
                        rfl

theorem cell23_1600636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_1600636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600636 prefixEnd_1600636 := by exact prefixLift 1600636
  have htrace : WordTrace (prefixWord ++ tailWord_1600636) baseStart_1600636 baseEnd_1600636 := by
    simpa [prefixWord, tailWord_1600636, baseEnd_1600636] using wordTrace_append hprefix tailTrace_1600636
  have hstable : (prefixWord ++ tailWord_1600636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600636).length < 2 ^ (prefixWord ++ tailWord_1600636).sum := by decide
  have hdescent : baseEnd_1600636 < baseStart_1600636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600654 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1600654 : Nat := 118140960795 + 1600654 * 2 ^ 59
def prefixEnd_1600654 : Nat := 4983230072969 + 3 ^ 40 * 1600654 * 2
def baseEnd_1600654 : Nat := 821904863541885667563733

theorem tailTrace_1600654 : CollatzResearch.WordTrace tailWord_1600654 prefixEnd_1600654 821904863541885667563733 := by
  unfold tailWord_1600654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297580942888925348027127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38920431695407601856144677 7297580942888925348027127)
  ·
    refine ⟨10946371414333388022040691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7297580942888925348027127 10946371414333388022040691)
    ·
      refine ⟨16419557121500082033061037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10946371414333388022040691 16419557121500082033061037)
      ·
        refine ⟨6157333920562530762397889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16419557121500082033061037 6157333920562530762397889)
        ·
          refine ⟨4618000440421898071798417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157333920562530762397889 4618000440421898071798417)
          ·
            refine ⟨3463500330316423553848813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618000440421898071798417 3463500330316423553848813)
            ·
              refine ⟨1298812623868658832693305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3463500330316423553848813 1298812623868658832693305)
              ·
                refine ⟨974109467901494124519979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298812623868658832693305 974109467901494124519979)
                ·
                  refine ⟨1461164201852241186779969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974109467901494124519979 1461164201852241186779969)
                  ·
                    refine ⟨1095873151389180890084977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1461164201852241186779969 1095873151389180890084977)
                    ·
                      refine ⟨821904863541885667563733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1095873151389180890084977 821904863541885667563733)
                      ·
                        rfl

theorem cell23_1600654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1600654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600654 prefixEnd_1600654 := by exact prefixLift 1600654
  have htrace : WordTrace (prefixWord ++ tailWord_1600654) baseStart_1600654 baseEnd_1600654 := by
    simpa [prefixWord, tailWord_1600654, baseEnd_1600654] using wordTrace_append hprefix tailTrace_1600654
  have hstable : (prefixWord ++ tailWord_1600654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600654).length < 2 ^ (prefixWord ++ tailWord_1600654).sum := by decide
  have hdescent : baseEnd_1600654 < baseStart_1600654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600669 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1600669 : Nat := 118140960795 + 1600669 * 2 ^ 59
def prefixEnd_1600669 : Nat := 4983230072969 + 3 ^ 40 * 1600669 * 2
def baseEnd_1600669 : Nat := 273970855250567702958721

theorem tailTrace_1600669 : CollatzResearch.WordTrace tailWord_1600669 prefixEnd_1600669 273970855250567702958721 := by
  unfold tailWord_1600669
  simp only [CollatzResearch.WordTrace]
  refine ⟨58381194638057060346013061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38920796425371373564008707 58381194638057060346013061)
  ·
    refine ⟨10946473994635698814877449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58381194638057060346013061 10946473994635698814877449)
    ·
      refine ⟨8209855495976774111158087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10946473994635698814877449 8209855495976774111158087)
      ·
        refine ⟨12314783243965161166737131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209855495976774111158087 12314783243965161166737131)
        ·
          refine ⟨18472174865947741750105697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12314783243965161166737131 18472174865947741750105697)
          ·
            refine ⟨13854131149460806312579273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18472174865947741750105697 13854131149460806312579273)
            ·
              refine ⟨10390598362095604734434455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13854131149460806312579273 10390598362095604734434455)
              ·
                refine ⟨15585897543143407101651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390598362095604734434455 15585897543143407101651683)
                ·
                  refine ⟨23378846314715110652477525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15585897543143407101651683 23378846314715110652477525)
                  ·
                    refine ⟨273970855250567702958721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23378846314715110652477525 273970855250567702958721)
                    ·
                      rfl

theorem cell23_1600669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1600669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600669 prefixEnd_1600669 := by exact prefixLift 1600669
  have htrace : WordTrace (prefixWord ++ tailWord_1600669) baseStart_1600669 baseEnd_1600669 := by
    simpa [prefixWord, tailWord_1600669, baseEnd_1600669] using wordTrace_append hprefix tailTrace_1600669
  have hstable : (prefixWord ++ tailWord_1600669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600669).length < 2 ^ (prefixWord ++ tailWord_1600669).sum := by decide
  have hdescent : baseEnd_1600669 < baseStart_1600669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600729 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_1600729 : Nat := 118140960795 + 1600729 * 2 ^ 59
def prefixEnd_1600729 : Nat := 4983230072969 + 3 ^ 40 * 1600729 * 2
def baseEnd_1600729 : Nat := 273981124863657624708629

theorem tailTrace_1600729 : CollatzResearch.WordTrace tailWord_1600729 prefixEnd_1600729 273981124863657624708629 := by
  unfold tailWord_1600729
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383383017839690593197241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38922255345226460395464827 58383383017839690593197241)
  ·
    refine ⟨43787537263379767944897931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58383383017839690593197241 43787537263379767944897931)
    ·
      refine ⟨65681305895069651917346897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43787537263379767944897931 65681305895069651917346897)
      ·
        refine ⟨49260979421302238938010173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65681305895069651917346897 49260979421302238938010173)
        ·
          refine ⟨18472867282988339601753815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49260979421302238938010173 18472867282988339601753815)
          ·
            refine ⟨27709300924482509402630723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18472867282988339601753815 27709300924482509402630723)
            ·
              refine ⟨41563951386723764103946085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709300924482509402630723 41563951386723764103946085)
              ·
                refine ⟨7793240885010705769489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41563951386723764103946085 7793240885010705769489891)
                ·
                  refine ⟨11689861327516058654234837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793240885010705769489891 11689861327516058654234837)
                  ·
                    refine ⟨273981124863657624708629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11689861327516058654234837 273981124863657624708629)
                    ·
                      rfl

theorem cell23_1600729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_1600729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600729 prefixEnd_1600729 := by exact prefixLift 1600729
  have htrace : WordTrace (prefixWord ++ tailWord_1600729) baseStart_1600729 baseEnd_1600729 := by
    simpa [prefixWord, tailWord_1600729, baseEnd_1600729] using wordTrace_append hprefix tailTrace_1600729
  have hstable : (prefixWord ++ tailWord_1600729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600729).length < 2 ^ (prefixWord ++ tailWord_1600729).sum := by decide
  have hdescent : baseEnd_1600729 < baseStart_1600729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600733 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1600733 : Nat := 118140960795 + 1600733 * 2 ^ 59
def prefixEnd_1600733 : Nat := 4983230072969 + 3 ^ 40 * 1600733 * 2
def baseEnd_1600733 : Nat := 91327269834843428719541

theorem tailTrace_1600733 : CollatzResearch.WordTrace tailWord_1600733 prefixEnd_1600733 91327269834843428719541 := by
  unfold tailWord_1600733
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383528909825199276342853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38922352606550132850895235 58383528909825199276342853)
  ·
    refine ⟨10946911670592224864314285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58383528909825199276342853 10946911670592224864314285)
    ·
      refine ⟨4105091876472084324117857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10946911670592224864314285 4105091876472084324117857)
      ·
        refine ⟨3078818907354063243088393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4105091876472084324117857 3078818907354063243088393)
        ·
          refine ⟨2309114180515547432316295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078818907354063243088393 2309114180515547432316295)
          ·
            refine ⟨3463671270773321148474443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309114180515547432316295 3463671270773321148474443)
            ·
              refine ⟨5195506906159981722711665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463671270773321148474443 5195506906159981722711665)
              ·
                refine ⟨3896630179619986292033749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195506906159981722711665 3896630179619986292033749)
                ·
                  refine ⟨91327269834843428719541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3896630179619986292033749 91327269834843428719541)
                  ·
                    rfl

theorem cell23_1600733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1600733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600733 prefixEnd_1600733 := by exact prefixLift 1600733
  have htrace : WordTrace (prefixWord ++ tailWord_1600733) baseStart_1600733 baseEnd_1600733 := by
    simpa [prefixWord, tailWord_1600733, baseEnd_1600733] using wordTrace_append hprefix tailTrace_1600733
  have hstable : (prefixWord ++ tailWord_1600733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600733).length < 2 ^ (prefixWord ++ tailWord_1600733).sum := by decide
  have hdescent : baseEnd_1600733 < baseStart_1600733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600746 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1600746 : Nat := 118140960795 + 1600746 * 2 ^ 59
def prefixEnd_1600746 : Nat := 4983230072969 + 3 ^ 40 * 1600746 * 2
def baseEnd_1600746 : Nat := 273984034587366435871103

theorem tailTrace_1600746 : CollatzResearch.WordTrace tailWord_1600746 prefixEnd_1600746 273984034587366435871103 := by
  unfold tailWord_1600746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596000764694525624141523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38922668705852068331044061 14596000764694525624141523)
  ·
    refine ⟨21894001147041788436212285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596000764694525624141523 21894001147041788436212285)
    ·
      refine ⟨8210250430140670663579607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21894001147041788436212285 8210250430140670663579607)
      ·
        refine ⟨12315375645211005995369411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210250430140670663579607 12315375645211005995369411)
        ·
          refine ⟨18473063467816508993054117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315375645211005995369411 18473063467816508993054117)
          ·
            refine ⟨3463699400215595436197647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18473063467816508993054117 3463699400215595436197647)
            ·
              refine ⟨5195549100323393154296471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463699400215595436197647 5195549100323393154296471)
              ·
                refine ⟨7793323650485089731444707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195549100323393154296471 7793323650485089731444707)
                ·
                  refine ⟨11689985475727634597167061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793323650485089731444707 11689985475727634597167061)
                  ·
                    refine ⟨273984034587366435871103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11689985475727634597167061 273984034587366435871103)
                    ·
                      rfl

theorem cell23_1600746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1600746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600746 prefixEnd_1600746 := by exact prefixLift 1600746
  have htrace : WordTrace (prefixWord ++ tailWord_1600746) baseStart_1600746 baseEnd_1600746 := by
    simpa [prefixWord, tailWord_1600746, baseEnd_1600746] using wordTrace_append hprefix tailTrace_1600746
  have hstable : (prefixWord ++ tailWord_1600746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600746).length < 2 ^ (prefixWord ++ tailWord_1600746).sum := by decide
  have hdescent : baseEnd_1600746 < baseStart_1600746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600820 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1600820 : Nat := 118140960795 + 1600820 * 2 ^ 59
def prefixEnd_1600820 : Nat := 4983230072969 + 3 ^ 40 * 1600820 * 2
def baseEnd_1600820 : Nat := 821990101330532018087969

theorem tailTrace_1600820 : CollatzResearch.WordTrace tailWord_1600820 prefixEnd_1600820 821990101330532018087969 := by
  unfold tailWord_1600820
  simp only [CollatzResearch.WordTrace]
  refine ⟨29193351030255006567379957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38924468040340008756506609 29193351030255006567379957)
  ·
    refine ⟨2736876659086406865691871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29193351030255006567379957 2736876659086406865691871)
    ·
      refine ⟨4105314988629610298537807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736876659086406865691871 4105314988629610298537807)
      ·
        refine ⟨6157972482944415447806711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105314988629610298537807 6157972482944415447806711)
        ·
          refine ⟨9236958724416623171710067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157972482944415447806711 9236958724416623171710067)
          ·
            refine ⟨13855438086624934757565101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9236958724416623171710067 13855438086624934757565101)
            ·
              refine ⟨5195789282484350534086913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13855438086624934757565101 5195789282484350534086913)
              ·
                refine ⟨3896841961863262900565185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195789282484350534086913 3896841961863262900565185)
                ·
                  refine ⟨2922631471397447175423889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896841961863262900565185 2922631471397447175423889)
                  ·
                    refine ⟨2191973603548085381567917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922631471397447175423889 2191973603548085381567917)
                    ·
                      refine ⟨821990101330532018087969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2191973603548085381567917 821990101330532018087969)
                      ·
                        rfl

theorem cell23_1600820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1600820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600820 prefixEnd_1600820 := by exact prefixLift 1600820
  have htrace : WordTrace (prefixWord ++ tailWord_1600820) baseStart_1600820 baseEnd_1600820 := by
    simpa [prefixWord, tailWord_1600820, baseEnd_1600820] using wordTrace_append hprefix tailTrace_1600820
  have hstable : (prefixWord ++ tailWord_1600820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600820).length < 2 ^ (prefixWord ++ tailWord_1600820).sum := by decide
  have hdescent : baseEnd_1600820 < baseStart_1600820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600853 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1600853 : Nat := 118140960795 + 1600853 * 2 ^ 59
def prefixEnd_1600853 : Nat := 4983230072969 + 3 ^ 40 * 1600853 * 2
def baseEnd_1600853 : Nat := 274002348730710129658439

theorem tailTrace_1600853 : CollatzResearch.WordTrace tailWord_1600853 prefixEnd_1600853 274002348730710129658439 := by
  unfold tailWord_1600853
  simp only [CollatzResearch.WordTrace]
  refine ⟨58387905669390459770711213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38925270446260306513807475 58387905669390459770711213)
  ·
    refine ⟨21895464626021422414016705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58387905669390459770711213 21895464626021422414016705)
    ·
      refine ⟨16421598469516066810512529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21895464626021422414016705 16421598469516066810512529)
      ·
        refine ⟨12316198852137050107884397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16421598469516066810512529 12316198852137050107884397)
        ·
          refine ⟨4618574569551393790456649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12316198852137050107884397 4618574569551393790456649)
          ·
            refine ⟨3463930927163545342842487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618574569551393790456649 3463930927163545342842487)
            ·
              refine ⟨5195896390745318014263731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463930927163545342842487 5195896390745318014263731)
              ·
                refine ⟨7793844586117977021395597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195896390745318014263731 7793844586117977021395597)
                ·
                  refine ⟨2922691719794241383023349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7793844586117977021395597 2922691719794241383023349)
                  ·
                    refine ⟨274002348730710129658439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2922691719794241383023349 274002348730710129658439)
                    ·
                      rfl

theorem cell23_1600853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1600853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600853 prefixEnd_1600853 := by exact prefixLift 1600853
  have htrace : WordTrace (prefixWord ++ tailWord_1600853) baseStart_1600853 baseEnd_1600853 := by
    simpa [prefixWord, tailWord_1600853, baseEnd_1600853] using wordTrace_append hprefix tailTrace_1600853
  have hstable : (prefixWord ++ tailWord_1600853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600853).length < 2 ^ (prefixWord ++ tailWord_1600853).sum := by decide
  have hdescent : baseEnd_1600853 < baseStart_1600853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600878 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1600878 : Nat := 118140960795 + 1600878 * 2 ^ 59
def prefixEnd_1600878 : Nat := 4983230072969 + 3 ^ 40 * 1600878 * 2
def baseEnd_1600878 : Nat := 274006627736164263720901

theorem tailTrace_1600878 : CollatzResearch.WordTrace tailWord_1600878 prefixEnd_1600878 274006627736164263720901 := by
  unfold tailWord_1600878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298602186787486130046411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38925878329533259360247525 7298602186787486130046411)
  ·
    refine ⟨10947903280181229195069617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298602186787486130046411 10947903280181229195069617)
    ·
      refine ⟨8210927460135921896302213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947903280181229195069617 8210927460135921896302213)
      ·
        refine ⟨1539548898775485355556665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8210927460135921896302213 1539548898775485355556665)
        ·
          refine ⟨1154661674081614016667499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539548898775485355556665 1154661674081614016667499)
          ·
            refine ⟨1731992511122421025001249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154661674081614016667499 1731992511122421025001249)
            ·
              refine ⟨1298994383341815768750937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731992511122421025001249 1298994383341815768750937)
              ·
                refine ⟨974245787506361826563203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298994383341815768750937 974245787506361826563203)
                ·
                  refine ⟨1461368681259542739844805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974245787506361826563203 1461368681259542739844805)
                  ·
                    refine ⟨274006627736164263720901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461368681259542739844805 274006627736164263720901)
                    ·
                      rfl

theorem cell23_1600878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1600878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600878 prefixEnd_1600878 := by exact prefixLift 1600878
  have htrace : WordTrace (prefixWord ++ tailWord_1600878) baseStart_1600878 baseEnd_1600878 := by
    simpa [prefixWord, tailWord_1600878, baseEnd_1600878] using wordTrace_append hprefix tailTrace_1600878
  have hstable : (prefixWord ++ tailWord_1600878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600878).length < 2 ^ (prefixWord ++ tailWord_1600878).sum := by decide
  have hdescent : baseEnd_1600878 < baseStart_1600878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600893 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1600893 : Nat := 118140960795 + 1600893 * 2 ^ 59
def prefixEnd_1600893 : Nat := 4983230072969 + 3 ^ 40 * 1600893 * 2
def baseEnd_1600893 : Nat := 822027585418310232475133

theorem tailTrace_1600893 : CollatzResearch.WordTrace tailWord_1600893 prefixEnd_1600893 822027585418310232475133 := by
  unfold tailWord_1600893
  simp only [CollatzResearch.WordTrace]
  refine ⟨58389364589245546602167333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38926243059497031068111555 58389364589245546602167333)
  ·
    refine ⟨10948005860483539987906375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58389364589245546602167333 10948005860483539987906375)
    ·
      refine ⟨16422008790725309981859563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10948005860483539987906375 16422008790725309981859563)
      ·
        refine ⟨24633013186087964972789345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16422008790725309981859563 24633013186087964972789345)
        ·
          refine ⟨18474759889565973729592009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24633013186087964972789345 18474759889565973729592009)
          ·
            refine ⟨13856069917174480297194007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18474759889565973729592009 13856069917174480297194007)
            ·
              refine ⟨20784104875761720445791011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856069917174480297194007 20784104875761720445791011)
              ·
                refine ⟨31176157313642580668686517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20784104875761720445791011 31176157313642580668686517)
                ·
                  refine ⟨2922764748153991937689361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31176157313642580668686517 2922764748153991937689361)
                  ·
                    refine ⟨2192073561115493953267021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922764748153991937689361 2192073561115493953267021)
                    ·
                      refine ⟨822027585418310232475133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192073561115493953267021 822027585418310232475133)
                      ·
                        rfl

theorem cell23_1600893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1600893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600893 prefixEnd_1600893 := by exact prefixLift 1600893
  have htrace : WordTrace (prefixWord ++ tailWord_1600893) baseStart_1600893 baseEnd_1600893 := by
    simpa [prefixWord, tailWord_1600893, baseEnd_1600893] using wordTrace_append hprefix tailTrace_1600893
  have hstable : (prefixWord ++ tailWord_1600893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600893).length < 2 ^ (prefixWord ++ tailWord_1600893).sum := by decide
  have hdescent : baseEnd_1600893 < baseStart_1600893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600900 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1600900 : Nat := 118140960795 + 1600900 * 2 ^ 59
def prefixEnd_1600900 : Nat := 4983230072969 + 3 ^ 40 * 1600900 * 2
def baseEnd_1600900 : Nat := 274010393260963901695867

theorem tailTrace_1600900 : CollatzResearch.WordTrace tailWord_1600900 prefixEnd_1600900 274010393260963901695867 := by
  unfold tailWord_1600900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194809950110093398836077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38926413266813457865114769 29194809950110093398836077)
  ·
    refine ⟨10948053731291285024563529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29194809950110093398836077 10948053731291285024563529)
    ·
      refine ⟨8211040298468463768422647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10948053731291285024563529 8211040298468463768422647)
      ·
        refine ⟨12316560447702695652633971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211040298468463768422647 12316560447702695652633971)
        ·
          refine ⟨18474840671554043478950957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316560447702695652633971 18474840671554043478950957)
          ·
            refine ⟨6928065251832766304606609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18474840671554043478950957 6928065251832766304606609)
            ·
              refine ⟨5196048938874574728454957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6928065251832766304606609 5196048938874574728454957)
              ·
                refine ⟨1948518352077965523170609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196048938874574728454957 1948518352077965523170609)
                ·
                  refine ⟨1461388764058474142377957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948518352077965523170609 1461388764058474142377957)
                  ·
                    refine ⟨274010393260963901695867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461388764058474142377957 274010393260963901695867)
                    ·
                      rfl

theorem cell23_1600900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1600900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600900 prefixEnd_1600900 := by exact prefixLift 1600900
  have htrace : WordTrace (prefixWord ++ tailWord_1600900) baseStart_1600900 baseEnd_1600900 := by
    simpa [prefixWord, tailWord_1600900, baseEnd_1600900] using wordTrace_append hprefix tailTrace_1600900
  have hstable : (prefixWord ++ tailWord_1600900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600900).length < 2 ^ (prefixWord ++ tailWord_1600900).sum := by decide
  have hdescent : baseEnd_1600900 < baseStart_1600900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600903 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1600903 : Nat := 118140960795 + 1600903 * 2 ^ 59
def prefixEnd_1600903 : Nat := 4983230072969 + 3 ^ 40 * 1600903 * 2
def baseEnd_1600903 : Nat := 822032720224855193350087

theorem tailTrace_1600903 : CollatzResearch.WordTrace tailWord_1600903 prefixEnd_1600903 822032720224855193350087 := by
  unfold tailWord_1600903
  simp only [CollatzResearch.WordTrace]
  refine ⟨58389729319209318310031363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38926486212806212206687575 58389729319209318310031363)
  ·
    refine ⟨87584593978813977465047045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58389729319209318310031363 87584593978813977465047045)
    ·
      refine ⟨16422111371027620774696321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87584593978813977465047045 16422111371027620774696321)
      ·
        refine ⟨12316583528270715581022241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16422111371027620774696321 12316583528270715581022241)
        ·
          refine ⟨9237437646203036685766681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12316583528270715581022241 9237437646203036685766681)
          ·
            refine ⟨6928078234652277514325011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9237437646203036685766681 6928078234652277514325011)
            ·
              refine ⟨10392117351978416271487517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6928078234652277514325011 10392117351978416271487517)
              ·
                refine ⟨3897044006991906101807819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10392117351978416271487517 3897044006991906101807819)
                ·
                  refine ⟨5845566010487859152711729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897044006991906101807819 5845566010487859152711729)
                  ·
                    refine ⟨4384174507865894364533797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5845566010487859152711729 4384174507865894364533797)
                    ·
                      refine ⟨822032720224855193350087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4384174507865894364533797 822032720224855193350087)
                      ·
                        rfl

theorem cell23_1600903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1600903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600903 prefixEnd_1600903 := by exact prefixLift 1600903
  have htrace : WordTrace (prefixWord ++ tailWord_1600903) baseStart_1600903 baseEnd_1600903 := by
    simpa [prefixWord, tailWord_1600903, baseEnd_1600903] using wordTrace_append hprefix tailTrace_1600903
  have hstable : (prefixWord ++ tailWord_1600903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600903).length < 2 ^ (prefixWord ++ tailWord_1600903).sum := by decide
  have hdescent : baseEnd_1600903 < baseStart_1600903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600927 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1600927 : Nat := 118140960795 + 1600927 * 2 ^ 59
def prefixEnd_1600927 : Nat := 4983230072969 + 3 ^ 40 * 1600927 * 2
def baseEnd_1600927 : Nat := 822045043760563099449977

theorem tailTrace_1600927 : CollatzResearch.WordTrace tailWord_1600927 prefixEnd_1600927 822045043760563099449977 := by
  unfold tailWord_1600927
  simp only [CollatzResearch.WordTrace]
  refine ⟨58390604671122370408905035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38927069780748246939270023 58390604671122370408905035)
  ·
    refine ⟨87585907006683555613357553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58390604671122370408905035 87585907006683555613357553)
    ·
      refine ⟨65689430255012666710018165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87585907006683555613357553 65689430255012666710018165)
      ·
        refine ⟨6158384086407437504064203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65689430255012666710018165 6158384086407437504064203)
        ·
          refine ⟨9237576129611156256096305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158384086407437504064203 9237576129611156256096305)
          ·
            refine ⟨6928182097208367192072229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9237576129611156256096305 6928182097208367192072229)
            ·
              refine ⟨1299034143226568848513543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6928182097208367192072229 1299034143226568848513543)
              ·
                refine ⟨1948551214839853272770315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299034143226568848513543 1948551214839853272770315)
                ·
                  refine ⟨2922826822259779909155473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948551214839853272770315 2922826822259779909155473)
                  ·
                    refine ⟨2192120116694834931866605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922826822259779909155473 2192120116694834931866605)
                    ·
                      refine ⟨822045043760563099449977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192120116694834931866605 822045043760563099449977)
                      ·
                        rfl

theorem cell23_1600927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1600927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600927 prefixEnd_1600927 := by exact prefixLift 1600927
  have htrace : WordTrace (prefixWord ++ tailWord_1600927) baseStart_1600927 baseEnd_1600927 := by
    simpa [prefixWord, tailWord_1600927, baseEnd_1600927] using wordTrace_append hprefix tailTrace_1600927
  have hstable : (prefixWord ++ tailWord_1600927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600927).length < 2 ^ (prefixWord ++ tailWord_1600927).sum := by decide
  have hdescent : baseEnd_1600927 < baseStart_1600927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600941 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1600941 : Nat := 118140960795 + 1600941 * 2 ^ 59
def prefixEnd_1600941 : Nat := 4983230072969 + 3 ^ 40 * 1600941 * 2
def baseEnd_1600941 : Nat := 822052232489726044674913

theorem tailTrace_1600941 : CollatzResearch.WordTrace tailWord_1600941 prefixEnd_1600941 822052232489726044674913 := by
  unfold tailWord_1600941
  simp only [CollatzResearch.WordTrace]
  refine ⟨58391115293071650799914677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38927410195381100533276451 58391115293071650799914677)
  ·
    refine ⟨5474167058725467262492001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58391115293071650799914677 5474167058725467262492001)
    ·
      refine ⟨4105625294044100446869001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5474167058725467262492001 4105625294044100446869001)
      ·
        refine ⟨3079218970533075335151751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4105625294044100446869001 3079218970533075335151751)
        ·
          refine ⟨4618828455799613002727627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079218970533075335151751 4618828455799613002727627)
          ·
            refine ⟨6928242683699419504091441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618828455799613002727627 6928242683699419504091441)
            ·
              refine ⟨5196182012774564628068581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6928242683699419504091441 5196182012774564628068581)
              ·
                refine ⟨974284127395230867762859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5196182012774564628068581 974284127395230867762859)
                ·
                  refine ⟨1461426191092846301644289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974284127395230867762859 1461426191092846301644289)
                  ·
                    refine ⟨1096069643319634726233217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1461426191092846301644289 1096069643319634726233217)
                    ·
                      refine ⟨822052232489726044674913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096069643319634726233217 822052232489726044674913)
                      ·
                        rfl

theorem cell23_1600941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1600941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600941 prefixEnd_1600941 := by exact prefixLift 1600941
  have htrace : WordTrace (prefixWord ++ tailWord_1600941) baseStart_1600941 baseEnd_1600941 := by
    simpa [prefixWord, tailWord_1600941, baseEnd_1600941] using wordTrace_append hprefix tailTrace_1600941
  have hstable : (prefixWord ++ tailWord_1600941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600941).length < 2 ^ (prefixWord ++ tailWord_1600941).sum := by decide
  have hdescent : baseEnd_1600941 < baseStart_1600941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600967 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_1600967 : Nat := 118140960795 + 1600967 * 2 ^ 59
def prefixEnd_1600967 : Nat := 4983230072969 + 3 ^ 40 * 1600967 * 2
def baseEnd_1600967 : Nat := 822065582986742942949793

theorem tailTrace_1600967 : CollatzResearch.WordTrace tailWord_1600967 prefixEnd_1600967 822065582986742942949793 := by
  unfold tailWord_1600967
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392063590977457240361155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38928042393984971493574103 58392063590977457240361155)
  ·
    refine ⟨87588095386466185860541733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58392063590977457240361155 87588095386466185860541733)
    ·
      refine ⟨16422767884962409848851575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87588095386466185860541733 16422767884962409848851575)
      ·
        refine ⟨24634151827443614773277363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16422767884962409848851575 24634151827443614773277363)
        ·
          refine ⟨36951227741165422159916045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24634151827443614773277363 36951227741165422159916045)
          ·
            refine ⟨13856710402937033309968517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36951227741165422159916045 13856710402937033309968517)
            ·
              refine ⟨2598133200550693745619097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13856710402937033309968517 2598133200550693745619097)
              ·
                refine ⟨1948599900413020309214323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598133200550693745619097 1948599900413020309214323)
                ·
                  refine ⟨2922899850619530463821485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948599900413020309214323 2922899850619530463821485)
                  ·
                    refine ⟨1096087443982323923933057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922899850619530463821485 1096087443982323923933057)
                    ·
                      refine ⟨822065582986742942949793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096087443982323923933057 822065582986742942949793)
                      ·
                        rfl

theorem cell23_1600967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_1600967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1600967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1600967 prefixEnd_1600967 := by exact prefixLift 1600967
  have htrace : WordTrace (prefixWord ++ tailWord_1600967) baseStart_1600967 baseEnd_1600967 := by
    simpa [prefixWord, tailWord_1600967, baseEnd_1600967] using wordTrace_append hprefix tailTrace_1600967
  have hstable : (prefixWord ++ tailWord_1600967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600967).length < 2 ^ (prefixWord ++ tailWord_1600967).sum := by decide
  have hdescent : baseEnd_1600967 < baseStart_1600967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601043 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1601043 : Nat := 118140960795 + 1601043 * 2 ^ 59
def prefixEnd_1601043 : Nat := 4983230072969 + 3 ^ 40 * 1601043 * 2
def baseEnd_1601043 : Nat := 822104607516484645599443

theorem tailTrace_1601043 : CollatzResearch.WordTrace tailWord_1601043 prefixEnd_1601043 822104607516484645599443 := by
  unfold tailWord_1601043
  simp only [CollatzResearch.WordTrace]
  refine ⟨58394835538702122220127783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38929890359134748146751855 58394835538702122220127783)
  ·
    refine ⟨87592253308053183330191675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58394835538702122220127783 87592253308053183330191675)
    ·
      refine ⟨131388379962079774995287513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87592253308053183330191675 131388379962079774995287513)
      ·
        refine ⟨98541284971559831246465635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131388379962079774995287513 98541284971559831246465635)
        ·
          refine ⟨147811927457339746869698453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98541284971559831246465635 147811927457339746869698453)
          ·
            refine ⟨6928684099562800634517115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147811927457339746869698453 6928684099562800634517115)
            ·
              refine ⟨10393026149344200951775673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6928684099562800634517115 10393026149344200951775673)
              ·
                refine ⟨7794769612008150713831755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10393026149344200951775673 7794769612008150713831755)
                ·
                  refine ⟨11692154418012226070747633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7794769612008150713831755 11692154418012226070747633)
                  ·
                    refine ⟨8769115813509169553060725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11692154418012226070747633 8769115813509169553060725)
                    ·
                      refine ⟨822104607516484645599443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8769115813509169553060725 822104607516484645599443)
                      ·
                        rfl

theorem cell23_1601043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1601043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601043 prefixEnd_1601043 := by exact prefixLift 1601043
  have htrace : WordTrace (prefixWord ++ tailWord_1601043) baseStart_1601043 baseEnd_1601043 := by
    simpa [prefixWord, tailWord_1601043, baseEnd_1601043] using wordTrace_append hprefix tailTrace_1601043
  have hstable : (prefixWord ++ tailWord_1601043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601043).length < 2 ^ (prefixWord ++ tailWord_1601043).sum := by decide
  have hdescent : baseEnd_1601043 < baseStart_1601043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601080 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1601080 : Nat := 118140960795 + 1601080 * 2 ^ 59
def prefixEnd_1601080 : Nat := 4983230072969 + 3 ^ 40 * 1601080 * 2
def baseEnd_1601080 : Nat := 274041202100233666945591

theorem tailTrace_1601080 : CollatzResearch.WordTrace tailWord_1601080 prefixEnd_1601080 274041202100233666945591 := by
  unfold tailWord_1601080
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198092519784038769612347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38930790026378718359483129 29198092519784038769612347)
  ·
    refine ⟨43797138779676058154418521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29198092519784038769612347 43797138779676058154418521)
    ·
      refine ⟨32847854084757043615813891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43797138779676058154418521 32847854084757043615813891)
      ·
        refine ⟨49271781127135565423720837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32847854084757043615813891 49271781127135565423720837)
        ·
          refine ⟨9238458961337918516947657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49271781127135565423720837 9238458961337918516947657)
          ·
            refine ⟨6928844221003438887710743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9238458961337918516947657 6928844221003438887710743)
            ·
              refine ⟨10393266331505158331566115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6928844221003438887710743 10393266331505158331566115)
              ·
                refine ⟨15589899497257737497349173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10393266331505158331566115 15589899497257737497349173)
                ·
                  refine ⟨1461553077867912890376485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15589899497257737497349173 1461553077867912890376485)
                  ·
                    refine ⟨274041202100233666945591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461553077867912890376485 274041202100233666945591)
                    ·
                      rfl

theorem cell23_1601080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1601080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601080 prefixEnd_1601080 := by exact prefixLift 1601080
  have htrace : WordTrace (prefixWord ++ tailWord_1601080) baseStart_1601080 baseEnd_1601080 := by
    simpa [prefixWord, tailWord_1601080, baseEnd_1601080] using wordTrace_append hprefix tailTrace_1601080
  have hstable : (prefixWord ++ tailWord_1601080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601080).length < 2 ^ (prefixWord ++ tailWord_1601080).sum := by decide
  have hdescent : baseEnd_1601080 < baseStart_1601080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601084 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1601084 : Nat := 118140960795 + 1601084 * 2 ^ 59
def prefixEnd_1601084 : Nat := 4983230072969 + 3 ^ 40 * 1601084 * 2
def baseEnd_1601084 : Nat := 274041886741106328395585

theorem tailTrace_1601084 : CollatzResearch.WordTrace tailWord_1601084 prefixEnd_1601084 274041886741106328395585 := by
  unfold tailWord_1601084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198165465776793111185153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38930887287702390814913537 29198165465776793111185153)
  ·
    refine ⟨21898624099332594833388865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29198165465776793111185153 21898624099332594833388865)
    ·
      refine ⟨16423968074499446125041649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21898624099332594833388865 16423968074499446125041649)
      ·
        refine ⟨12317976055874584593781237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16423968074499446125041649 12317976055874584593781237)
        ·
          refine ⟨1154810255238242305666991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12317976055874584593781237 1154810255238242305666991)
          ·
            refine ⟨1732215382857363458500487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154810255238242305666991 1732215382857363458500487)
            ·
              refine ⟨2598323074286045187750731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732215382857363458500487 2598323074286045187750731)
              ·
                refine ⟨3897484611429067781626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598323074286045187750731 3897484611429067781626097)
                ·
                  refine ⟨2923113458571800836219573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897484611429067781626097 2923113458571800836219573)
                  ·
                    refine ⟨274041886741106328395585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2923113458571800836219573 274041886741106328395585)
                    ·
                      rfl

theorem cell23_1601084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1601084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601084 prefixEnd_1601084 := by exact prefixLift 1601084
  have htrace : WordTrace (prefixWord ++ tailWord_1601084) baseStart_1601084 baseEnd_1601084 := by
    simpa [prefixWord, tailWord_1601084, baseEnd_1601084] using wordTrace_append hprefix tailTrace_1601084
  have hstable : (prefixWord ++ tailWord_1601084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601084).length < 2 ^ (prefixWord ++ tailWord_1601084).sum := by decide
  have hdescent : baseEnd_1601084 < baseStart_1601084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601087 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_1601087 : Nat := 118140960795 + 1601087 * 2 ^ 59
def prefixEnd_1601087 : Nat := 4983230072969 + 3 ^ 40 * 1601087 * 2
def baseEnd_1601087 : Nat := 822127200665282473449241

theorem tailTrace_1601087 : CollatzResearch.WordTrace tailWord_1601087 prefixEnd_1601087 822127200665282473449241 := by
  unfold tailWord_1601087
  simp only [CollatzResearch.WordTrace]
  refine ⟨58396440350542717734729515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38930960233695145156486343 58396440350542717734729515)
  ·
    refine ⟨87594660525814076602094273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58396440350542717734729515 87594660525814076602094273)
    ·
      refine ⟨65695995394360557451570705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87594660525814076602094273 65695995394360557451570705)
      ·
        refine ⟨49271996545770418088678029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65695995394360557451570705 49271996545770418088678029)
        ·
          refine ⟨18476998704663906783254261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49271996545770418088678029 18476998704663906783254261)
          ·
            refine ⟨1732218628562241260930087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18476998704663906783254261 1732218628562241260930087)
            ·
              refine ⟨2598327942843361891395131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732218628562241260930087 2598327942843361891395131)
              ·
                refine ⟨3897491914265042837092697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598327942843361891395131 3897491914265042837092697)
                ·
                  refine ⟨2923118935698782127819523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897491914265042837092697 2923118935698782127819523)
                  ·
                    refine ⟨4384678403548173191729285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923118935698782127819523 4384678403548173191729285)
                    ·
                      refine ⟨822127200665282473449241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4384678403548173191729285 822127200665282473449241)
                      ·
                        rfl

theorem cell23_1601087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_1601087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601087 prefixEnd_1601087 := by exact prefixLift 1601087
  have htrace : WordTrace (prefixWord ++ tailWord_1601087) baseStart_1601087 baseEnd_1601087 := by
    simpa [prefixWord, tailWord_1601087, baseEnd_1601087] using wordTrace_append hprefix tailTrace_1601087
  have hstable : (prefixWord ++ tailWord_1601087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601087).length < 2 ^ (prefixWord ++ tailWord_1601087).sum := by decide
  have hdescent : baseEnd_1601087 < baseStart_1601087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601093 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 8]
def baseStart_1601093 : Nat := 118140960795 + 1601093 * 2 ^ 59
def prefixEnd_1601093 : Nat := 4983230072969 + 3 ^ 40 * 1601093 * 2
def baseEnd_1601093 : Nat := 91347809061023272219357

theorem tailTrace_1601093 : CollatzResearch.WordTrace tailWord_1601093 prefixEnd_1601093 91347809061023272219357 := by
  unfold tailWord_1601093
  simp only [CollatzResearch.WordTrace]
  refine ⟨58396659188520980759447933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38931106125680653839631955 58396659188520980759447933)
  ·
    refine ⟨21898747195695367784792975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58396659188520980759447933 21898747195695367784792975)
    ·
      refine ⟨32848120793543051677189463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21898747195695367784792975 32848120793543051677189463)
      ·
        refine ⟨49272181190314577515784195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32848120793543051677189463 49272181190314577515784195)
        ·
          refine ⟨73908271785471866273676293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49272181190314577515784195 73908271785471866273676293)
          ·
            refine ⟨13857800959775974926314305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73908271785471866273676293 13857800959775974926314305)
            ·
              refine ⟨10393350719831981194735729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13857800959775974926314305 10393350719831981194735729)
              ·
                refine ⟨7795013039873985896051797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10393350719831981194735729 7795013039873985896051797)
                ·
                  refine ⟨91347809061023272219357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7795013039873985896051797 91347809061023272219357)
                  ·
                    rfl

theorem cell23_1601093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_1601093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601093 prefixEnd_1601093 := by exact prefixLift 1601093
  have htrace : WordTrace (prefixWord ++ tailWord_1601093) baseStart_1601093 baseEnd_1601093 := by
    simpa [prefixWord, tailWord_1601093, baseEnd_1601093] using wordTrace_append hprefix tailTrace_1601093
  have hstable : (prefixWord ++ tailWord_1601093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601093).length < 2 ^ (prefixWord ++ tailWord_1601093).sum := by decide
  have hdescent : baseEnd_1601093 < baseStart_1601093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601147 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 2, 3, 2]
def baseStart_1601147 : Nat := 118140960795 + 1601147 * 2 ^ 59
def prefixEnd_1601147 : Nat := 4983230072969 + 3 ^ 40 * 1601147 * 2
def baseEnd_1601147 : Nat := 822158009504552238698965

theorem tailTrace_1601147 : CollatzResearch.WordTrace tailWord_1601147 prefixEnd_1601147 822158009504552238698965 := by
  unfold tailWord_1601147
  simp only [CollatzResearch.WordTrace]
  refine ⟨58398628730325347981913695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38932419153550231987942463 58398628730325347981913695)
  ·
    refine ⟨87597943095488021972870543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58398628730325347981913695 87597943095488021972870543)
    ·
      refine ⟨131396914643232032959305815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87597943095488021972870543 131396914643232032959305815)
      ·
        refine ⟨197095371964848049438958723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131396914643232032959305815 197095371964848049438958723)
        ·
          refine ⟨295643057947272074158438085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197095371964848049438958723 295643057947272074158438085)
          ·
            refine ⟨55433073365113513904707141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295643057947272074158438085 55433073365113513904707141)
            ·
              refine ⟨10393701255958783857132589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55433073365113513904707141 10393701255958783857132589)
              ·
                refine ⟨3897637970984543946424721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10393701255958783857132589 3897637970984543946424721)
                ·
                  refine ⟨2923228478238407959818541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897637970984543946424721 2923228478238407959818541)
                  ·
                    refine ⟨1096210679339402984931953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923228478238407959818541 1096210679339402984931953)
                    ·
                      refine ⟨822158009504552238698965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096210679339402984931953 822158009504552238698965)
                      ·
                        rfl

theorem cell23_1601147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3, 2].length) (baseStart_1601147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601147 prefixEnd_1601147 := by exact prefixLift 1601147
  have htrace : WordTrace (prefixWord ++ tailWord_1601147) baseStart_1601147 baseEnd_1601147 := by
    simpa [prefixWord, tailWord_1601147, baseEnd_1601147] using wordTrace_append hprefix tailTrace_1601147
  have hstable : (prefixWord ++ tailWord_1601147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601147).length < 2 ^ (prefixWord ++ tailWord_1601147).sum := by decide
  have hdescent : baseEnd_1601147 < baseStart_1601147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601187 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 2, 4]
def baseStart_1601187 : Nat := 118140960795 + 1601187 * 2 ^ 59
def prefixEnd_1601187 : Nat := 4983230072969 + 3 ^ 40 * 1601187 * 2
def baseEnd_1601187 : Nat := 274059516243577360732927

theorem tailTrace_1601187 : CollatzResearch.WordTrace tailWord_1601187 prefixEnd_1601187 274059516243577360732927 := by
  unfold tailWord_1601187
  simp only [CollatzResearch.WordTrace]
  refine ⟨58400087650180434813369815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38933391766786956542246543 58400087650180434813369815)
  ·
    refine ⟨87600131475270652220054723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58400087650180434813369815 87600131475270652220054723)
    ·
      refine ⟨131400197212905978330082085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87600131475270652220054723 131400197212905978330082085)
      ·
        refine ⟨24637536977419870936890391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131400197212905978330082085 24637536977419870936890391)
        ·
          refine ⟨36956305466129806405335587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24637536977419870936890391 36956305466129806405335587)
          ·
            refine ⟨55434458199194709608003381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36956305466129806405335587 55434458199194709608003381)
            ·
              refine ⟨5196980456174504025750317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55434458199194709608003381 5196980456174504025750317)
              ·
                refine ⟨1948867671065439009656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196980456174504025750317 1948867671065439009656369)
                ·
                  refine ⟨1461650753299079257242277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948867671065439009656369 1461650753299079257242277)
                  ·
                    refine ⟨274059516243577360732927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461650753299079257242277 274059516243577360732927)
                    ·
                      rfl

theorem cell23_1601187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 4].length) (baseStart_1601187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601187 prefixEnd_1601187 := by exact prefixLift 1601187
  have htrace : WordTrace (prefixWord ++ tailWord_1601187) baseStart_1601187 baseEnd_1601187 := by
    simpa [prefixWord, tailWord_1601187, baseEnd_1601187] using wordTrace_append hprefix tailTrace_1601187
  have hstable : (prefixWord ++ tailWord_1601187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601187).length < 2 ^ (prefixWord ++ tailWord_1601187).sum := by decide
  have hdescent : baseEnd_1601187 < baseStart_1601187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601198 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1601198 : Nat := 118140960795 + 1601198 * 2 ^ 59
def prefixEnd_1601198 : Nat := 4983230072969 + 3 ^ 40 * 1601198 * 2
def baseEnd_1601198 : Nat := 822184197017931539161231

theorem tailTrace_1601198 : CollatzResearch.WordTrace tailWord_1601198 prefixEnd_1601198 822184197017931539161231 := by
  unfold tailWord_1601198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300061106642572961502531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38933659235427055794680165 7300061106642572961502531)
  ·
    refine ⟨10950091659963859442253797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300061106642572961502531 10950091659963859442253797)
    ·
      refine ⟨2053142186243223645422587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10950091659963859442253797 2053142186243223645422587)
      ·
        refine ⟨3079713279364835468133881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053142186243223645422587 3079713279364835468133881)
        ·
          refine ⟨2309784959523626601100411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079713279364835468133881 2309784959523626601100411)
          ·
            refine ⟨3464677439285439901650617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309784959523626601100411 3464677439285439901650617)
            ·
              refine ⟨2598508079464079926237963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464677439285439901650617 2598508079464079926237963)
              ·
                refine ⟨3897762119196119889356945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598508079464079926237963 3897762119196119889356945)
                ·
                  refine ⟨2923321589397089917017709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897762119196119889356945 2923321589397089917017709)
                  ·
                    refine ⟨1096245596023908718881641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923321589397089917017709 1096245596023908718881641)
                    ·
                      refine ⟨822184197017931539161231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096245596023908718881641 822184197017931539161231)
                      ·
                        rfl

theorem cell23_1601198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1601198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601198 prefixEnd_1601198 := by exact prefixLift 1601198
  have htrace : WordTrace (prefixWord ++ tailWord_1601198) baseStart_1601198 baseEnd_1601198 := by
    simpa [prefixWord, tailWord_1601198, baseEnd_1601198] using wordTrace_append hprefix tailTrace_1601198
  have hstable : (prefixWord ++ tailWord_1601198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601198).length < 2 ^ (prefixWord ++ tailWord_1601198).sum := by decide
  have hdescent : baseEnd_1601198 < baseStart_1601198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601207 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1601207 : Nat := 118140960795 + 1601207 * 2 ^ 59
def prefixEnd_1601207 : Nat := 4983230072969 + 3 ^ 40 * 1601207 * 2
def baseEnd_1601207 : Nat := 822188818343822003948689

theorem tailTrace_1601207 : CollatzResearch.WordTrace tailWord_1601207 prefixEnd_1601207 822188818343822003948689 := by
  unfold tailWord_1601207
  simp only [CollatzResearch.WordTrace]
  refine ⟨58400817110107978229097875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38933878073405318819398583 58400817110107978229097875)
  ·
    refine ⟨87601225665161967343646813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58400817110107978229097875 87601225665161967343646813)
    ·
      refine ⟨32850459624435737753867555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87601225665161967343646813 32850459624435737753867555)
      ·
        refine ⟨49275689436653606630801333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32850459624435737753867555 49275689436653606630801333)
        ·
          refine ⟨4619595884686275621637625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49275689436653606630801333 4619595884686275621637625)
          ·
            refine ⟨3464696913514706716228219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619595884686275621637625 3464696913514706716228219)
            ·
              refine ⟨5197045370272060074342329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464696913514706716228219 5197045370272060074342329)
              ·
                refine ⟨3897784027704045055756747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5197045370272060074342329 3897784027704045055756747)
                ·
                  refine ⟨5846676041556067583635121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897784027704045055756747 5846676041556067583635121)
                  ·
                    refine ⟨4385007031167050687726341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5846676041556067583635121 4385007031167050687726341)
                    ·
                      refine ⟨822188818343822003948689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4385007031167050687726341 822188818343822003948689)
                      ·
                        rfl

theorem cell23_1601207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1601207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601207 prefixEnd_1601207 := by exact prefixLift 1601207
  have htrace : WordTrace (prefixWord ++ tailWord_1601207) baseStart_1601207 baseEnd_1601207 := by
    simpa [prefixWord, tailWord_1601207, baseEnd_1601207] using wordTrace_append hprefix tailTrace_1601207
  have hstable : (prefixWord ++ tailWord_1601207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601207).length < 2 ^ (prefixWord ++ tailWord_1601207).sum := by decide
  have hdescent : baseEnd_1601207 < baseStart_1601207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601214 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1601214 : Nat := 118140960795 + 1601214 * 2 ^ 59
def prefixEnd_1601214 : Nat := 4983230072969 + 3 ^ 40 * 1601214 * 2
def baseEnd_1601214 : Nat := 822192412708403476561157

theorem tailTrace_1601214 : CollatzResearch.WordTrace tailWord_1601214 prefixEnd_1601214 822192412708403476561157 := by
  unfold tailWord_1601214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300134052635327303075337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38934048280721745616401797 7300134052635327303075337)
  ·
    refine ⟨5475100539476495477306503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7300134052635327303075337 5475100539476495477306503)
    ·
      refine ⟨8212650809214743215959755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475100539476495477306503 8212650809214743215959755)
      ·
        refine ⟨12318976213822114823939633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212650809214743215959755 12318976213822114823939633)
        ·
          refine ⟨9239232160366586117954725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12318976213822114823939633 9239232160366586117954725)
          ·
            refine ⟨1732356030068734897116511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9239232160366586117954725 1732356030068734897116511)
            ·
              refine ⟨2598534045103102345674767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732356030068734897116511 2598534045103102345674767)
              ·
                refine ⟨3897801067654653518512151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598534045103102345674767 3897801067654653518512151)
                ·
                  refine ⟨5846701601481980277768227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897801067654653518512151 5846701601481980277768227)
                  ·
                    refine ⟨8770052402222970416652341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846701601481980277768227 8770052402222970416652341)
                    ·
                      refine ⟨822192412708403476561157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8770052402222970416652341 822192412708403476561157)
                      ·
                        rfl

theorem cell23_1601214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1601214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601214 prefixEnd_1601214 := by exact prefixLift 1601214
  have htrace : WordTrace (prefixWord ++ tailWord_1601214) baseStart_1601214 baseEnd_1601214 := by
    simpa [prefixWord, tailWord_1601214, baseEnd_1601214] using wordTrace_append hprefix tailTrace_1601214
  have hstable : (prefixWord ++ tailWord_1601214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601214).length < 2 ^ (prefixWord ++ tailWord_1601214).sum := by decide
  have hdescent : baseEnd_1601214 < baseStart_1601214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601222 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1601222 : Nat := 118140960795 + 1601222 * 2 ^ 59
def prefixEnd_1601222 : Nat := 4983230072969 + 3 ^ 40 * 1601222 * 2
def baseEnd_1601222 : Nat := 822196520553639445261121

theorem tailTrace_1601222 : CollatzResearch.WordTrace tailWord_1601222 prefixEnd_1601222 822196520553639445261121 := by
  unfold tailWord_1601222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825042631407926118465435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38934242803369090527262613 1825042631407926118465435)
  ·
    refine ⟨2737563947111889177698153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825042631407926118465435 2737563947111889177698153)
    ·
      refine ⟨2053172960333916883273615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2737563947111889177698153 2053172960333916883273615)
      ·
        refine ⟨3079759440500875324910423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053172960333916883273615 3079759440500875324910423)
        ·
          refine ⟨4619639160751312987365635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079759440500875324910423 4619639160751312987365635)
          ·
            refine ⟨6929458741126969481048453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619639160751312987365635 6929458741126969481048453)
            ·
              refine ⟨1299273513961306777696585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6929458741126969481048453 1299273513961306777696585)
              ·
                refine ⟨974455135470980083272439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299273513961306777696585 974455135470980083272439)
                ·
                  refine ⟨1461682703206470124908659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974455135470980083272439 1461682703206470124908659)
                  ·
                    refine ⟨2192524054809705187362989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461682703206470124908659 2192524054809705187362989)
                    ·
                      refine ⟨822196520553639445261121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192524054809705187362989 822196520553639445261121)
                      ·
                        rfl

theorem cell23_1601222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1601222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601222 prefixEnd_1601222 := by exact prefixLift 1601222
  have htrace : WordTrace (prefixWord ++ tailWord_1601222) baseStart_1601222 baseEnd_1601222 := by
    simpa [prefixWord, tailWord_1601222, baseEnd_1601222] using wordTrace_append hprefix tailTrace_1601222
  have hstable : (prefixWord ++ tailWord_1601222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601222).length < 2 ^ (prefixWord ++ tailWord_1601222).sum := by decide
  have hdescent : baseEnd_1601222 < baseStart_1601222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601227 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 3]
def baseStart_1601227 : Nat := 118140960795 + 1601227 * 2 ^ 59
def prefixEnd_1601227 : Nat := 4983230072969 + 3 ^ 40 * 1601227 * 2
def baseEnd_1601227 : Nat := 822199087956911925698597

theorem tailTrace_1601227 : CollatzResearch.WordTrace tailWord_1601227 prefixEnd_1601227 822199087956911925698597 := by
  unfold tailWord_1601227
  simp only [CollatzResearch.WordTrace]
  refine ⟨58401546570035521644825935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38934364380023681096550623 58401546570035521644825935)
  ·
    refine ⟨87602319855053282467238903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58401546570035521644825935 87602319855053282467238903)
    ·
      refine ⟨131403479782579923700858355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87602319855053282467238903 131403479782579923700858355)
      ·
        refine ⟨197105219673869885551287533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131403479782579923700858355 197105219673869885551287533)
        ·
          refine ⟨73914457377701207081732825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197105219673869885551287533 73914457377701207081732825)
          ·
            refine ⟨55435843033275905311299619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73914457377701207081732825 55435843033275905311299619)
            ·
              refine ⟨83153764549913857966949429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55435843033275905311299619 83153764549913857966949429)
              ·
                refine ⟨7795665426554424184401509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83153764549913857966949429 7795665426554424184401509)
                ·
                  refine ⟨1461687267478954534575283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7795665426554424184401509 1461687267478954534575283)
                  ·
                    refine ⟨2192530901218431801862925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461687267478954534575283 2192530901218431801862925)
                    ·
                      refine ⟨822199087956911925698597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192530901218431801862925 822199087956911925698597)
                      ·
                        rfl

theorem cell23_1601227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 3].length) (baseStart_1601227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601227 prefixEnd_1601227 := by exact prefixLift 1601227
  have htrace : WordTrace (prefixWord ++ tailWord_1601227) baseStart_1601227 baseEnd_1601227 := by
    simpa [prefixWord, tailWord_1601227, baseEnd_1601227] using wordTrace_append hprefix tailTrace_1601227
  have hstable : (prefixWord ++ tailWord_1601227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601227).length < 2 ^ (prefixWord ++ tailWord_1601227).sum := by decide
  have hdescent : baseEnd_1601227 < baseStart_1601227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601230 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1601230 : Nat := 118140960795 + 1601230 * 2 ^ 59
def prefixEnd_1601230 : Nat := 4983230072969 + 3 ^ 40 * 1601230 * 2
def baseEnd_1601230 : Nat := 274066876132958471320361

theorem tailTrace_1601230 : CollatzResearch.WordTrace tailWord_1601230 prefixEnd_1601230 274066876132958471320361 := by
  unfold tailWord_1601230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300206998628081644648143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38934437326016435438123429 7300206998628081644648143)
  ·
    refine ⟨10950310497942122466972215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300206998628081644648143 10950310497942122466972215)
    ·
      refine ⟨16425465746913183700458323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950310497942122466972215 16425465746913183700458323)
      ·
        refine ⟨24638198620369775550687485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16425465746913183700458323 24638198620369775550687485)
        ·
          refine ⟨9239324482638665831507807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24638198620369775550687485 9239324482638665831507807)
          ·
            refine ⟨13858986723957998747261711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9239324482638665831507807 13858986723957998747261711)
            ·
              refine ⟨20788480085936998120892567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13858986723957998747261711 20788480085936998120892567)
              ·
                refine ⟨31182720128905497181338851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20788480085936998120892567 31182720128905497181338851)
                ·
                  refine ⟨46774080193358245772008277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31182720128905497181338851 46774080193358245772008277)
                  ·
                    refine ⟨274066876132958471320361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46774080193358245772008277 274066876132958471320361)
                    ·
                      rfl

theorem cell23_1601230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1601230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601230 prefixEnd_1601230 := by exact prefixLift 1601230
  have htrace : WordTrace (prefixWord ++ tailWord_1601230) baseStart_1601230 baseEnd_1601230 := by
    simpa [prefixWord, tailWord_1601230, baseEnd_1601230] using wordTrace_append hprefix tailTrace_1601230
  have hstable : (prefixWord ++ tailWord_1601230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601230).length < 2 ^ (prefixWord ++ tailWord_1601230).sum := by decide
  have hdescent : baseEnd_1601230 < baseStart_1601230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601271 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_1601271 : Nat := 118140960795 + 1601271 * 2 ^ 59
def prefixEnd_1601271 : Nat := 4983230072969 + 3 ^ 40 * 1601271 * 2
def baseEnd_1601271 : Nat := 822221681105709753548395

theorem tailTrace_1601271 : CollatzResearch.WordTrace tailWord_1601271 prefixEnd_1601271 822221681105709753548395 := by
  unfold tailWord_1601271
  simp only [CollatzResearch.WordTrace]
  refine ⟨58403151381876117159427667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38935434254584078106285111 58403151381876117159427667)
  ·
    refine ⟨87604727072814175739141501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58403151381876117159427667 87604727072814175739141501)
    ·
      refine ⟨32851772652305315902178063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87604727072814175739141501 32851772652305315902178063)
      ·
        refine ⟨49277658978457973853267095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32851772652305315902178063 49277658978457973853267095)
        ·
          refine ⟨73916488467686960779900643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49277658978457973853267095 73916488467686960779900643)
          ·
            refine ⟨110874732701530441169850965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73916488467686960779900643 110874732701530441169850965)
            ·
              refine ⟨1299313273846059857459191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 110874732701530441169850965 1299313273846059857459191)
              ·
                refine ⟨1948969910769089786188787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299313273846059857459191 1948969910769089786188787)
                ·
                  refine ⟨2923454866153634679283181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948969910769089786188787 2923454866153634679283181)
                  ·
                    refine ⟨1096295574807613004731193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923454866153634679283181 1096295574807613004731193)
                    ·
                      refine ⟨822221681105709753548395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096295574807613004731193 822221681105709753548395)
                      ·
                        rfl

theorem cell23_1601271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_1601271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601271 prefixEnd_1601271 := by exact prefixLift 1601271
  have htrace : WordTrace (prefixWord ++ tailWord_1601271) baseStart_1601271 baseEnd_1601271 := by
    simpa [prefixWord, tailWord_1601271, baseEnd_1601271] using wordTrace_append hprefix tailTrace_1601271
  have hstable : (prefixWord ++ tailWord_1601271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601271).length < 2 ^ (prefixWord ++ tailWord_1601271).sum := by decide
  have hdescent : baseEnd_1601271 < baseStart_1601271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601280 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1601280 : Nat := 118140960795 + 1601280 * 2 ^ 59
def prefixEnd_1601280 : Nat := 4983230072969 + 3 ^ 40 * 1601280 * 2
def baseEnd_1601280 : Nat := 822226302431600218335853

theorem tailTrace_1601280 : CollatzResearch.WordTrace tailWord_1601280 prefixEnd_1601280 822226302431600218335853 := by
  unfold tailWord_1601280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29201739819421755848252647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38935653092562341131003529 29201739819421755848252647)
  ·
    refine ⟨43802609729132633772378971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29201739819421755848252647 43802609729132633772378971)
    ·
      refine ⟨65703914593698950658568457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43802609729132633772378971 65703914593698950658568457)
      ·
        refine ⟨49277935945274212993926343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65703914593698950658568457 49277935945274212993926343)
        ·
          refine ⟨73916903917911319490889515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49277935945274212993926343 73916903917911319490889515)
          ·
            refine ⟨110875355876866979236334273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73916903917911319490889515 110875355876866979236334273)
            ·
              refine ⟨83156516907650234427250705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110875355876866979236334273 83156516907650234427250705)
              ·
                refine ⟨62367387680737675820438029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83156516907650234427250705 62367387680737675820438029)
                ·
                  refine ⟨23387770380276628432664261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62367387680737675820438029 23387770380276628432664261)
                  ·
                    refine ⟨4385206946301867831124549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23387770380276628432664261 4385206946301867831124549)
                    ·
                      refine ⟨822226302431600218335853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4385206946301867831124549 822226302431600218335853)
                      ·
                        rfl

theorem cell23_1601280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1601280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601280 prefixEnd_1601280 := by exact prefixLift 1601280
  have htrace : WordTrace (prefixWord ++ tailWord_1601280) baseStart_1601280 baseEnd_1601280 := by
    simpa [prefixWord, tailWord_1601280, baseEnd_1601280] using wordTrace_append hprefix tailTrace_1601280
  have hstable : (prefixWord ++ tailWord_1601280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601280).length < 2 ^ (prefixWord ++ tailWord_1601280).sum := by decide
  have hdescent : baseEnd_1601280 < baseStart_1601280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601301 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_1601301 : Nat := 118140960795 + 1601301 * 2 ^ 59
def prefixEnd_1601301 : Nat := 4983230072969 + 3 ^ 40 * 1601301 * 2
def baseEnd_1601301 : Nat := 822237085525344636173257

theorem tailTrace_1601301 : CollatzResearch.WordTrace tailWord_1601301 prefixEnd_1601301 822237085525344636173257 := by
  unfold tailWord_1601301
  simp only [CollatzResearch.WordTrace]
  refine ⟨58404245571767432283019757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38936163714511621522013171 58404245571767432283019757)
  ·
    refine ⟨21901592089412787106132409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58404245571767432283019757 21901592089412787106132409)
    ·
      refine ⟨16426194067059590329599307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21901592089412787106132409 16426194067059590329599307)
      ·
        refine ⟨24639291100589385494398961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16426194067059590329599307 24639291100589385494398961)
        ·
          refine ⟨18479468325442039120799221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24639291100589385494398961 18479468325442039120799221)
          ·
            refine ⟨1732450155510191167574927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18479468325442039120799221 1732450155510191167574927)
            ·
              refine ⟨2598675233265286751362391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732450155510191167574927 2598675233265286751362391)
              ·
                refine ⟨3898012849897930127043587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598675233265286751362391 3898012849897930127043587)
                ·
                  refine ⟨5847019274846895190565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898012849897930127043587 5847019274846895190565381)
                  ·
                    refine ⟨1096316114033792848231009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847019274846895190565381 1096316114033792848231009)
                    ·
                      refine ⟨822237085525344636173257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096316114033792848231009 822237085525344636173257)
                      ·
                        rfl

theorem cell23_1601301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_1601301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601301 prefixEnd_1601301 := by exact prefixLift 1601301
  have htrace : WordTrace (prefixWord ++ tailWord_1601301) baseStart_1601301 baseEnd_1601301 := by
    simpa [prefixWord, tailWord_1601301, baseEnd_1601301] using wordTrace_append hprefix tailTrace_1601301
  have hstable : (prefixWord ++ tailWord_1601301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601301).length < 2 ^ (prefixWord ++ tailWord_1601301).sum := by decide
  have hdescent : baseEnd_1601301 < baseStart_1601301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601324 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 5]
def baseStart_1601324 : Nat := 118140960795 + 1601324 * 2 ^ 59
def prefixEnd_1601324 : Nat := 4983230072969 + 3 ^ 40 * 1601324 * 2
def baseEnd_1601324 : Nat := 91360988397822005131739

theorem tailTrace_1601324 : CollatzResearch.WordTrace tailWord_1601324 prefixEnd_1601324 91360988397822005131739 := by
  unfold tailWord_1601324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29202542225342053605553513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38936722967122738140738017 29202542225342053605553513)
  ·
    refine ⟨21901906669006540204165135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29202542225342053605553513 21901906669006540204165135)
    ·
      refine ⟨32852860003509810306247703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21901906669006540204165135 32852860003509810306247703)
      ·
        refine ⟨49279290005264715459371555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32852860003509810306247703 49279290005264715459371555)
        ·
          refine ⟨73918935007897073189057333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49279290005264715459371555 73918935007897073189057333)
          ·
            refine ⟨6929900156990350611474125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73918935007897073189057333 6929900156990350611474125)
            ·
              refine ⟨2598712558871381479302797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6929900156990350611474125 2598712558871381479302797)
              ·
                refine ⟨974517209576768054738549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2598712558871381479302797 974517209576768054738549)
                ·
                  refine ⟨91360988397822005131739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974517209576768054738549 91360988397822005131739)
                  ·
                    rfl

theorem cell23_1601324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_1601324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601324 prefixEnd_1601324 := by exact prefixLift 1601324
  have htrace : WordTrace (prefixWord ++ tailWord_1601324) baseStart_1601324 baseEnd_1601324 := by
    simpa [prefixWord, tailWord_1601324, baseEnd_1601324] using wordTrace_append hprefix tailTrace_1601324
  have hstable : (prefixWord ++ tailWord_1601324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601324).length < 2 ^ (prefixWord ++ tailWord_1601324).sum := by decide
  have hdescent : baseEnd_1601324 < baseStart_1601324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601347 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1601347 : Nat := 118140960795 + 1601347 * 2 ^ 59
def prefixEnd_1601347 : Nat := 4983230072969 + 3 ^ 40 * 1601347 * 2
def baseEnd_1601347 : Nat := 822260705635451456198045

theorem tailTrace_1601347 : CollatzResearch.WordTrace tailWord_1601347 prefixEnd_1601347 822260705635451456198045 := by
  unfold tailWord_1601347
  simp only [CollatzResearch.WordTrace]
  refine ⟨58405923329600782139194295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38937282219733854759462863 58405923329600782139194295)
  ·
    refine ⟨87608884994401173208791443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58405923329600782139194295 87608884994401173208791443)
    ·
      refine ⟨131413327491601759813187165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87608884994401173208791443 131413327491601759813187165)
      ·
        refine ⟨49279997809350659929945187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131413327491601759813187165 49279997809350659929945187)
        ·
          refine ⟨73919996714025989894917781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49279997809350659929945187 73919996714025989894917781)
          ·
            refine ⟨3464999845969968276324271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73919996714025989894917781 3464999845969968276324271)
            ·
              refine ⟨5197499768954952414486407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464999845969968276324271 5197499768954952414486407)
              ·
                refine ⟨7796249653432428621729611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197499768954952414486407 7796249653432428621729611)
                ·
                  refine ⟨11694374480148642932594417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796249653432428621729611 11694374480148642932594417)
                  ·
                    refine ⟨8770780860111482199445813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11694374480148642932594417 8770780860111482199445813)
                    ·
                      refine ⟨822260705635451456198045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8770780860111482199445813 822260705635451456198045)
                      ·
                        rfl

theorem cell23_1601347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1601347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601347 prefixEnd_1601347 := by exact prefixLift 1601347
  have htrace : WordTrace (prefixWord ++ tailWord_1601347) baseStart_1601347 baseEnd_1601347 := by
    simpa [prefixWord, tailWord_1601347, baseEnd_1601347] using wordTrace_append hprefix tailTrace_1601347
  have hstable : (prefixWord ++ tailWord_1601347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601347).length < 2 ^ (prefixWord ++ tailWord_1601347).sum := by decide
  have hdescent : baseEnd_1601347 < baseStart_1601347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601401 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 1, 4]
def baseStart_1601401 : Nat := 118140960795 + 1601401 * 2 ^ 59
def prefixEnd_1601401 : Nat := 4983230072969 + 3 ^ 40 * 1601401 * 2
def baseEnd_1601401 : Nat := 274096144530264748307599

theorem tailTrace_1601401 : CollatzResearch.WordTrace tailWord_1601401 prefixEnd_1601401 274096144530264748307599 := by
  unfold tailWord_1601401
  simp only [CollatzResearch.WordTrace]
  refine ⟨58407892871405149361660057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38938595247603432907773371 58407892871405149361660057)
  ·
    refine ⟨43805919653553862021245043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58407892871405149361660057 43805919653553862021245043)
    ·
      refine ⟨65708879480330793031867565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43805919653553862021245043 65708879480330793031867565)
      ·
        refine ⟨24640829805124047386950337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65708879480330793031867565 24640829805124047386950337)
        ·
          refine ⟨18480622353843035540212753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24640829805124047386950337 18480622353843035540212753)
          ·
            refine ⟨13860466765382276655159565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18480622353843035540212753 13860466765382276655159565)
            ·
              refine ⟨5197675037018353745684837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13860466765382276655159565 5197675037018353745684837)
              ·
                refine ⟨974564069440941327315907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5197675037018353745684837 974564069440941327315907)
                ·
                  refine ⟨1461846104161411990973861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974564069440941327315907 1461846104161411990973861)
                  ·
                    refine ⟨274096144530264748307599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461846104161411990973861 274096144530264748307599)
                    ·
                      rfl

theorem cell23_1601401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_1601401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601401 prefixEnd_1601401 := by exact prefixLift 1601401
  have htrace : WordTrace (prefixWord ++ tailWord_1601401) baseStart_1601401 baseEnd_1601401 := by
    simpa [prefixWord, tailWord_1601401, baseEnd_1601401] using wordTrace_append hprefix tailTrace_1601401
  have hstable : (prefixWord ++ tailWord_1601401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601401).length < 2 ^ (prefixWord ++ tailWord_1601401).sum := by decide
  have hdescent : baseEnd_1601401 < baseStart_1601401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601407 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1601407 : Nat := 118140960795 + 1601407 * 2 ^ 59
def prefixEnd_1601407 : Nat := 4983230072969 + 3 ^ 40 * 1601407 * 2
def baseEnd_1601407 : Nat := 822291514474721221447769

theorem tailTrace_1601407 : CollatzResearch.WordTrace tailWord_1601407 prefixEnd_1601407 822291514474721221447769 := by
  unfold tailWord_1601407
  simp only [CollatzResearch.WordTrace]
  refine ⟨58408111709383412386378475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38938741139588941590918983 58408111709383412386378475)
  ·
    refine ⟨87612167564075118579567713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58408111709383412386378475 87612167564075118579567713)
    ·
      refine ⟨65709125673056338934675785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87612167564075118579567713 65709125673056338934675785)
      ·
        refine ⟨49281844254792254201006839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65709125673056338934675785 49281844254792254201006839)
        ·
          refine ⟨73922766382188381301510259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49281844254792254201006839 73922766382188381301510259)
          ·
            refine ⟨110884149573282571952265389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73922766382188381301510259 110884149573282571952265389)
            ·
              refine ⟨41581556089980964482099521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110884149573282571952265389 41581556089980964482099521)
              ·
                refine ⟨31186167067485723361574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41581556089980964482099521 31186167067485723361574641)
                ·
                  refine ⟨23389625300614292521180981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31186167067485723361574641 23389625300614292521180981)
                  ·
                    refine ⟨2192777371932589923860717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23389625300614292521180981 2192777371932589923860717)
                    ·
                      refine ⟨822291514474721221447769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192777371932589923860717 822291514474721221447769)
                      ·
                        rfl

theorem cell23_1601407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1601407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601407 prefixEnd_1601407 := by exact prefixLift 1601407
  have htrace : WordTrace (prefixWord ++ tailWord_1601407) baseStart_1601407 baseEnd_1601407 := by
    simpa [prefixWord, tailWord_1601407, baseEnd_1601407] using wordTrace_append hprefix tailTrace_1601407
  have hstable : (prefixWord ++ tailWord_1601407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601407).length < 2 ^ (prefixWord ++ tailWord_1601407).sum := by decide
  have hdescent : baseEnd_1601407 < baseStart_1601407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601424 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_1601424 : Nat := 118140960795 + 1601424 * 2 ^ 59
def prefixEnd_1601424 : Nat := 4983230072969 + 3 ^ 40 * 1601424 * 2
def baseEnd_1601424 : Nat := 822300243645847654935191

theorem tailTrace_1601424 : CollatzResearch.WordTrace tailWord_1601424 prefixEnd_1601424 822300243645847654935191 := by
  unfold tailWord_1601424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204365875160912144873663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38939154500214549526498217 29204365875160912144873663)
  ·
    refine ⟨43806548812741368217310495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29204365875160912144873663 43806548812741368217310495)
    ·
      refine ⟨65709823219112052325965743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43806548812741368217310495 65709823219112052325965743)
      ·
        refine ⟨98564734828668078488948615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65709823219112052325965743 98564734828668078488948615)
        ·
          refine ⟨147847102243002117733422923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98564734828668078488948615 147847102243002117733422923)
          ·
            refine ⟨221770653364503176600134385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147847102243002117733422923 221770653364503176600134385)
            ·
              refine ⟨166327990023377382450100789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221770653364503176600134385 166327990023377382450100789)
              ·
                refine ⟨15593249064691629604696949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166327990023377382450100789 15593249064691629604696949)
                ·
                  refine ⟨1461867099814840275440339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15593249064691629604696949 1461867099814840275440339)
                  ·
                    refine ⟨2192800649722260413160509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461867099814840275440339 2192800649722260413160509)
                    ·
                      refine ⟨822300243645847654935191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192800649722260413160509 822300243645847654935191)
                      ·
                        rfl

theorem cell23_1601424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_1601424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601424 prefixEnd_1601424 := by exact prefixLift 1601424
  have htrace : WordTrace (prefixWord ++ tailWord_1601424) baseStart_1601424 baseEnd_1601424 := by
    simpa [prefixWord, tailWord_1601424, baseEnd_1601424] using wordTrace_append hprefix tailTrace_1601424
  have hstable : (prefixWord ++ tailWord_1601424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601424).length < 2 ^ (prefixWord ++ tailWord_1601424).sum := by decide
  have hdescent : baseEnd_1601424 < baseStart_1601424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601428 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1601428 : Nat := 118140960795 + 1601428 * 2 ^ 59
def prefixEnd_1601428 : Nat := 4983230072969 + 3 ^ 40 * 1601428 * 2
def baseEnd_1601428 : Nat := 822302297568465639285173

theorem tailTrace_1601428 : CollatzResearch.WordTrace tailWord_1601428 prefixEnd_1601428 822302297568465639285173 := by
  unfold tailWord_1601428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204438821153666486446469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38939251761538221981928625 29204438821153666486446469)
  ·
    refine ⟨5475832278966312466208713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29204438821153666486446469 5475832278966312466208713)
    ·
      refine ⟨4106874209224734349656535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475832278966312466208713 4106874209224734349656535)
      ·
        refine ⟨6160311313837101524484803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106874209224734349656535 6160311313837101524484803)
        ·
          refine ⟨9240466970755652286727205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160311313837101524484803 9240466970755652286727205)
          ·
            refine ⟨1732587557016684803761351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9240466970755652286727205 1732587557016684803761351)
            ·
              refine ⟨2598881335525027205642027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732587557016684803761351 2598881335525027205642027)
              ·
                refine ⟨3898322003287540808463041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598881335525027205642027 3898322003287540808463041)
                ·
                  refine ⟨2923741502465655606347281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898322003287540808463041 2923741502465655606347281)
                  ·
                    refine ⟨2192806126849241704760461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2923741502465655606347281 2192806126849241704760461)
                    ·
                      refine ⟨822302297568465639285173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192806126849241704760461 822302297568465639285173)
                      ·
                        rfl

theorem cell23_1601428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1601428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601428 prefixEnd_1601428 := by exact prefixLift 1601428
  have htrace : WordTrace (prefixWord ++ tailWord_1601428) baseStart_1601428 baseEnd_1601428 := by
    simpa [prefixWord, tailWord_1601428, baseEnd_1601428] using wordTrace_append hprefix tailTrace_1601428
  have hstable : (prefixWord ++ tailWord_1601428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601428).length < 2 ^ (prefixWord ++ tailWord_1601428).sum := by decide
  have hdescent : baseEnd_1601428 < baseStart_1601428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601467 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_1601467 : Nat := 118140960795 + 1601467 * 2 ^ 59
def prefixEnd_1601467 : Nat := 4983230072969 + 3 ^ 40 * 1601467 * 2
def baseEnd_1601467 : Nat := 822322323313990986697493

theorem tailTrace_1601467 : CollatzResearch.WordTrace tailWord_1601467 prefixEnd_1601467 822322323313990986697493 := by
  unfold tailWord_1601467
  simp only [CollatzResearch.WordTrace]
  refine ⟨58410300089166042633562655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38940200059444028422375103 58410300089166042633562655)
  ·
    refine ⟨87615450133749063950343983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58410300089166042633562655 87615450133749063950343983)
    ·
      refine ⟨131423175200623595925515975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87615450133749063950343983 131423175200623595925515975)
      ·
        refine ⟨197134762800935393888273963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131423175200623595925515975 197134762800935393888273963)
        ·
          refine ⟨295702144201403090832410945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197134762800935393888273963 295702144201403090832410945)
          ·
            refine ⟨221776608151052318124308209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295702144201403090832410945 221776608151052318124308209)
            ·
              refine ⟨166332456113289238593231157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221776608151052318124308209 166332456113289238593231157)
              ·
                refine ⟨15593667760620866118115421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166332456113289238593231157 15593667760620866118115421)
                ·
                  refine ⟨5847625410232824794293283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15593667760620866118115421 5847625410232824794293283)
                  ·
                    refine ⟨8771438115349237191439925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5847625410232824794293283 8771438115349237191439925)
                    ·
                      refine ⟨822322323313990986697493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8771438115349237191439925 822322323313990986697493)
                      ·
                        rfl

theorem cell23_1601467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_1601467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601467 prefixEnd_1601467 := by exact prefixLift 1601467
  have htrace : WordTrace (prefixWord ++ tailWord_1601467) baseStart_1601467 baseEnd_1601467 := by
    simpa [prefixWord, tailWord_1601467, baseEnd_1601467] using wordTrace_append hprefix tailTrace_1601467
  have hstable : (prefixWord ++ tailWord_1601467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601467).length < 2 ^ (prefixWord ++ tailWord_1601467).sum := by decide
  have hdescent : baseEnd_1601467 < baseStart_1601467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601487 : List Nat := [1, 1, 2, 1, 1, 5, 3, 9]
def baseStart_1601487 : Nat := 118140960795 + 1601487 * 2 ^ 59
def prefixEnd_1601487 : Nat := 4983230072969 + 3 ^ 40 * 1601487 * 2
def baseEnd_1601487 : Nat := 30456762701002996609163

theorem tailTrace_1601487 : CollatzResearch.WordTrace tailWord_1601487 prefixEnd_1601487 30456762701002996609163 := by
  unfold tailWord_1601487
  simp only [CollatzResearch.WordTrace]
  refine ⟨58411029549093586049290715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38940686366062390699527143 58411029549093586049290715)
  ·
    refine ⟨87616544323640379073936073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58411029549093586049290715 87616544323640379073936073)
    ·
      refine ⟨65712408242730284305452055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87616544323640379073936073 65712408242730284305452055)
      ·
        refine ⟨98568612364095426458178083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65712408242730284305452055 98568612364095426458178083)
        ·
          refine ⟨147852918546143139687267125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98568612364095426458178083 147852918546143139687267125)
          ·
            refine ⟨13861211113700919345681293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147852918546143139687267125 13861211113700919345681293)
            ·
              refine ⟨5197954167637844754630485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13861211113700919345681293 5197954167637844754630485)
              ·
                refine ⟨30456762701002996609163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5197954167637844754630485 30456762701002996609163)
                ·
                  rfl

theorem cell23_1601487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 9].length) (baseStart_1601487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601487 prefixEnd_1601487 := by exact prefixLift 1601487
  have htrace : WordTrace (prefixWord ++ tailWord_1601487) baseStart_1601487 baseEnd_1601487 := by
    simpa [prefixWord, tailWord_1601487, baseEnd_1601487] using wordTrace_append hprefix tailTrace_1601487
  have hstable : (prefixWord ++ tailWord_1601487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601487).length < 2 ^ (prefixWord ++ tailWord_1601487).sum := by decide
  have hdescent : baseEnd_1601487 < baseStart_1601487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601542 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1601542 : Nat := 118140960795 + 1601542 * 2 ^ 59
def prefixEnd_1601542 : Nat := 4983230072969 + 3 ^ 40 * 1601542 * 2
def baseEnd_1601542 : Nat := 274120278121026064419883

theorem tailTrace_1601542 : CollatzResearch.WordTrace tailWord_1601542 prefixEnd_1601542 274120278121026064419883 := by
  unfold tailWord_1601542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825407361371697826329465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38942023709262886961695253 1825407361371697826329465)
  ·
    refine ⟨1369055521028773369747099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1825407361371697826329465 1369055521028773369747099)
    ·
      refine ⟨2053583281543160054620649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369055521028773369747099 2053583281543160054620649)
      ·
        refine ⟨1540187461157370040965487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053583281543160054620649 1540187461157370040965487)
        ·
          refine ⟨2310281191736055061448231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540187461157370040965487 2310281191736055061448231)
          ·
            refine ⟨3465421787604082592172347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310281191736055061448231 3465421787604082592172347)
            ·
              refine ⟨5198132681406123888258521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465421787604082592172347 5198132681406123888258521)
              ·
                refine ⟨3898599511054592916193891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5198132681406123888258521 3898599511054592916193891)
                ·
                  refine ⟨5847899266581889374290837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898599511054592916193891 5847899266581889374290837)
                  ·
                    refine ⟨274120278121026064419883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5847899266581889374290837 274120278121026064419883)
                    ·
                      rfl

theorem cell23_1601542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1601542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601542 prefixEnd_1601542 := by exact prefixLift 1601542
  have htrace : WordTrace (prefixWord ++ tailWord_1601542) baseStart_1601542 baseEnd_1601542 := by
    simpa [prefixWord, tailWord_1601542, baseEnd_1601542] using wordTrace_append hprefix tailTrace_1601542
  have hstable : (prefixWord ++ tailWord_1601542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601542).length < 2 ^ (prefixWord ++ tailWord_1601542).sum := by decide
  have hdescent : baseEnd_1601542 < baseStart_1601542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601549 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1601549 : Nat := 118140960795 + 1601549 * 2 ^ 59
def prefixEnd_1601549 : Nat := 4983230072969 + 3 ^ 40 * 1601549 * 2
def baseEnd_1601549 : Nat := 822364428727659665872117

theorem tailTrace_1601549 : CollatzResearch.WordTrace tailWord_1601549 prefixEnd_1601549 822364428727659665872117 := by
  unfold tailWord_1601549
  simp only [CollatzResearch.WordTrace]
  refine ⟨58413290874868970638047701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38942193916579313758698467 58413290874868970638047701)
  ·
    refine ⟨1369061504879741499329243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 58413290874868970638047701 1369061504879741499329243)
    ·
      refine ⟨2053592257319612248993865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369061504879741499329243 2053592257319612248993865)
      ·
        refine ⟨1540194192989709186745399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053592257319612248993865 1540194192989709186745399)
        ·
          refine ⟨2310291289484563780118099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540194192989709186745399 2310291289484563780118099)
          ·
            refine ⟨3465436934226845670177149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310291289484563780118099 3465436934226845670177149)
            ·
              refine ⟨1299538850335067126316431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3465436934226845670177149 1299538850335067126316431)
              ·
                refine ⟨1949308275502600689474647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299538850335067126316431 1949308275502600689474647)
                ·
                  refine ⟨2923962413253901034211971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949308275502600689474647 2923962413253901034211971)
                  ·
                    refine ⟨4385943619880851551317957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923962413253901034211971 4385943619880851551317957)
                    ·
                      refine ⟨822364428727659665872117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4385943619880851551317957 822364428727659665872117)
                      ·
                        rfl

theorem cell23_1601549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1601549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601549 prefixEnd_1601549 := by exact prefixLift 1601549
  have htrace : WordTrace (prefixWord ++ tailWord_1601549) baseStart_1601549 baseEnd_1601549 := by
    simpa [prefixWord, tailWord_1601549, baseEnd_1601549] using wordTrace_append hprefix tailTrace_1601549
  have hstable : (prefixWord ++ tailWord_1601549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601549).length < 2 ^ (prefixWord ++ tailWord_1601549).sum := by decide
  have hdescent : baseEnd_1601549 < baseStart_1601549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601565 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1601565 : Nat := 118140960795 + 1601565 * 2 ^ 59
def prefixEnd_1601565 : Nat := 4983230072969 + 3 ^ 40 * 1601565 * 2
def baseEnd_1601565 : Nat := 822372644418131603272043

theorem tailTrace_1601565 : CollatzResearch.WordTrace tailWord_1601565 prefixEnd_1601565 822372644418131603272043 := by
  unfold tailWord_1601565
  simp only [CollatzResearch.WordTrace]
  refine ⟨58413874442811005370630149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38942582961874003580420099 58413874442811005370630149)
  ·
    refine ⟨10952601458027063506993153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58413874442811005370630149 10952601458027063506993153)
    ·
      refine ⟨8214451093520297630244865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10952601458027063506993153 8214451093520297630244865)
      ·
        refine ⟨6160838320140223222683649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8214451093520297630244865 6160838320140223222683649)
        ·
          refine ⟨4620628740105167417012737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6160838320140223222683649 4620628740105167417012737)
          ·
            refine ⟨3465471555078875562759553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4620628740105167417012737 3465471555078875562759553)
            ·
              refine ⟨2599103666309156672069665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465471555078875562759553 2599103666309156672069665)
              ·
                refine ⟨1949327749731867504052249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599103666309156672069665 1949327749731867504052249)
                ·
                  refine ⟨1461995812298900628039187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1949327749731867504052249 1461995812298900628039187)
                  ·
                    refine ⟨2192993718448350942058781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461995812298900628039187 2192993718448350942058781)
                    ·
                      refine ⟨822372644418131603272043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2192993718448350942058781 822372644418131603272043)
                      ·
                        rfl

theorem cell23_1601565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1601565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601565 prefixEnd_1601565 := by exact prefixLift 1601565
  have htrace : WordTrace (prefixWord ++ tailWord_1601565) baseStart_1601565 baseEnd_1601565 := by
    simpa [prefixWord, tailWord_1601565, baseEnd_1601565] using wordTrace_append hprefix tailTrace_1601565
  have hstable : (prefixWord ++ tailWord_1601565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601565).length < 2 ^ (prefixWord ++ tailWord_1601565).sum := by decide
  have hdescent : baseEnd_1601565 < baseStart_1601565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601571 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 4, 2]
def baseStart_1601571 : Nat := 118140960795 + 1601571 * 2 ^ 59
def prefixEnd_1601571 : Nat := 4983230072969 + 3 ^ 40 * 1601571 * 2
def baseEnd_1601571 : Nat := 822375725302058579797015

theorem tailTrace_1601571 : CollatzResearch.WordTrace tailWord_1601571 prefixEnd_1601571 822375725302058579797015 := by
  unfold tailWord_1601571
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414093280789268395348567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38942728853859512263565711 58414093280789268395348567)
  ·
    refine ⟨87621139921183902593022851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58414093280789268395348567 87621139921183902593022851)
    ·
      refine ⟨131431709881775853889534277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87621139921183902593022851 131431709881775853889534277)
      ·
        refine ⟨24643445602832972604287677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131431709881775853889534277 24643445602832972604287677)
        ·
          refine ⟨9241292101062364726607879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24643445602832972604287677 9241292101062364726607879)
          ·
            refine ⟨13861938151593547089911819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241292101062364726607879 13861938151593547089911819)
            ·
              refine ⟨20792907227390320634867729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13861938151593547089911819 20792907227390320634867729)
              ·
                refine ⟨15594680420542740476150797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20792907227390320634867729 15594680420542740476150797)
                ·
                  refine ⟨5848005157703527678556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15594680420542740476150797 5848005157703527678556549)
                  ·
                    refine ⟨1096500967069411439729353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848005157703527678556549 1096500967069411439729353)
                    ·
                      refine ⟨822375725302058579797015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096500967069411439729353 822375725302058579797015)
                      ·
                        rfl

theorem cell23_1601571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_1601571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601571 prefixEnd_1601571 := by exact prefixLift 1601571
  have htrace : WordTrace (prefixWord ++ tailWord_1601571) baseStart_1601571 baseEnd_1601571 := by
    simpa [prefixWord, tailWord_1601571, baseEnd_1601571] using wordTrace_append hprefix tailTrace_1601571
  have hstable : (prefixWord ++ tailWord_1601571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601571).length < 2 ^ (prefixWord ++ tailWord_1601571).sum := by decide
  have hdescent : baseEnd_1601571 < baseStart_1601571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601584 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_1601584 : Nat := 118140960795 + 1601584 * 2 ^ 59
def prefixEnd_1601584 : Nat := 4983230072969 + 3 ^ 40 * 1601584 * 2
def baseEnd_1601584 : Nat := 822382400550567028934455

theorem tailTrace_1601584 : CollatzResearch.WordTrace tailWord_1601584 prefixEnd_1601584 822382400550567028934455 := by
  unfold tailWord_1601584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29207283714871085807785903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38943044953161447743714537 29207283714871085807785903)
  ·
    refine ⟨43810925572306628711678855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29207283714871085807785903 43810925572306628711678855)
    ·
      refine ⟨65716388358459943067518283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43810925572306628711678855 65716388358459943067518283)
      ·
        refine ⟨98574582537689914601277425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65716388358459943067518283 98574582537689914601277425)
        ·
          refine ⟨73930936903267435950958069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98574582537689914601277425 73930936903267435950958069)
          ·
            refine ⟨6931025334681322120402319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73930936903267435950958069 6931025334681322120402319)
            ·
              refine ⟨10396538002021983180603479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931025334681322120402319 10396538002021983180603479)
              ·
                refine ⟨15594807003032974770905219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396538002021983180603479 15594807003032974770905219)
                ·
                  refine ⟨23392210504549462156357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594807003032974770905219 23392210504549462156357829)
                  ·
                    refine ⟨4386039469603024154317093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23392210504549462156357829 4386039469603024154317093)
                    ·
                      refine ⟨822382400550567028934455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4386039469603024154317093 822382400550567028934455)
                      ·
                        rfl

theorem cell23_1601584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_1601584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601584 prefixEnd_1601584 := by exact prefixLift 1601584
  have htrace : WordTrace (prefixWord ++ tailWord_1601584) baseStart_1601584 baseEnd_1601584 := by
    simpa [prefixWord, tailWord_1601584, baseEnd_1601584] using wordTrace_append hprefix tailTrace_1601584
  have hstable : (prefixWord ++ tailWord_1601584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601584).length < 2 ^ (prefixWord ++ tailWord_1601584).sum := by decide
  have hdescent : baseEnd_1601584 < baseStart_1601584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601621 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1601621 : Nat := 118140960795 + 1601621 * 2 ^ 59
def prefixEnd_1601621 : Nat := 4983230072969 + 3 ^ 40 * 1601621 * 2
def baseEnd_1601621 : Nat := 822401399334783384171785

theorem tailTrace_1601621 : CollatzResearch.WordTrace tailWord_1601621 prefixEnd_1601621 822401399334783384171785 := by
  unfold tailWord_1601621
  simp only [CollatzResearch.WordTrace]
  refine ⟨58415916930608126934668717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38943944620405417956445811 58415916930608126934668717)
  ·
    refine ⟨21905968848978047600500769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58415916930608126934668717 21905968848978047600500769)
    ·
      refine ⟨16429476636733535700375577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21905968848978047600500769 16429476636733535700375577)
      ·
        refine ⟨12322107477550151775281683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16429476636733535700375577 12322107477550151775281683)
        ·
          refine ⟨18483161216325227662922525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322107477550151775281683 18483161216325227662922525)
          ·
            refine ⟨6931185456121960373595947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18483161216325227662922525 6931185456121960373595947)
            ·
              refine ⟨10396778184182940560393921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931185456121960373595947 10396778184182940560393921)
              ·
                refine ⟨7797583638137205420295441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396778184182940560393921 7797583638137205420295441)
                ·
                  refine ⟨5848187728602904065221581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797583638137205420295441 5848187728602904065221581)
                  ·
                    refine ⟨2193070398226089024458093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5848187728602904065221581 2193070398226089024458093)
                    ·
                      refine ⟨822401399334783384171785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2193070398226089024458093 822401399334783384171785)
                      ·
                        rfl

theorem cell23_1601621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1601621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601621 prefixEnd_1601621 := by exact prefixLift 1601621
  have htrace : WordTrace (prefixWord ++ tailWord_1601621) baseStart_1601621 baseEnd_1601621 := by
    simpa [prefixWord, tailWord_1601621, baseEnd_1601621] using wordTrace_append hprefix tailTrace_1601621
  have hstable : (prefixWord ++ tailWord_1601621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601621).length < 2 ^ (prefixWord ++ tailWord_1601621).sum := by decide
  have hdescent : baseEnd_1601621 < baseStart_1601621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601628 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 5]
def baseStart_1601628 : Nat := 118140960795 + 1601628 * 2 ^ 59
def prefixEnd_1601628 : Nat := 4983230072969 + 3 ^ 40 * 1601628 * 2
def baseEnd_1601628 : Nat := 91378332633262761864917

theorem tailTrace_1601628 : CollatzResearch.WordTrace tailWord_1601628 prefixEnd_1601628 91378332633262761864917 := by
  unfold tailWord_1601628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208086120791383565086769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38944114827721844753449025 29208086120791383565086769)
  ·
    refine ⟨21906064590593537673815077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29208086120791383565086769 21906064590593537673815077)
    ·
      refine ⟨4107387110736288313840327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21906064590593537673815077 4107387110736288313840327)
      ·
        refine ⟨6161080666104432470760491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107387110736288313840327 6161080666104432470760491)
        ·
          refine ⟨9241620999156648706140737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161080666104432470760491 9241620999156648706140737)
          ·
            refine ⟨6931215749367486529605553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9241620999156648706140737 6931215749367486529605553)
            ·
              refine ⟨5198411812025614897204165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931215749367486529605553 5198411812025614897204165)
              ·
                refine ⟨974702214754802793225781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5198411812025614897204165 974702214754802793225781)
                ·
                  refine ⟨91378332633262761864917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974702214754802793225781 91378332633262761864917)
                  ·
                    rfl

theorem cell23_1601628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_1601628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601628 prefixEnd_1601628 := by exact prefixLift 1601628
  have htrace : WordTrace (prefixWord ++ tailWord_1601628) baseStart_1601628 baseEnd_1601628 := by
    simpa [prefixWord, tailWord_1601628, baseEnd_1601628] using wordTrace_append hprefix tailTrace_1601628
  have hstable : (prefixWord ++ tailWord_1601628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601628).length < 2 ^ (prefixWord ++ tailWord_1601628).sum := by decide
  have hdescent : baseEnd_1601628 < baseStart_1601628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601631 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 5, 2]
def baseStart_1601631 : Nat := 118140960795 + 1601631 * 2 ^ 59
def prefixEnd_1601631 : Nat := 4983230072969 + 3 ^ 40 * 1601631 * 2
def baseEnd_1601631 : Nat := 822406534141328345046739

theorem tailTrace_1601631 : CollatzResearch.WordTrace tailWord_1601631 prefixEnd_1601631 822406534141328345046739 := by
  unfold tailWord_1601631
  simp only [CollatzResearch.WordTrace]
  refine ⟨58416281660571898642532747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38944187773714599095021831 58416281660571898642532747)
  ·
    refine ⟨87624422490857847963799121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58416281660571898642532747 87624422490857847963799121)
    ·
      refine ⟨65718316868143385972849341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87624422490857847963799121 65718316868143385972849341)
      ·
        refine ⟨24644368825553769739818503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65718316868143385972849341 24644368825553769739818503)
        ·
          refine ⟨36966553238330654609727755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24644368825553769739818503 36966553238330654609727755)
          ·
            refine ⟨55449829857495981914591633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36966553238330654609727755 55449829857495981914591633)
            ·
              refine ⟨41587372393121986435943725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55449829857495981914591633 41587372393121986435943725)
              ·
                refine ⟨15595264647420744913478897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41587372393121986435943725 15595264647420744913478897)
                ·
                  refine ⟨11696448485565558685109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15595264647420744913478897 11696448485565558685109173)
                  ·
                    refine ⟨1096542045521771126728985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11696448485565558685109173 1096542045521771126728985)
                    ·
                      refine ⟨822406534141328345046739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096542045521771126728985 822406534141328345046739)
                      ·
                        rfl

theorem cell23_1601631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_1601631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601631 prefixEnd_1601631 := by exact prefixLift 1601631
  have htrace : WordTrace (prefixWord ++ tailWord_1601631) baseStart_1601631 baseEnd_1601631 := by
    simpa [prefixWord, tailWord_1601631, baseEnd_1601631] using wordTrace_append hprefix tailTrace_1601631
  have hstable : (prefixWord ++ tailWord_1601631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601631).length < 2 ^ (prefixWord ++ tailWord_1601631).sum := by decide
  have hdescent : baseEnd_1601631 < baseStart_1601631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601661 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1601661 : Nat := 118140960795 + 1601661 * 2 ^ 59
def prefixEnd_1601661 : Nat := 4983230072969 + 3 ^ 40 * 1601661 * 2
def baseEnd_1601661 : Nat := 822421938560963227671601

theorem tailTrace_1601661 : CollatzResearch.WordTrace tailWord_1601661 prefixEnd_1601661 822421938560963227671601 := by
  unfold tailWord_1601661
  simp only [CollatzResearch.WordTrace]
  refine ⟨58417375850463213766124837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38944917233642142510749891 58417375850463213766124837)
  ·
    refine ⟨10953257971961852581148407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58417375850463213766124837 10953257971961852581148407)
    ·
      refine ⟨16429886957942778871722611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953257971961852581148407 16429886957942778871722611)
      ·
        refine ⟨24644830436914168307583917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429886957942778871722611 24644830436914168307583917)
        ·
          refine ⟨9241811413842813115343969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24644830436914168307583917 9241811413842813115343969)
          ·
            refine ⟨6931358560382109836507977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9241811413842813115343969 6931358560382109836507977)
            ·
              refine ⟨5198518920286582377380983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931358560382109836507977 5198518920286582377380983)
              ·
                refine ⟨7797778380429873566071475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198518920286582377380983 7797778380429873566071475)
                ·
                  refine ⟨11696667570644810349107213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7797778380429873566071475 11696667570644810349107213)
                  ·
                    refine ⟨4386250338991803880915205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11696667570644810349107213 4386250338991803880915205)
                    ·
                      refine ⟨822421938560963227671601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4386250338991803880915205 822421938560963227671601)
                      ·
                        rfl

theorem cell23_1601661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1601661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601661 prefixEnd_1601661 := by exact prefixLift 1601661
  have htrace : WordTrace (prefixWord ++ tailWord_1601661) baseStart_1601661 baseEnd_1601661 := by
    simpa [prefixWord, tailWord_1601661, baseEnd_1601661] using wordTrace_append hprefix tailTrace_1601661
  have hstable : (prefixWord ++ tailWord_1601661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601661).length < 2 ^ (prefixWord ++ tailWord_1601661).sum := by decide
  have hdescent : baseEnd_1601661 < baseStart_1601661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601664 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1601664 : Nat := 118140960795 + 1601664 * 2 ^ 59
def prefixEnd_1601664 : Nat := 4983230072969 + 3 ^ 40 * 1601664 * 2
def baseEnd_1601664 : Nat := 822423479002926715934087

theorem tailTrace_1601664 : CollatzResearch.WordTrace tailWord_1601664 prefixEnd_1601664 822423479002926715934087 := by
  unfold tailWord_1601664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208742634726172639242023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38944990179634896852322697 29208742634726172639242023)
  ·
    refine ⟨43813113952089258958863035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29208742634726172639242023 43813113952089258958863035)
    ·
      refine ⟨65719670928133888438294553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43813113952089258958863035 65719670928133888438294553)
      ·
        refine ⟨49289753196100416328720915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65719670928133888438294553 49289753196100416328720915)
        ·
          refine ⟨73934629794150624493081373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49289753196100416328720915 73934629794150624493081373)
          ·
            refine ⟨27725486172806484184905515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73934629794150624493081373 27725486172806484184905515)
            ·
              refine ⟨41588229259209726277358273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27725486172806484184905515 41588229259209726277358273)
              ·
                refine ⟨31191171944407294708018705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41588229259209726277358273 31191171944407294708018705)
                ·
                  refine ⟨23393378958305471031014029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31191171944407294708018705 23393378958305471031014029)
                  ·
                    refine ⟨8772517109364551636630261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23393378958305471031014029 8772517109364551636630261)
                    ·
                      refine ⟨822423479002926715934087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8772517109364551636630261 822423479002926715934087)
                      ·
                        rfl

theorem cell23_1601664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1601664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601664 prefixEnd_1601664 := by exact prefixLift 1601664
  have htrace : WordTrace (prefixWord ++ tailWord_1601664) baseStart_1601664 baseEnd_1601664 := by
    simpa [prefixWord, tailWord_1601664, baseEnd_1601664] using wordTrace_append hprefix tailTrace_1601664
  have hstable : (prefixWord ++ tailWord_1601664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601664).length < 2 ^ (prefixWord ++ tailWord_1601664).sum := by decide
  have hdescent : baseEnd_1601664 < baseStart_1601664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601671 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1601671 : Nat := 118140960795 + 1601671 * 2 ^ 59
def prefixEnd_1601671 : Nat := 4983230072969 + 3 ^ 40 * 1601671 * 2
def baseEnd_1601671 : Nat := 274142357789169396182185

theorem tailTrace_1601671 : CollatzResearch.WordTrace tailWord_1601671 prefixEnd_1601671 274142357789169396182185 := by
  unfold tailWord_1601671
  simp only [CollatzResearch.WordTrace]
  refine ⟨58417740580426985473988867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38945160386951323649325911 58417740580426985473988867)
  ·
    refine ⟨87626610870640478210983301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58417740580426985473988867 87626610870640478210983301)
    ·
      refine ⟨16429989538245089664559369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87626610870640478210983301 16429989538245089664559369)
      ·
        refine ⟨12322492153683817248419527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16429989538245089664559369 12322492153683817248419527)
        ·
          refine ⟨18483738230525725872629291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322492153683817248419527 18483738230525725872629291)
          ·
            refine ⟨27725607345788588808943937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18483738230525725872629291 27725607345788588808943937)
            ·
              refine ⟨20794205509341441606707953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27725607345788588808943937 20794205509341441606707953)
              ·
                refine ⟨15595654132006081205030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20794205509341441606707953 15595654132006081205030965)
                ·
                  refine ⟨1462092574875570112971653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15595654132006081205030965 1462092574875570112971653)
                  ·
                    refine ⟨274142357789169396182185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462092574875570112971653 274142357789169396182185)
                    ·
                      rfl

theorem cell23_1601671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1601671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601671 prefixEnd_1601671 := by exact prefixLift 1601671
  have htrace : WordTrace (prefixWord ++ tailWord_1601671) baseStart_1601671 baseEnd_1601671 := by
    simpa [prefixWord, tailWord_1601671, baseEnd_1601671] using wordTrace_append hprefix tailTrace_1601671
  have hstable : (prefixWord ++ tailWord_1601671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601671).length < 2 ^ (prefixWord ++ tailWord_1601671).sum := by decide
  have hdescent : baseEnd_1601671 < baseStart_1601671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601701 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 6]
def baseStart_1601701 : Nat := 118140960795 + 1601701 * 2 ^ 59
def prefixEnd_1601701 : Nat := 4983230072969 + 3 ^ 40 * 1601701 * 2
def baseEnd_1601701 : Nat := 91382497531904785685713

theorem tailTrace_1601701 : CollatzResearch.WordTrace tailWord_1601701 prefixEnd_1601701 91382497531904785685713 := by
  unfold tailWord_1601701
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418834770318300597580957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38945889846878867065053971 58418834770318300597580957)
  ·
    refine ⟨21907063038869362724092859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58418834770318300597580957 21907063038869362724092859)
    ·
      refine ⟨32860594558304044086139289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21907063038869362724092859 32860594558304044086139289)
      ·
        refine ⟨24645445918728033064604467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32860594558304044086139289 24645445918728033064604467)
        ·
          refine ⟨36968168878092049596906701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24645445918728033064604467 36968168878092049596906701)
          ·
            refine ⟨13863063329284518598840013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36968168878092049596906701 13863063329284518598840013)
            ·
              refine ⟨5198648748481694474565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13863063329284518598840013 5198648748481694474565005)
              ·
                refine ⟨1949493280680635427961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5198648748481694474565005 1949493280680635427961877)
                ·
                  refine ⟨91382497531904785685713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1949493280680635427961877 91382497531904785685713)
                  ·
                    rfl

theorem cell23_1601701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_1601701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601701 prefixEnd_1601701 := by exact prefixLift 1601701
  have htrace : WordTrace (prefixWord ++ tailWord_1601701) baseStart_1601701 baseEnd_1601701 := by
    simpa [prefixWord, tailWord_1601701, baseEnd_1601701] using wordTrace_append hprefix tailTrace_1601701
  have hstable : (prefixWord ++ tailWord_1601701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601701).length < 2 ^ (prefixWord ++ tailWord_1601701).sum := by decide
  have hdescent : baseEnd_1601701 < baseStart_1601701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601768 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1601768 : Nat := 118140960795 + 1601768 * 2 ^ 59
def prefixEnd_1601768 : Nat := 4983230072969 + 3 ^ 40 * 1601768 * 2
def baseEnd_1601768 : Nat := 822476880990994309033609

theorem tailTrace_1601768 : CollatzResearch.WordTrace tailWord_1601768 prefixEnd_1601768 822476880990994309033609 := by
  unfold tailWord_1601768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29210639230537785520134979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38947518974050380693513305 29210639230537785520134979)
  ·
    refine ⟨43815958845806678280202469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29210639230537785520134979 43815958845806678280202469)
    ·
      refine ⟨8215492283588752177537963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43815958845806678280202469 8215492283588752177537963)
      ·
        refine ⟨12323238425383128266306945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8215492283588752177537963 12323238425383128266306945)
        ·
          refine ⟨9242428819037346199730209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12323238425383128266306945 9242428819037346199730209)
          ·
            refine ⟨6931821614278009649797657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9242428819037346199730209 6931821614278009649797657)
            ·
              refine ⟨5198866210708507237348243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931821614278009649797657 5198866210708507237348243)
              ·
                refine ⟨7798299316062760856022365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198866210708507237348243 7798299316062760856022365)
                ·
                  refine ⟨2924362243523535321008387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7798299316062760856022365 2924362243523535321008387)
                  ·
                    refine ⟨4386543365285302981512581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924362243523535321008387 4386543365285302981512581)
                    ·
                      refine ⟨822476880990994309033609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4386543365285302981512581 822476880990994309033609)
                      ·
                        rfl

theorem cell23_1601768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1601768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601768 prefixEnd_1601768 := by exact prefixLift 1601768
  have htrace : WordTrace (prefixWord ++ tailWord_1601768) baseStart_1601768 baseEnd_1601768 := by
    simpa [prefixWord, tailWord_1601768, baseEnd_1601768] using wordTrace_append hprefix tailTrace_1601768
  have hstable : (prefixWord ++ tailWord_1601768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601768).length < 2 ^ (prefixWord ++ tailWord_1601768).sum := by decide
  have hdescent : baseEnd_1601768 < baseStart_1601768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601778 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1601778 : Nat := 118140960795 + 1601778 * 2 ^ 59
def prefixEnd_1601778 : Nat := 4983230072969 + 3 ^ 40 * 1601778 * 2
def baseEnd_1601778 : Nat := 274160671932513089969521

theorem tailTrace_1601778 : CollatzResearch.WordTrace tailWord_1601778 prefixEnd_1601778 274160671932513089969521 := by
  unfold tailWord_1601778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605410797759835687033497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38947762127359561832089325 14605410797759835687033497)
  ·
    refine ⟨10954058098319876765275123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14605410797759835687033497 10954058098319876765275123)
    ·
      refine ⟨16431087147479815147912685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10954058098319876765275123 16431087147479815147912685)
      ·
        refine ⟨6161657680304930680467257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16431087147479815147912685 6161657680304930680467257)
        ·
          refine ⟨4621243260228698010350443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161657680304930680467257 4621243260228698010350443)
          ·
            refine ⟨6931864890343047015525665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621243260228698010350443 6931864890343047015525665)
            ·
              refine ⟨5198898667757285261644249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931864890343047015525665 5198898667757285261644249)
              ·
                refine ⟨3899174000817963946233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5198898667757285261644249 3899174000817963946233187)
                ·
                  refine ⟨5848761001226945919349781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899174000817963946233187 5848761001226945919349781)
                  ·
                    refine ⟨274160671932513089969521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5848761001226945919349781 274160671932513089969521)
                    ·
                      rfl

theorem cell23_1601778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1601778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601778 prefixEnd_1601778 := by exact prefixLift 1601778
  have htrace : WordTrace (prefixWord ++ tailWord_1601778) baseStart_1601778 baseEnd_1601778 := by
    simpa [prefixWord, tailWord_1601778, baseEnd_1601778] using wordTrace_append hprefix tailTrace_1601778
  have hstable : (prefixWord ++ tailWord_1601778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601778).length < 2 ^ (prefixWord ++ tailWord_1601778).sum := by decide
  have hdescent : baseEnd_1601778 < baseStart_1601778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601815 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1601815 : Nat := 118140960795 + 1601815 * 2 ^ 59
def prefixEnd_1601815 : Nat := 4983230072969 + 3 ^ 40 * 1601815 * 2
def baseEnd_1601815 : Nat := 822501014581755625145893

theorem tailTrace_1601815 : CollatzResearch.WordTrace tailWord_1601815 prefixEnd_1601815 822501014581755625145893 := by
  unfold tailWord_1601815
  simp only [CollatzResearch.WordTrace]
  refine ⟨58422992691905298067230899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38948661794603532044820599 58422992691905298067230899)
  ·
    refine ⟨87634489037857947100846349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58422992691905298067230899 87634489037857947100846349)
    ·
      refine ⟨32862933389196730162817381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87634489037857947100846349 32862933389196730162817381)
      ·
        refine ⟨6161800010474386905528259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32862933389196730162817381 6161800010474386905528259)
        ·
          refine ⟨9242700015711580358292389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161800010474386905528259 9242700015711580358292389)
          ·
            refine ⟨1733006252945921317179823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9242700015711580358292389 1733006252945921317179823)
            ·
              refine ⟨2599509379418881975769735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733006252945921317179823 2599509379418881975769735)
              ·
                refine ⟨3899264069128322963654603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599509379418881975769735 3899264069128322963654603)
                ·
                  refine ⟨5848896103692484445481905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899264069128322963654603 5848896103692484445481905)
                  ·
                    refine ⟨4386672077769363334111429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848896103692484445481905 4386672077769363334111429)
                    ·
                      refine ⟨822501014581755625145893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4386672077769363334111429 822501014581755625145893)
                      ·
                        rfl

theorem cell23_1601815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1601815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601815 prefixEnd_1601815 := by exact prefixLift 1601815
  have htrace : WordTrace (prefixWord ++ tailWord_1601815) baseStart_1601815 baseEnd_1601815 := by
    simpa [prefixWord, tailWord_1601815, baseEnd_1601815] using wordTrace_append hprefix tailTrace_1601815
  have hstable : (prefixWord ++ tailWord_1601815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601815).length < 2 ^ (prefixWord ++ tailWord_1601815).sum := by decide
  have hdescent : baseEnd_1601815 < baseStart_1601815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601875 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 6, 2, 2]
def baseStart_1601875 : Nat := 118140960795 + 1601875 * 2 ^ 59
def prefixEnd_1601875 : Nat := 4983230072969 + 3 ^ 40 * 1601875 * 2
def baseEnd_1601875 : Nat := 822531823421025390395617

theorem tailTrace_1601875 : CollatzResearch.WordTrace tailWord_1601875 prefixEnd_1601875 822531823421025390395617 := by
  unfold tailWord_1601875
  simp only [CollatzResearch.WordTrace]
  refine ⟨58425181071687928314415079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38950120714458618876276719 58425181071687928314415079)
  ·
    refine ⟨87637771607531892471622619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58425181071687928314415079 87637771607531892471622619)
    ·
      refine ⟨131456657411297838707433929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87637771607531892471622619 131456657411297838707433929)
      ·
        refine ⟨98592493058473379030575447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131456657411297838707433929 98592493058473379030575447)
        ·
          refine ⟨147888739587710068545863171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98592493058473379030575447 147888739587710068545863171)
          ·
            refine ⟨221833109381565102818794757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147888739587710068545863171 221833109381565102818794757)
            ·
              refine ⟨41593708009043456778524017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221833109381565102818794757 41593708009043456778524017)
              ·
                refine ⟨31195281006782592583893013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41593708009043456778524017 31195281006782592583893013)
                ·
                  refine ⟨1462278797192934027369985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31195281006782592583893013 1462278797192934027369985)
                  ·
                    refine ⟨1096709097894700520527489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462278797192934027369985 1096709097894700520527489)
                    ·
                      refine ⟨822531823421025390395617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096709097894700520527489 822531823421025390395617)
                      ·
                        rfl

theorem cell23_1601875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2, 2].length) (baseStart_1601875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601875 prefixEnd_1601875 := by exact prefixLift 1601875
  have htrace : WordTrace (prefixWord ++ tailWord_1601875) baseStart_1601875 baseEnd_1601875 := by
    simpa [prefixWord, tailWord_1601875, baseEnd_1601875] using wordTrace_append hprefix tailTrace_1601875
  have hstable : (prefixWord ++ tailWord_1601875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601875).length < 2 ^ (prefixWord ++ tailWord_1601875).sum := by decide
  have hdescent : baseEnd_1601875 < baseStart_1601875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601881 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 9]
def baseStart_1601881 : Nat := 118140960795 + 1601881 * 2 ^ 59
def prefixEnd_1601881 : Nat := 4983230072969 + 3 ^ 40 * 1601881 * 2
def baseEnd_1601881 : Nat := 91392767144994707435621

theorem tailTrace_1601881 : CollatzResearch.WordTrace tailWord_1601881 prefixEnd_1601881 91392767144994707435621 := by
  unfold tailWord_1601881
  simp only [CollatzResearch.WordTrace]
  refine ⟨58425399909666191339133497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38950266606444127559422331 58425399909666191339133497)
  ·
    refine ⟨43819049932249643504350123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58425399909666191339133497 43819049932249643504350123)
    ·
      refine ⟨65728574898374465256525185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43819049932249643504350123 65728574898374465256525185)
      ·
        refine ⟨49296431173780848942393889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65728574898374465256525185 49296431173780848942393889)
        ·
          refine ⟨36972323380335636706795417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49296431173780848942393889 36972323380335636706795417)
          ·
            refine ⟨27729242535251727530096563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36972323380335636706795417 27729242535251727530096563)
            ·
              refine ⟨41593863802877591295144845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27729242535251727530096563 41593863802877591295144845)
              ·
                refine ⟨15597698926079096735679317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41593863802877591295144845 15597698926079096735679317)
                ·
                  refine ⟨91392767144994707435621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15597698926079096735679317 91392767144994707435621)
                  ·
                    rfl

theorem cell23_1601881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_1601881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601881 prefixEnd_1601881 := by exact prefixLift 1601881
  have htrace : WordTrace (prefixWord ++ tailWord_1601881) baseStart_1601881 baseEnd_1601881 := by
    simpa [prefixWord, tailWord_1601881, baseEnd_1601881] using wordTrace_append hprefix tailTrace_1601881
  have hstable : (prefixWord ++ tailWord_1601881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601881).length < 2 ^ (prefixWord ++ tailWord_1601881).sum := by decide
  have hdescent : baseEnd_1601881 < baseStart_1601881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601909 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1601909 : Nat := 118140960795 + 1601909 * 2 ^ 59
def prefixEnd_1601909 : Nat := 4983230072969 + 3 ^ 40 * 1601909 * 2
def baseEnd_1601909 : Nat := 822549281763278257370461

theorem tailTrace_1601909 : CollatzResearch.WordTrace tailWord_1601909 prefixEnd_1601909 822549281763278257370461 := by
  unfold tailWord_1601909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58426421153564752121152781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38950947435709834747435187 58426421153564752121152781)
  ·
    refine ⟨21909907932586782045432293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58426421153564752121152781 21909907932586782045432293)
    ·
      refine ⟨4108107737360021633518555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21909907932586782045432293 4108107737360021633518555)
      ·
        refine ⟨6162161606040032450277833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108107737360021633518555 6162161606040032450277833)
        ·
          refine ⟨4621621204530024337708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6162161606040032450277833 4621621204530024337708375)
          ·
            refine ⟨6932431806795036506562563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621621204530024337708375 6932431806795036506562563)
            ·
              refine ⟨10398647710192554759843845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932431806795036506562563 10398647710192554759843845)
              ·
                refine ⟨1949746445661104017470721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10398647710192554759843845 1949746445661104017470721)
                ·
                  refine ⟨1462309834245828013103041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1949746445661104017470721 1462309834245828013103041)
                  ·
                    refine ⟨1096732375684371009827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462309834245828013103041 1096732375684371009827281)
                    ·
                      refine ⟨822549281763278257370461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096732375684371009827281 822549281763278257370461)
                      ·
                        rfl

theorem cell23_1601909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1601909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601909 prefixEnd_1601909 := by exact prefixLift 1601909
  have htrace : WordTrace (prefixWord ++ tailWord_1601909) baseStart_1601909 baseEnd_1601909 := by
    simpa [prefixWord, tailWord_1601909, baseEnd_1601909] using wordTrace_append hprefix tailTrace_1601909
  have hstable : (prefixWord ++ tailWord_1601909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601909).length < 2 ^ (prefixWord ++ tailWord_1601909).sum := by decide
  have hdescent : baseEnd_1601909 < baseStart_1601909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601915 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 5]
def baseStart_1601915 : Nat := 118140960795 + 1601915 * 2 ^ 59
def prefixEnd_1601915 : Nat := 4983230072969 + 3 ^ 40 * 1601915 * 2
def baseEnd_1601915 : Nat := 91394706960800581543937

theorem tailTrace_1601915 : CollatzResearch.WordTrace tailWord_1601915 prefixEnd_1601915 91394706960800581543937 := by
  unfold tailWord_1601915
  simp only [CollatzResearch.WordTrace]
  refine ⟨58426639991543015145871199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38951093327695343430580799 58426639991543015145871199)
  ·
    refine ⟨87639959987314522718806799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58426639991543015145871199 87639959987314522718806799)
    ·
      refine ⟨131459939980971784078210199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87639959987314522718806799 131459939980971784078210199)
      ·
        refine ⟨197189909971457676117315299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131459939980971784078210199 197189909971457676117315299)
        ·
          refine ⟨295784864957186514175972949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197189909971457676117315299 295784864957186514175972949)
          ·
            refine ⟨3466228886217029462999683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 295784864957186514175972949 3466228886217029462999683)
            ·
              refine ⟨5199343329325544194499525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466228886217029462999683 5199343329325544194499525)
              ·
                refine ⟨974876874248539536468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5199343329325544194499525 974876874248539536468661)
                ·
                  refine ⟨91394706960800581543937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974876874248539536468661 91394706960800581543937)
                  ·
                    rfl

theorem cell23_1601915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 5].length) (baseStart_1601915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601915 prefixEnd_1601915 := by exact prefixLift 1601915
  have htrace : WordTrace (prefixWord ++ tailWord_1601915) baseStart_1601915 baseEnd_1601915 := by
    simpa [prefixWord, tailWord_1601915, baseEnd_1601915] using wordTrace_append hprefix tailTrace_1601915
  have hstable : (prefixWord ++ tailWord_1601915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601915).length < 2 ^ (prefixWord ++ tailWord_1601915).sum := by decide
  have hdescent : baseEnd_1601915 < baseStart_1601915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601928 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1601928 : Nat := 118140960795 + 1601928 * 2 ^ 59
def prefixEnd_1601928 : Nat := 4983230072969 + 3 ^ 40 * 1601928 * 2
def baseEnd_1601928 : Nat := 274186345965237894344291

theorem tailTrace_1601928 : CollatzResearch.WordTrace tailWord_1601928 prefixEnd_1601928 274186345965237894344291 := by
  unfold tailWord_1601928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29213557070247959183047219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38951409426997278910729625 29213557070247959183047219)
  ·
    refine ⟨43820335605371938774570829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29213557070247959183047219 43820335605371938774570829)
    ·
      refine ⟨16432625852014477040464061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43820335605371938774570829 16432625852014477040464061)
      ·
        refine ⟨6162234694505428890174023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16432625852014477040464061 6162234694505428890174023)
        ·
          refine ⟨9243352041758143335261035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162234694505428890174023 9243352041758143335261035)
          ·
            refine ⟨13865028062637215002891553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243352041758143335261035 13865028062637215002891553)
            ·
              refine ⟨10398771046977911252168665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13865028062637215002891553 10398771046977911252168665)
              ·
                refine ⟨7799078285233433439126499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10398771046977911252168665 7799078285233433439126499)
                ·
                  refine ⟨11698617427850150158689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799078285233433439126499 11698617427850150158689749)
                  ·
                    refine ⟨274186345965237894344291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11698617427850150158689749 274186345965237894344291)
                    ·
                      rfl

theorem cell23_1601928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1601928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601928 prefixEnd_1601928 := by exact prefixLift 1601928
  have htrace : WordTrace (prefixWord ++ tailWord_1601928) baseStart_1601928 baseEnd_1601928 := by
    simpa [prefixWord, tailWord_1601928, baseEnd_1601928] using wordTrace_append hprefix tailTrace_1601928
  have hstable : (prefixWord ++ tailWord_1601928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601928).length < 2 ^ (prefixWord ++ tailWord_1601928).sum := by decide
  have hdescent : baseEnd_1601928 < baseStart_1601928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601975 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 3, 4]
def baseStart_1601975 : Nat := 118140960795 + 1601975 * 2 ^ 59
def prefixEnd_1601975 : Nat := 4983230072969 + 3 ^ 40 * 1601975 * 2
def baseEnd_1601975 : Nat := 274194390495491666381719

theorem tailTrace_1601975 : CollatzResearch.WordTrace tailWord_1601975 prefixEnd_1601975 274194390495491666381719 := by
  unfold tailWord_1601975
  simp only [CollatzResearch.WordTrace]
  refine ⟨58428828371325645393055379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38952552247550430262036919 58428828371325645393055379)
  ·
    refine ⟨87643242556988468089583069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58428828371325645393055379 87643242556988468089583069)
    ·
      refine ⟨32866215958870675533593651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87643242556988468089583069 32866215958870675533593651)
      ·
        refine ⟨49299323938306013300390477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32866215958870675533593651 49299323938306013300390477)
        ·
          refine ⟨18487246476864754987646429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49299323938306013300390477 18487246476864754987646429)
          ·
            refine ⟨6932717428824283120367411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18487246476864754987646429 6932717428824283120367411)
            ·
              refine ⟨10399076143236424680551117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932717428824283120367411 10399076143236424680551117)
              ·
                refine ⟨3899653553713659255206669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10399076143236424680551117 3899653553713659255206669)
                ·
                  refine ⟨1462370082642622220702501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3899653553713659255206669 1462370082642622220702501)
                  ·
                    refine ⟨274194390495491666381719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462370082642622220702501 274194390495491666381719)
                    ·
                      rfl

theorem cell23_1601975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_1601975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601975 prefixEnd_1601975 := by exact prefixLift 1601975
  have htrace : WordTrace (prefixWord ++ tailWord_1601975) baseStart_1601975 baseEnd_1601975 := by
    simpa [prefixWord, tailWord_1601975, baseEnd_1601975] using wordTrace_append hprefix tailTrace_1601975
  have hstable : (prefixWord ++ tailWord_1601975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601975).length < 2 ^ (prefixWord ++ tailWord_1601975).sum := by decide
  have hdescent : baseEnd_1601975 < baseStart_1601975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601982 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_1601982 : Nat := 118140960795 + 1601982 * 2 ^ 59
def prefixEnd_1601982 : Nat := 4983230072969 + 3 ^ 40 * 1601982 * 2
def baseEnd_1601982 : Nat := 822586765851056471757625

theorem tailTrace_1601982 : CollatzResearch.WordTrace tailWord_1601982 prefixEnd_1601982 822586765851056471757625 := by
  unfold tailWord_1601982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303635460287535698570025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38952722454866857059040133 7303635460287535698570025)
  ·
    refine ⟨5477726595215651773927519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7303635460287535698570025 5477726595215651773927519)
    ·
      refine ⟨8216589892823477660891279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5477726595215651773927519 8216589892823477660891279)
      ·
        refine ⟨12324884839235216491336919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8216589892823477660891279 12324884839235216491336919)
        ·
          refine ⟨18487327258852824737005379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12324884839235216491336919 18487327258852824737005379)
          ·
            refine ⟨27730990888279237105508069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18487327258852824737005379 27730990888279237105508069)
            ·
              refine ⟨5199560791552356957282763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27730990888279237105508069 5199560791552356957282763)
              ·
                refine ⟨7799341187328535435924145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199560791552356957282763 7799341187328535435924145)
                ·
                  refine ⟨5849505890496401576943109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799341187328535435924145 5849505890496401576943109)
                  ·
                    refine ⟨1096782354468075295676833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849505890496401576943109 1096782354468075295676833)
                    ·
                      refine ⟨822586765851056471757625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096782354468075295676833 822586765851056471757625)
                      ·
                        rfl

theorem cell23_1601982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_1601982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1601982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1601982 prefixEnd_1601982 := by exact prefixLift 1601982
  have htrace : WordTrace (prefixWord ++ tailWord_1601982) baseStart_1601982 baseEnd_1601982 := by
    simpa [prefixWord, tailWord_1601982, baseEnd_1601982] using wordTrace_append hprefix tailTrace_1601982
  have hstable : (prefixWord ++ tailWord_1601982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601982).length < 2 ^ (prefixWord ++ tailWord_1601982).sum := by decide
  have hdescent : baseEnd_1601982 < baseStart_1601982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602025 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 5, 2]
def baseStart_1602025 : Nat := 118140960795 + 1602025 * 2 ^ 59
def prefixEnd_1602025 : Nat := 4983230072969 + 3 ^ 40 * 1602025 * 2
def baseEnd_1602025 : Nat := 822608845519199803519927

theorem tailTrace_1602025 : CollatzResearch.WordTrace tailWord_1602025 prefixEnd_1602025 822608845519199803519927 := by
  unfold tailWord_1602025
  simp only [CollatzResearch.WordTrace]
  refine ⟨58430652021144503932375529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38953768014096335954917019 58430652021144503932375529)
  ·
    refine ⟨43822989015858377949281647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58430652021144503932375529 43822989015858377949281647)
    ·
      refine ⟨65734483523787566923922471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43822989015858377949281647 65734483523787566923922471)
      ·
        refine ⟨98601725285681350385883707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65734483523787566923922471 98601725285681350385883707)
        ·
          refine ⟨147902587928522025578825561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98601725285681350385883707 147902587928522025578825561)
          ·
            refine ⟨110926940946391519184119171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147902587928522025578825561 110926940946391519184119171)
            ·
              refine ⟨166390411419587278776178757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110926940946391519184119171 166390411419587278776178757)
              ·
                refine ⟨31198202141172614770533517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166390411419587278776178757 31198202141172614770533517)
                ·
                  refine ⟨11699325802939730538950069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31198202141172614770533517 11699325802939730538950069)
                  ·
                    refine ⟨1096811794025599738026569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11699325802939730538950069 1096811794025599738026569)
                    ·
                      refine ⟨822608845519199803519927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096811794025599738026569 822608845519199803519927)
                      ·
                        rfl

theorem cell23_1602025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5, 2].length) (baseStart_1602025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602025 prefixEnd_1602025 := by exact prefixLift 1602025
  have htrace : WordTrace (prefixWord ++ tailWord_1602025) baseStart_1602025 baseEnd_1602025 := by
    simpa [prefixWord, tailWord_1602025, baseEnd_1602025] using wordTrace_append hprefix tailTrace_1602025
  have hstable : (prefixWord ++ tailWord_1602025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602025).length < 2 ^ (prefixWord ++ tailWord_1602025).sum := by decide
  have hdescent : baseEnd_1602025 < baseStart_1602025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602026 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1602026 : Nat := 118140960795 + 1602026 * 2 ^ 59
def prefixEnd_1602026 : Nat := 4983230072969 + 3 ^ 40 * 1602026 * 2
def baseEnd_1602026 : Nat := 274203119666618099869141

theorem tailTrace_1602026 : CollatzResearch.WordTrace tailWord_1602026 prefixEnd_1602026 274203119666618099869141 := by
  unfold tailWord_1602026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607672123535220275790483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38953792329427254068774621 14607672123535220275790483)
  ·
    refine ⟨21911508185302830413685725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14607672123535220275790483 21911508185302830413685725)
    ·
      refine ⟨8216815569488561405132147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21911508185302830413685725 8216815569488561405132147)
      ·
        refine ⟨12325223354232842107698221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8216815569488561405132147 12325223354232842107698221)
        ·
          refine ⟨4621958757837315790386833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12325223354232842107698221 4621958757837315790386833)
          ·
            refine ⟨3466469068377986842790125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621958757837315790386833 3466469068377986842790125)
            ·
              refine ⟨1299925900641745066046297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3466469068377986842790125 1299925900641745066046297)
              ·
                refine ⟨974944425481308799534723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299925900641745066046297 974944425481308799534723)
                ·
                  refine ⟨1462416638221963199302085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974944425481308799534723 1462416638221963199302085)
                  ·
                    refine ⟨274203119666618099869141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462416638221963199302085 274203119666618099869141)
                    ·
                      rfl

theorem cell23_1602026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1602026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602026 prefixEnd_1602026 := by exact prefixLift 1602026
  have htrace : WordTrace (prefixWord ++ tailWord_1602026) baseStart_1602026 baseEnd_1602026 := by
    simpa [prefixWord, tailWord_1602026, baseEnd_1602026] using wordTrace_append hprefix tailTrace_1602026
  have hstable : (prefixWord ++ tailWord_1602026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602026).length < 2 ^ (prefixWord ++ tailWord_1602026).sum := by decide
  have hdescent : baseEnd_1602026 < baseStart_1602026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602048 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_1602048 : Nat := 118140960795 + 1602048 * 2 ^ 59
def prefixEnd_1602048 : Nat := 4983230072969 + 3 ^ 40 * 1602048 * 2
def baseEnd_1602048 : Nat := 274206885191417737844107

theorem tailTrace_1602048 : CollatzResearch.WordTrace tailWord_1602048 prefixEnd_1602048 274206885191417737844107 := by
  unfold tailWord_1602048
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215745450030589430231399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38954327266707452573641865 29215745450030589430231399)
  ·
    refine ⟨43823618175045884145347099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29215745450030589430231399 43823618175045884145347099)
    ·
      refine ⟨65735427262568826218020649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43823618175045884145347099 65735427262568826218020649)
      ·
        refine ⟨49301570446926619663515487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65735427262568826218020649 49301570446926619663515487)
        ·
          refine ⟨73952355670389929495273231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49301570446926619663515487 73952355670389929495273231)
          ·
            refine ⟨110928533505584894242909847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73952355670389929495273231 110928533505584894242909847)
            ·
              refine ⟨166392800258377341364364771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110928533505584894242909847 166392800258377341364364771)
              ·
                refine ⟨249589200387566012046547157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166392800258377341364364771 249589200387566012046547157)
                ·
                  refine ⟨5849746884083578407340949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249589200387566012046547157 5849746884083578407340949)
                  ·
                    refine ⟨274206885191417737844107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5849746884083578407340949 274206885191417737844107)
                    ·
                      rfl

theorem cell23_1602048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_1602048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602048 prefixEnd_1602048 := by exact prefixLift 1602048
  have htrace : WordTrace (prefixWord ++ tailWord_1602048) baseStart_1602048 baseEnd_1602048 := by
    simpa [prefixWord, tailWord_1602048, baseEnd_1602048] using wordTrace_append hprefix tailTrace_1602048
  have hstable : (prefixWord ++ tailWord_1602048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602048).length < 2 ^ (prefixWord ++ tailWord_1602048).sum := by decide
  have hdescent : baseEnd_1602048 < baseStart_1602048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602052 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1602052 : Nat := 118140960795 + 1602052 * 2 ^ 59
def prefixEnd_1602052 : Nat := 4983230072969 + 3 ^ 40 * 1602052 * 2
def baseEnd_1602052 : Nat := 274207569832290399294101

theorem tailTrace_1602052 : CollatzResearch.WordTrace tailWord_1602052 prefixEnd_1602052 274207569832290399294101 := by
  unfold tailWord_1602052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215818396023343771804205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38954424528031125029072273 29215818396023343771804205)
  ·
    refine ⟨10955931898508753914426577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29215818396023343771804205 10955931898508753914426577)
    ·
      refine ⟨8216948923881565435819933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10955931898508753914426577 8216948923881565435819933)
      ·
        refine ⟨3081355846455587038432475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8216948923881565435819933 3081355846455587038432475)
        ·
          refine ⟨4622033769683380557648713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081355846455587038432475 4622033769683380557648713)
          ·
            refine ⟨3466525327262535418236535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622033769683380557648713 3466525327262535418236535)
            ·
              refine ⟨5199787990893803127354803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466525327262535418236535 5199787990893803127354803)
              ·
                refine ⟨7799681986340704691032205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199787990893803127354803 7799681986340704691032205)
                ·
                  refine ⟨2924880744877764259137077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7799681986340704691032205 2924880744877764259137077)
                  ·
                    refine ⟨274207569832290399294101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2924880744877764259137077 274207569832290399294101)
                    ·
                      rfl

theorem cell23_1602052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1602052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602052 prefixEnd_1602052 := by exact prefixLift 1602052
  have htrace : WordTrace (prefixWord ++ tailWord_1602052) baseStart_1602052 baseEnd_1602052 := by
    simpa [prefixWord, tailWord_1602052, baseEnd_1602052] using wordTrace_append hprefix tailTrace_1602052
  have hstable : (prefixWord ++ tailWord_1602052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602052).length < 2 ^ (prefixWord ++ tailWord_1602052).sum := by decide
  have hdescent : baseEnd_1602052 < baseStart_1602052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602059 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 2, 3, 2]
def baseStart_1602059 : Nat := 118140960795 + 1602059 * 2 ^ 59
def prefixEnd_1602059 : Nat := 4983230072969 + 3 ^ 40 * 1602059 * 2
def baseEnd_1602059 : Nat := 822626303861452670494771

theorem tailTrace_1602059 : CollatzResearch.WordTrace tailWord_1602059 prefixEnd_1602059 822626303861452670494771 := by
  unfold tailWord_1602059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58431892103021327739113231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38954594735347551826075487 58431892103021327739113231)
  ·
    refine ⟨87647838154531991608669847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58431892103021327739113231 87647838154531991608669847)
    ·
      refine ⟨131471757231797987413004771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87647838154531991608669847 131471757231797987413004771)
      ·
        refine ⟨197207635847696981119507157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131471757231797987413004771 197207635847696981119507157)
        ·
          refine ⟨4622053965180397994988449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 197207635847696981119507157 4622053965180397994988449)
          ·
            refine ⟨3466540473885298496241337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622053965180397994988449 3466540473885298496241337)
            ·
              refine ⟨2599905355413973872181003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466540473885298496241337 2599905355413973872181003)
              ·
                refine ⟨3899858033120960808271505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599905355413973872181003 3899858033120960808271505)
                ·
                  refine ⟨2924893524840720606203629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899858033120960808271505 2924893524840720606203629)
                  ·
                    refine ⟨1096835071815270227326361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924893524840720606203629 1096835071815270227326361)
                    ·
                      refine ⟨822626303861452670494771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096835071815270227326361 822626303861452670494771)
                      ·
                        rfl

theorem cell23_1602059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3, 2].length) (baseStart_1602059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602059 prefixEnd_1602059 := by exact prefixLift 1602059
  have htrace : WordTrace (prefixWord ++ tailWord_1602059) baseStart_1602059 baseEnd_1602059 := by
    simpa [prefixWord, tailWord_1602059, baseEnd_1602059] using wordTrace_append hprefix tailTrace_1602059
  have hstable : (prefixWord ++ tailWord_1602059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602059).length < 2 ^ (prefixWord ++ tailWord_1602059).sum := by decide
  have hdescent : baseEnd_1602059 < baseStart_1602059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602065 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_1602065 : Nat := 118140960795 + 1602065 * 2 ^ 59
def prefixEnd_1602065 : Nat := 4983230072969 + 3 ^ 40 * 1602065 * 2
def baseEnd_1602065 : Nat := 274209794915126549006581

theorem tailTrace_1602065 : CollatzResearch.WordTrace tailWord_1602065 prefixEnd_1602065 274209794915126549006581 := by
  unfold tailWord_1602065
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432110940999590763831649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38954740627333060509221099 58432110940999590763831649)
  ·
    refine ⟨43824083205749693072873737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58432110940999590763831649 43824083205749693072873737)
    ·
      refine ⟨32868062404312269804655303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43824083205749693072873737 32868062404312269804655303)
      ·
        refine ⟨49302093606468404706982955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32868062404312269804655303 49302093606468404706982955)
        ·
          refine ⟨73953140409702607060474433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49302093606468404706982955 73953140409702607060474433)
          ·
            refine ⟨55464855307276955295355825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73953140409702607060474433 55464855307276955295355825)
            ·
              refine ⟨41598641480457716471516869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55464855307276955295355825 41598641480457716471516869)
              ·
                refine ⟨7799745277585821838409413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41598641480457716471516869 7799745277585821838409413)
                ·
                  refine ⟨1462452239547341594701765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7799745277585821838409413 1462452239547341594701765)
                  ·
                    refine ⟨274209794915126549006581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462452239547341594701765 274209794915126549006581)
                    ·
                      rfl

theorem cell23_1602065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_1602065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602065 prefixEnd_1602065 := by exact prefixLift 1602065
  have htrace : WordTrace (prefixWord ++ tailWord_1602065) baseStart_1602065 baseEnd_1602065 := by
    simpa [prefixWord, tailWord_1602065, baseEnd_1602065] using wordTrace_append hprefix tailTrace_1602065
  have hstable : (prefixWord ++ tailWord_1602065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602065).length < 2 ^ (prefixWord ++ tailWord_1602065).sum := by decide
  have hdescent : baseEnd_1602065 < baseStart_1602065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602083 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 1, 1, 3]
def baseStart_1602083 : Nat := 118140960795 + 1602083 * 2 ^ 59
def prefixEnd_1602083 : Nat := 4983230072969 + 3 ^ 40 * 1602083 * 2
def baseEnd_1602083 : Nat := 822638627397160576594661

theorem tailTrace_1602083 : CollatzResearch.WordTrace tailWord_1602083 prefixEnd_1602083 822638627397160576594661 := by
  unfold tailWord_1602083
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432767454934379837986903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38955178303289586558657935 58432767454934379837986903)
  ·
    refine ⟨87649151182401569756980355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58432767454934379837986903 87649151182401569756980355)
    ·
      refine ⟨131473726773602354635470533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87649151182401569756980355 131473726773602354635470533)
      ·
        refine ⟨24651323770050441494150725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131473726773602354635470533 24651323770050441494150725)
        ·
          refine ⟨4622123206884457780153261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24651323770050441494150725 4622123206884457780153261)
          ·
            refine ⟨1733296202581671667557473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4622123206884457780153261 1733296202581671667557473)
            ·
              refine ⟨1299972151936253750668105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733296202581671667557473 1299972151936253750668105)
              ·
                refine ⟨974979113952190313001079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299972151936253750668105 974979113952190313001079)
                ·
                  refine ⟨1462468670928285469501619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974979113952190313001079 1462468670928285469501619)
                  ·
                    refine ⟨2193703006392428204252429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1462468670928285469501619 2193703006392428204252429)
                    ·
                      refine ⟨822638627397160576594661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2193703006392428204252429 822638627397160576594661)
                      ·
                        rfl

theorem cell23_1602083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_1602083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602083 prefixEnd_1602083 := by exact prefixLift 1602083
  have htrace : WordTrace (prefixWord ++ tailWord_1602083) baseStart_1602083 baseEnd_1602083 := by
    simpa [prefixWord, tailWord_1602083, baseEnd_1602083] using wordTrace_append hprefix tailTrace_1602083
  have hstable : (prefixWord ++ tailWord_1602083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602083).length < 2 ^ (prefixWord ++ tailWord_1602083).sum := by decide
  have hdescent : baseEnd_1602083 < baseStart_1602083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602110 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1602110 : Nat := 118140960795 + 1602110 * 2 ^ 59
def prefixEnd_1602110 : Nat := 4983230072969 + 3 ^ 40 * 1602110 * 2
def baseEnd_1602110 : Nat := 822652491374831970957037

theorem tailTrace_1602110 : CollatzResearch.WordTrace tailWord_1602110 prefixEnd_1602110 822652491374831970957037 := by
  unfold tailWord_1602110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304219028229570431152473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38955834817224375632813189 7304219028229570431152473)
  ·
    refine ⟨5478164271172177823364355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7304219028229570431152473 5478164271172177823364355)
    ·
      refine ⟨8217246406758266735046533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5478164271172177823364355 8217246406758266735046533)
      ·
        refine ⟨1540733701267175012821225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8217246406758266735046533 1540733701267175012821225)
        ·
          refine ⟨1155550275950381259615919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1540733701267175012821225 1155550275950381259615919)
          ·
            refine ⟨1733325413925571889423879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155550275950381259615919 1733325413925571889423879)
            ·
              refine ⟨2599988120888357834135819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733325413925571889423879 2599988120888357834135819)
              ·
                refine ⟨3899982181332536751203729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599988120888357834135819 3899982181332536751203729)
                ·
                  refine ⟨2924986635999402563402797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899982181332536751203729 2924986635999402563402797)
                  ·
                    refine ⟨1096869988499775961276049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924986635999402563402797 1096869988499775961276049)
                    ·
                      refine ⟨822652491374831970957037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096869988499775961276049 822652491374831970957037)
                      ·
                        rfl

theorem cell23_1602110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1602110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602110 prefixEnd_1602110 := by exact prefixLift 1602110
  have htrace : WordTrace (prefixWord ++ tailWord_1602110) baseStart_1602110 baseEnd_1602110 := by
    simpa [prefixWord, tailWord_1602110, baseEnd_1602110] using wordTrace_append hprefix tailTrace_1602110
  have hstable : (prefixWord ++ tailWord_1602110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602110).length < 2 ^ (prefixWord ++ tailWord_1602110).sum := by decide
  have hdescent : baseEnd_1602110 < baseStart_1602110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602122 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_1602122 : Nat := 118140960795 + 1602122 * 2 ^ 59
def prefixEnd_1602122 : Nat := 4983230072969 + 3 ^ 40 * 1602122 * 2
def baseEnd_1602122 : Nat := 822658653142685924006981

theorem tailTrace_1602122 : CollatzResearch.WordTrace tailWord_1602122 prefixEnd_1602122 822658653142685924006981 := by
  unfold tailWord_1602122
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608547475448272374664155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38956126601195392999104413 14608547475448272374664155)
  ·
    refine ⟨21912821213172408561996233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608547475448272374664155 21912821213172408561996233)
    ·
      refine ⟨16434615909879306421497175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21912821213172408561996233 16434615909879306421497175)
      ·
        refine ⟨24651923864818959632245763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434615909879306421497175 24651923864818959632245763)
        ·
          refine ⟨36977885797228439448368645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24651923864818959632245763 36977885797228439448368645)
          ·
            refine ⟨6933353586980332396569121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36977885797228439448368645 6933353586980332396569121)
            ·
              refine ⟨5200015190235249297426841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6933353586980332396569121 5200015190235249297426841)
              ·
                refine ⟨3900011392676436973070131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200015190235249297426841 3900011392676436973070131)
                ·
                  refine ⟨5850017089014655459605197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900011392676436973070131 5850017089014655459605197)
                  ·
                    refine ⟨2193756408380495797351949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5850017089014655459605197 2193756408380495797351949)
                    ·
                      refine ⟨822658653142685924006981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2193756408380495797351949 822658653142685924006981)
                      ·
                        rfl

theorem cell23_1602122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_1602122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602122 prefixEnd_1602122 := by exact prefixLift 1602122
  have htrace : WordTrace (prefixWord ++ tailWord_1602122) baseStart_1602122 baseEnd_1602122 := by
    simpa [prefixWord, tailWord_1602122, baseEnd_1602122] using wordTrace_append hprefix tailTrace_1602122
  have hstable : (prefixWord ++ tailWord_1602122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602122).length < 2 ^ (prefixWord ++ tailWord_1602122).sum := by decide
  have hdescent : baseEnd_1602122 < baseStart_1602122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602175 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1602175 : Nat := 118140960795 + 1602175 * 2 ^ 59
def prefixEnd_1602175 : Nat := 4983230072969 + 3 ^ 40 * 1602175 * 2
def baseEnd_1602175 : Nat := 822685867617374216644237

theorem tailTrace_1602175 : CollatzResearch.WordTrace tailWord_1602175 prefixEnd_1602175 822685867617374216644237 := by
  unfold tailWord_1602175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58436122970601079550335979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38957415313734053033557319 58436122970601079550335979)
  ·
    refine ⟨87654184455901619325503969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58436122970601079550335979 87654184455901619325503969)
    ·
      refine ⟨65740638341926214494127977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87654184455901619325503969 65740638341926214494127977)
      ·
        refine ⟨49305478756444660870595983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65740638341926214494127977 49305478756444660870595983)
        ·
          refine ⟨73958218134666991305893975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49305478756444660870595983 73958218134666991305893975)
          ·
            refine ⟨110937327202000486958840963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73958218134666991305893975 110937327202000486958840963)
            ·
              refine ⟨166405990803000730438261445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110937327202000486958840963 166405990803000730438261445)
              ·
                refine ⟨31201123275562636957174021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166405990803000730438261445 31201123275562636957174021)
                ·
                  refine ⟨5850210614167994429470129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31201123275562636957174021 5850210614167994429470129)
                  ·
                    refine ⟨4387657960625995822102597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850210614167994429470129 4387657960625995822102597)
                    ·
                      refine ⟨822685867617374216644237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4387657960625995822102597 822685867617374216644237)
                      ·
                        rfl

theorem cell23_1602175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1602175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602175 prefixEnd_1602175 := by exact prefixLift 1602175
  have htrace : WordTrace (prefixWord ++ tailWord_1602175) baseStart_1602175 baseEnd_1602175 := by
    simpa [prefixWord, tailWord_1602175, baseEnd_1602175] using wordTrace_append hprefix tailTrace_1602175
  have hstable : (prefixWord ++ tailWord_1602175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602175).length < 2 ^ (prefixWord ++ tailWord_1602175).sum := by decide
  have hdescent : baseEnd_1602175 < baseStart_1602175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602179 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 4, 2, 2]
def baseStart_1602179 : Nat := 118140960795 + 1602179 * 2 ^ 59
def prefixEnd_1602179 : Nat := 4983230072969 + 3 ^ 40 * 1602179 * 2
def baseEnd_1602179 : Nat := 822687921539992200994219

theorem tailTrace_1602179 : CollatzResearch.WordTrace tailWord_1602179 prefixEnd_1602179 822687921539992200994219 := by
  unfold tailWord_1602179
  simp only [CollatzResearch.WordTrace]
  refine ⟨58436268862586588233481591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38957512575057725488987727 58436268862586588233481591)
  ·
    refine ⟨87654403293879882350222387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58436268862586588233481591 87654403293879882350222387)
    ·
      refine ⟨131481604940819823525333581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87654403293879882350222387 131481604940819823525333581)
      ·
        refine ⟨49305601852807433822000093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131481604940819823525333581 49305601852807433822000093)
        ·
          refine ⟨18489600694802787683250035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49305601852807433822000093 18489600694802787683250035)
          ·
            refine ⟨27734401042204181524875053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489600694802787683250035 27734401042204181524875053)
            ·
              refine ⟨10400400390826568071828145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27734401042204181524875053 10400400390826568071828145)
              ·
                refine ⟨7800300293119926053871109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400400390826568071828145 7800300293119926053871109)
                ·
                  refine ⟨1462556304959986135100833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7800300293119926053871109 1462556304959986135100833)
                  ·
                    refine ⟨1096917228719989601325625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462556304959986135100833 1096917228719989601325625)
                    ·
                      refine ⟨822687921539992200994219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1096917228719989601325625 822687921539992200994219)
                      ·
                        rfl

theorem cell23_1602179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_1602179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602179 prefixEnd_1602179 := by exact prefixLift 1602179
  have htrace : WordTrace (prefixWord ++ tailWord_1602179) baseStart_1602179 baseEnd_1602179 := by
    simpa [prefixWord, tailWord_1602179, baseEnd_1602179] using wordTrace_append hprefix tailTrace_1602179
  have hstable : (prefixWord ++ tailWord_1602179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602179).length < 2 ^ (prefixWord ++ tailWord_1602179).sum := by decide
  have hdescent : baseEnd_1602179 < baseStart_1602179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602212 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_1602212 : Nat := 118140960795 + 1602212 * 2 ^ 59
def prefixEnd_1602212 : Nat := 4983230072969 + 3 ^ 40 * 1602212 * 2
def baseEnd_1602212 : Nat := 822704866401590571881567

theorem tailTrace_1602212 : CollatzResearch.WordTrace tailWord_1602212 prefixEnd_1602212 822704866401590571881567 := by
  unfold tailWord_1602212
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218736235733517434716445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38958314980978023246288593 29218736235733517434716445)
  ·
    refine ⟨10957026088400069038018667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29218736235733517434716445 10957026088400069038018667)
    ·
      refine ⟨16435539132600103557028001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10957026088400069038018667 16435539132600103557028001)
      ·
        refine ⟨12326654349450077667771001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16435539132600103557028001 12326654349450077667771001)
        ·
          refine ⟨9244990762087558250828251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12326654349450077667771001 9244990762087558250828251)
          ·
            refine ⟨13867486143131337376242377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244990762087558250828251 13867486143131337376242377)
            ·
              refine ⟨10400614607348503032181783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867486143131337376242377 10400614607348503032181783)
              ·
                refine ⟨15600921911022754548272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400614607348503032181783 15600921911022754548272675)
                ·
                  refine ⟨23401382866534131822409013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600921911022754548272675 23401382866534131822409013)
                  ·
                    refine ⟨2193879643737574858350845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23401382866534131822409013 2193879643737574858350845)
                    ·
                      refine ⟨822704866401590571881567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2193879643737574858350845 822704866401590571881567)
                      ·
                        rfl

theorem cell23_1602212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_1602212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602212 prefixEnd_1602212 := by exact prefixLift 1602212
  have htrace : WordTrace (prefixWord ++ tailWord_1602212) baseStart_1602212 baseEnd_1602212 := by
    simpa [prefixWord, tailWord_1602212, baseEnd_1602212] using wordTrace_append hprefix tailTrace_1602212
  have hstable : (prefixWord ++ tailWord_1602212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602212).length < 2 ^ (prefixWord ++ tailWord_1602212).sum := by decide
  have hdescent : baseEnd_1602212 < baseStart_1602212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602253 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1602253 : Nat := 118140960795 + 1602253 * 2 ^ 59
def prefixEnd_1602253 : Nat := 4983230072969 + 3 ^ 40 * 1602253 * 2
def baseEnd_1602253 : Nat := 91413991012047212385431

theorem tailTrace_1602253 : CollatzResearch.WordTrace tailWord_1602253 prefixEnd_1602253 91413991012047212385431 := by
  unfold tailWord_1602253
  simp only [CollatzResearch.WordTrace]
  refine ⟨58438967864318498871675413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38959311909545665914450275 58438967864318498871675413)
  ·
    refine ⟨2739326618639929634609785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58438967864318498871675413 2739326618639929634609785)
    ·
      refine ⟨2054494963979947225957339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739326618639929634609785 2054494963979947225957339)
      ·
        refine ⟨3081742445969920838936009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054494963979947225957339 3081742445969920838936009)
        ·
          refine ⟨2311306834477440629202007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081742445969920838936009 2311306834477440629202007)
          ·
            refine ⟨3466960251716160943803011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311306834477440629202007 3466960251716160943803011)
            ·
              refine ⟨5200440377574241415704517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466960251716160943803011 5200440377574241415704517)
              ·
                refine ⟨975082570795170265444597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5200440377574241415704517 975082570795170265444597)
                ·
                  refine ⟨91413991012047212385431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975082570795170265444597 91413991012047212385431)
                  ·
                    rfl

theorem cell23_1602253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1602253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602253 prefixEnd_1602253 := by exact prefixLift 1602253
  have htrace : WordTrace (prefixWord ++ tailWord_1602253) baseStart_1602253 baseEnd_1602253 := by
    simpa [prefixWord, tailWord_1602253, baseEnd_1602253] using wordTrace_append hprefix tailTrace_1602253
  have hstable : (prefixWord ++ tailWord_1602253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602253).length < 2 ^ (prefixWord ++ tailWord_1602253).sum := by decide
  have hdescent : baseEnd_1602253 < baseStart_1602253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602272 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1602272 : Nat := 118140960795 + 1602272 * 2 ^ 59
def prefixEnd_1602272 : Nat := 4983230072969 + 3 ^ 40 * 1602272 * 2
def baseEnd_1602272 : Nat := 822735675240860337131291

theorem tailTrace_1602272 : CollatzResearch.WordTrace tailWord_1602272 prefixEnd_1602272 822735675240860337131291 := by
  unfold tailWord_1602272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29219830425624832558308535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38959773900833110077744713 29219830425624832558308535)
  ·
    refine ⟨43829745638437248837462803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29219830425624832558308535 43829745638437248837462803)
    ·
      refine ⟨65744618457655873256194205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43829745638437248837462803 65744618457655873256194205)
      ·
        refine ⟨24654231921620952471072827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65744618457655873256194205 24654231921620952471072827)
        ·
          refine ⟨36981347882431428706609241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24654231921620952471072827 36981347882431428706609241)
          ·
            refine ⟨27736010911823571529956931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36981347882431428706609241 27736010911823571529956931)
            ·
              refine ⟨41604016367735357294935397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27736010911823571529956931 41604016367735357294935397)
              ·
                refine ⟨7800753068950379492800387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41604016367735357294935397 7800753068950379492800387)
                ·
                  refine ⟨11701129603425569239200581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7800753068950379492800387 11701129603425569239200581)
                  ·
                    refine ⟨2193961800642294232350109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11701129603425569239200581 2193961800642294232350109)
                    ·
                      refine ⟨822735675240860337131291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2193961800642294232350109 822735675240860337131291)
                      ·
                        rfl

theorem cell23_1602272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1602272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602272 prefixEnd_1602272 := by exact prefixLift 1602272
  have htrace : WordTrace (prefixWord ++ tailWord_1602272) baseStart_1602272 baseEnd_1602272 := by
    simpa [prefixWord, tailWord_1602272, baseEnd_1602272] using wordTrace_append hprefix tailTrace_1602272
  have hstable : (prefixWord ++ tailWord_1602272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602272).length < 2 ^ (prefixWord ++ tailWord_1602272).sum := by decide
  have hdescent : baseEnd_1602272 < baseStart_1602272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602286 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1602286 : Nat := 118140960795 + 1602286 * 2 ^ 59
def prefixEnd_1602286 : Nat := 4983230072969 + 3 ^ 40 * 1602286 * 2
def baseEnd_1602286 : Nat := 822742863970023282356227

theorem tailTrace_1602286 : CollatzResearch.WordTrace tailWord_1602286 prefixEnd_1602286 822742863970023282356227 := by
  unfold tailWord_1602286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305021434149868188453339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38960114315465963671751141 7305021434149868188453339)
  ·
    refine ⟨10957532151224802282680009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7305021434149868188453339 10957532151224802282680009)
    ·
      refine ⟨8218149113418601712010007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10957532151224802282680009 8218149113418601712010007)
      ·
        refine ⟨12327223670127902568015011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218149113418601712010007 12327223670127902568015011)
        ·
          refine ⟨18490835505191853852022517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327223670127902568015011 18490835505191853852022517)
          ·
            refine ⟨1733515828611736298627111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18490835505191853852022517 1733515828611736298627111)
            ·
              refine ⟨2600273742917604447940667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733515828611736298627111 2600273742917604447940667)
              ·
                refine ⟨3900410614376406671911001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600273742917604447940667 3900410614376406671911001)
                ·
                  refine ⟨2925307960782305003933251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3900410614376406671911001 2925307960782305003933251)
                  ·
                    refine ⟨4387961941173457505899877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2925307960782305003933251 4387961941173457505899877)
                    ·
                      refine ⟨822742863970023282356227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4387961941173457505899877 822742863970023282356227)
                      ·
                        rfl

theorem cell23_1602286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1602286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602286 prefixEnd_1602286 := by exact prefixLift 1602286
  have htrace : WordTrace (prefixWord ++ tailWord_1602286) baseStart_1602286 baseEnd_1602286 := by
    simpa [prefixWord, tailWord_1602286, baseEnd_1602286] using wordTrace_append hprefix tailTrace_1602286
  have hstable : (prefixWord ++ tailWord_1602286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602286).length < 2 ^ (prefixWord ++ tailWord_1602286).sum := by decide
  have hdescent : baseEnd_1602286 < baseStart_1602286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602296 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 1, 4]
def baseStart_1602296 : Nat := 118140960795 + 1602296 * 2 ^ 59
def prefixEnd_1602296 : Nat := 4983230072969 + 3 ^ 40 * 1602296 * 2
def baseEnd_1602296 : Nat := 274249332925522747743727

theorem tailTrace_1602296 : CollatzResearch.WordTrace tailWord_1602296 prefixEnd_1602296 274249332925522747743727 := by
  unfold tailWord_1602296
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220268101581358607745371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38960357468775144810327161 29220268101581358607745371)
  ·
    refine ⟨43830402152372037911618057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29220268101581358607745371 43830402152372037911618057)
    ·
      refine ⟨32872801614279028433713543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43830402152372037911618057 32872801614279028433713543)
      ·
        refine ⟨49309202421418542650570315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32872801614279028433713543 49309202421418542650570315)
        ·
          refine ⟨73963803632127813975855473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49309202421418542650570315 73963803632127813975855473)
          ·
            refine ⟨55472852724095860481891605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73963803632127813975855473 55472852724095860481891605)
            ·
              refine ⟨2600289971441993460088669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55472852724095860481891605 2600289971441993460088669)
              ·
                refine ⟨975108739290747547533251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600289971441993460088669 975108739290747547533251)
                ·
                  refine ⟨1462663108936121321299877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975108739290747547533251 1462663108936121321299877)
                  ·
                    refine ⟨274249332925522747743727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462663108936121321299877 274249332925522747743727)
                    ·
                      rfl

theorem cell23_1602296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_1602296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602296 prefixEnd_1602296 := by exact prefixLift 1602296
  have htrace : WordTrace (prefixWord ++ tailWord_1602296) baseStart_1602296 baseEnd_1602296 := by
    simpa [prefixWord, tailWord_1602296, baseEnd_1602296] using wordTrace_append hprefix tailTrace_1602296
  have hstable : (prefixWord ++ tailWord_1602296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602296).length < 2 ^ (prefixWord ++ tailWord_1602296).sum := by decide
  have hdescent : baseEnd_1602296 < baseStart_1602296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602312 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1602312 : Nat := 118140960795 + 1602312 * 2 ^ 59
def prefixEnd_1602312 : Nat := 4983230072969 + 3 ^ 40 * 1602312 * 2
def baseEnd_1602312 : Nat := 822756214467040180631107

theorem tailTrace_1602312 : CollatzResearch.WordTrace tailWord_1602312 prefixEnd_1602312 822756214467040180631107 := by
  unfold tailWord_1602312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220559885552375974036595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38960746514069834632048793 29220559885552375974036595)
  ·
    refine ⟨43830839828328563961054893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29220559885552375974036595 43830839828328563961054893)
    ·
      refine ⟨16436564935623211485395585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43830839828328563961054893 16436564935623211485395585)
      ·
        refine ⟨12327423701717408614046689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16436564935623211485395585 12327423701717408614046689)
        ·
          refine ⟨9245567776288056460535017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12327423701717408614046689 9245567776288056460535017)
          ·
            refine ⟨6934175832216042345401263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9245567776288056460535017 6934175832216042345401263)
            ·
              refine ⟨10401263748324063518101895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934175832216042345401263 10401263748324063518101895)
              ·
                refine ⟨15601895622486095277152843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401263748324063518101895 15601895622486095277152843)
                ·
                  refine ⟨23402843433729142915729265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15601895622486095277152843 23402843433729142915729265)
                  ·
                    refine ⟨17552132575296857186796949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23402843433729142915729265 17552132575296857186796949)
                    ·
                      refine ⟨822756214467040180631107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17552132575296857186796949 822756214467040180631107)
                      ·
                        rfl

theorem cell23_1602312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1602312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602312 prefixEnd_1602312 := by exact prefixLift 1602312
  have htrace : WordTrace (prefixWord ++ tailWord_1602312) baseStart_1602312 baseEnd_1602312 := by
    simpa [prefixWord, tailWord_1602312, baseEnd_1602312] using wordTrace_append hprefix tailTrace_1602312
  have hstable : (prefixWord ++ tailWord_1602312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602312).length < 2 ^ (prefixWord ++ tailWord_1602312).sum := by decide
  have hdescent : baseEnd_1602312 < baseStart_1602312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602329 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 6, 3, 2]
def baseStart_1602329 : Nat := 118140960795 + 1602329 * 2 ^ 59
def prefixEnd_1602329 : Nat := 4983230072969 + 3 ^ 40 * 1602329 * 2
def baseEnd_1602329 : Nat := 822764943638166614118529

theorem tailTrace_1602329 : CollatzResearch.WordTrace tailWord_1602329 prefixEnd_1602329 822764943638166614118529 := by
  unfold tailWord_1602329
  simp only [CollatzResearch.WordTrace]
  refine ⟨58441739812043163851442041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38961159874695442567628027 58441739812043163851442041)
  ·
    refine ⟨43831304859032372888581531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58441739812043163851442041 43831304859032372888581531)
    ·
      refine ⟨65746957288548559332872297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43831304859032372888581531 65746957288548559332872297)
      ·
        refine ⟨49310217966411419499654223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65746957288548559332872297 49310217966411419499654223)
        ·
          refine ⟨73965326949617129249481335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49310217966411419499654223 73965326949617129249481335)
          ·
            refine ⟨110947990424425693874222003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73965326949617129249481335 110947990424425693874222003)
            ·
              refine ⟨166421985636638540811333005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110947990424425693874222003 166421985636638540811333005)
              ·
                refine ⟨62408244613739452804249877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166421985636638540811333005 62408244613739452804249877)
                ·
                  refine ⟨2925386466269036850199213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62408244613739452804249877 2925386466269036850199213)
                  ·
                    refine ⟨1097019924850888818824705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925386466269036850199213 1097019924850888818824705)
                    ·
                      refine ⟨822764943638166614118529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097019924850888818824705 822764943638166614118529)
                      ·
                        rfl

theorem cell23_1602329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_1602329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602329 prefixEnd_1602329 := by exact prefixLift 1602329
  have htrace : WordTrace (prefixWord ++ tailWord_1602329) baseStart_1602329 baseEnd_1602329 := by
    simpa [prefixWord, tailWord_1602329, baseEnd_1602329] using wordTrace_append hprefix tailTrace_1602329
  have hstable : (prefixWord ++ tailWord_1602329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602329).length < 2 ^ (prefixWord ++ tailWord_1602329).sum := by decide
  have hdescent : baseEnd_1602329 < baseStart_1602329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602336 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1602336 : Nat := 118140960795 + 1602336 * 2 ^ 59
def prefixEnd_1602336 : Nat := 4983230072969 + 3 ^ 40 * 1602336 * 2
def baseEnd_1602336 : Nat := 822768538002748086730997

theorem tailTrace_1602336 : CollatzResearch.WordTrace tailWord_1602336 prefixEnd_1602336 822768538002748086730997 := by
  unfold tailWord_1602336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220997561508902023473431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38961330082011869364631241 29220997561508902023473431)
  ·
    refine ⟨43831496342263353035210147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29220997561508902023473431 43831496342263353035210147)
    ·
      refine ⟨65747244513395029552815221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43831496342263353035210147 65747244513395029552815221)
      ·
        refine ⟨6163804173130784020576427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65747244513395029552815221 6163804173130784020576427)
        ·
          refine ⟨9245706259696176030864641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163804173130784020576427 9245706259696176030864641)
          ·
            refine ⟨6934279694772132023148481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9245706259696176030864641 6934279694772132023148481)
            ·
              refine ⟨5200709771079099017361361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6934279694772132023148481 5200709771079099017361361)
              ·
                refine ⟨3900532328309324263021021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200709771079099017361361 3900532328309324263021021)
                ·
                  refine ⟨1462699623115996598632883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3900532328309324263021021 1462699623115996598632883)
                  ·
                    refine ⟨2194049434673994897949325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1462699623115996598632883 2194049434673994897949325)
                    ·
                      refine ⟨822768538002748086730997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2194049434673994897949325 822768538002748086730997)
                      ·
                        rfl

theorem cell23_1602336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1602336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602336 prefixEnd_1602336 := by exact prefixLift 1602336
  have htrace : WordTrace (prefixWord ++ tailWord_1602336) baseStart_1602336 baseEnd_1602336 := by
    simpa [prefixWord, tailWord_1602336, baseEnd_1602336] using wordTrace_append hprefix tailTrace_1602336
  have hstable : (prefixWord ++ tailWord_1602336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602336).length < 2 ^ (prefixWord ++ tailWord_1602336).sum := by decide
  have hdescent : baseEnd_1602336 < baseStart_1602336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602352 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_1602352 : Nat := 118140960795 + 1602352 * 2 ^ 59
def prefixEnd_1602352 : Nat := 4983230072969 + 3 ^ 40 * 1602352 * 2
def baseEnd_1602352 : Nat := 274258917897740008043641

theorem tailTrace_1602352 : CollatzResearch.WordTrace tailWord_1602352 prefixEnd_1602352 274258917897740008043641 := by
  unfold tailWord_1602352
  simp only [CollatzResearch.WordTrace]
  refine ⟨29221289345479919389764655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38961719127306559186352873 29221289345479919389764655)
  ·
    refine ⟨43831934018219879084646983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29221289345479919389764655 43831934018219879084646983)
    ·
      refine ⟨65747901027329818626970475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43831934018219879084646983 65747901027329818626970475)
      ·
        refine ⟨98621851540994727940455713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65747901027329818626970475 98621851540994727940455713)
        ·
          refine ⟨73966388655746045955341785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98621851540994727940455713 73966388655746045955341785)
          ·
            refine ⟨55474791491809534466506339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73966388655746045955341785 55474791491809534466506339)
            ·
              refine ⟨83212187237714301699759509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55474791491809534466506339 83212187237714301699759509)
              ·
                refine ⟨3900571276767857892176227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83212187237714301699759509 3900571276767857892176227)
                ·
                  refine ⟨5850856915151786838264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900571276767857892176227 5850856915151786838264341)
                  ·
                    refine ⟨274258917897740008043641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5850856915151786838264341 274258917897740008043641)
                    ·
                      rfl

theorem cell23_1602352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_1602352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602352 prefixEnd_1602352 := by exact prefixLift 1602352
  have htrace : WordTrace (prefixWord ++ tailWord_1602352) baseStart_1602352 baseEnd_1602352 := by
    simpa [prefixWord, tailWord_1602352, baseEnd_1602352] using wordTrace_append hprefix tailTrace_1602352
  have hstable : (prefixWord ++ tailWord_1602352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602352).length < 2 ^ (prefixWord ++ tailWord_1602352).sum := by decide
  have hdescent : baseEnd_1602352 < baseStart_1602352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602359 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_1602359 : Nat := 118140960795 + 1602359 * 2 ^ 59
def prefixEnd_1602359 : Nat := 4983230072969 + 3 ^ 40 * 1602359 * 2
def baseEnd_1602359 : Nat := 822780348057801496743391

theorem tailTrace_1602359 : CollatzResearch.WordTrace tailWord_1602359 prefixEnd_1602359 822780348057801496743391 := by
  unfold tailWord_1602359
  simp only [CollatzResearch.WordTrace]
  refine ⟨58442834001934478975034131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38961889334622985983356087 58442834001934478975034131)
  ·
    refine ⟨87664251002901718462551197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58442834001934478975034131 87664251002901718462551197)
    ·
      refine ⟨32874094126088144423456699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87664251002901718462551197 32874094126088144423456699)
      ·
        refine ⟨49311141189132216635185049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32874094126088144423456699 49311141189132216635185049)
        ·
          refine ⟨36983355891849162476388787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49311141189132216635185049 36983355891849162476388787)
          ·
            refine ⟨55475033837773743714583181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36983355891849162476388787 55475033837773743714583181)
            ·
              refine ⟨20803137689165153892968693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55475033837773743714583181 20803137689165153892968693)
              ·
                refine ⟨1950294158359233177465815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20803137689165153892968693 1950294158359233177465815)
                ·
                  refine ⟨2925441237538849766198723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950294158359233177465815 2925441237538849766198723)
                  ·
                    refine ⟨4388161856308274649298085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2925441237538849766198723 4388161856308274649298085)
                    ·
                      refine ⟨822780348057801496743391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4388161856308274649298085 822780348057801496743391)
                      ·
                        rfl

theorem cell23_1602359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_1602359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602359 prefixEnd_1602359 := by exact prefixLift 1602359
  have htrace : WordTrace (prefixWord ++ tailWord_1602359) baseStart_1602359 baseEnd_1602359 := by
    simpa [prefixWord, tailWord_1602359, baseEnd_1602359] using wordTrace_append hprefix tailTrace_1602359
  have hstable : (prefixWord ++ tailWord_1602359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602359).length < 2 ^ (prefixWord ++ tailWord_1602359).sum := by decide
  have hdescent : baseEnd_1602359 < baseStart_1602359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602386 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1602386 : Nat := 118140960795 + 1602386 * 2 ^ 59
def prefixEnd_1602386 : Nat := 4983230072969 + 3 ^ 40 * 1602386 * 2
def baseEnd_1602386 : Nat := 274264737345157630368589

theorem tailTrace_1602386 : CollatzResearch.WordTrace tailWord_1602386 prefixEnd_1602386 274264737345157630368589 := by
  unfold tailWord_1602386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14610954693209165646566753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38962545848557775057511341 14610954693209165646566753)
  ·
    refine ⟨10958216019906874234925065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14610954693209165646566753 10958216019906874234925065)
    ·
      refine ⟨8218662014930155676193799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10958216019906874234925065 8218662014930155676193799)
      ·
        refine ⟨12327993022395233514290699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218662014930155676193799 12327993022395233514290699)
        ·
          refine ⟨18491989533592850271436049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327993022395233514290699 18491989533592850271436049)
          ·
            refine ⟨13868992150194637703577037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18491989533592850271436049 13868992150194637703577037)
            ·
              refine ⟨5200872056322989138841389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13868992150194637703577037 5200872056322989138841389)
              ·
                refine ⟨1950327021121120927065521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200872056322989138841389 1950327021121120927065521)
                ·
                  refine ⟨1462745265840840695299141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950327021121120927065521 1462745265840840695299141)
                  ·
                    refine ⟨274264737345157630368589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462745265840840695299141 274264737345157630368589)
                    ·
                      rfl

theorem cell23_1602386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1602386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602386 prefixEnd_1602386 := by exact prefixLift 1602386
  have htrace : WordTrace (prefixWord ++ tailWord_1602386) baseStart_1602386 baseEnd_1602386 := by
    simpa [prefixWord, tailWord_1602386, baseEnd_1602386] using wordTrace_append hprefix tailTrace_1602386
  have hstable : (prefixWord ++ tailWord_1602386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602386).length < 2 ^ (prefixWord ++ tailWord_1602386).sum := by decide
  have hdescent : baseEnd_1602386 < baseStart_1602386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602389 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1602389 : Nat := 118140960795 + 1602389 * 2 ^ 59
def prefixEnd_1602389 : Nat := 4983230072969 + 3 ^ 40 * 1602389 * 2
def baseEnd_1602389 : Nat := 822795752477436379368253

theorem tailTrace_1602389 : CollatzResearch.WordTrace tailWord_1602389 prefixEnd_1602389 822795752477436379368253 := by
  unfold tailWord_1602389
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443928191825794098626221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38962618794550529399084147 58443928191825794098626221)
  ·
    refine ⟨21916473071934672786984833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58443928191825794098626221 21916473071934672786984833)
    ·
      refine ⟨16437354803951004590238625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21916473071934672786984833 16437354803951004590238625)
      ·
        refine ⟨12328016102963253442678969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16437354803951004590238625 12328016102963253442678969)
        ·
          refine ⟨9246012077222440082009227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12328016102963253442678969 9246012077222440082009227)
          ·
            refine ⟨13869018115833660123013841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246012077222440082009227 13869018115833660123013841)
            ·
              refine ⟨10401763586875245092260381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13869018115833660123013841 10401763586875245092260381)
              ·
                refine ⟨3900661345078216909597643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10401763586875245092260381 3900661345078216909597643)
                ·
                  refine ⟨5850992017617325364396465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900661345078216909597643 5850992017617325364396465)
                  ·
                    refine ⟨4388244013212994023297349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5850992017617325364396465 4388244013212994023297349)
                    ·
                      refine ⟨822795752477436379368253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4388244013212994023297349 822795752477436379368253)
                      ·
                        rfl

theorem cell23_1602389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1602389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602389 prefixEnd_1602389 := by exact prefixLift 1602389
  have htrace : WordTrace (prefixWord ++ tailWord_1602389) baseStart_1602389 baseEnd_1602389 := by
    simpa [prefixWord, tailWord_1602389, baseEnd_1602389] using wordTrace_append hprefix tailTrace_1602389
  have hstable : (prefixWord ++ tailWord_1602389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602389).length < 2 ^ (prefixWord ++ tailWord_1602389).sum := by decide
  have hdescent : baseEnd_1602389 < baseStart_1602389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602483 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 2, 2, 2]
def baseStart_1602483 : Nat := 118140960795 + 1602483 * 2 ^ 59
def prefixEnd_1602483 : Nat := 4983230072969 + 3 ^ 40 * 1602483 * 2
def baseEnd_1602483 : Nat := 822844019658959011592821

theorem tailTrace_1602483 : CollatzResearch.WordTrace tailWord_1602483 prefixEnd_1602483 822844019658959011592821 := by
  unfold tailWord_1602483
  simp only [CollatzResearch.WordTrace]
  refine ⟨58447356653485248152548103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38964904435656832101698735 58447356653485248152548103)
  ·
    refine ⟨87671034980227872228822155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58447356653485248152548103 87671034980227872228822155)
    ·
      refine ⟨131506552470341808343233233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87671034980227872228822155 131506552470341808343233233)
      ·
        refine ⟨98629914352756356257424925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131506552470341808343233233 98629914352756356257424925)
        ·
          refine ⟨36986217882283633596534347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98629914352756356257424925 36986217882283633596534347)
          ·
            refine ⟨55479326823425450394801521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36986217882283633596534347 55479326823425450394801521)
            ·
              refine ⟨41609495117569087796101141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55479326823425450394801521 41609495117569087796101141)
              ·
                refine ⟨1950445083636050990442241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41609495117569087796101141 1950445083636050990442241)
                ·
                  refine ⟨1462833812727038242831681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950445083636050990442241 1462833812727038242831681)
                  ·
                    refine ⟨1097125359545278682123761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462833812727038242831681 1097125359545278682123761)
                    ·
                      refine ⟨822844019658959011592821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097125359545278682123761 822844019658959011592821)
                      ·
                        rfl

theorem cell23_1602483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2, 2].length) (baseStart_1602483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602483 prefixEnd_1602483 := by exact prefixLift 1602483
  have htrace : WordTrace (prefixWord ++ tailWord_1602483) baseStart_1602483 baseEnd_1602483 := by
    simpa [prefixWord, tailWord_1602483, baseEnd_1602483] using wordTrace_append hprefix tailTrace_1602483
  have hstable : (prefixWord ++ tailWord_1602483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602483).length < 2 ^ (prefixWord ++ tailWord_1602483).sum := by decide
  have hdescent : baseEnd_1602483 < baseStart_1602483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602489 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 7]
def baseStart_1602489 : Nat := 118140960795 + 1602489 * 2 ^ 59
def prefixEnd_1602489 : Nat := 4983230072969 + 3 ^ 40 * 1602489 * 2
def baseEnd_1602489 : Nat := 91427455615876220901977

theorem tailTrace_1602489 : CollatzResearch.WordTrace tailWord_1602489 prefixEnd_1602489 91427455615876220901977 := by
  unfold tailWord_1602489
  simp only [CollatzResearch.WordTrace]
  refine ⟨58447575491463511177266521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38965050327642340784844347 58447575491463511177266521)
  ·
    refine ⟨43835681618597633382949891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58447575491463511177266521 43835681618597633382949891)
    ·
      refine ⟨65753522427896450074424837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43835681618597633382949891 65753522427896450074424837)
      ·
        refine ⟨12328785455230584388954657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65753522427896450074424837 12328785455230584388954657)
        ·
          refine ⟨9246589091422938291715993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12328785455230584388954657 9246589091422938291715993)
          ·
            refine ⟨6934941818567203718786995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9246589091422938291715993 6934941818567203718786995)
            ·
              refine ⟨10402412727850805578180493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934941818567203718786995 10402412727850805578180493)
              ·
                refine ⟨3900904772944052091817685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10402412727850805578180493 3900904772944052091817685)
                ·
                  refine ⟨91427455615876220901977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3900904772944052091817685 91427455615876220901977)
                  ·
                    rfl

theorem cell23_1602489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_1602489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602489 prefixEnd_1602489 := by exact prefixLift 1602489
  have htrace : WordTrace (prefixWord ++ tailWord_1602489) baseStart_1602489 baseEnd_1602489 := by
    simpa [prefixWord, tailWord_1602489, baseEnd_1602489] using wordTrace_append hprefix tailTrace_1602489
  have hstable : (prefixWord ++ tailWord_1602489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602489).length < 2 ^ (prefixWord ++ tailWord_1602489).sum := by decide
  have hdescent : baseEnd_1602489 < baseStart_1602489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602529 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1602529 : Nat := 118140960795 + 1602529 * 2 ^ 59
def prefixEnd_1602529 : Nat := 4983230072969 + 3 ^ 40 * 1602529 * 2
def baseEnd_1602529 : Nat := 822867639769065831617609

theorem tailTrace_1602529 : CollatzResearch.WordTrace tailWord_1602529 prefixEnd_1602529 822867639769065831617609 := by
  unfold tailWord_1602529
  simp only [CollatzResearch.WordTrace]
  refine ⟨58449034411318598008722641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38966022940879065339148427 58449034411318598008722641)
  ·
    refine ⟨43836775808488948506541981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58449034411318598008722641 43836775808488948506541981)
    ·
      refine ⟨16438790928183355689953243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43836775808488948506541981 16438790928183355689953243)
      ·
        refine ⟨24658186392275033534929865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16438790928183355689953243 24658186392275033534929865)
        ·
          refine ⟨18493639794206275151197399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24658186392275033534929865 18493639794206275151197399)
          ·
            refine ⟨27740459691309412726796099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18493639794206275151197399 27740459691309412726796099)
            ·
              refine ⟨41610689536964119090194149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27740459691309412726796099 41610689536964119090194149)
              ·
                refine ⟨7802004288180772329411403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41610689536964119090194149 7802004288180772329411403)
                ·
                  refine ⟨11703006432271158494117105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7802004288180772329411403 11703006432271158494117105)
                  ·
                    refine ⟨8777254824203368870587829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11703006432271158494117105 8777254824203368870587829)
                    ·
                      refine ⟨822867639769065831617609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8777254824203368870587829 822867639769065831617609)
                      ·
                        rfl

theorem cell23_1602529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1602529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602529 prefixEnd_1602529 := by exact prefixLift 1602529
  have htrace : WordTrace (prefixWord ++ tailWord_1602529) baseStart_1602529 baseEnd_1602529 := by
    simpa [prefixWord, tailWord_1602529, baseEnd_1602529] using wordTrace_append hprefix tailTrace_1602529
  have hstable : (prefixWord ++ tailWord_1602529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602529).length < 2 ^ (prefixWord ++ tailWord_1602529).sum := by decide
  have hdescent : baseEnd_1602529 < baseStart_1602529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602569 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_1602569 : Nat := 118140960795 + 1602569 * 2 ^ 59
def prefixEnd_1602569 : Nat := 4983230072969 + 3 ^ 40 * 1602569 * 2
def baseEnd_1602569 : Nat := 822888178995245675117425

theorem tailTrace_1602569 : CollatzResearch.WordTrace tailWord_1602569 prefixEnd_1602569 822888178995245675117425 := by
  unfold tailWord_1602569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58450493331173684840178761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38966995554115789893452507 58450493331173684840178761)
  ·
    refine ⟨43837869998380263630134071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58450493331173684840178761 43837869998380263630134071)
    ·
      refine ⟨65756804997570395445201107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43837869998380263630134071 65756804997570395445201107)
      ·
        refine ⟨98635207496355593167801661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65756804997570395445201107 98635207496355593167801661)
        ·
          refine ⟨36988202811133347437925623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98635207496355593167801661 36988202811133347437925623)
          ·
            refine ⟨55482304216700021156888435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36988202811133347437925623 55482304216700021156888435)
            ·
              refine ⟨83223456325050031735332653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55482304216700021156888435 83223456325050031735332653)
              ·
                refine ⟨31208796121893761900749745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83223456325050031735332653 31208796121893761900749745)
                ·
                  refine ⟨23406597091420321425562309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31208796121893761900749745 23406597091420321425562309)
                  ·
                    refine ⟨4388736954641310267292933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23406597091420321425562309 4388736954641310267292933)
                    ·
                      refine ⟨822888178995245675117425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4388736954641310267292933 822888178995245675117425)
                      ·
                        rfl

theorem cell23_1602569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_1602569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602569 prefixEnd_1602569 := by exact prefixLift 1602569
  have htrace : WordTrace (prefixWord ++ tailWord_1602569) baseStart_1602569 baseEnd_1602569 := by
    simpa [prefixWord, tailWord_1602569, baseEnd_1602569] using wordTrace_append hprefix tailTrace_1602569
  have hstable : (prefixWord ++ tailWord_1602569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602569).length < 2 ^ (prefixWord ++ tailWord_1602569).sum := by decide
  have hdescent : baseEnd_1602569 < baseStart_1602569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602593 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1602593 : Nat := 118140960795 + 1602593 * 2 ^ 59
def prefixEnd_1602593 : Nat := 4983230072969 + 3 ^ 40 * 1602593 * 2
def baseEnd_1602593 : Nat := 822900502530953581217315

theorem tailTrace_1602593 : CollatzResearch.WordTrace tailWord_1602593 prefixEnd_1602593 822900502530953581217315 := by
  unfold tailWord_1602593
  simp only [CollatzResearch.WordTrace]
  refine ⟨58451368683086736939052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38967579122057824626034955 58451368683086736939052433)
  ·
    refine ⟨43838526512315052704289325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58451368683086736939052433 43838526512315052704289325)
    ·
      refine ⟨16439447442118144764108497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43838526512315052704289325 16439447442118144764108497)
      ·
        refine ⟨12329585581588608573081373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16439447442118144764108497 12329585581588608573081373)
        ·
          refine ⟨4623594593095728214905515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12329585581588608573081373 4623594593095728214905515)
          ·
            refine ⟨6935391889643592322358273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623594593095728214905515 6935391889643592322358273)
            ·
              refine ⟨5201543917232694241768705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935391889643592322358273 5201543917232694241768705)
              ·
                refine ⟨3901157937924520681326529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201543917232694241768705 3901157937924520681326529)
                ·
                  refine ⟨2925868453443390510994897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901157937924520681326529 2925868453443390510994897)
                  ·
                    refine ⟨2194401340082542883246173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2925868453443390510994897 2194401340082542883246173)
                    ·
                      refine ⟨822900502530953581217315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2194401340082542883246173 822900502530953581217315)
                      ·
                        rfl

theorem cell23_1602593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1602593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602593 prefixEnd_1602593 := by exact prefixLift 1602593
  have htrace : WordTrace (prefixWord ++ tailWord_1602593) baseStart_1602593 baseEnd_1602593 := by
    simpa [prefixWord, tailWord_1602593, baseEnd_1602593] using wordTrace_append hprefix tailTrace_1602593
  have hstable : (prefixWord ++ tailWord_1602593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602593).length < 2 ^ (prefixWord ++ tailWord_1602593).sum := by decide
  have hdescent : baseEnd_1602593 < baseStart_1602593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602633 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 2, 3, 2]
def baseStart_1602633 : Nat := 118140960795 + 1602633 * 2 ^ 59
def prefixEnd_1602633 : Nat := 4983230072969 + 3 ^ 40 * 1602633 * 2
def baseEnd_1602633 : Nat := 822921041757133424717131

theorem tailTrace_1602633 : CollatzResearch.WordTrace tailWord_1602633 prefixEnd_1602633 822921041757133424717131 := by
  unfold tailWord_1602633
  simp only [CollatzResearch.WordTrace]
  refine ⟨58452827602941823770508553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38968551735294549180339035 58452827602941823770508553)
  ·
    refine ⟨43839620702206367827881415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58452827602941823770508553 43839620702206367827881415)
    ·
      refine ⟨65759431053309551741822123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43839620702206367827881415 65759431053309551741822123)
      ·
        refine ⟨98639146579964327612733185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65759431053309551741822123 98639146579964327612733185)
        ·
          refine ⟨73979359934973245709549889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98639146579964327612733185 73979359934973245709549889)
          ·
            refine ⟨55484519951229934282162417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73979359934973245709549889 55484519951229934282162417)
            ·
              refine ⟨41613389963422450711621813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55484519951229934282162417 41613389963422450711621813)
              ·
                refine ⟨3901255309070854754214545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41613389963422450711621813 3901255309070854754214545)
                ·
                  refine ⟨2925941481803141065660909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901255309070854754214545 2925941481803141065660909)
                  ·
                    refine ⟨1097228055676177899622841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925941481803141065660909 1097228055676177899622841)
                    ·
                      refine ⟨822921041757133424717131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097228055676177899622841 822921041757133424717131)
                      ·
                        rfl

theorem cell23_1602633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3, 2].length) (baseStart_1602633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602633 prefixEnd_1602633 := by exact prefixLift 1602633
  have htrace : WordTrace (prefixWord ++ tailWord_1602633) baseStart_1602633 baseEnd_1602633 := by
    simpa [prefixWord, tailWord_1602633, baseEnd_1602633] using wordTrace_append hprefix tailTrace_1602633
  have hstable : (prefixWord ++ tailWord_1602633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602633).length < 2 ^ (prefixWord ++ tailWord_1602633).sum := by decide
  have hdescent : baseEnd_1602633 < baseStart_1602633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602677 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1602677 : Nat := 118140960795 + 1602677 * 2 ^ 59
def prefixEnd_1602677 : Nat := 4983230072969 + 3 ^ 40 * 1602677 * 2
def baseEnd_1602677 : Nat := 274314544968643750855643

theorem tailTrace_1602677 : CollatzResearch.WordTrace tailWord_1602677 prefixEnd_1602677 274314544968643750855643 := by
  unfold tailWord_1602677
  simp only [CollatzResearch.WordTrace]
  refine ⟨58454432414782419285110285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38969621609854946190073523 58454432414782419285110285)
  ·
    refine ⟨21920412155543407231916357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58454432414782419285110285 21920412155543407231916357)
    ·
      refine ⟨4110077279164388855984317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21920412155543407231916357 4110077279164388855984317)
      ·
        refine ⟨1541278979686645820994119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4110077279164388855984317 1541278979686645820994119)
        ·
          refine ⟨2311918469529968731491179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541278979686645820994119 2311918469529968731491179)
          ·
            refine ⟨3467877704294953097236769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311918469529968731491179 3467877704294953097236769)
            ·
              refine ⟨2600908278221214822927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467877704294953097236769 2600908278221214822927577)
              ·
                refine ⟨1950681208665911117195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600908278221214822927577 1950681208665911117195683)
                ·
                  refine ⟨2926021812998866675793525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950681208665911117195683 2926021812998866675793525)
                  ·
                    refine ⟨274314544968643750855643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2926021812998866675793525 274314544968643750855643)
                    ·
                      rfl

theorem cell23_1602677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1602677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602677 prefixEnd_1602677 := by exact prefixLift 1602677
  have htrace : WordTrace (prefixWord ++ tailWord_1602677) baseStart_1602677 baseEnd_1602677 := by
    simpa [prefixWord, tailWord_1602677, baseEnd_1602677] using wordTrace_append hprefix tailTrace_1602677
  have hstable : (prefixWord ++ tailWord_1602677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602677).length < 2 ^ (prefixWord ++ tailWord_1602677).sum := by decide
  have hdescent : baseEnd_1602677 < baseStart_1602677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602680 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_1602680 : Nat := 118140960795 + 1602680 * 2 ^ 59
def prefixEnd_1602680 : Nat := 4983230072969 + 3 ^ 40 * 1602680 * 2
def baseEnd_1602680 : Nat := 822945175347894740829415

theorem tailTrace_1602680 : CollatzResearch.WordTrace tailWord_1602680 prefixEnd_1602680 822945175347894740829415 := by
  unfold tailWord_1602680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29227270916885775398734747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38969694555847700531646329 29227270916885775398734747)
  ·
    refine ⟨43840906375328663098102121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29227270916885775398734747 43840906375328663098102121)
    ·
      refine ⟨32880679781496497323576591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43840906375328663098102121 32880679781496497323576591)
      ·
        refine ⟨49321019672244745985364887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32880679781496497323576591 49321019672244745985364887)
        ·
          refine ⟨73981529508367118978047331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49321019672244745985364887 73981529508367118978047331)
          ·
            refine ⟨110972294262550678467070997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73981529508367118978047331 110972294262550678467070997)
            ·
              refine ⟨5201826293557063053143953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110972294262550678467070997 5201826293557063053143953)
              ·
                refine ⟨3901369720167797289857965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201826293557063053143953 3901369720167797289857965)
                ·
                  refine ⟨1463013645062923983696737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3901369720167797289857965 1463013645062923983696737)
                  ·
                    refine ⟨1097260233797192987772553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463013645062923983696737 1097260233797192987772553)
                    ·
                      refine ⟨822945175347894740829415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097260233797192987772553 822945175347894740829415)
                      ·
                        rfl

theorem cell23_1602680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_1602680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602680 prefixEnd_1602680 := by exact prefixLift 1602680
  have htrace : WordTrace (prefixWord ++ tailWord_1602680) baseStart_1602680 baseEnd_1602680 := by
    simpa [prefixWord, tailWord_1602680, baseEnd_1602680] using wordTrace_append hprefix tailTrace_1602680
  have hstable : (prefixWord ++ tailWord_1602680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602680).length < 2 ^ (prefixWord ++ tailWord_1602680).sum := by decide
  have hdescent : baseEnd_1602680 < baseStart_1602680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602714 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1602714 : Nat := 118140960795 + 1602714 * 2 ^ 59
def prefixEnd_1602714 : Nat := 4983230072969 + 3 ^ 40 * 1602714 * 2
def baseEnd_1602714 : Nat := 822962633690147607804259

theorem tailTrace_1602714 : CollatzResearch.WordTrace tailWord_1602714 prefixEnd_1602714 822962633690147607804259 := by
  unfold tailWord_1602714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613945478912093651051799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38970521277098916402804797 14613945478912093651051799)
  ·
    refine ⟨21920918218368140476577699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14613945478912093651051799 21920918218368140476577699)
    ·
      refine ⟨32881377327552210714866549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21920918218368140476577699 32881377327552210714866549)
      ·
        refine ⟨3082629124458019754518739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32881377327552210714866549 3082629124458019754518739)
        ·
          refine ⟨4623943686687029631778109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082629124458019754518739 4623943686687029631778109)
          ·
            refine ⟨1733978882507636111916791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4623943686687029631778109 1733978882507636111916791)
            ·
              refine ⟨2600968323761454167875187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733978882507636111916791 2600968323761454167875187)
              ·
                refine ⟨3901452485642181251812781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600968323761454167875187 3901452485642181251812781)
                ·
                  refine ⟨1463044682115817969429793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3901452485642181251812781 1463044682115817969429793)
                  ·
                    refine ⟨1097283511586863477072345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463044682115817969429793 1097283511586863477072345)
                    ·
                      refine ⟨822962633690147607804259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097283511586863477072345 822962633690147607804259)
                      ·
                        rfl

theorem cell23_1602714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1602714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602714 prefixEnd_1602714 := by exact prefixLift 1602714
  have htrace : WordTrace (prefixWord ++ tailWord_1602714) baseStart_1602714 baseEnd_1602714 := by
    simpa [prefixWord, tailWord_1602714, baseEnd_1602714] using wordTrace_append hprefix tailTrace_1602714
  have hstable : (prefixWord ++ tailWord_1602714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602714).length < 2 ^ (prefixWord ++ tailWord_1602714).sum := by decide
  have hdescent : baseEnd_1602714 < baseStart_1602714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602736 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_1602736 : Nat := 118140960795 + 1602736 * 2 ^ 59
def prefixEnd_1602736 : Nat := 4983230072969 + 3 ^ 40 * 1602736 * 2
def baseEnd_1602736 : Nat := 822973930264546521729157

theorem tailTrace_1602736 : CollatzResearch.WordTrace tailWord_1602736 prefixEnd_1602736 822973930264546521729157 := by
  unfold tailWord_1602736
  simp only [CollatzResearch.WordTrace]
  refine ⟨29228292160784336180754031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38971056214379114907672041 29228292160784336180754031)
  ·
    refine ⟨43842438241176504271131047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29228292160784336180754031 43842438241176504271131047)
    ·
      refine ⟨65763657361764756406696571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43842438241176504271131047 65763657361764756406696571)
      ·
        refine ⟨98645486042647134610044857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65763657361764756406696571 98645486042647134610044857)
        ·
          refine ⟨73984114531985350957533643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98645486042647134610044857 73984114531985350957533643)
          ·
            refine ⟨110976171797978026436300465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73984114531985350957533643 110976171797978026436300465)
            ·
              refine ⟨83232128848483519827225349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110976171797978026436300465 83232128848483519827225349)
              ·
                refine ⟨15606024159090659967604753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83232128848483519827225349 15606024159090659967604753)
                ·
                  refine ⟨11704518119317994975703565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15606024159090659967604753 11704518119317994975703565)
                  ·
                    refine ⟨4389194294744248115888837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11704518119317994975703565 4389194294744248115888837)
                    ·
                      refine ⟨822973930264546521729157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4389194294744248115888837 822973930264546521729157)
                      ·
                        rfl

theorem cell23_1602736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_1602736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602736 prefixEnd_1602736 := by exact prefixLift 1602736
  have htrace : WordTrace (prefixWord ++ tailWord_1602736) baseStart_1602736 baseEnd_1602736 := by
    simpa [prefixWord, tailWord_1602736, baseEnd_1602736] using wordTrace_append hprefix tailTrace_1602736
  have hstable : (prefixWord ++ tailWord_1602736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602736).length < 2 ^ (prefixWord ++ tailWord_1602736).sum := by decide
  have hdescent : baseEnd_1602736 < baseStart_1602736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602746 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_1602746 : Nat := 118140960795 + 1602746 * 2 ^ 59
def prefixEnd_1602746 : Nat := 4983230072969 + 3 ^ 40 * 1602746 * 2
def baseEnd_1602746 : Nat := 274326355023697160868037

theorem tailTrace_1602746 : CollatzResearch.WordTrace tailWord_1602746 prefixEnd_1602746 274326355023697160868037 := by
  unfold tailWord_1602746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614237262883111017343023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38971299367688296046248061 14614237262883111017343023)
  ·
    refine ⟨21921355894324666526014535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14614237262883111017343023 21921355894324666526014535)
    ·
      refine ⟨32882033841486999789021803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21921355894324666526014535 32882033841486999789021803)
      ·
        refine ⟨49323050762230499683532705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32882033841486999789021803 49323050762230499683532705)
        ·
          refine ⟨36992288071672874762649529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49323050762230499683532705 36992288071672874762649529)
          ·
            refine ⟨27744216053754656071987147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36992288071672874762649529 27744216053754656071987147)
            ·
              refine ⟨41616324080631984107980721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27744216053754656071987147 41616324080631984107980721)
              ·
                refine ⟨31212243060473988080985541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41616324080631984107980721 31212243060473988080985541)
                ·
                  refine ⟨5852295573838872765184789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31212243060473988080985541 5852295573838872765184789)
                  ·
                    refine ⟨274326355023697160868037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5852295573838872765184789 274326355023697160868037)
                    ·
                      rfl

theorem cell23_1602746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_1602746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602746 prefixEnd_1602746 := by exact prefixLift 1602746
  have htrace : WordTrace (prefixWord ++ tailWord_1602746) baseStart_1602746 baseEnd_1602746 := by
    simpa [prefixWord, tailWord_1602746, baseEnd_1602746] using wordTrace_append hprefix tailTrace_1602746
  have hstable : (prefixWord ++ tailWord_1602746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602746).length < 2 ^ (prefixWord ++ tailWord_1602746).sum := by decide
  have hdescent : baseEnd_1602746 < baseStart_1602746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602770 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1602770 : Nat := 118140960795 + 1602770 * 2 ^ 59
def prefixEnd_1602770 : Nat := 4983230072969 + 3 ^ 40 * 1602770 * 2
def baseEnd_1602770 : Nat := 822991388606799388704001

theorem tailTrace_1602770 : CollatzResearch.WordTrace tailWord_1602770 prefixEnd_1602770 822991388606799388704001 := by
  unfold tailWord_1602770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614456100861374042061441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38971882935630330778830509 14614456100861374042061441)
  ·
    refine ⟨10960842075646030531546081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14614456100861374042061441 10960842075646030531546081)
    ·
      refine ⟨8220631556734522898659561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10960842075646030531546081 8220631556734522898659561)
      ·
        refine ⟨6165473667550892173994671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8220631556734522898659561 6165473667550892173994671)
        ·
          refine ⟨9248210501326338260992007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165473667550892173994671 9248210501326338260992007)
          ·
            refine ⟨13872315751989507391488011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248210501326338260992007 13872315751989507391488011)
            ·
              refine ⟨20808473627984261087232017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13872315751989507391488011 20808473627984261087232017)
              ·
                refine ⟨15606355220988195815424013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20808473627984261087232017 15606355220988195815424013)
                ·
                  refine ⟨5852383207870573430784005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15606355220988195815424013 5852383207870573430784005)
                  ·
                    refine ⟨1097321851475732518272001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852383207870573430784005 1097321851475732518272001)
                    ·
                      refine ⟨822991388606799388704001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097321851475732518272001 822991388606799388704001)
                      ·
                        rfl

theorem cell23_1602770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1602770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602770 prefixEnd_1602770 := by exact prefixLift 1602770
  have htrace : WordTrace (prefixWord ++ tailWord_1602770) baseStart_1602770 baseEnd_1602770 := by
    simpa [prefixWord, tailWord_1602770, baseEnd_1602770] using wordTrace_append hprefix tailTrace_1602770
  have hstable : (prefixWord ++ tailWord_1602770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602770).length < 2 ^ (prefixWord ++ tailWord_1602770).sum := by decide
  have hdescent : baseEnd_1602770 < baseStart_1602770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602810 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_1602810 : Nat := 118140960795 + 1602810 * 2 ^ 59
def prefixEnd_1602810 : Nat := 4983230072969 + 3 ^ 40 * 1602810 * 2
def baseEnd_1602810 : Nat := 91445769759219914689313

theorem tailTrace_1602810 : CollatzResearch.WordTrace tailWord_1602810 prefixEnd_1602810 91445769759219914689313 := by
  unfold tailWord_1602810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614820830825145749925471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38972855548867055333134589 14614820830825145749925471)
  ·
    refine ⟨21922231246237718624888207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14614820830825145749925471 21922231246237718624888207)
    ·
      refine ⟨32883346869356577937332311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21922231246237718624888207 32883346869356577937332311)
      ·
        refine ⟨49325020304034866905998467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32883346869356577937332311 49325020304034866905998467)
        ·
          refine ⟨73987530456052300358997701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49325020304034866905998467 73987530456052300358997701)
          ·
            refine ⟨13872661960509806317312069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73987530456052300358997701 13872661960509806317312069)
            ·
              refine ⟨2601124117595588684496013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13872661960509806317312069 2601124117595588684496013)
              ·
                refine ⟨975421544098345756686005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2601124117595588684496013 975421544098345756686005)
                ·
                  refine ⟨91445769759219914689313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975421544098345756686005 91445769759219914689313)
                  ·
                    rfl

theorem cell23_1602810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_1602810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602810 prefixEnd_1602810 := by exact prefixLift 1602810
  have htrace : WordTrace (prefixWord ++ tailWord_1602810) baseStart_1602810 baseEnd_1602810 := by
    simpa [prefixWord, tailWord_1602810, baseEnd_1602810] using wordTrace_append hprefix tailTrace_1602810
  have hstable : (prefixWord ++ tailWord_1602810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602810).length < 2 ^ (prefixWord ++ tailWord_1602810).sum := by decide
  have hdescent : baseEnd_1602810 < baseStart_1602810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602820 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1602820 : Nat := 118140960795 + 1602820 * 2 ^ 59
def prefixEnd_1602820 : Nat := 4983230072969 + 3 ^ 40 * 1602820 * 2
def baseEnd_1602820 : Nat := 823017062639524193078771

theorem tailTrace_1602820 : CollatzResearch.WordTrace tailWord_1602820 prefixEnd_1602820 823017062639524193078771 := by
  unfold tailWord_1602820
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229824026632177353782957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38973098702176236471710609 29229824026632177353782957)
  ·
    refine ⟨10961184009987066507668609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29229824026632177353782957 10961184009987066507668609)
    ·
      refine ⟨8220888007490299880751457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10961184009987066507668609 8220888007490299880751457)
      ·
        refine ⟨6165666005617724910563593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8220888007490299880751457 6165666005617724910563593)
        ·
          refine ⟨4624249504213293682922695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165666005617724910563593 4624249504213293682922695)
          ·
            refine ⟨6936374256319940524384043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624249504213293682922695 6936374256319940524384043)
            ·
              refine ⟨10404561384479910786576065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936374256319940524384043 10404561384479910786576065)
              ·
                refine ⟨7803421038359933089932049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404561384479910786576065 7803421038359933089932049)
                ·
                  refine ⟨5852565778769949817449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803421038359933089932049 5852565778769949817449037)
                  ·
                    refine ⟨2194712167038731181543389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5852565778769949817449037 2194712167038731181543389)
                    ·
                      refine ⟨823017062639524193078771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2194712167038731181543389 823017062639524193078771)
                      ·
                        rfl

theorem cell23_1602820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1602820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602820 prefixEnd_1602820 := by exact prefixLift 1602820
  have htrace : WordTrace (prefixWord ++ tailWord_1602820) baseStart_1602820 baseEnd_1602820 := by
    simpa [prefixWord, tailWord_1602820, baseEnd_1602820] using wordTrace_append hprefix tailTrace_1602820
  have hstable : (prefixWord ++ tailWord_1602820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602820).length < 2 ^ (prefixWord ++ tailWord_1602820).sum := by decide
  have hdescent : baseEnd_1602820 < baseStart_1602820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602880 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_1602880 : Nat := 118140960795 + 1602880 * 2 ^ 59
def prefixEnd_1602880 : Nat := 4983230072969 + 3 ^ 40 * 1602880 * 2
def baseEnd_1602880 : Nat := 823047871478793958328495

theorem tailTrace_1602880 : CollatzResearch.WordTrace tailWord_1602880 prefixEnd_1602880 823047871478793958328495 := by
  unfold tailWord_1602880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29230918216523492477375047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38974557622031323303166729 29230918216523492477375047)
  ·
    refine ⟨43846377324785238716062571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29230918216523492477375047 43846377324785238716062571)
    ·
      refine ⟨65769565987177858074093857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43846377324785238716062571 65769565987177858074093857)
      ·
        refine ⟨49327174490383393555570393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65769565987177858074093857 49327174490383393555570393)
        ·
          refine ⟨36995380867787545166677795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49327174490383393555570393 36995380867787545166677795)
          ·
            refine ⟨55493071301681317750016693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36995380867787545166677795 55493071301681317750016693)
            ·
              refine ⟨5202475434532623539064065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55493071301681317750016693 5202475434532623539064065)
              ·
                refine ⟨3901856575899467654298049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5202475434532623539064065 3901856575899467654298049)
                ·
                  refine ⟨2926392431924600740723537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901856575899467654298049 2926392431924600740723537)
                  ·
                    refine ⟨2194794323943450555542653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926392431924600740723537 2194794323943450555542653)
                    ·
                      refine ⟨823047871478793958328495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2194794323943450555542653 823047871478793958328495)
                      ·
                        rfl

theorem cell23_1602880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_1602880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602880 prefixEnd_1602880 := by exact prefixLift 1602880
  have htrace : WordTrace (prefixWord ++ tailWord_1602880) baseStart_1602880 baseEnd_1602880 := by
    simpa [prefixWord, tailWord_1602880, baseEnd_1602880] using wordTrace_append hprefix tailTrace_1602880
  have hstable : (prefixWord ++ tailWord_1602880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602880).length < 2 ^ (prefixWord ++ tailWord_1602880).sum := by decide
  have hdescent : baseEnd_1602880 < baseStart_1602880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602883 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 6]
def baseStart_1602883 : Nat := 118140960795 + 1602883 * 2 ^ 59
def prefixEnd_1602883 : Nat := 4983230072969 + 3 ^ 40 * 1602883 * 2
def baseEnd_1602883 : Nat := 91449934657861938510109

theorem tailTrace_1602883 : CollatzResearch.WordTrace tailWord_1602883 prefixEnd_1602883 91449934657861938510109 := by
  unfold tailWord_1602883
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461945852036116467109303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38974630568024077644739535 58461945852036116467109303)
  ·
    refine ⟨87692918778054174700663955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58461945852036116467109303 87692918778054174700663955)
    ·
      refine ⟨131539378167081262050995933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87692918778054174700663955 131539378167081262050995933)
      ·
        refine ⟨49327266812655473269123475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131539378167081262050995933 49327266812655473269123475)
        ·
          refine ⟨73990900218983209903685213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49327266812655473269123475 73990900218983209903685213)
          ·
            refine ⟨27746587582118703713881955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73990900218983209903685213 27746587582118703713881955)
            ·
              refine ⟨41619881373178055570822933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27746587582118703713881955 41619881373178055570822933)
              ·
                refine ⟨1950931939367721354882325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41619881373178055570822933 1950931939367721354882325)
                ·
                  refine ⟨91449934657861938510109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1950931939367721354882325 91449934657861938510109)
                  ·
                    rfl

theorem cell23_1602883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 6].length) (baseStart_1602883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602883 prefixEnd_1602883 := by exact prefixLift 1602883
  have htrace : WordTrace (prefixWord ++ tailWord_1602883) baseStart_1602883 baseEnd_1602883 := by
    simpa [prefixWord, tailWord_1602883, baseEnd_1602883] using wordTrace_append hprefix tailTrace_1602883
  have hstable : (prefixWord ++ tailWord_1602883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602883).length < 2 ^ (prefixWord ++ tailWord_1602883).sum := by decide
  have hdescent : baseEnd_1602883 < baseStart_1602883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602887 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1602887 : Nat := 118140960795 + 1602887 * 2 ^ 59
def prefixEnd_1602887 : Nat := 4983230072969 + 3 ^ 40 * 1602887 * 2
def baseEnd_1602887 : Nat := 274350488614458476980321

theorem tailTrace_1602887 : CollatzResearch.WordTrace tailWord_1602887 prefixEnd_1602887 274350488614458476980321 := by
  unfold tailWord_1602887
  simp only [CollatzResearch.WordTrace]
  refine ⟨58462091744021625150254915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38974727829347750100169943 58462091744021625150254915)
  ·
    refine ⟨87693137616032437725382373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58462091744021625150254915 87693137616032437725382373)
    ·
      refine ⟨16442463303006082073509195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87693137616032437725382373 16442463303006082073509195)
      ·
        refine ⟨24663694954509123110263793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16442463303006082073509195 24663694954509123110263793)
        ·
          refine ⟨18497771215881842332697845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24663694954509123110263793 18497771215881842332697845)
          ·
            refine ⟨1734166051488922718690423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18497771215881842332697845 1734166051488922718690423)
            ·
              refine ⟨2601249077233384078035635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734166051488922718690423 2601249077233384078035635)
              ·
                refine ⟨3901873615850076117053453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601249077233384078035635 3901873615850076117053453)
                ·
                  refine ⟨1463202605943778543895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3901873615850076117053453 1463202605943778543895045)
                  ·
                    refine ⟨274350488614458476980321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463202605943778543895045 274350488614458476980321)
                    ·
                      rfl

theorem cell23_1602887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1602887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602887 prefixEnd_1602887 := by exact prefixLift 1602887
  have htrace : WordTrace (prefixWord ++ tailWord_1602887) baseStart_1602887 baseEnd_1602887 := by
    simpa [prefixWord, tailWord_1602887, baseEnd_1602887] using wordTrace_append hprefix tailTrace_1602887
  have hstable : (prefixWord ++ tailWord_1602887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602887).length < 2 ^ (prefixWord ++ tailWord_1602887).sum := by decide
  have hdescent : baseEnd_1602887 < baseStart_1602887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602900 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1602900 : Nat := 118140960795 + 1602900 * 2 ^ 59
def prefixEnd_1602900 : Nat := 4983230072969 + 3 ^ 40 * 1602900 * 2
def baseEnd_1602900 : Nat := 91450904565764875564267

theorem tailTrace_1602900 : CollatzResearch.WordTrace tailWord_1602900 prefixEnd_1602900 91450904565764875564267 := by
  unfold tailWord_1602900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29231282946487264185239077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38975043928649685580318769 29231282946487264185239077)
  ·
    refine ⟨5480865552466362034732327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29231282946487264185239077 5480865552466362034732327)
    ·
      refine ⟨8221298328699543052098491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5480865552466362034732327 8221298328699543052098491)
      ·
        refine ⟨12331947493049314578147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221298328699543052098491 12331947493049314578147737)
        ·
          refine ⟨9248960619786985933610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12331947493049314578147737 9248960619786985933610803)
          ·
            refine ⟨13873440929680478900416205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248960619786985933610803 13873440929680478900416205)
            ·
              refine ⟨5202540348630179587656077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13873440929680478900416205 5202540348630179587656077)
              ·
                refine ⟨1950952630736317345371029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5202540348630179587656077 1950952630736317345371029)
                ·
                  refine ⟨91450904565764875564267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1950952630736317345371029 91450904565764875564267)
                  ·
                    rfl

theorem cell23_1602900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1602900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602900 prefixEnd_1602900 := by exact prefixLift 1602900
  have htrace : WordTrace (prefixWord ++ tailWord_1602900) baseStart_1602900 baseEnd_1602900 := by
    simpa [prefixWord, tailWord_1602900, baseEnd_1602900] using wordTrace_append hprefix tailTrace_1602900
  have hstable : (prefixWord ++ tailWord_1602900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602900).length < 2 ^ (prefixWord ++ tailWord_1602900).sum := by decide
  have hdescent : baseEnd_1602900 < baseStart_1602900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602937 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 2, 3, 2]
def baseStart_1602937 : Nat := 118140960795 + 1602937 * 2 ^ 59
def prefixEnd_1602937 : Nat := 4983230072969 + 3 ^ 40 * 1602937 * 2
def baseEnd_1602937 : Nat := 823077139876100235315733

theorem tailTrace_1602937 : CollatzResearch.WordTrace tailWord_1602937 prefixEnd_1602937 823077139876100235315733 := by
  unfold tailWord_1602937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58463915393840483689575065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38975943595893655793050043 58463915393840483689575065)
  ·
    refine ⟨43847936545380362767181299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58463915393840483689575065 43847936545380362767181299)
    ·
      refine ⟨65771904818070544150771949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43847936545380362767181299 65771904818070544150771949)
      ·
        refine ⟨24664464306776454056539481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65771904818070544150771949 24664464306776454056539481)
        ·
          refine ⟨18498348230082340542404611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24664464306776454056539481 18498348230082340542404611)
          ·
            refine ⟨27747522345123510813606917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18498348230082340542404611 27747522345123510813606917)
            ·
              refine ⟨5202660439710658277551297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27747522345123510813606917 5202660439710658277551297)
              ·
                refine ⟨3901995329782993708163473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5202660439710658277551297 3901995329782993708163473)
                ·
                  refine ⟨2926496497337245281122605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901995329782993708163473 2926496497337245281122605)
                  ·
                    refine ⟨1097436186501466980420977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926496497337245281122605 1097436186501466980420977)
                    ·
                      refine ⟨823077139876100235315733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097436186501466980420977 823077139876100235315733)
                      ·
                        rfl

theorem cell23_1602937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_1602937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1602937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1602937 prefixEnd_1602937 := by exact prefixLift 1602937
  have htrace : WordTrace (prefixWord ++ tailWord_1602937) baseStart_1602937 baseEnd_1602937 := by
    simpa [prefixWord, tailWord_1602937, baseEnd_1602937] using wordTrace_append hprefix tailTrace_1602937
  have hstable : (prefixWord ++ tailWord_1602937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602937).length < 2 ^ (prefixWord ++ tailWord_1602937).sum := by decide
  have hdescent : baseEnd_1602937 < baseStart_1602937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603000 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1603000 : Nat := 118140960795 + 1603000 * 2 ^ 59
def prefixEnd_1603000 : Nat := 4983230072969 + 3 ^ 40 * 1603000 * 2
def baseEnd_1603000 : Nat := 823109489157333488827943

theorem tailTrace_1603000 : CollatzResearch.WordTrace tailWord_1603000 prefixEnd_1603000 823109489157333488827943 := by
  unfold tailWord_1603000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233106596306122724559227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38977475461741496966078969 29233106596306122724559227)
  ·
    refine ⟨43849659894459184086838841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29233106596306122724559227 43849659894459184086838841)
    ·
      refine ⟨32887244920844388065129131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43849659894459184086838841 32887244920844388065129131)
      ·
        refine ⟨49330867381266582097693697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32887244920844388065129131 49330867381266582097693697)
        ·
          refine ⟨36998150535949936573270273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49330867381266582097693697 36998150535949936573270273)
          ·
            refine ⟨27748612901962452429952705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36998150535949936573270273 27748612901962452429952705)
            ·
              refine ⟨20811459676471839322464529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748612901962452429952705 20811459676471839322464529)
              ·
                refine ⟨15608594757353879491848397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811459676471839322464529 15608594757353879491848397)
                ·
                  refine ⟨5853223034007704809443149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15608594757353879491848397 5853223034007704809443149)
                  ·
                    refine ⟨2194958637752889303541181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5853223034007704809443149 2194958637752889303541181)
                    ·
                      refine ⟨823109489157333488827943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2194958637752889303541181 823109489157333488827943)
                      ·
                        rfl

theorem cell23_1603000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1603000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603000 prefixEnd_1603000 := by exact prefixLift 1603000
  have htrace : WordTrace (prefixWord ++ tailWord_1603000) baseStart_1603000 baseEnd_1603000 := by
    simpa [prefixWord, tailWord_1603000, baseEnd_1603000] using wordTrace_append hprefix tailTrace_1603000
  have hstable : (prefixWord ++ tailWord_1603000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603000).length < 2 ^ (prefixWord ++ tailWord_1603000).sum := by decide
  have hdescent : baseEnd_1603000 < baseStart_1603000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603001 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1603001 : Nat := 118140960795 + 1603001 * 2 ^ 59
def prefixEnd_1603001 : Nat := 4983230072969 + 3 ^ 40 * 1603001 * 2
def baseEnd_1603001 : Nat := 823110002637987984915439

theorem tailTrace_1603001 : CollatzResearch.WordTrace tailWord_1603001 prefixEnd_1603001 823110002637987984915439 := by
  unfold tailWord_1603001
  simp only [CollatzResearch.WordTrace]
  refine ⟨58466249665608622619904857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38977499777072415079936571 58466249665608622619904857)
  ·
    refine ⟨43849687249206466964928643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58466249665608622619904857 43849687249206466964928643)
    ·
      refine ⟨65774530873809700447392965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43849687249206466964928643 65774530873809700447392965)
      ·
        refine ⟨12332724538839318833886181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65774530873809700447392965 12332724538839318833886181)
        ·
          refine ⟨2312385851032372281353659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12332724538839318833886181 2312385851032372281353659)
          ·
            refine ⟨3468578776548558422030489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312385851032372281353659 3468578776548558422030489)
            ·
              refine ⟨2601434082411418816522867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468578776548558422030489 2601434082411418816522867)
              ·
                refine ⟨3902151123617128224784301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601434082411418816522867 3902151123617128224784301)
                ·
                  refine ⟨1463306671356423084294113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3902151123617128224784301 1463306671356423084294113)
                  ·
                    refine ⟨1097480003517317313220585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463306671356423084294113 1097480003517317313220585)
                    ·
                      refine ⟨823110002637987984915439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097480003517317313220585 823110002637987984915439)
                      ·
                        rfl

theorem cell23_1603001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1603001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603001 prefixEnd_1603001 := by exact prefixLift 1603001
  have htrace : WordTrace (prefixWord ++ tailWord_1603001) baseStart_1603001 baseEnd_1603001 := by
    simpa [prefixWord, tailWord_1603001, baseEnd_1603001] using wordTrace_append hprefix tailTrace_1603001
  have hstable : (prefixWord ++ tailWord_1603001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603001).length < 2 ^ (prefixWord ++ tailWord_1603001).sum := by decide
  have hdescent : baseEnd_1603001 < baseStart_1603001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603080 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 7]
def baseStart_1603080 : Nat := 118140960795 + 1603080 * 2 ^ 59
def prefixEnd_1603080 : Nat := 4983230072969 + 3 ^ 40 * 1603080 * 2
def baseEnd_1603080 : Nat := 91461174178854797314175

theorem tailTrace_1603080 : CollatzResearch.WordTrace tailWord_1603080 prefixEnd_1603080 91461174178854797314175 := by
  unfold tailWord_1603080
  simp only [CollatzResearch.WordTrace]
  refine ⟨29234565516161209556015347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38979420688214946074687129 29234565516161209556015347)
  ·
    refine ⟨43851848274241814334023021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29234565516161209556015347 43851848274241814334023021)
    ·
      refine ⟨16444443102840680375258633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43851848274241814334023021 16444443102840680375258633)
      ·
        refine ⟨12333332327130510281443975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16444443102840680375258633 12333332327130510281443975)
        ·
          refine ⟨18499998490695765422165963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12333332327130510281443975 18499998490695765422165963)
          ·
            refine ⟨27749997736043648133248945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18499998490695765422165963 27749997736043648133248945)
            ·
              refine ⟨20812498302032736099936709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27749997736043648133248945 20812498302032736099936709)
              ·
                refine ⟨3902343431631138018738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20812498302032736099936709 3902343431631138018738133)
                ·
                  refine ⟨91461174178854797314175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3902343431631138018738133 91461174178854797314175)
                  ·
                    rfl

theorem cell23_1603080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_1603080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603080 prefixEnd_1603080 := by exact prefixLift 1603080
  have htrace : WordTrace (prefixWord ++ tailWord_1603080) baseStart_1603080 baseEnd_1603080 := by
    simpa [prefixWord, tailWord_1603080, baseEnd_1603080] using wordTrace_append hprefix tailTrace_1603080
  have hstable : (prefixWord ++ tailWord_1603080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603080).length < 2 ^ (prefixWord ++ tailWord_1603080).sum := by decide
  have hdescent : baseEnd_1603080 < baseStart_1603080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603102 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1603102 : Nat := 118140960795 + 1603102 * 2 ^ 59
def prefixEnd_1603102 : Nat := 4983230072969 + 3 ^ 40 * 1603102 * 2
def baseEnd_1603102 : Nat := 823161864184092089752475

theorem tailTrace_1603102 : CollatzResearch.WordTrace tailWord_1603102 prefixEnd_1603102 823161864184092089752475 := by
  unfold tailWord_1603102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308741679780339608666445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38979955625495144579554373 7308741679780339608666445)
  ·
    refine ⟨2740778129917627353249917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7308741679780339608666445 2740778129917627353249917)
    ·
      refine ⟨1027791798719110257468719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2740778129917627353249917 1027791798719110257468719)
      ·
        refine ⟨1541687698078665386203079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027791798719110257468719 1541687698078665386203079)
        ·
          refine ⟨2312531547117998079304619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541687698078665386203079 2312531547117998079304619)
          ·
            refine ⟨3468797320676997118956929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312531547117998079304619 3468797320676997118956929)
            ·
              refine ⟨2601597990507747839217697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468797320676997118956929 2601597990507747839217697)
              ·
                refine ⟨1951198492880810879413273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601597990507747839217697 1951198492880810879413273)
                ·
                  refine ⟨1463398869660608159559955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951198492880810879413273 1463398869660608159559955)
                  ·
                    refine ⟨2195098304490912239339933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463398869660608159559955 2195098304490912239339933)
                    ·
                      refine ⟨823161864184092089752475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195098304490912239339933 823161864184092089752475)
                      ·
                        rfl

theorem cell23_1603102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1603102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603102 prefixEnd_1603102 := by exact prefixLift 1603102
  have htrace : WordTrace (prefixWord ++ tailWord_1603102) baseStart_1603102 baseEnd_1603102 := by
    simpa [prefixWord, tailWord_1603102, baseEnd_1603102] using wordTrace_append hprefix tailTrace_1603102
  have hstable : (prefixWord ++ tailWord_1603102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603102).length < 2 ^ (prefixWord ++ tailWord_1603102).sum := by decide
  have hdescent : baseEnd_1603102 < baseStart_1603102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603114 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_1603114 : Nat := 118140960795 + 1603114 * 2 ^ 59
def prefixEnd_1603114 : Nat := 4983230072969 + 3 ^ 40 * 1603114 * 2
def baseEnd_1603114 : Nat := 91463113994660671422491

theorem tailTrace_1603114 : CollatzResearch.WordTrace tailWord_1603114 prefixEnd_1603114 91463113994660671422491 := by
  unfold tailWord_1603114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617592778549810729692099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38980247409466161945845597 14617592778549810729692099)
  ·
    refine ⟨21926389167824716094538149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14617592778549810729692099 21926389167824716094538149)
    ·
      refine ⟨4111197968967134267725903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21926389167824716094538149 4111197968967134267725903)
      ·
        refine ⟨6166796953450701401588855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111197968967134267725903 6166796953450701401588855)
        ·
          refine ⟨9250195430176052102383283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166796953450701401588855 9250195430176052102383283)
          ·
            refine ⟨13875293145264078153574925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250195430176052102383283 13875293145264078153574925)
            ·
              refine ⟨5203234929474029307590597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13875293145264078153574925 5203234929474029307590597)
              ·
                refine ⟨975606549276380495173237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5203234929474029307590597 975606549276380495173237)
                ·
                  refine ⟨91463113994660671422491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975606549276380495173237 91463113994660671422491)
                  ·
                    rfl

theorem cell23_1603114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_1603114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603114 prefixEnd_1603114 := by exact prefixLift 1603114
  have htrace : WordTrace (prefixWord ++ tailWord_1603114) baseStart_1603114 baseEnd_1603114 := by
    simpa [prefixWord, tailWord_1603114, baseEnd_1603114] using wordTrace_append hprefix tailTrace_1603114
  have hstable : (prefixWord ++ tailWord_1603114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603114).length < 2 ^ (prefixWord ++ tailWord_1603114).sum := by decide
  have hdescent : baseEnd_1603114 < baseStart_1603114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603147 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 6, 2]
def baseStart_1603147 : Nat := 118140960795 + 1603147 * 2 ^ 59
def prefixEnd_1603147 : Nat := 4983230072969 + 3 ^ 40 * 1603147 * 2
def baseEnd_1603147 : Nat := 823184970813544413689767

theorem tailTrace_1603147 : CollatzResearch.WordTrace tailWord_1603147 prefixEnd_1603147 823184970813544413689767 := by
  unfold tailWord_1603147
  simp only [CollatzResearch.WordTrace]
  refine ⟨58471574723079689554719695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38981049815386459703146463 58471574723079689554719695)
  ·
    refine ⟨87707362084619534332079543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58471574723079689554719695 87707362084619534332079543)
    ·
      refine ⟨131561043126929301498119315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87707362084619534332079543 131561043126929301498119315)
      ·
        refine ⟨197341564690393952247178973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131561043126929301498119315 197341564690393952247178973)
        ·
          refine ⟨74003086758897732092692115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197341564690393952247178973 74003086758897732092692115)
          ·
            refine ⟨111004630138346598139038173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74003086758897732092692115 111004630138346598139038173)
            ·
              refine ⟨41626736301879974302139315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111004630138346598139038173 41626736301879974302139315)
              ·
                refine ⟨62440104452819961453208973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41626736301879974302139315 62440104452819961453208973)
                ·
                  refine ⟨23415039169807485544953365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62440104452819961453208973 23415039169807485544953365)
                  ·
                    refine ⟨1097579961084725884919689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23415039169807485544953365 1097579961084725884919689)
                    ·
                      refine ⟨823184970813544413689767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097579961084725884919689 823184970813544413689767)
                      ·
                        rfl

theorem cell23_1603147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6, 2].length) (baseStart_1603147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603147 prefixEnd_1603147 := by exact prefixLift 1603147
  have htrace : WordTrace (prefixWord ++ tailWord_1603147) baseStart_1603147 baseEnd_1603147 := by
    simpa [prefixWord, tailWord_1603147, baseEnd_1603147] using wordTrace_append hprefix tailTrace_1603147
  have hstable : (prefixWord ++ tailWord_1603147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603147).length < 2 ^ (prefixWord ++ tailWord_1603147).sum := by decide
  have hdescent : baseEnd_1603147 < baseStart_1603147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603157 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1603157 : Nat := 118140960795 + 1603157 * 2 ^ 59
def prefixEnd_1603157 : Nat := 4983230072969 + 3 ^ 40 * 1603157 * 2
def baseEnd_1603157 : Nat := 274396701873363124854907

theorem tailTrace_1603157 : CollatzResearch.WordTrace tailWord_1603157 prefixEnd_1603157 274396701873363124854907 := by
  unfold tailWord_1603157
  simp only [CollatzResearch.WordTrace]
  refine ⟨58471939453043461262583725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38981292968695640841722483 58471939453043461262583725)
  ·
    refine ⟨21926977294891297973468897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58471939453043461262583725 21926977294891297973468897)
    ·
      refine ⟨16445232971168473480101673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21926977294891297973468897 16445232971168473480101673)
      ·
        refine ⟨12333924728376355110076255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16445232971168473480101673 12333924728376355110076255)
        ·
          refine ⟨18500887092564532665114383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12333924728376355110076255 18500887092564532665114383)
          ·
            refine ⟨27751330638846798997671575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18500887092564532665114383 27751330638846798997671575)
            ·
              refine ⟨41626995958270198496507363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27751330638846798997671575 41626995958270198496507363)
              ·
                refine ⟨62440493937405297744761045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41626995958270198496507363 62440493937405297744761045)
                ·
                  refine ⟨1463449076657936665892837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62440493937405297744761045 1463449076657936665892837)
                  ·
                    refine ⟨274396701873363124854907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463449076657936665892837 274396701873363124854907)
                    ·
                      rfl

theorem cell23_1603157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1603157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603157 prefixEnd_1603157 := by exact prefixLift 1603157
  have htrace : WordTrace (prefixWord ++ tailWord_1603157) baseStart_1603157 baseEnd_1603157 := by
    simpa [prefixWord, tailWord_1603157, baseEnd_1603157] using wordTrace_append hprefix tailTrace_1603157
  have hstable : (prefixWord ++ tailWord_1603157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603157).length < 2 ^ (prefixWord ++ tailWord_1603157).sum := by decide
  have hdescent : baseEnd_1603157 < baseStart_1603157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603247 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 6]
def baseStart_1603247 : Nat := 118140960795 + 1603247 * 2 ^ 59
def prefixEnd_1603247 : Nat := 4983230072969 + 3 ^ 40 * 1603247 * 2
def baseEnd_1603247 : Nat := 274412106292998007479769

theorem tailTrace_1603247 : CollatzResearch.WordTrace tailWord_1603247 prefixEnd_1603247 274412106292998007479769 := by
  unfold tailWord_1603247
  simp only [CollatzResearch.WordTrace]
  refine ⟨58475222022717406633359995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38983481348478271088906663 58475222022717406633359995)
  ·
    refine ⟨87712833034076109950039993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58475222022717406633359995 87712833034076109950039993)
    ·
      refine ⟨65784624775557082462529995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87712833034076109950039993 65784624775557082462529995)
      ·
        refine ⟨98676937163335623693794993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65784624775557082462529995 98676937163335623693794993)
        ·
          refine ⟨74007702872501717770346245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98676937163335623693794993 74007702872501717770346245)
          ·
            refine ⟨13876444288594072081939921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74007702872501717770346245 13876444288594072081939921)
            ·
              refine ⟨10407333216445554061454941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13876444288594072081939921 10407333216445554061454941)
              ·
                refine ⟨3902749956167082773045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10407333216445554061454941 3902749956167082773045603)
                ·
                  refine ⟨5854124934250624159568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902749956167082773045603 5854124934250624159568405)
                  ·
                    refine ⟨274412106292998007479769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5854124934250624159568405 274412106292998007479769)
                    ·
                      rfl

theorem cell23_1603247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_1603247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603247 prefixEnd_1603247 := by exact prefixLift 1603247
  have htrace : WordTrace (prefixWord ++ tailWord_1603247) baseStart_1603247 baseEnd_1603247 := by
    simpa [prefixWord, tailWord_1603247, baseEnd_1603247] using wordTrace_append hprefix tailTrace_1603247
  have hstable : (prefixWord ++ tailWord_1603247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603247).length < 2 ^ (prefixWord ++ tailWord_1603247).sum := by decide
  have hdescent : baseEnd_1603247 < baseStart_1603247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
