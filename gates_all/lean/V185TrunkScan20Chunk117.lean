import V185TrunkScan20Chunk116

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_711922 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_711922 : Nat := 118140960795 + 711922 * 2 ^ 59
def prefixEnd_711922 : Nat := 4983230072969 + 3 ^ 40 * 711922 * 2
def baseEnd_711922 : Nat := 324940599564683409423055

theorem tailTrace_711922 : CollatzResearch.WordTrace tailWord_711922 prefixEnd_711922 324940599564683409423055 := by
  unfold tailWord_711922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491482131708913860676505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17310619017890436961804013 6491482131708913860676505)
  ·
    refine ⟨4868611598781685395507379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6491482131708913860676505 4868611598781685395507379)
    ·
      refine ⟨7302917398172528093261069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868611598781685395507379 7302917398172528093261069)
      ·
        refine ⟨2738594024314698034972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7302917398172528093261069 2738594024314698034972901)
        ·
          refine ⟨513486379559005881557419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2738594024314698034972901 513486379559005881557419)
          ·
            refine ⟨770229569338508822336129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513486379559005881557419 770229569338508822336129)
            ·
              refine ⟨577672177003881616752097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770229569338508822336129 577672177003881616752097)
              ·
                refine ⟨433254132752911212564073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577672177003881616752097 433254132752911212564073)
                ·
                  refine ⟨324940599564683409423055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433254132752911212564073 324940599564683409423055)
                  ·
                    rfl

theorem cell20_711922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_711922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711922 prefixEnd_711922 := by exact prefixLift 711922
  have htrace : WordTrace (prefixWord ++ tailWord_711922) baseStart_711922 baseEnd_711922 := by
    simpa [prefixWord, tailWord_711922, baseEnd_711922] using wordTrace_append hprefix tailTrace_711922
  have hstable : (prefixWord ++ tailWord_711922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711922).length < 2 ^ (prefixWord ++ tailWord_711922).sum := by decide
  have hdescent : baseEnd_711922 < baseStart_711922 := by decide
  rcases family_descends (prefixWord ++ tailWord_711922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711923 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_711923 : Nat := 118140960795 + 711923 * 2 ^ 59
def prefixEnd_711923 : Nat := 4983230072969 + 3 ^ 40 * 711923 * 2
def baseEnd_711923 : Nat := 324941055991931850389717

theorem tailTrace_711923 : CollatzResearch.WordTrace tailWord_711923 prefixEnd_711923 324941055991931850389717 := by
  unfold tailWord_711923
  simp only [CollatzResearch.WordTrace]
  refine ⟨25965964999832032613492423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17310643333221355075661615 25965964999832032613492423)
  ·
    refine ⟨38948947499748048920238635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25965964999832032613492423 38948947499748048920238635)
    ·
      refine ⟨58423421249622073380357953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38948947499748048920238635 58423421249622073380357953)
      ·
        refine ⟨43817565937216555035268465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58423421249622073380357953 43817565937216555035268465)
        ·
          refine ⟨32863174452912416276451349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43817565937216555035268465 32863174452912416276451349)
          ·
            refine ⟨1540461302480269512958657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32863174452912416276451349 1540461302480269512958657)
            ·
              refine ⟨1155345976860202134718993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540461302480269512958657 1155345976860202134718993)
              ·
                refine ⟨866509482645151601039245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155345976860202134718993 866509482645151601039245)
                ·
                  refine ⟨324941055991931850389717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866509482645151601039245 324941055991931850389717)
                  ·
                    rfl

theorem cell20_711923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_711923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711923 prefixEnd_711923 := by exact prefixLift 711923
  have htrace : WordTrace (prefixWord ++ tailWord_711923) baseStart_711923 baseEnd_711923 := by
    simpa [prefixWord, tailWord_711923, baseEnd_711923] using wordTrace_append hprefix tailTrace_711923
  have hstable : (prefixWord ++ tailWord_711923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711923).length < 2 ^ (prefixWord ++ tailWord_711923).sum := by decide
  have hdescent : baseEnd_711923 < baseStart_711923 := by decide
  rcases family_descends (prefixWord ++ tailWord_711923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711937 : List Nat := [1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_711937 : Nat := 118140960795 + 711937 * 2 ^ 59
def prefixEnd_711937 : Nat := 4983230072969 + 3 ^ 40 * 711937 * 2
def baseEnd_711937 : Nat := 108315815324470007974331

theorem tailTrace_711937 : CollatzResearch.WordTrace tailWord_711937 prefixEnd_711937 108315815324470007974331 := by
  unfold tailWord_711937
  simp only [CollatzResearch.WordTrace]
  refine ⟨25966475621781313004502065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17310983747854208669668043 25966475621781313004502065)
  ·
    refine ⟨19474856716335984753376549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25966475621781313004502065 19474856716335984753376549)
    ·
      refine ⟨3651535634312997141258103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19474856716335984753376549 3651535634312997141258103)
      ·
        refine ⟨5477303451469495711887155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651535634312997141258103 5477303451469495711887155)
        ·
          refine ⟨8215955177204243567830733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477303451469495711887155 8215955177204243567830733)
          ·
            refine ⟨3080983191451591337936525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8215955177204243567830733 3080983191451591337936525)
            ·
              refine ⟨1155368696794346751726197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3080983191451591337936525 1155368696794346751726197)
              ·
                refine ⟨108315815324470007974331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155368696794346751726197 108315815324470007974331)
                ·
                  rfl

theorem cell20_711937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_711937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711937 prefixEnd_711937 := by exact prefixLift 711937
  have htrace : WordTrace (prefixWord ++ tailWord_711937) baseStart_711937 baseEnd_711937 := by
    simpa [prefixWord, tailWord_711937, baseEnd_711937] using wordTrace_append hprefix tailTrace_711937
  have hstable : (prefixWord ++ tailWord_711937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711937).length < 2 ^ (prefixWord ++ tailWord_711937).sum := by decide
  have hdescent : baseEnd_711937 < baseStart_711937 := by decide
  rcases family_descends (prefixWord ++ tailWord_711937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711978 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_711978 : Nat := 118140960795 + 711978 * 2 ^ 59
def prefixEnd_711978 : Nat := 4983230072969 + 3 ^ 40 * 711978 * 2
def baseEnd_711978 : Nat := 324966159490596103556159

theorem tailTrace_711978 : CollatzResearch.WordTrace tailWord_711978 prefixEnd_711978 324966159490596103556159 := by
  unfold tailWord_711978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491992753658194251686147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17311980676421851337829725 6491992753658194251686147)
  ·
    refine ⟨9737989130487291377529221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491992753658194251686147 9737989130487291377529221)
    ·
      refine ⟨1825872961966367133286729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9737989130487291377529221 1825872961966367133286729)
      ·
        refine ⟨1369404721474775349965047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825872961966367133286729 1369404721474775349965047)
        ·
          refine ⟨2054107082212163024947571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369404721474775349965047 2054107082212163024947571)
          ·
            refine ⟨3081160623318244537421357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054107082212163024947571 3081160623318244537421357)
            ·
              refine ⟨1155435233744341701533009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3081160623318244537421357 1155435233744341701533009)
              ·
                refine ⟨866576425308256276149757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155435233744341701533009 866576425308256276149757)
                ·
                  refine ⟨324966159490596103556159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866576425308256276149757 324966159490596103556159)
                  ·
                    rfl

theorem cell20_711978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_711978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711978 prefixEnd_711978 := by exact prefixLift 711978
  have htrace : WordTrace (prefixWord ++ tailWord_711978) baseStart_711978 baseEnd_711978 := by
    simpa [prefixWord, tailWord_711978, baseEnd_711978] using wordTrace_append hprefix tailTrace_711978
  have hstable : (prefixWord ++ tailWord_711978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711978).length < 2 ^ (prefixWord ++ tailWord_711978).sum := by decide
  have hdescent : baseEnd_711978 < baseStart_711978 := by decide
  rcases family_descends (prefixWord ++ tailWord_711978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711985 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 2]
def baseStart_711985 : Nat := 118140960795 + 711985 * 2 ^ 59
def prefixEnd_711985 : Nat := 4983230072969 + 3 ^ 40 * 711985 * 2
def baseEnd_711985 : Nat := 324969354481335190322797

theorem tailTrace_711985 : CollatzResearch.WordTrace tailWord_711985 prefixEnd_711985 324969354481335190322797 := by
  unfold tailWord_711985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968226325607417202249409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17312150883738278134832939 25968226325607417202249409)
  ·
    refine ⟨19476169744205562901687057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25968226325607417202249409 19476169744205562901687057)
    ·
      refine ⟨14607127308154172176265293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19476169744205562901687057 14607127308154172176265293)
      ·
        refine ⟨5477672740557814566099485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14607127308154172176265293 5477672740557814566099485)
        ·
          refine ⟨2054127277709180462287307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5477672740557814566099485 2054127277709180462287307)
          ·
            refine ⟨3081190916563770693430961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054127277709180462287307 3081190916563770693430961)
            ·
              refine ⟨2310893187422828020073221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081190916563770693430961 2310893187422828020073221)
              ·
                refine ⟨433292472641780253763729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2310893187422828020073221 433292472641780253763729)
                ·
                  refine ⟨324969354481335190322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433292472641780253763729 324969354481335190322797)
                  ·
                    rfl

theorem cell20_711985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_711985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711985 prefixEnd_711985 := by exact prefixLift 711985
  have htrace : WordTrace (prefixWord ++ tailWord_711985) baseStart_711985 baseEnd_711985 := by
    simpa [prefixWord, tailWord_711985, baseEnd_711985] using wordTrace_append hprefix tailTrace_711985
  have hstable : (prefixWord ++ tailWord_711985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711985).length < 2 ^ (prefixWord ++ tailWord_711985).sum := by decide
  have hdescent : baseEnd_711985 < baseStart_711985 := by decide
  rcases family_descends (prefixWord ++ tailWord_711985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712020 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_712020 : Nat := 118140960795 + 712020 * 2 ^ 59
def prefixEnd_712020 : Nat := 4983230072969 + 3 ^ 40 * 712020 * 2
def baseEnd_712020 : Nat := 324985329435030624155987

theorem tailTrace_712020 : CollatzResearch.WordTrace tailWord_712020 prefixEnd_712020 324985329435030624155987 := by
  unfold tailWord_712020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984751440240309089886757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17313001920320412119849009 12984751440240309089886757)
  ·
    refine ⟨2434640895045057954353767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12984751440240309089886757 2434640895045057954353767)
    ·
      refine ⟨3651961342567586931530651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434640895045057954353767 3651961342567586931530651)
      ·
        refine ⟨5477942013851380397295977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651961342567586931530651 5477942013851380397295977)
        ·
          refine ⟨4108456510388535297971983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5477942013851380397295977 4108456510388535297971983)
          ·
            refine ⟨6162684765582802946957975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108456510388535297971983 6162684765582802946957975)
            ·
              refine ⟨9244027148374204420436963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162684765582802946957975 9244027148374204420436963)
              ·
                refine ⟨13866040722561306630655445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244027148374204420436963 13866040722561306630655445)
                ·
                  refine ⟨324985329435030624155987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13866040722561306630655445 324985329435030624155987)
                  ·
                    rfl

theorem cell20_712020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_712020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712020 prefixEnd_712020 := by exact prefixLift 712020
  have htrace : WordTrace (prefixWord ++ tailWord_712020) baseStart_712020 baseEnd_712020 := by
    simpa [prefixWord, tailWord_712020, baseEnd_712020] using wordTrace_append hprefix tailTrace_712020
  have hstable : (prefixWord ++ tailWord_712020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712020).length < 2 ^ (prefixWord ++ tailWord_712020).sum := by decide
  have hdescent : baseEnd_712020 < baseStart_712020 := by decide
  rcases family_descends (prefixWord ++ tailWord_712020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712023 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 2]
def baseStart_712023 : Nat := 118140960795 + 712023 * 2 ^ 59
def prefixEnd_712023 : Nat := 4983230072969 + 3 ^ 40 * 712023 * 2
def baseEnd_712023 : Nat := 324986698716775947055975

theorem tailTrace_712023 : CollatzResearch.WordTrace tailWord_712023 prefixEnd_712023 324986698716775947055975 := by
  unfold tailWord_712023
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969612299469749692132723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17313074866313166461421815 25969612299469749692132723)
  ·
    refine ⟨38954418449204624538199085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25969612299469749692132723 38954418449204624538199085)
    ·
      refine ⟨14607906918451734201824657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38954418449204624538199085 14607906918451734201824657)
      ·
        refine ⟨10955930188838800651368493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14607906918451734201824657 10955930188838800651368493)
        ·
          refine ⟨4108473820814550244263185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10955930188838800651368493 4108473820814550244263185)
          ·
            refine ⟨3081355365610912683197389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108473820814550244263185 3081355365610912683197389)
            ·
              refine ⟨1155508262104092256199021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3081355365610912683197389 1155508262104092256199021)
              ·
                refine ⟨433315598289034596074633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1155508262104092256199021 433315598289034596074633)
                ·
                  refine ⟨324986698716775947055975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433315598289034596074633 324986698716775947055975)
                  ·
                    rfl

theorem cell20_712023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2].length) (baseStart_712023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712023 prefixEnd_712023 := by exact prefixLift 712023
  have htrace : WordTrace (prefixWord ++ tailWord_712023) baseStart_712023 baseEnd_712023 := by
    simpa [prefixWord, tailWord_712023, baseEnd_712023] using wordTrace_append hprefix tailTrace_712023
  have hstable : (prefixWord ++ tailWord_712023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712023).length < 2 ^ (prefixWord ++ tailWord_712023).sum := by decide
  have hdescent : baseEnd_712023 < baseStart_712023 := by decide
  rcases family_descends (prefixWord ++ tailWord_712023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712040 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_712040 : Nat := 118140960795 + 712040 * 2 ^ 59
def prefixEnd_712040 : Nat := 4983230072969 + 3 ^ 40 * 712040 * 2
def baseEnd_712040 : Nat := 324994457979999443489239

theorem tailTrace_712040 : CollatzResearch.WordTrace tailWord_712040 prefixEnd_712040 324994457979999443489239 := by
  unfold tailWord_712040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985116170204080797750787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17313488226938774397001049 12985116170204080797750787)
  ·
    refine ⟨19477674255306121196626181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985116170204080797750787 19477674255306121196626181)
    ·
      refine ⟨3652063922869897724367409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19477674255306121196626181 3652063922869897724367409)
      ·
        refine ⟨2739047942152423293275557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652063922869897724367409 2739047942152423293275557)
        ·
          refine ⟨513571489153579367489167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2739047942152423293275557 513571489153579367489167)
          ·
            refine ⟨770357233730369051233751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513571489153579367489167 770357233730369051233751)
            ·
              refine ⟨1155535850595553576850627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770357233730369051233751 1155535850595553576850627)
              ·
                refine ⟨1733303775893330365275941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155535850595553576850627 1733303775893330365275941)
                ·
                  refine ⟨324994457979999443489239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733303775893330365275941 324994457979999443489239)
                  ·
                    rfl

theorem cell20_712040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_712040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712040 prefixEnd_712040 := by exact prefixLift 712040
  have htrace : WordTrace (prefixWord ++ tailWord_712040) baseStart_712040 baseEnd_712040 := by
    simpa [prefixWord, tailWord_712040, baseEnd_712040] using wordTrace_append hprefix tailTrace_712040
  have hstable : (prefixWord ++ tailWord_712040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712040).length < 2 ^ (prefixWord ++ tailWord_712040).sum := by decide
  have hdescent : baseEnd_712040 < baseStart_712040 := by decide
  rcases family_descends (prefixWord ++ tailWord_712040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712044 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_712044 : Nat := 118140960795 + 712044 * 2 ^ 59
def prefixEnd_712044 : Nat := 4983230072969 + 3 ^ 40 * 712044 * 2
def baseEnd_712044 : Nat := 324996283688993207355889

theorem tailTrace_712044 : CollatzResearch.WordTrace tailWord_712044 prefixEnd_712044 324996283688993207355889 := by
  unfold tailWord_712044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985189116196835139323593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17313585488262446852431457 12985189116196835139323593)
  ·
    refine ⟨9738891837147626354492695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12985189116196835139323593 9738891837147626354492695)
    ·
      refine ⟨14608337755721439531739043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9738891837147626354492695 14608337755721439531739043)
      ·
        refine ⟨21912506633582159297608565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14608337755721439531739043 21912506633582159297608565)
        ·
          refine ⟨2054297496898327434150803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21912506633582159297608565 2054297496898327434150803)
          ·
            refine ⟨3081446245347491151226205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054297496898327434150803 3081446245347491151226205)
            ·
              refine ⟨1155542342005309181709827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3081446245347491151226205 1155542342005309181709827)
              ·
                refine ⟨1733313513007963772564741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155542342005309181709827 1733313513007963772564741)
                ·
                  refine ⟨324996283688993207355889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733313513007963772564741 324996283688993207355889)
                  ·
                    rfl

theorem cell20_712044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_712044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712044 prefixEnd_712044 := by exact prefixLift 712044
  have htrace : WordTrace (prefixWord ++ tailWord_712044) baseStart_712044 baseEnd_712044 := by
    simpa [prefixWord, tailWord_712044, baseEnd_712044] using wordTrace_append hprefix tailTrace_712044
  have hstable : (prefixWord ++ tailWord_712044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712044).length < 2 ^ (prefixWord ++ tailWord_712044).sum := by decide
  have hdescent : baseEnd_712044 < baseStart_712044 := by decide
  rcases family_descends (prefixWord ++ tailWord_712044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712058 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_712058 : Nat := 118140960795 + 712058 * 2 ^ 59
def prefixEnd_712058 : Nat := 4983230072969 + 3 ^ 40 * 712058 * 2
def baseEnd_712058 : Nat := 325002673670471380889165

theorem tailTrace_712058 : CollatzResearch.WordTrace tailWord_712058 prefixEnd_712058 325002673670471380889165 := by
  unfold tailWord_712058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492722213585737667414207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17313925902895300446437885 6492722213585737667414207)
  ·
    refine ⟨9739083320378606501121311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6492722213585737667414207 9739083320378606501121311)
    ·
      refine ⟨14608624980567909751681967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9739083320378606501121311 14608624980567909751681967)
      ·
        refine ⟨21912937470851864627522951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14608624980567909751681967 21912937470851864627522951)
        ·
          refine ⟨32869406206277796941284427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21912937470851864627522951 32869406206277796941284427)
          ·
            refine ⟨49304109309416695411926641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32869406206277796941284427 49304109309416695411926641)
            ·
              refine ⟨36978081982062521558944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49304109309416695411926641 36978081982062521558944981)
              ·
                refine ⟨866673796454590349037773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36978081982062521558944981 866673796454590349037773)
                ·
                  refine ⟨325002673670471380889165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866673796454590349037773 325002673670471380889165)
                  ·
                    rfl

theorem cell20_712058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_712058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712058 prefixEnd_712058 := by exact prefixLift 712058
  have htrace : WordTrace (prefixWord ++ tailWord_712058) baseStart_712058 baseEnd_712058 := by
    simpa [prefixWord, tailWord_712058, baseEnd_712058] using wordTrace_append hprefix tailTrace_712058
  have hstable : (prefixWord ++ tailWord_712058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712058).length < 2 ^ (prefixWord ++ tailWord_712058).sum := by decide
  have hdescent : baseEnd_712058 < baseStart_712058 := by decide
  rcases family_descends (prefixWord ++ tailWord_712058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712182 : List Nat := [5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_712182 : Nat := 118140960795 + 712182 * 2 ^ 59
def prefixEnd_712182 : Nat := 4983230072969 + 3 ^ 40 * 712182 * 2
def baseEnd_712182 : Nat := 108353090216426020251775

theorem tailTrace_712182 : CollatzResearch.WordTrace tailWord_712182 prefixEnd_712182 108353090216426020251775 := by
  unfold tailWord_712182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623463219118357490448175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17316941003929146564780533 1623463219118357490448175)
  ·
    refine ⟨2435194828677536235672263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623463219118357490448175 2435194828677536235672263)
    ·
      refine ⟨3652792243016304353508395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435194828677536235672263 3652792243016304353508395)
      ·
        refine ⟨5479188364524456530262593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652792243016304353508395 5479188364524456530262593)
        ·
          refine ⟨4109391273393342397696945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479188364524456530262593 4109391273393342397696945)
          ·
            refine ⟨3082043455045006798272709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4109391273393342397696945 3082043455045006798272709)
            ·
              refine ⟨577883147820938774676133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3082043455045006798272709 577883147820938774676133)
              ·
                refine ⟨108353090216426020251775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577883147820938774676133 108353090216426020251775)
                ·
                  rfl

theorem cell20_712182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_712182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712182 prefixEnd_712182 := by exact prefixLift 712182
  have htrace : WordTrace (prefixWord ++ tailWord_712182) baseStart_712182 baseEnd_712182 := by
    simpa [prefixWord, tailWord_712182, baseEnd_712182] using wordTrace_append hprefix tailTrace_712182
  have hstable : (prefixWord ++ tailWord_712182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712182).length < 2 ^ (prefixWord ++ tailWord_712182).sum := by decide
  have hdescent : baseEnd_712182 < baseStart_712182 := by decide
  rcases family_descends (prefixWord ++ tailWord_712182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712186 : List Nat := [3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_712186 : Nat := 118140960795 + 712186 * 2 ^ 59
def prefixEnd_712186 : Nat := 4983230072969 + 3 ^ 40 * 712186 * 2
def baseEnd_712186 : Nat := 108353698786090608207325

theorem tailTrace_712186 : CollatzResearch.WordTrace tailWord_712186 prefixEnd_712186 108353698786090608207325 := by
  unfold tailWord_712186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493889349469807132579103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17317038265252819020210941 6493889349469807132579103)
  ·
    refine ⟨9740834024204710698868655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6493889349469807132579103 9740834024204710698868655)
    ·
      refine ⟨14611251036307066048302983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9740834024204710698868655 14611251036307066048302983)
      ·
        refine ⟨21916876554460599072454475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14611251036307066048302983 21916876554460599072454475)
        ·
          refine ⟨32875314831690898608681713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21916876554460599072454475 32875314831690898608681713)
          ·
            refine ⟨24656486123768173956511285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32875314831690898608681713 24656486123768173956511285)
            ·
              refine ⟨2311545574103266308422933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24656486123768173956511285 2311545574103266308422933)
              ·
                refine ⟨108353698786090608207325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2311545574103266308422933 108353698786090608207325)
                ·
                  rfl

theorem cell20_712186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_712186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712186 prefixEnd_712186 := by exact prefixLift 712186
  have htrace : WordTrace (prefixWord ++ tailWord_712186) baseStart_712186 baseEnd_712186 := by
    simpa [prefixWord, tailWord_712186, baseEnd_712186] using wordTrace_append hprefix tailTrace_712186
  have hstable : (prefixWord ++ tailWord_712186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712186).length < 2 ^ (prefixWord ++ tailWord_712186).sum := by decide
  have hdescent : baseEnd_712186 < baseStart_712186 := by decide
  rcases family_descends (prefixWord ++ tailWord_712186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712203 : List Nat := [1, 1, 1, 1, 8, 2, 6]
def baseStart_712203 : Nat := 118140960795 + 712203 * 2 ^ 59
def prefixEnd_712203 : Nat := 4983230072969 + 3 ^ 40 * 712203 * 2
def baseEnd_712203 : Nat := 36118761735721702339471

theorem tailTrace_712203 : CollatzResearch.WordTrace tailWord_712203 prefixEnd_712203 36118761735721702339471 := by
  unfold tailWord_712203
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976177438817640433685263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17317451625878426955790175 25976177438817640433685263)
  ·
    refine ⟨38964266158226460650527895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25976177438817640433685263 38964266158226460650527895)
    ·
      refine ⟨58446399237339690975791843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38964266158226460650527895 58446399237339690975791843)
      ·
        refine ⟨87669598856009536463687765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58446399237339690975791843 87669598856009536463687765)
        ·
          refine ⟨1027378111593861755433841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 87669598856009536463687765 1027378111593861755433841)
          ·
            refine ⟨770533583695396316575381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027378111593861755433841 770533583695396316575381)
            ·
              refine ⟨36118761735721702339471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 770533583695396316575381 36118761735721702339471)
              ·
                rfl

theorem cell20_712203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_712203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712203 prefixEnd_712203 := by exact prefixLift 712203
  have htrace : WordTrace (prefixWord ++ tailWord_712203) baseStart_712203 baseEnd_712203 := by
    simpa [prefixWord, tailWord_712203, baseEnd_712203] using wordTrace_append hprefix tailTrace_712203
  have hstable : (prefixWord ++ tailWord_712203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712203).length < 2 ^ (prefixWord ++ tailWord_712203).sum := by decide
  have hdescent : baseEnd_712203 < baseStart_712203 := by decide
  rcases family_descends (prefixWord ++ tailWord_712203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712227 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_712227 : Nat := 118140960795 + 712227 * 2 ^ 59
def prefixEnd_712227 : Nat := 4983230072969 + 3 ^ 40 * 712227 * 2
def baseEnd_712227 : Nat := 325079809875457904255141

theorem tailTrace_712227 : CollatzResearch.WordTrace tailWord_712227 prefixEnd_712227 325079809875457904255141 := by
  unfold tailWord_712227
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977052790730692532558935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17318035193820461688372623 25977052790730692532558935)
  ·
    refine ⟨38965579186096038798838403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25977052790730692532558935 38965579186096038798838403)
    ·
      refine ⟨58448368779144058198257605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38965579186096038798838403 58448368779144058198257605)
      ·
        refine ⟨10959069146089510912173301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58448368779144058198257605 10959069146089510912173301)
        ·
          refine ⟨1027412732445891648016247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10959069146089510912173301 1027412732445891648016247)
          ·
            refine ⟨1541119098668837472024371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027412732445891648016247 1541119098668837472024371)
            ·
              refine ⟨2311678648003256208036557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541119098668837472024371 2311678648003256208036557)
              ·
                refine ⟨866879493001221078013709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311678648003256208036557 866879493001221078013709)
                ·
                  refine ⟨325079809875457904255141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866879493001221078013709 325079809875457904255141)
                  ·
                    rfl

theorem cell20_712227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_712227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712227 prefixEnd_712227 := by exact prefixLift 712227
  have htrace : WordTrace (prefixWord ++ tailWord_712227) baseStart_712227 baseEnd_712227 := by
    simpa [prefixWord, tailWord_712227, baseEnd_712227] using wordTrace_append hprefix tailTrace_712227
  have hstable : (prefixWord ++ tailWord_712227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712227).length < 2 ^ (prefixWord ++ tailWord_712227).sum := by decide
  have hdescent : baseEnd_712227 < baseStart_712227 := by decide
  rcases family_descends (prefixWord ++ tailWord_712227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712268 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_712268 : Nat := 118140960795 + 712268 * 2 ^ 59
def prefixEnd_712268 : Nat := 4983230072969 + 3 ^ 40 * 712268 * 2
def baseEnd_712268 : Nat := 325098523392643983888307

theorem tailTrace_712268 : CollatzResearch.WordTrace tailWord_712268 prefixEnd_712268 325098523392643983888307 := by
  unfold tailWord_712268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989274091791078267400729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319032122388104356534305 12989274091791078267400729)
  ·
    refine ⟨9741955568843308700550547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12989274091791078267400729 9741955568843308700550547)
    ·
      refine ⟨14612933353264963050825821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741955568843308700550547 14612933353264963050825821)
      ·
        refine ⟨5479850007474361144059683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14612933353264963050825821 5479850007474361144059683)
        ·
          refine ⟨8219775011211541716089525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479850007474361144059683 8219775011211541716089525)
          ·
            refine ⟨770603907301082035883393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8219775011211541716089525 770603907301082035883393)
            ·
              refine ⟨577952930475811526912545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770603907301082035883393 577952930475811526912545)
              ·
                refine ⟨433464697856858645184409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577952930475811526912545 433464697856858645184409)
                ·
                  refine ⟨325098523392643983888307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433464697856858645184409 325098523392643983888307)
                  ·
                    rfl

theorem cell20_712268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_712268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712268 prefixEnd_712268 := by exact prefixLift 712268
  have htrace : WordTrace (prefixWord ++ tailWord_712268) baseStart_712268 baseEnd_712268 := by
    simpa [prefixWord, tailWord_712268, baseEnd_712268] using wordTrace_append hprefix tailTrace_712268
  have hstable : (prefixWord ++ tailWord_712268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712268).length < 2 ^ (prefixWord ++ tailWord_712268).sum := by decide
  have hdescent : baseEnd_712268 < baseStart_712268 := by decide
  rcases family_descends (prefixWord ++ tailWord_712268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712272 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_712272 : Nat := 118140960795 + 712272 * 2 ^ 59
def prefixEnd_712272 : Nat := 4983230072969 + 3 ^ 40 * 712272 * 2
def baseEnd_712272 : Nat := 325100349101637747754957

theorem tailTrace_712272 : CollatzResearch.WordTrace tailWord_712272 prefixEnd_712272 325100349101637747754957 := by
  unfold tailWord_712272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989347037783832608973535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319129383711776811964713 12989347037783832608973535)
  ·
    refine ⟨19484020556675748913460303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989347037783832608973535 19484020556675748913460303)
    ·
      refine ⟨29226030835013623370190455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19484020556675748913460303 29226030835013623370190455)
      ·
        refine ⟨43839046252520435055285683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29226030835013623370190455 43839046252520435055285683)
        ·
          refine ⟨65758569378780652582928525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43839046252520435055285683 65758569378780652582928525)
          ·
            refine ⟨24659463517042744718598197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65758569378780652582928525 24659463517042744718598197)
            ·
              refine ⟨2311824704722757317368581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24659463517042744718598197 2311824704722757317368581)
              ·
                refine ⟨433467132135516997006609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2311824704722757317368581 433467132135516997006609)
                ·
                  refine ⟨325100349101637747754957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433467132135516997006609 325100349101637747754957)
                  ·
                    rfl

theorem cell20_712272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_712272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712272 prefixEnd_712272 := by exact prefixLift 712272
  have htrace : WordTrace (prefixWord ++ tailWord_712272) baseStart_712272 baseEnd_712272 := by
    simpa [prefixWord, tailWord_712272, baseEnd_712272] using wordTrace_append hprefix tailTrace_712272
  have hstable : (prefixWord ++ tailWord_712272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712272).length < 2 ^ (prefixWord ++ tailWord_712272).sum := by decide
  have hdescent : baseEnd_712272 < baseStart_712272 := by decide
  rcases family_descends (prefixWord ++ tailWord_712272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712279 : List Nat := [1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_712279 : Nat := 118140960795 + 712279 * 2 ^ 59
def prefixEnd_712279 : Nat := 4983230072969 + 3 ^ 40 * 712279 * 2
def baseEnd_712279 : Nat := 108367848030792278173865

theorem tailTrace_712279 : CollatzResearch.WordTrace tailWord_712279 prefixEnd_712279 108367848030792278173865 := by
  unfold tailWord_712279
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978949386542305413451891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17319299591028203608967927 25978949386542305413451891)
  ·
    refine ⟨38968424079813458120177837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978949386542305413451891 38968424079813458120177837)
    ·
      refine ⟨14613159029930046795066689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38968424079813458120177837 14613159029930046795066689)
      ·
        refine ⟨10959869272447535096300017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14613159029930046795066689 10959869272447535096300017)
        ·
          refine ⟨8219901954335651322225013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10959869272447535096300017 8219901954335651322225013)
          ·
            refine ⟨770615808218967311458595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8219901954335651322225013 770615808218967311458595)
            ·
              refine ⟨1155923712328450967187893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770615808218967311458595 1155923712328450967187893)
              ·
                refine ⟨108367848030792278173865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155923712328450967187893 108367848030792278173865)
                ·
                  rfl

theorem cell20_712279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_712279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712279 prefixEnd_712279 := by exact prefixLift 712279
  have htrace : WordTrace (prefixWord ++ tailWord_712279) baseStart_712279 baseEnd_712279 := by
    simpa [prefixWord, tailWord_712279, baseEnd_712279] using wordTrace_append hprefix tailTrace_712279
  have hstable : (prefixWord ++ tailWord_712279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712279).length < 2 ^ (prefixWord ++ tailWord_712279).sum := by decide
  have hdescent : baseEnd_712279 < baseStart_712279 := by decide
  rcases family_descends (prefixWord ++ tailWord_712279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712293 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_712293 : Nat := 118140960795 + 712293 * 2 ^ 59
def prefixEnd_712293 : Nat := 4983230072969 + 3 ^ 40 * 712293 * 2
def baseEnd_712293 : Nat := 325109934073855008054871

theorem tailTrace_712293 : CollatzResearch.WordTrace tailWord_712293 prefixEnd_712293 325109934073855008054871 := by
  unfold tailWord_712293
  simp only [CollatzResearch.WordTrace]
  refine ⟨25979460008491585804461533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17319640005661057202974355 25979460008491585804461533)
  ·
    refine ⟨9742297503184344676673075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25979460008491585804461533 9742297503184344676673075)
    ·
      refine ⟨14613446254776517015009613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9742297503184344676673075 14613446254776517015009613)
      ·
        refine ⟨5480042345541193880628605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14613446254776517015009613 5480042345541193880628605)
        ·
          refine ⟨2055015879577947705235727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5480042345541193880628605 2055015879577947705235727)
          ·
            refine ⟨3082523819366921557853591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055015879577947705235727 3082523819366921557853591)
            ·
              refine ⟨4623785729050382336780387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082523819366921557853591 4623785729050382336780387)
              ·
                refine ⟨6935678593575573505170581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623785729050382336780387 6935678593575573505170581)
                ·
                  refine ⟨325109934073855008054871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6935678593575573505170581 325109934073855008054871)
                  ·
                    rfl

theorem cell20_712293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_712293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712293 prefixEnd_712293 := by exact prefixLift 712293
  have htrace : WordTrace (prefixWord ++ tailWord_712293) baseStart_712293 baseEnd_712293 := by
    simpa [prefixWord, tailWord_712293, baseEnd_712293] using wordTrace_append hprefix tailTrace_712293
  have hstable : (prefixWord ++ tailWord_712293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712293).length < 2 ^ (prefixWord ++ tailWord_712293).sum := by decide
  have hdescent : baseEnd_712293 < baseStart_712293 := by decide
  rcases family_descends (prefixWord ++ tailWord_712293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712296 : List Nat := [2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_712296 : Nat := 118140960795 + 712296 * 2 ^ 59
def prefixEnd_712296 : Nat := 4983230072969 + 3 ^ 40 * 712296 * 2
def baseEnd_712296 : Nat := 108370434451866776984953

theorem tailTrace_712296 : CollatzResearch.WordTrace tailWord_712296 prefixEnd_712296 108370434451866776984953 := by
  unfold tailWord_712296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989784713740358658410371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319712951653811544547161 12989784713740358658410371)
  ·
    refine ⟨19484677070610537987615557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989784713740358658410371 19484677070610537987615557)
    ·
      refine ⟨3653376950739475872677917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19484677070610537987615557 3653376950739475872677917)
      ·
        refine ⟨1370016356527303452254219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3653376950739475872677917 1370016356527303452254219)
        ·
          refine ⟨2055024534790955178381329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370016356527303452254219 2055024534790955178381329)
          ·
            refine ⟨1541268401093216383785997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055024534790955178381329 1541268401093216383785997)
            ·
              refine ⟨577975650409956143919749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541268401093216383785997 577975650409956143919749)
              ·
                refine ⟨108370434451866776984953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577975650409956143919749 108370434451866776984953)
                ·
                  rfl

theorem cell20_712296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_712296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712296 prefixEnd_712296 := by exact prefixLift 712296
  have htrace : WordTrace (prefixWord ++ tailWord_712296) baseStart_712296 baseEnd_712296 := by
    simpa [prefixWord, tailWord_712296, baseEnd_712296] using wordTrace_append hprefix tailTrace_712296
  have hstable : (prefixWord ++ tailWord_712296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712296).length < 2 ^ (prefixWord ++ tailWord_712296).sum := by decide
  have hdescent : baseEnd_712296 < baseStart_712296 := by decide
  rcases family_descends (prefixWord ++ tailWord_712296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712331 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_712331 : Nat := 118140960795 + 712331 * 2 ^ 59
def prefixEnd_712331 : Nat := 4983230072969 + 3 ^ 40 * 712331 * 2
def baseEnd_712331 : Nat := 325127278309295764788049

theorem tailTrace_712331 : CollatzResearch.WordTrace tailWord_712331 prefixEnd_712331 325127278309295764788049 := by
  unfold tailWord_712331
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980845982353918294344847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17320563988235945529563231 25980845982353918294344847)
  ·
    refine ⟨38971268973530877441517271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25980845982353918294344847 38971268973530877441517271)
    ·
      refine ⟨58456903460296316162275907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38971268973530877441517271 58456903460296316162275907)
      ·
        refine ⟨87685355190444474243413861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58456903460296316162275907 87685355190444474243413861)
        ·
          refine ⟨16441004098208338920640099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87685355190444474243413861 16441004098208338920640099)
          ·
            refine ⟨24661506147312508380960149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16441004098208338920640099 24661506147312508380960149)
            ·
              refine ⟨1156008100655273830357507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24661506147312508380960149 1156008100655273830357507)
              ·
                refine ⟨1734012150982910745536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156008100655273830357507 1734012150982910745536261)
                ·
                  refine ⟨325127278309295764788049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734012150982910745536261 325127278309295764788049)
                  ·
                    rfl

theorem cell20_712331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_712331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712331 prefixEnd_712331 := by exact prefixLift 712331
  have htrace : WordTrace (prefixWord ++ tailWord_712331) baseStart_712331 baseEnd_712331 := by
    simpa [prefixWord, tailWord_712331, baseEnd_712331] using wordTrace_append hprefix tailTrace_712331
  have hstable : (prefixWord ++ tailWord_712331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712331).length < 2 ^ (prefixWord ++ tailWord_712331).sum := by decide
  have hdescent : baseEnd_712331 < baseStart_712331 := by decide
  rcases family_descends (prefixWord ++ tailWord_712331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712351 : List Nat := [1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_712351 : Nat := 118140960795 + 712351 * 2 ^ 59
def prefixEnd_712351 : Nat := 4983230072969 + 3 ^ 40 * 712351 * 2
def baseEnd_712351 : Nat := 108378802284754861373767

theorem tailTrace_712351 : CollatzResearch.WordTrace tailWord_712351 prefixEnd_712351 108378802284754861373767 := by
  unfold tailWord_712351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981575442281461710072907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17321050294854307806715271 25981575442281461710072907)
  ·
    refine ⟨38972363163422192565109361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25981575442281461710072907 38972363163422192565109361)
    ·
      refine ⟨29229272372566644423832021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38972363163422192565109361 29229272372566644423832021)
      ·
        refine ⟨685061071232030728683563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29229272372566644423832021 685061071232030728683563)
        ·
          refine ⟨1027591606848046093025345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685061071232030728683563 1027591606848046093025345)
          ·
            refine ⟨770693705136034569769009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027591606848046093025345 770693705136034569769009)
            ·
              refine ⟨578020278852025927326757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770693705136034569769009 578020278852025927326757)
              ·
                refine ⟨108378802284754861373767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578020278852025927326757 108378802284754861373767)
                ·
                  rfl

theorem cell20_712351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_712351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712351 prefixEnd_712351 := by exact prefixLift 712351
  have htrace : WordTrace (prefixWord ++ tailWord_712351) baseStart_712351 baseEnd_712351 := by
    simpa [prefixWord, tailWord_712351, baseEnd_712351] using wordTrace_append hprefix tailTrace_712351
  have hstable : (prefixWord ++ tailWord_712351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712351).length < 2 ^ (prefixWord ++ tailWord_712351).sum := by decide
  have hdescent : baseEnd_712351 < baseStart_712351 := by decide
  rcases family_descends (prefixWord ++ tailWord_712351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712382 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_712382 : Nat := 118140960795 + 712382 * 2 ^ 59
def prefixEnd_712382 : Nat := 4983230072969 + 3 ^ 40 * 712382 * 2
def baseEnd_712382 : Nat := 325150556098966254087841

theorem tailTrace_712382 : CollatzResearch.WordTrace tailWord_712382 prefixEnd_712382 325150556098966254087841 := by
  unfold tailWord_712382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247838263146144250556425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17321804070112769336300933 3247838263146144250556425)
  ·
    refine ⟨2435878697359608187917319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3247838263146144250556425 2435878697359608187917319)
    ·
      refine ⟨3653818046039412281875979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435878697359608187917319 3653818046039412281875979)
      ·
        refine ⟨5480727069059118422813969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653818046039412281875979 5480727069059118422813969)
        ·
          refine ⟨4110545301794338817110477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5480727069059118422813969 4110545301794338817110477)
          ·
            refine ⟨1541454488172877056416429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4110545301794338817110477 1541454488172877056416429)
            ·
              refine ⟨578045433064828896156161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541454488172877056416429 578045433064828896156161)
              ·
                refine ⟨433534074798621672117121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578045433064828896156161 433534074798621672117121)
                ·
                  refine ⟨325150556098966254087841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433534074798621672117121 325150556098966254087841)
                  ·
                    rfl

theorem cell20_712382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_712382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712382 prefixEnd_712382 := by exact prefixLift 712382
  have htrace : WordTrace (prefixWord ++ tailWord_712382) baseStart_712382 baseEnd_712382 := by
    simpa [prefixWord, tailWord_712382, baseEnd_712382] using wordTrace_append hprefix tailTrace_712382
  have hstable : (prefixWord ++ tailWord_712382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712382).length < 2 ^ (prefixWord ++ tailWord_712382).sum := by decide
  have hdescent : baseEnd_712382 < baseStart_712382 := by decide
  rcases family_descends (prefixWord ++ tailWord_712382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712383 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_712383 : Nat := 118140960795 + 712383 * 2 ^ 59
def prefixEnd_712383 : Nat := 4983230072969 + 3 ^ 40 * 712383 * 2
def baseEnd_712383 : Nat := 325151012526214695054503

theorem tailTrace_712383 : CollatzResearch.WordTrace tailWord_712383 prefixEnd_712383 325151012526214695054503 := by
  unfold tailWord_712383
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982742578165531175237803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17321828385443687450158535 25982742578165531175237803)
  ·
    refine ⟨38974113867248296762856705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25982742578165531175237803 38974113867248296762856705)
    ·
      refine ⟨29230585400436222572142529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38974113867248296762856705 29230585400436222572142529)
      ·
        refine ⟨21922939050327166929106897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29230585400436222572142529 21922939050327166929106897)
        ·
          refine ⟨16442204287745375196830173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21922939050327166929106897 16442204287745375196830173)
          ·
            refine ⟨6165826607904515698811315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16442204287745375196830173 6165826607904515698811315)
            ·
              refine ⟨9248739911856773548216973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165826607904515698811315 9248739911856773548216973)
              ·
                refine ⟨3468277466946290080581365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9248739911856773548216973 3468277466946290080581365)
                ·
                  refine ⟨325151012526214695054503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468277466946290080581365 325151012526214695054503)
                  ·
                    rfl

theorem cell20_712383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_712383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712383 prefixEnd_712383 := by exact prefixLift 712383
  have htrace : WordTrace (prefixWord ++ tailWord_712383) baseStart_712383 baseEnd_712383 := by
    simpa [prefixWord, tailWord_712383, baseEnd_712383] using wordTrace_append hprefix tailTrace_712383
  have hstable : (prefixWord ++ tailWord_712383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712383).length < 2 ^ (prefixWord ++ tailWord_712383).sum := by decide
  have hdescent : baseEnd_712383 < baseStart_712383 := by decide
  rcases family_descends (prefixWord ++ tailWord_712383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712454 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_712454 : Nat := 118140960795 + 712454 * 2 ^ 59
def prefixEnd_712454 : Nat := 4983230072969 + 3 ^ 40 * 712454 * 2
def baseEnd_712454 : Nat := 325183418860854003687547

theorem tailTrace_712454 : CollatzResearch.WordTrace tailWord_712454 prefixEnd_712454 325183418860854003687547 := by
  unfold tailWord_712454
  simp only [CollatzResearch.WordTrace]
  refine ⟨812041630028384696908513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17323554773938873534048277 812041630028384696908513)
  ·
    refine ⟨609031222521288522681385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 812041630028384696908513 609031222521288522681385)
    ·
      refine ⟨456773416890966392011039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 609031222521288522681385 456773416890966392011039)
      ·
        refine ⟨685160125336449588016559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456773416890966392011039 685160125336449588016559)
        ·
          refine ⟨1027740188004674382024839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685160125336449588016559 1027740188004674382024839)
          ·
            refine ⟨1541610282007011573037259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027740188004674382024839 1541610282007011573037259)
            ·
              refine ⟨2312415423010517359555889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541610282007011573037259 2312415423010517359555889)
              ·
                refine ⟨1734311567257888019666917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312415423010517359555889 1734311567257888019666917)
                ·
                  refine ⟨325183418860854003687547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734311567257888019666917 325183418860854003687547)
                  ·
                    rfl

theorem cell20_712454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_712454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712454 prefixEnd_712454 := by exact prefixLift 712454
  have htrace : WordTrace (prefixWord ++ tailWord_712454) baseStart_712454 baseEnd_712454 := by
    simpa [prefixWord, tailWord_712454, baseEnd_712454] using wordTrace_append hprefix tailTrace_712454
  have hstable : (prefixWord ++ tailWord_712454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712454).length < 2 ^ (prefixWord ++ tailWord_712454).sum := by decide
  have hdescent : baseEnd_712454 < baseStart_712454 := by decide
  rcases family_descends (prefixWord ++ tailWord_712454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712461 : List Nat := [1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_712461 : Nat := 118140960795 + 712461 * 2 ^ 59
def prefixEnd_712461 : Nat := 4983230072969 + 3 ^ 40 * 712461 * 2
def baseEnd_712461 : Nat := 108395537950531030151395

theorem tailTrace_712461 : CollatzResearch.WordTrace tailWord_712461 prefixEnd_712461 108395537950531030151395 := by
  unfold tailWord_712461
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985587471882950496577237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17323724981255300331051491 25985587471882950496577237)
  ·
    refine ⟨609037206372256652263529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25985587471882950496577237 609037206372256652263529)
    ·
      refine ⟨456777904779192489197647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 609037206372256652263529 456777904779192489197647)
      ·
        refine ⟨685166857168788733796471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456777904779192489197647 685166857168788733796471)
        ·
          refine ⟨1027750285753183100694707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685166857168788733796471 1027750285753183100694707)
          ·
            refine ⟨1541625428629774651042061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027750285753183100694707 1541625428629774651042061)
            ·
              refine ⟨578109535736165494140773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541625428629774651042061 578109535736165494140773)
              ·
                refine ⟨108395537950531030151395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578109535736165494140773 108395537950531030151395)
                ·
                  rfl

theorem cell20_712461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_712461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712461 prefixEnd_712461 := by exact prefixLift 712461
  have htrace : WordTrace (prefixWord ++ tailWord_712461) baseStart_712461 baseEnd_712461 := by
    simpa [prefixWord, tailWord_712461, baseEnd_712461] using wordTrace_append hprefix tailTrace_712461
  have hstable : (prefixWord ++ tailWord_712461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712461).length < 2 ^ (prefixWord ++ tailWord_712461).sum := by decide
  have hdescent : baseEnd_712461 < baseStart_712461 := by decide
  rcases family_descends (prefixWord ++ tailWord_712461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712469 : List Nat := [1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_712469 : Nat := 118140960795 + 712469 * 2 ^ 59
def prefixEnd_712469 : Nat := 4983230072969 + 3 ^ 40 * 712469 * 2
def baseEnd_712469 : Nat := 108396755089860206062495

theorem tailTrace_712469 : CollatzResearch.WordTrace tailWord_712469 prefixEnd_712469 108396755089860206062495 := by
  unfold tailWord_712469
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985879255853967862868461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17323919503902645241912307 25985879255853967862868461)
  ·
    refine ⟨9744704720945237948575673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25985879255853967862868461 9744704720945237948575673)
    ·
      refine ⟨7308528540708928461431755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9744704720945237948575673 7308528540708928461431755)
      ·
        refine ⟨10962792811063392692147633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7308528540708928461431755 10962792811063392692147633)
        ·
          refine ⟨8222094608297544519110725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10962792811063392692147633 8222094608297544519110725)
          ·
            refine ⟨1541642739055789597333261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8222094608297544519110725 1541642739055789597333261)
            ·
              refine ⟨578116027145921098999973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541642739055789597333261 578116027145921098999973)
              ·
                refine ⟨108396755089860206062495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578116027145921098999973 108396755089860206062495)
                ·
                  rfl

theorem cell20_712469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_712469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712469 prefixEnd_712469 := by exact prefixLift 712469
  have htrace : WordTrace (prefixWord ++ tailWord_712469) baseStart_712469 baseEnd_712469 := by
    simpa [prefixWord, tailWord_712469, baseEnd_712469] using wordTrace_append hprefix tailTrace_712469
  have hstable : (prefixWord ++ tailWord_712469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712469).length < 2 ^ (prefixWord ++ tailWord_712469).sum := by decide
  have hdescent : baseEnd_712469 < baseStart_712469 := by decide
  rcases family_descends (prefixWord ++ tailWord_712469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712500 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_712500 : Nat := 118140960795 + 712500 * 2 ^ 59
def prefixEnd_712500 : Nat := 4983230072969 + 3 ^ 40 * 712500 * 2
def baseEnd_712500 : Nat := 325204414514282288154025

theorem tailTrace_712500 : CollatzResearch.WordTrace tailWord_712500 prefixEnd_712500 325204414514282288154025 := by
  unfold tailWord_712500
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993504959370830078623477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17324673279161106771497969 12993504959370830078623477)
  ·
    refine ⟨1218141089941015319870951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12993504959370830078623477 1218141089941015319870951)
    ·
      refine ⟨1827211634911522979806427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218141089941015319870951 1827211634911522979806427)
      ·
        refine ⟨2740817452367284469709641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827211634911522979806427 2740817452367284469709641)
        ·
          refine ⟨2055613089275463352282231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740817452367284469709641 2055613089275463352282231)
          ·
            refine ⟨3083419633913195028423347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055613089275463352282231 3083419633913195028423347)
            ·
              refine ⟨4625129450869792542635021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083419633913195028423347 4625129450869792542635021)
              ·
                refine ⟨1734423544076172203488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4625129450869792542635021 1734423544076172203488133)
                ·
                  refine ⟨325204414514282288154025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734423544076172203488133 325204414514282288154025)
                  ·
                    rfl

theorem cell20_712500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_712500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712500 prefixEnd_712500 := by exact prefixLift 712500
  have htrace : WordTrace (prefixWord ++ tailWord_712500) baseStart_712500 baseEnd_712500 := by
    simpa [prefixWord, tailWord_712500, baseEnd_712500] using wordTrace_append hprefix tailTrace_712500
  have hstable : (prefixWord ++ tailWord_712500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712500).length < 2 ^ (prefixWord ++ tailWord_712500).sum := by decide
  have hdescent : baseEnd_712500 < baseStart_712500 := by decide
  rcases family_descends (prefixWord ++ tailWord_712500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712510 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_712510 : Nat := 118140960795 + 712510 * 2 ^ 59
def prefixEnd_712510 : Nat := 4983230072969 + 3 ^ 40 * 712510 * 2
def baseEnd_712510 : Nat := 325208978786766697820651

theorem tailTrace_712510 : CollatzResearch.WordTrace tailWord_712510 prefixEnd_712510 325208978786766697820651 := by
  unfold tailWord_712510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248421831088178983138873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17324916432470287910073989 3248421831088178983138873)
  ·
    refine ⟨2436316373316134237354155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248421831088178983138873 2436316373316134237354155)
    ·
      refine ⟨3654474559974201356031233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436316373316134237354155 3654474559974201356031233)
      ·
        refine ⟨2740855919980651017023425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3654474559974201356031233 2740855919980651017023425)
        ·
          refine ⟨2055641939985488262767569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740855919980651017023425 2055641939985488262767569)
          ·
            refine ⟨1541731454989116197075677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055641939985488262767569 1541731454989116197075677)
            ·
              refine ⟨578149295620918573903379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541731454989116197075677 578149295620918573903379)
              ·
                refine ⟨867223943431377860855069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578149295620918573903379 867223943431377860855069)
                ·
                  refine ⟨325208978786766697820651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867223943431377860855069 325208978786766697820651)
                  ·
                    rfl

theorem cell20_712510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_712510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712510 prefixEnd_712510 := by exact prefixLift 712510
  have htrace : WordTrace (prefixWord ++ tailWord_712510) baseStart_712510 baseEnd_712510 := by
    simpa [prefixWord, tailWord_712510, baseEnd_712510] using wordTrace_append hprefix tailTrace_712510
  have hstable : (prefixWord ++ tailWord_712510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712510).length < 2 ^ (prefixWord ++ tailWord_712510).sum := by decide
  have hdescent : baseEnd_712510 < baseStart_712510 := by decide
  rcases family_descends (prefixWord ++ tailWord_712510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712524 : List Nat := [2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_712524 : Nat := 118140960795 + 712524 * 2 ^ 59
def prefixEnd_712524 : Nat := 4983230072969 + 3 ^ 40 * 712524 * 2
def baseEnd_712524 : Nat := 108405122922748290451309

theorem tailTrace_712524 : CollatzResearch.WordTrace tailWord_712524 prefixEnd_712524 108405122922748290451309 := by
  unfold tailWord_712524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993942635327356128060313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17325256847103141504080417 12993942635327356128060313)
  ·
    refine ⟨9745456976495517096045235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12993942635327356128060313 9745456976495517096045235)
    ·
      refine ⟨14618185464743275644067853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9745456976495517096045235 14618185464743275644067853)
      ·
        refine ⟨5481819549278728366525445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14618185464743275644067853 5481819549278728366525445)
        ·
          refine ⟨1027841165489761568723521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5481819549278728366525445 1027841165489761568723521)
          ·
            refine ⟨770880874117321176542641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027841165489761568723521 770880874117321176542641)
            ·
              refine ⟨578160655587990882406981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770880874117321176542641 578160655587990882406981)
              ·
                refine ⟨108405122922748290451309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578160655587990882406981 108405122922748290451309)
                ·
                  rfl

theorem cell20_712524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_712524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712524 prefixEnd_712524 := by exact prefixLift 712524
  have htrace : WordTrace (prefixWord ++ tailWord_712524) baseStart_712524 baseEnd_712524 := by
    simpa [prefixWord, tailWord_712524, baseEnd_712524] using wordTrace_append hprefix tailTrace_712524
  have hstable : (prefixWord ++ tailWord_712524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712524).length < 2 ^ (prefixWord ++ tailWord_712524).sum := by decide
  have hdescent : baseEnd_712524 < baseStart_712524 := by decide
  rcases family_descends (prefixWord ++ tailWord_712524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712552 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_712552 : Nat := 118140960795 + 712552 * 2 ^ 59
def prefixEnd_712552 : Nat := 4983230072969 + 3 ^ 40 * 712552 * 2
def baseEnd_712552 : Nat := 325228148731201218420479

theorem tailTrace_712552 : CollatzResearch.WordTrace tailWord_712552 prefixEnd_712552 325228148731201218420479 := by
  unfold tailWord_712552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994453257276636519069955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17325937676368848692093273 12994453257276636519069955)
  ·
    refine ⟨19491679885914954778604933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12994453257276636519069955 19491679885914954778604933)
    ·
      refine ⟨3654689978609054020988425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19491679885914954778604933 3654689978609054020988425)
      ·
        refine ⟨2741017483956790515741319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3654689978609054020988425 2741017483956790515741319)
        ·
          refine ⟨4111526225935185773611979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741017483956790515741319 4111526225935185773611979)
          ·
            refine ⟨6167289338902778660417969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4111526225935185773611979 6167289338902778660417969)
            ·
              refine ⟨4625467004177083995313477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6167289338902778660417969 4625467004177083995313477)
              ·
                refine ⟨867275063283203249121277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4625467004177083995313477 867275063283203249121277)
                ·
                  refine ⟨325228148731201218420479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867275063283203249121277 325228148731201218420479)
                  ·
                    rfl

theorem cell20_712552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_712552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712552 prefixEnd_712552 := by exact prefixLift 712552
  have htrace : WordTrace (prefixWord ++ tailWord_712552) baseStart_712552 baseEnd_712552 := by
    simpa [prefixWord, tailWord_712552, baseEnd_712552] using wordTrace_append hprefix tailTrace_712552
  have hstable : (prefixWord ++ tailWord_712552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712552).length < 2 ^ (prefixWord ++ tailWord_712552).sum := by decide
  have hdescent : baseEnd_712552 < baseStart_712552 := by decide
  rcases family_descends (prefixWord ++ tailWord_712552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712604 : List Nat := [2, 2, 3, 3, 1, 9]
def baseStart_712604 : Nat := 118140960795 + 712604 * 2 ^ 59
def prefixEnd_712604 : Nat := 4983230072969 + 3 ^ 40 * 712604 * 2
def baseEnd_712604 : Nat := 12046366035115561062479

theorem tailTrace_712604 : CollatzResearch.WordTrace tailWord_712604 prefixEnd_712604 12046366035115561062479 := by
  unfold tailWord_712604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995401555182442959516433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17327202073576590612688577 12995401555182442959516433)
  ·
    refine ⟨9746551166386832219637325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12995401555182442959516433 9746551166386832219637325)
    ·
      refine ⟨3654956687395062082363997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9746551166386832219637325 3654956687395062082363997)
      ·
        refine ⟨1370608757773148280886499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3654956687395062082363997 1370608757773148280886499)
        ·
          refine ⟨2055913136659722421329749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370608757773148280886499 2055913136659722421329749)
          ·
            refine ⟨12046366035115561062479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2055913136659722421329749 12046366035115561062479)
            ·
              rfl

theorem cell20_712604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 9].length) (baseStart_712604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712604 prefixEnd_712604 := by exact prefixLift 712604
  have htrace : WordTrace (prefixWord ++ tailWord_712604) baseStart_712604 baseEnd_712604 := by
    simpa [prefixWord, tailWord_712604, baseEnd_712604] using wordTrace_append hprefix tailTrace_712604
  have hstable : (prefixWord ++ tailWord_712604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712604).length < 2 ^ (prefixWord ++ tailWord_712604).sum := by decide
  have hdescent : baseEnd_712604 < baseStart_712604 := by decide
  rcases family_descends (prefixWord ++ tailWord_712604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712606 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_712606 : Nat := 118140960795 + 712606 * 2 ^ 59
def prefixEnd_712606 : Nat := 4983230072969 + 3 ^ 40 * 712606 * 2
def baseEnd_712606 : Nat := 325252795802617030620259

theorem tailTrace_712606 : CollatzResearch.WordTrace tailWord_712606 prefixEnd_712606 325252795802617030620259 := by
  unfold tailWord_712606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248859507044705032575709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17327250704238426840403781 3248859507044705032575709)
  ·
    refine ⟨1218322315141764387215891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3248859507044705032575709 1218322315141764387215891)
    ·
      refine ⟨1827483472712646580823837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218322315141764387215891 1827483472712646580823837)
      ·
        refine ⟨685306302267242467808939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1827483472712646580823837 685306302267242467808939)
        ·
          refine ⟨1027959453400863701713409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685306302267242467808939 1027959453400863701713409)
          ·
            refine ⟨770969590050647776285057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027959453400863701713409 770969590050647776285057)
            ·
              refine ⟨578227192537985832213793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770969590050647776285057 578227192537985832213793)
              ·
                refine ⟨433670394403489374160345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578227192537985832213793 433670394403489374160345)
                ·
                  refine ⟨325252795802617030620259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433670394403489374160345 325252795802617030620259)
                  ·
                    rfl

theorem cell20_712606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_712606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712606 prefixEnd_712606 := by exact prefixLift 712606
  have htrace : WordTrace (prefixWord ++ tailWord_712606) baseStart_712606 baseEnd_712606 := by
    simpa [prefixWord, tailWord_712606, baseEnd_712606] using wordTrace_append hprefix tailTrace_712606
  have hstable : (prefixWord ++ tailWord_712606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712606).length < 2 ^ (prefixWord ++ tailWord_712606).sum := by decide
  have hdescent : baseEnd_712606 < baseStart_712606 := by decide
  rcases family_descends (prefixWord ++ tailWord_712606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712607 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_712607 : Nat := 118140960795 + 712607 * 2 ^ 59
def prefixEnd_712607 : Nat := 4983230072969 + 3 ^ 40 * 712607 * 2
def baseEnd_712607 : Nat := 325253252229865471586921

theorem tailTrace_712607 : CollatzResearch.WordTrace tailWord_712607 prefixEnd_712607 325253252229865471586921 := by
  unfold tailWord_712607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25990912529354017431392075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17327275019569344954261383 25990912529354017431392075)
  ·
    refine ⟨38986368794031026147088113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25990912529354017431392075 38986368794031026147088113)
    ·
      refine ⟨29239776595523269610316085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38986368794031026147088113 29239776595523269610316085)
      ·
        refine ⟨2741229055830306525967133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29239776595523269610316085 2741229055830306525967133)
        ·
          refine ⟨1027960895936364947237675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2741229055830306525967133 1027960895936364947237675)
          ·
            refine ⟨1541941343904547420856513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027960895936364947237675 1541941343904547420856513)
            ·
              refine ⟨1156456007928410565642385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541941343904547420856513 1156456007928410565642385)
              ·
                refine ⟨867342005946307924231789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156456007928410565642385 867342005946307924231789)
                ·
                  refine ⟨325253252229865471586921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867342005946307924231789 325253252229865471586921)
                  ·
                    rfl

theorem cell20_712607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_712607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712607 prefixEnd_712607 := by exact prefixLift 712607
  have htrace : WordTrace (prefixWord ++ tailWord_712607) baseStart_712607 baseEnd_712607 := by
    simpa [prefixWord, tailWord_712607, baseEnd_712607] using wordTrace_append hprefix tailTrace_712607
  have hstable : (prefixWord ++ tailWord_712607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712607).length < 2 ^ (prefixWord ++ tailWord_712607).sum := by decide
  have hdescent : baseEnd_712607 < baseStart_712607 := by decide
  rcases family_descends (prefixWord ++ tailWord_712607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712652 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_712652 : Nat := 118140960795 + 712652 * 2 ^ 59
def prefixEnd_712652 : Nat := 4983230072969 + 3 ^ 40 * 712652 * 2
def baseEnd_712652 : Nat := 325273791456045315086737

theorem tailTrace_712652 : CollatzResearch.WordTrace tailWord_712652 prefixEnd_712652 325273791456045315086737 := by
  unfold tailWord_712652
  simp only [CollatzResearch.WordTrace]
  refine ⟨12996276907095495058390105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17328369209460660077853473 12996276907095495058390105)
  ·
    refine ⟨9747207680321621293792579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12996276907095495058390105 9747207680321621293792579)
    ·
      refine ⟨14620811520482431940688869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9747207680321621293792579 14620811520482431940688869)
      ·
        refine ⟨2741402160090455988879163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14620811520482431940688869 2741402160090455988879163)
        ·
          refine ⟨4112103240135683983318745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741402160090455988879163 4112103240135683983318745)
          ·
            refine ⟨3084077430101762987489059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112103240135683983318745 3084077430101762987489059)
            ·
              refine ⟨4626116145152644481233589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084077430101762987489059 4626116145152644481233589)
              ·
                refine ⟨433698388608060420115649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4626116145152644481233589 433698388608060420115649)
                ·
                  refine ⟨325273791456045315086737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433698388608060420115649 325273791456045315086737)
                  ·
                    rfl

theorem cell20_712652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_712652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712652 prefixEnd_712652 := by exact prefixLift 712652
  have htrace : WordTrace (prefixWord ++ tailWord_712652) baseStart_712652 baseEnd_712652 := by
    simpa [prefixWord, tailWord_712652, baseEnd_712652] using wordTrace_append hprefix tailTrace_712652
  have hstable : (prefixWord ++ tailWord_712652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712652).length < 2 ^ (prefixWord ++ tailWord_712652).sum := by decide
  have hdescent : baseEnd_712652 < baseStart_712652 := by decide
  rcases family_descends (prefixWord ++ tailWord_712652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712663 : List Nat := [1, 1, 3, 2, 1, 1, 11]
def baseStart_712663 : Nat := 118140960795 + 712663 * 2 ^ 59
def prefixEnd_712663 : Nat := 4983230072969 + 3 ^ 40 * 712663 * 2
def baseEnd_712663 : Nat := 36142090239530907302225

theorem tailTrace_712663 : CollatzResearch.WordTrace tailWord_712663 prefixEnd_712663 36142090239530907302225 := by
  unfold tailWord_712663
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992955017151138995430643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17328636678100759330287095 25992955017151138995430643)
  ·
    refine ⟨38989432525726708493145965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25992955017151138995430643 38989432525726708493145965)
    ·
      refine ⟨14621037197147515684929737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38989432525726708493145965 14621037197147515684929737)
      ·
        refine ⟨10965777897860636763697303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14621037197147515684929737 10965777897860636763697303)
        ·
          refine ⟨16448666846790955145545955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965777897860636763697303 16448666846790955145545955)
          ·
            refine ⟨24673000270186432718318933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16448666846790955145545955 24673000270186432718318933)
            ·
              refine ⟨36142090239530907302225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24673000270186432718318933 36142090239530907302225)
              ·
                rfl

theorem cell20_712663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_712663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712663 prefixEnd_712663 := by exact prefixLift 712663
  have htrace : WordTrace (prefixWord ++ tailWord_712663) baseStart_712663 baseEnd_712663 := by
    simpa [prefixWord, tailWord_712663, baseEnd_712663] using wordTrace_append hprefix tailTrace_712663
  have hstable : (prefixWord ++ tailWord_712663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712663).length < 2 ^ (prefixWord ++ tailWord_712663).sum := by decide
  have hdescent : baseEnd_712663 < baseStart_712663 := by decide
  rcases family_descends (prefixWord ++ tailWord_712663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712666 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_712666 : Nat := 118140960795 + 712666 * 2 ^ 59
def prefixEnd_712666 : Nat := 4983230072969 + 3 ^ 40 * 712666 * 2
def baseEnd_712666 : Nat := 325280181437523488620013

theorem tailTrace_712666 : CollatzResearch.WordTrace tailWord_712666 prefixEnd_712666 325280181437523488620013 := by
  unfold tailWord_712666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498266109035067626947463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17328709624093513671859901 6498266109035067626947463)
  ·
    refine ⟨9747399163552601440421195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6498266109035067626947463 9747399163552601440421195)
    ·
      refine ⟨14621098745328902160631793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9747399163552601440421195 14621098745328902160631793)
      ·
        refine ⟨10965824058996676620473845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14621098745328902160631793 10965824058996676620473845)
        ·
          refine ⟨1028046005530938433169423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10965824058996676620473845 1028046005530938433169423)
          ·
            refine ⟨1542069008296407649754135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028046005530938433169423 1542069008296407649754135)
            ·
              refine ⟨2313103512444611474631203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542069008296407649754135 2313103512444611474631203)
              ·
                refine ⟨3469655268666917211946805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313103512444611474631203 3469655268666917211946805)
                ·
                  refine ⟨325280181437523488620013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3469655268666917211946805 325280181437523488620013)
                  ·
                    rfl

theorem cell20_712666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_712666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712666 prefixEnd_712666 := by exact prefixLift 712666
  have htrace : WordTrace (prefixWord ++ tailWord_712666) baseStart_712666 baseEnd_712666 := by
    simpa [prefixWord, tailWord_712666, baseEnd_712666] using wordTrace_append hprefix tailTrace_712666
  have hstable : (prefixWord ++ tailWord_712666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712666).length < 2 ^ (prefixWord ++ tailWord_712666).sum := by decide
  have hdescent : baseEnd_712666 < baseStart_712666 := by decide
  rcases family_descends (prefixWord ++ tailWord_712666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712697 : List Nat := [1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_712697 : Nat := 118140960795 + 712697 * 2 ^ 59
def prefixEnd_712697 : Nat := 4983230072969 + 3 ^ 40 * 712697 * 2
def baseEnd_712697 : Nat := 108431443560741719528851

theorem tailTrace_712697 : CollatzResearch.WordTrace tailWord_712697 prefixEnd_712697 108431443560741719528851 := by
  unfold tailWord_712697
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994195099027962802168345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17329463399351975201445563 25994195099027962802168345)
  ·
    refine ⟨19495646324270972101626259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25994195099027962802168345 19495646324270972101626259)
    ·
      refine ⟨29243469486406458152439389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19495646324270972101626259 29243469486406458152439389)
      ·
        refine ⟨10966301057402421807164771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29243469486406458152439389 10966301057402421807164771)
        ·
          refine ⟨16449451586103632710747157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10966301057402421807164771 16449451586103632710747157)
          ·
            refine ⟨771068043098607783316273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16449451586103632710747157 771068043098607783316273)
            ·
              refine ⟨578301032323955837487205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771068043098607783316273 578301032323955837487205)
              ·
                refine ⟨108431443560741719528851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578301032323955837487205 108431443560741719528851)
                ·
                  rfl

theorem cell20_712697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_712697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712697 prefixEnd_712697 := by exact prefixLift 712697
  have htrace : WordTrace (prefixWord ++ tailWord_712697) baseStart_712697 baseEnd_712697 := by
    simpa [prefixWord, tailWord_712697, baseEnd_712697] using wordTrace_append hprefix tailTrace_712697
  have hstable : (prefixWord ++ tailWord_712697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712697).length < 2 ^ (prefixWord ++ tailWord_712697).sum := by decide
  have hdescent : baseEnd_712697 < baseStart_712697 := by decide
  rcases family_descends (prefixWord ++ tailWord_712697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712710 : List Nat := [6, 2, 1, 2, 1, 2, 6]
def baseStart_712710 : Nat := 118140960795 + 712710 * 2 ^ 59
def prefixEnd_712710 : Nat := 4983230072969 + 3 ^ 40 * 712710 * 2
def baseEnd_712710 : Nat := 36144473804050543461463

theorem tailTrace_712710 : CollatzResearch.WordTrace tailWord_712710 prefixEnd_712710 36144473804050543461463 := by
  unfold tailWord_712710
  simp only [CollatzResearch.WordTrace]
  refine ⟨812333413999402063199737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17329779498653910681594389 812333413999402063199737)
  ·
    refine ⟨609250060499551547399803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 812333413999402063199737 609250060499551547399803)
    ·
      refine ⟨913875090749327321099705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609250060499551547399803 913875090749327321099705)
      ·
        refine ⟨685406318061995490824779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913875090749327321099705 685406318061995490824779)
        ·
          refine ⟨1028109477092993236237169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685406318061995490824779 1028109477092993236237169)
          ·
            refine ⟨771082107819744927177877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028109477092993236237169 771082107819744927177877)
            ·
              refine ⟨36144473804050543461463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 771082107819744927177877 36144473804050543461463)
              ·
                rfl

theorem cell20_712710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_712710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712710 prefixEnd_712710 := by exact prefixLift 712710
  have htrace : WordTrace (prefixWord ++ tailWord_712710) baseStart_712710 baseEnd_712710 := by
    simpa [prefixWord, tailWord_712710, baseEnd_712710] using wordTrace_append hprefix tailTrace_712710
  have hstable : (prefixWord ++ tailWord_712710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712710).length < 2 ^ (prefixWord ++ tailWord_712710).sum := by decide
  have hdescent : baseEnd_712710 < baseStart_712710 := by decide
  rcases family_descends (prefixWord ++ tailWord_712710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712724 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_712724 : Nat := 118140960795 + 712724 * 2 ^ 59
def prefixEnd_712724 : Nat := 4983230072969 + 3 ^ 40 * 712724 * 2
def baseEnd_712724 : Nat := 325306654217933064686443

theorem tailTrace_712724 : CollatzResearch.WordTrace tailWord_712724 prefixEnd_712724 325306654217933064686443 := by
  unfold tailWord_712724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997589934965073206700613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17330119913286764275600817 12997589934965073206700613)
  ·
    refine ⟨2437048112805951226256365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12997589934965073206700613 2437048112805951226256365)
    ·
      refine ⟨913893042302231709846137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2437048112805951226256365 913893042302231709846137)
      ·
        refine ⟨685419781726673782384603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913893042302231709846137 685419781726673782384603)
        ·
          refine ⟨1028129672590010673576905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685419781726673782384603 1028129672590010673576905)
          ·
            refine ⟨771097254442508005182679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028129672590010673576905 771097254442508005182679)
            ·
              refine ⟨1156645881663762007774019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771097254442508005182679 1156645881663762007774019)
              ·
                refine ⟨1734968822495643011661029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156645881663762007774019 1734968822495643011661029)
                ·
                  refine ⟨325306654217933064686443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734968822495643011661029 325306654217933064686443)
                  ·
                    rfl

theorem cell20_712724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_712724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712724 prefixEnd_712724 := by exact prefixLift 712724
  have htrace : WordTrace (prefixWord ++ tailWord_712724) baseStart_712724 baseEnd_712724 := by
    simpa [prefixWord, tailWord_712724, baseEnd_712724] using wordTrace_append hprefix tailTrace_712724
  have hstable : (prefixWord ++ tailWord_712724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712724).length < 2 ^ (prefixWord ++ tailWord_712724).sum := by decide
  have hdescent : baseEnd_712724 < baseStart_712724 := by decide
  rcases family_descends (prefixWord ++ tailWord_712724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712790 : List Nat := [5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_712790 : Nat := 118140960795 + 712790 * 2 ^ 59
def prefixEnd_712790 : Nat := 4983230072969 + 3 ^ 40 * 712790 * 2
def baseEnd_712790 : Nat := 108445592805443389495391

theorem tailTrace_712790 : CollatzResearch.WordTrace tailWord_712790 prefixEnd_712790 108445592805443389495391 := by
  unfold tailWord_712790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624849192980689980331489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17331724725127359790202549 1624849192980689980331489)
  ·
    refine ⟨1218636894735517485248617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1624849192980689980331489 1218636894735517485248617)
    ·
      refine ⟨913977671051638113936463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218636894735517485248617 913977671051638113936463)
      ·
        refine ⟨1370966506577457170904695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913977671051638113936463 1370966506577457170904695)
        ·
          refine ⟨2056449759866185756357043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370966506577457170904695 2056449759866185756357043)
          ·
            refine ⟨3084674639799278634535565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056449759866185756357043 3084674639799278634535565)
            ·
              refine ⟨1156752989924729487950837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084674639799278634535565 1156752989924729487950837)
              ·
                refine ⟨108445592805443389495391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156752989924729487950837 108445592805443389495391)
                ·
                  rfl

theorem cell20_712790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_712790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712790 prefixEnd_712790 := by exact prefixLift 712790
  have htrace : WordTrace (prefixWord ++ tailWord_712790) baseStart_712790 baseEnd_712790 := by
    simpa [prefixWord, tailWord_712790, baseEnd_712790] using wordTrace_append hprefix tailTrace_712790
  have hstable : (prefixWord ++ tailWord_712790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712790).length < 2 ^ (prefixWord ++ tailWord_712790).sum := by decide
  have hdescent : baseEnd_712790 < baseStart_712790 := by decide
  rcases family_descends (prefixWord ++ tailWord_712790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712797 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_712797 : Nat := 118140960795 + 712797 * 2 ^ 59
def prefixEnd_712797 : Nat := 4983230072969 + 3 ^ 40 * 712797 * 2
def baseEnd_712797 : Nat := 325339973407069255252811

theorem tailTrace_712797 : CollatzResearch.WordTrace tailWord_712797 prefixEnd_712797 325339973407069255252811 := by
  unfold tailWord_712797
  simp only [CollatzResearch.WordTrace]
  refine ⟨25997842398665679880808645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17331894932443786587205763 25997842398665679880808645)
  ·
    refine ⟨4874595449749814977651621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25997842398665679880808645 4874595449749814977651621)
    ·
      refine ⟨913986646828090308309679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4874595449749814977651621 913986646828090308309679)
      ·
        refine ⟨1370979970242135462464519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913986646828090308309679 1370979970242135462464519)
        ·
          refine ⟨2056469955363203193696779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370979970242135462464519 2056469955363203193696779)
          ·
            refine ⟨3084704933044804790545169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056469955363203193696779 3084704933044804790545169)
            ·
              refine ⟨2313528699783603592908877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084704933044804790545169 2313528699783603592908877)
              ·
                refine ⟨867573262418851347340829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313528699783603592908877 867573262418851347340829)
                ·
                  refine ⟨325339973407069255252811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867573262418851347340829 325339973407069255252811)
                  ·
                    rfl

theorem cell20_712797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_712797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712797 prefixEnd_712797 := by exact prefixLift 712797
  have htrace : WordTrace (prefixWord ++ tailWord_712797) baseStart_712797 baseEnd_712797 := by
    simpa [prefixWord, tailWord_712797, baseEnd_712797] using wordTrace_append hprefix tailTrace_712797
  have hstable : (prefixWord ++ tailWord_712797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712797).length < 2 ^ (prefixWord ++ tailWord_712797).sum := by decide
  have hdescent : baseEnd_712797 < baseStart_712797 := by decide
  rcases family_descends (prefixWord ++ tailWord_712797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712842 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_712842 : Nat := 118140960795 + 712842 * 2 ^ 59
def prefixEnd_712842 : Nat := 4983230072969 + 3 ^ 40 * 712842 * 2
def baseEnd_712842 : Nat := 325360512633249098752627

theorem tailTrace_712842 : CollatzResearch.WordTrace tailWord_712842 prefixEnd_712842 325360512633249098752627 := by
  unfold tailWord_712842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499870920875663141549195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17332989122335101710797853 6499870920875663141549195)
  ·
    refine ⟨9749806381313494712323793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499870920875663141549195 9749806381313494712323793)
    ·
      refine ⟨7312354785985121034242845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9749806381313494712323793 7312354785985121034242845)
      ·
        refine ⟨2742133044744420387841067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7312354785985121034242845 2742133044744420387841067)
        ·
          refine ⟨4113199567116630581761601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742133044744420387841067 4113199567116630581761601)
          ·
            refine ⟨3084899675337472936321201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113199567116630581761601 3084899675337472936321201)
            ·
              refine ⟨2313674756503104702240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084899675337472936321201 2313674756503104702240901)
              ·
                refine ⟨433814016844332131670169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2313674756503104702240901 433814016844332131670169)
                ·
                  refine ⟨325360512633249098752627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433814016844332131670169 325360512633249098752627)
                  ·
                    rfl

theorem cell20_712842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_712842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712842 prefixEnd_712842 := by exact prefixLift 712842
  have htrace : WordTrace (prefixWord ++ tailWord_712842) baseStart_712842 baseEnd_712842 := by
    simpa [prefixWord, tailWord_712842, baseEnd_712842] using wordTrace_append hprefix tailTrace_712842
  have hstable : (prefixWord ++ tailWord_712842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712842).length < 2 ^ (prefixWord ++ tailWord_712842).sum := by decide
  have hdescent : baseEnd_712842 < baseStart_712842 := by decide
  rcases family_descends (prefixWord ++ tailWord_712842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712853 : List Nat := [1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_712853 : Nat := 118140960795 + 712853 * 2 ^ 59
def prefixEnd_712853 : Nat := 4983230072969 + 3 ^ 40 * 712853 * 2
def baseEnd_712853 : Nat := 108455177777660649795305

theorem tailTrace_712853 : CollatzResearch.WordTrace tailWord_712853 prefixEnd_712853 108455177777660649795305 := by
  unfold tailWord_712853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999884886462801444847213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17333256590975200963231475 25999884886462801444847213)
  ·
    refine ⟨9749956832423550541817705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25999884886462801444847213 9749956832423550541817705)
    ·
      refine ⟨7312467624317662906363279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9749956832423550541817705 7312467624317662906363279)
      ·
        refine ⟨10968701436476494359544919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312467624317662906363279 10968701436476494359544919)
        ·
          refine ⟨16453052154714741539317379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968701436476494359544919 16453052154714741539317379)
          ·
            refine ⟨24679578232072112308976069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16453052154714741539317379 24679578232072112308976069)
            ·
              refine ⟨4627420918513521057933013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24679578232072112308976069 4627420918513521057933013)
              ·
                refine ⟨108455177777660649795305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4627420918513521057933013 108455177777660649795305)
                ·
                  rfl

theorem cell20_712853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_712853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712853 prefixEnd_712853 := by exact prefixLift 712853
  have htrace : WordTrace (prefixWord ++ tailWord_712853) baseStart_712853 baseEnd_712853 := by
    simpa [prefixWord, tailWord_712853, baseEnd_712853] using wordTrace_append hprefix tailTrace_712853
  have hstable : (prefixWord ++ tailWord_712853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712853).length < 2 ^ (prefixWord ++ tailWord_712853).sum := by decide
  have hdescent : baseEnd_712853 < baseStart_712853 := by decide
  rcases family_descends (prefixWord ++ tailWord_712853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712863 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_712863 : Nat := 118140960795 + 712863 * 2 ^ 59
def prefixEnd_712863 : Nat := 4983230072969 + 3 ^ 40 * 712863 * 2
def baseEnd_712863 : Nat := 325370097605466359052541

theorem tailTrace_712863 : CollatzResearch.WordTrace tailWord_712863 prefixEnd_712863 325370097605466359052541 := by
  unfold tailWord_712863
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000249616426573152711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17333499744284382101807495 26000249616426573152711243)
  ·
    refine ⟨39000374424639859729066865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26000249616426573152711243 39000374424639859729066865)
    ·
      refine ⟨29250280818479894796800149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39000374424639859729066865 29250280818479894796800149)
      ·
        refine ⟨1371106913366245068600007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29250280818479894796800149 1371106913366245068600007)
        ·
          refine ⟨2056660370049367602900011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371106913366245068600007 2056660370049367602900011)
          ·
            refine ⟨3084990555074051404350017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056660370049367602900011 3084990555074051404350017)
            ·
              refine ⟨2313742916305538553262513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084990555074051404350017 2313742916305538553262513)
              ·
                refine ⟨1735307187229153914946885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313742916305538553262513 1735307187229153914946885)
                ·
                  refine ⟨325370097605466359052541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735307187229153914946885 325370097605466359052541)
                  ·
                    rfl

theorem cell20_712863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_712863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712863 prefixEnd_712863 := by exact prefixLift 712863
  have htrace : WordTrace (prefixWord ++ tailWord_712863) baseStart_712863 baseEnd_712863 := by
    simpa [prefixWord, tailWord_712863, baseEnd_712863] using wordTrace_append hprefix tailTrace_712863
  have hstable : (prefixWord ++ tailWord_712863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712863).length < 2 ^ (prefixWord ++ tailWord_712863).sum := by decide
  have hdescent : baseEnd_712863 < baseStart_712863 := by decide
  rcases family_descends (prefixWord ++ tailWord_712863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712866 : List Nat := [3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_712866 : Nat := 118140960795 + 712866 * 2 ^ 59
def prefixEnd_712866 : Nat := 4983230072969 + 3 ^ 40 * 712866 * 2
def baseEnd_712866 : Nat := 108457155629070560650843

theorem tailTrace_712866 : CollatzResearch.WordTrace tailWord_712866 prefixEnd_712866 108457155629070560650843 := by
  unfold tailWord_712866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500089758853926166267613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17333572690277136443380301 6500089758853926166267613)
  ·
    refine ⟨2437533659570222312350355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6500089758853926166267613 2437533659570222312350355)
    ·
      refine ⟨3656300489355333468525533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2437533659570222312350355 3656300489355333468525533)
      ·
        refine ⟨1371112683508250050697075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3656300489355333468525533 1371112683508250050697075)
        ·
          refine ⟨2056669025262375076045613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371112683508250050697075 2056669025262375076045613)
          ·
            refine ⟨771250884473390653517105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2056669025262375076045613 771250884473390653517105)
            ·
              refine ⟨578438163355042990137829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771250884473390653517105 578438163355042990137829)
              ·
                refine ⟨108457155629070560650843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578438163355042990137829 108457155629070560650843)
                ·
                  rfl

theorem cell20_712866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_712866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712866 prefixEnd_712866 := by exact prefixLift 712866
  have htrace : WordTrace (prefixWord ++ tailWord_712866) baseStart_712866 baseEnd_712866 := by
    simpa [prefixWord, tailWord_712866, baseEnd_712866] using wordTrace_append hprefix tailTrace_712866
  have hstable : (prefixWord ++ tailWord_712866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712866).length < 2 ^ (prefixWord ++ tailWord_712866).sum := by decide
  have hdescent : baseEnd_712866 < baseStart_712866 := by decide
  rcases family_descends (prefixWord ++ tailWord_712866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712897 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_712897 : Nat := 118140960795 + 712897 * 2 ^ 59
def prefixEnd_712897 : Nat := 4983230072969 + 3 ^ 40 * 712897 * 2
def baseEnd_712897 : Nat := 325385616131913351919069

theorem tailTrace_712897 : CollatzResearch.WordTrace tailWord_712897 prefixEnd_712897 325385616131913351919069 := by
  unfold tailWord_712897
  simp only [CollatzResearch.WordTrace]
  refine ⟨26001489698303396959448945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17334326465535597972965963 26001489698303396959448945)
  ·
    refine ⟨19501117273727547719586709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26001489698303396959448945 19501117273727547719586709)
    ·
      refine ⟨914114872205978799355627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19501117273727547719586709 914114872205978799355627)
      ·
        refine ⟨1371172308308968199033441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914114872205978799355627 1371172308308968199033441)
        ·
          refine ⟨1028379231231726149275081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371172308308968199033441 1028379231231726149275081)
          ·
            refine ⟨771284423423794611956311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028379231231726149275081 771284423423794611956311)
            ·
              refine ⟨1156926635135691917934467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771284423423794611956311 1156926635135691917934467)
              ·
                refine ⟨1735389952703537876901701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156926635135691917934467 1735389952703537876901701)
                ·
                  refine ⟨325385616131913351919069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735389952703537876901701 325385616131913351919069)
                  ·
                    rfl

theorem cell20_712897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_712897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712897 prefixEnd_712897 := by exact prefixLift 712897
  have htrace : WordTrace (prefixWord ++ tailWord_712897) baseStart_712897 baseEnd_712897 := by
    simpa [prefixWord, tailWord_712897, baseEnd_712897] using wordTrace_append hprefix tailTrace_712897
  have hstable : (prefixWord ++ tailWord_712897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712897).length < 2 ^ (prefixWord ++ tailWord_712897).sum := by decide
  have hdescent : baseEnd_712897 < baseStart_712897 := by decide
  rcases family_descends (prefixWord ++ tailWord_712897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712901 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 2]
def baseStart_712901 : Nat := 118140960795 + 712901 * 2 ^ 59
def prefixEnd_712901 : Nat := 4983230072969 + 3 ^ 40 * 712901 * 2
def baseEnd_712901 : Nat := 325387441840907115785719

theorem tailTrace_712901 : CollatzResearch.WordTrace tailWord_712901 prefixEnd_712901 325387441840907115785719 := by
  unfold tailWord_712901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26001635590288905642594557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17334423726859270428396371 26001635590288905642594557)
  ·
    refine ⟨9750613346358339615972959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26001635590288905642594557 9750613346358339615972959)
    ·
      refine ⟨14625920019537509423959439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9750613346358339615972959 14625920019537509423959439)
      ·
        refine ⟨21938880029306264135939159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14625920019537509423959439 21938880029306264135939159)
        ·
          refine ⟨32908320043959396203908739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21938880029306264135939159 32908320043959396203908739)
          ·
            refine ⟨49362480065939094305863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32908320043959396203908739 49362480065939094305863109)
            ·
              refine ⟨9255465012363580182349333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49362480065939094305863109 9255465012363580182349333)
              ·
                refine ⟨433849922454542821047625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9255465012363580182349333 433849922454542821047625)
                ·
                  refine ⟨325387441840907115785719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433849922454542821047625 325387441840907115785719)
                  ·
                    rfl

theorem cell20_712901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_712901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712901 prefixEnd_712901 := by exact prefixLift 712901
  have htrace : WordTrace (prefixWord ++ tailWord_712901) baseStart_712901 baseEnd_712901 := by
    simpa [prefixWord, tailWord_712901, baseEnd_712901] using wordTrace_append hprefix tailTrace_712901
  have hstable : (prefixWord ++ tailWord_712901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712901).length < 2 ^ (prefixWord ++ tailWord_712901).sum := by decide
  have hdescent : baseEnd_712901 < baseStart_712901 := by decide
  rcases family_descends (prefixWord ++ tailWord_712901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712922 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_712922 : Nat := 118140960795 + 712922 * 2 ^ 59
def prefixEnd_712922 : Nat := 4983230072969 + 3 ^ 40 * 712922 * 2
def baseEnd_712922 : Nat := 325397026813124376085633

theorem tailTrace_712922 : CollatzResearch.WordTrace tailWord_712922 prefixEnd_712922 325397026813124376085633 := by
  unfold tailWord_712922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500600380803206557277255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17334934348808550819406013 6500600380803206557277255)
  ·
    refine ⟨9750900571204809835915883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500600380803206557277255 9750900571204809835915883)
    ·
      refine ⟨14626350856807214753873825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9750900571204809835915883 14626350856807214753873825)
      ·
        refine ⟨10969763142605411065405369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14626350856807214753873825 10969763142605411065405369)
        ·
          refine ⟨8227322356954058299054027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10969763142605411065405369 8227322356954058299054027)
          ·
            refine ⟨12340983535431087448581041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227322356954058299054027 12340983535431087448581041)
            ·
              refine ⟨9255737651573315586435781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12340983535431087448581041 9255737651573315586435781)
              ·
                refine ⟨1735450809669996672456709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9255737651573315586435781 1735450809669996672456709)
                ·
                  refine ⟨325397026813124376085633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735450809669996672456709 325397026813124376085633)
                  ·
                    rfl

theorem cell20_712922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_712922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712922 prefixEnd_712922 := by exact prefixLift 712922
  have htrace : WordTrace (prefixWord ++ tailWord_712922) baseStart_712922 baseEnd_712922 := by
    simpa [prefixWord, tailWord_712922, baseEnd_712922] using wordTrace_append hprefix tailTrace_712922
  have hstable : (prefixWord ++ tailWord_712922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712922).length < 2 ^ (prefixWord ++ tailWord_712922).sum := by decide
  have hdescent : baseEnd_712922 < baseStart_712922 := by decide
  rcases family_descends (prefixWord ++ tailWord_712922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712929 : List Nat := [1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_712929 : Nat := 118140960795 + 712929 * 2 ^ 59
def prefixEnd_712929 : Nat := 4983230072969 + 3 ^ 40 * 712929 * 2
def baseEnd_712929 : Nat := 108466740601287820950757

theorem tailTrace_712929 : CollatzResearch.WordTrace tailWord_712929 prefixEnd_712929 108466740601287820950757 := by
  unfold tailWord_712929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002656834187466424613841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17335104556124977616409227 26002656834187466424613841)
  ·
    refine ⟨19501992625640599818460381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26002656834187466424613841 19501992625640599818460381)
    ·
      refine ⟨7313247234615224931922643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19501992625640599818460381 7313247234615224931922643)
      ·
        refine ⟨10969870851922837397883965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313247234615224931922643 10969870851922837397883965)
        ·
          refine ⟨4113701569471064024206487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10969870851922837397883965 4113701569471064024206487)
          ·
            refine ⟨6170552354206596036309731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113701569471064024206487 6170552354206596036309731)
            ·
              refine ⟨9255828531309894054464597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170552354206596036309731 9255828531309894054464597)
              ·
                refine ⟨108466740601287820950757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9255828531309894054464597 108466740601287820950757)
                ·
                  rfl

theorem cell20_712929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_712929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712929 prefixEnd_712929 := by exact prefixLift 712929
  have htrace : WordTrace (prefixWord ++ tailWord_712929) baseStart_712929 baseEnd_712929 := by
    simpa [prefixWord, tailWord_712929, baseEnd_712929] using wordTrace_append hprefix tailTrace_712929
  have hstable : (prefixWord ++ tailWord_712929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712929).length < 2 ^ (prefixWord ++ tailWord_712929).sum := by decide
  have hdescent : baseEnd_712929 < baseStart_712929 := by decide
  rcases family_descends (prefixWord ++ tailWord_712929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712939 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 2]
def baseStart_712939 : Nat := 118140960795 + 712939 * 2 ^ 59
def prefixEnd_712939 : Nat := 4983230072969 + 3 ^ 40 * 712939 * 2
def baseEnd_712939 : Nat := 325404786076347872518897

theorem tailTrace_712939 : CollatzResearch.WordTrace tailWord_712939 prefixEnd_712939 325404786076347872518897 := by
  unfold tailWord_712939
  simp only [CollatzResearch.WordTrace]
  refine ⟨26003021564151238132477871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17335347709434158754985247 26003021564151238132477871)
  ·
    refine ⟨39004532346226857198716807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26003021564151238132477871 39004532346226857198716807)
    ·
      refine ⟨58506798519340285798075211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39004532346226857198716807 58506798519340285798075211)
      ·
        refine ⟨87760197779010428697112817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58506798519340285798075211 87760197779010428697112817)
        ·
          refine ⟨65820148334257821522834613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87760197779010428697112817 65820148334257821522834613)
          ·
            refine ⟨6170638906336670767765745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65820148334257821522834613 6170638906336670767765745)
            ·
              refine ⟨4627979179752503075824309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170638906336670767765745 4627979179752503075824309)
              ·
                refine ⟨433873048101797163358529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4627979179752503075824309 433873048101797163358529)
                ·
                  refine ⟨325404786076347872518897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433873048101797163358529 325404786076347872518897)
                  ·
                    rfl

theorem cell20_712939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2].length) (baseStart_712939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712939 prefixEnd_712939 := by exact prefixLift 712939
  have htrace : WordTrace (prefixWord ++ tailWord_712939) baseStart_712939 baseEnd_712939 := by
    simpa [prefixWord, tailWord_712939, baseEnd_712939] using wordTrace_append hprefix tailTrace_712939
  have hstable : (prefixWord ++ tailWord_712939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712939).length < 2 ^ (prefixWord ++ tailWord_712939).sum := by decide
  have hdescent : baseEnd_712939 < baseStart_712939 := by decide
  rcases family_descends (prefixWord ++ tailWord_712939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712956 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_712956 : Nat := 118140960795 + 712956 * 2 ^ 59
def prefixEnd_712956 : Nat := 4983230072969 + 3 ^ 40 * 712956 * 2
def baseEnd_712956 : Nat := 325412545339571368952161

theorem tailTrace_712956 : CollatzResearch.WordTrace tailWord_712956 prefixEnd_712956 325412545339571368952161 := by
  unfold tailWord_712956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13001820802544825017923361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17335761070059766690564481 13001820802544825017923361)
  ·
    refine ⟨9751365601908618763442521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13001820802544825017923361 9751365601908618763442521)
    ·
      refine ⟨7313524201431464072581891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9751365601908618763442521 7313524201431464072581891)
      ·
        refine ⟨10970286302147196108872837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313524201431464072581891 10970286302147196108872837)
        ·
          refine ⟨2056928681652599270413657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10970286302147196108872837 2056928681652599270413657)
          ·
            refine ⟨1542696511239449452810243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056928681652599270413657 1542696511239449452810243)
            ·
              refine ⟨2314044766859174179215365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542696511239449452810243 2314044766859174179215365)
              ·
                refine ⟨433883393786095158602881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2314044766859174179215365 433883393786095158602881)
                ·
                  refine ⟨325412545339571368952161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433883393786095158602881 325412545339571368952161)
                  ·
                    rfl

theorem cell20_712956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_712956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712956 prefixEnd_712956 := by exact prefixLift 712956
  have htrace : WordTrace (prefixWord ++ tailWord_712956) baseStart_712956 baseEnd_712956 := by
    simpa [prefixWord, tailWord_712956, baseEnd_712956] using wordTrace_append hprefix tailTrace_712956
  have hstable : (prefixWord ++ tailWord_712956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712956).length < 2 ^ (prefixWord ++ tailWord_712956).sum := by decide
  have hdescent : baseEnd_712956 < baseStart_712956 := by decide
  rcases family_descends (prefixWord ++ tailWord_712956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712984 : List Nat := [2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_712984 : Nat := 118140960795 + 712984 * 2 ^ 59
def prefixEnd_712984 : Nat := 4983230072969 + 3 ^ 40 * 712984 * 2
def baseEnd_712984 : Nat := 108475108434175905339571

theorem tailTrace_712984 : CollatzResearch.WordTrace tailWord_712984 prefixEnd_712984 108475108434175905339571 := by
  unfold tailWord_712984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002331424494105408933003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17336441899325473878577337 13002331424494105408933003)
  ·
    refine ⟨19503497136741158113399505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13002331424494105408933003 19503497136741158113399505)
    ·
      refine ⟨14627622852555868585049629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19503497136741158113399505 14627622852555868585049629)
      ·
        refine ⟨5485358569708450719393611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14627622852555868585049629 5485358569708450719393611)
        ·
          refine ⟨8228037854562676079090417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485358569708450719393611 8228037854562676079090417)
          ·
            refine ⟨6171028390922007059317813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8228037854562676079090417 6171028390922007059317813)
            ·
              refine ⟨578533911648938161811045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6171028390922007059317813 578533911648938161811045)
              ·
                refine ⟨108475108434175905339571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578533911648938161811045 108475108434175905339571)
                ·
                  rfl

theorem cell20_712984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_712984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712984 prefixEnd_712984 := by exact prefixLift 712984
  have htrace : WordTrace (prefixWord ++ tailWord_712984) baseStart_712984 baseEnd_712984 := by
    simpa [prefixWord, tailWord_712984, baseEnd_712984] using wordTrace_append hprefix tailTrace_712984
  have hstable : (prefixWord ++ tailWord_712984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712984).length < 2 ^ (prefixWord ++ tailWord_712984).sum := by decide
  have hdescent : baseEnd_712984 < baseStart_712984 := by decide
  rcases family_descends (prefixWord ++ tailWord_712984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712990 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_712990 : Nat := 118140960795 + 712990 * 2 ^ 59
def prefixEnd_712990 : Nat := 4983230072969 + 3 ^ 40 * 712990 * 2
def baseEnd_712990 : Nat := 325428063866018361818689

theorem tailTrace_712990 : CollatzResearch.WordTrace tailWord_712990 prefixEnd_712990 325428063866018361818689 := by
  unfold tailWord_712990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250610210870809230323053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17336587791310982561722949 3250610210870809230323053)
  ·
    refine ⟨1218978829076553461371145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3250610210870809230323053 1218978829076553461371145)
    ·
      refine ⟨914234121807415096028359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218978829076553461371145 914234121807415096028359)
      ·
        refine ⟨1371351182711122644042539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914234121807415096028359 1371351182711122644042539)
        ·
          refine ⟨2057026774066683966063809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371351182711122644042539 2057026774066683966063809)
          ·
            refine ⟨1542770080550012974547857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057026774066683966063809 1542770080550012974547857)
            ·
              refine ⟨1157077560412509730910893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542770080550012974547857 1157077560412509730910893)
              ·
                refine ⟨433904085154691149091585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157077560412509730910893 433904085154691149091585)
                ·
                  refine ⟨325428063866018361818689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433904085154691149091585 325428063866018361818689)
                  ·
                    rfl

theorem cell20_712990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_712990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712990 prefixEnd_712990 := by exact prefixLift 712990
  have htrace : WordTrace (prefixWord ++ tailWord_712990) baseStart_712990 baseEnd_712990 := by
    simpa [prefixWord, tailWord_712990, baseEnd_712990] using wordTrace_append hprefix tailTrace_712990
  have hstable : (prefixWord ++ tailWord_712990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712990).length < 2 ^ (prefixWord ++ tailWord_712990).sum := by decide
  have hdescent : baseEnd_712990 < baseStart_712990 := by decide
  rcases family_descends (prefixWord ++ tailWord_712990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712994 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_712994 : Nat := 118140960795 + 712994 * 2 ^ 59
def prefixEnd_712994 : Nat := 4983230072969 + 3 ^ 40 * 712994 * 2
def baseEnd_712994 : Nat := 325429889575012125685339

theorem tailTrace_712994 : CollatzResearch.WordTrace tailWord_712994 prefixEnd_712994 325429889575012125685339 := by
  unfold tailWord_712994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501256894737995631432509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17336685052634655017153357 6501256894737995631432509)
  ·
    refine ⟨2437971335526748361787191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6501256894737995631432509 2437971335526748361787191)
    ·
      refine ⟨3656957003290122542680787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2437971335526748361787191 3656957003290122542680787)
      ·
        refine ⟨5485435504935183814021181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656957003290122542680787 5485435504935183814021181)
        ·
          refine ⟨2057038314350693930257943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5485435504935183814021181 2057038314350693930257943)
          ·
            refine ⟨3085557471526040895386915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057038314350693930257943 3085557471526040895386915)
            ·
              refine ⟨4628336207289061343080373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085557471526040895386915 4628336207289061343080373)
              ·
                refine ⟨433906519433349500913785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4628336207289061343080373 433906519433349500913785)
                ·
                  refine ⟨325429889575012125685339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433906519433349500913785 325429889575012125685339)
                  ·
                    rfl

theorem cell20_712994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_712994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_712994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_712994 prefixEnd_712994 := by exact prefixLift 712994
  have htrace : WordTrace (prefixWord ++ tailWord_712994) baseStart_712994 baseEnd_712994 := by
    simpa [prefixWord, tailWord_712994, baseEnd_712994] using wordTrace_append hprefix tailTrace_712994
  have hstable : (prefixWord ++ tailWord_712994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712994).length < 2 ^ (prefixWord ++ tailWord_712994).sum := by decide
  have hdescent : baseEnd_712994 < baseStart_712994 := by decide
  rcases family_descends (prefixWord ++ tailWord_712994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713036 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_713036 : Nat := 118140960795 + 713036 * 2 ^ 59
def prefixEnd_713036 : Nat := 4983230072969 + 3 ^ 40 * 713036 * 2
def baseEnd_713036 : Nat := 325449059519446646285167

theorem tailTrace_713036 : CollatzResearch.WordTrace tailWord_713036 prefixEnd_713036 325449059519446646285167 := by
  unfold tailWord_713036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003279722399911849379481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17337706296533215799172641 13003279722399911849379481)
  ·
    refine ⟨9752459791799933887034611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003279722399911849379481 9752459791799933887034611)
    ·
      refine ⟨14628689687699900830551917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9752459791799933887034611 14628689687699900830551917)
      ·
        refine ⟨5485758632887462811456969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14628689687699900830551917 5485758632887462811456969)
        ·
          refine ⟨4114318974665597108592727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485758632887462811456969 4114318974665597108592727)
          ·
            refine ⟨6171478461998395662889091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114318974665597108592727 6171478461998395662889091)
            ·
              refine ⟨9257217692997593494333637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171478461998395662889091 9257217692997593494333637)
              ·
                refine ⟨1735728317437048780187557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9257217692997593494333637 1735728317437048780187557)
                ·
                  refine ⟨325449059519446646285167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735728317437048780187557 325449059519446646285167)
                  ·
                    rfl

theorem cell20_713036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_713036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713036 prefixEnd_713036 := by exact prefixLift 713036
  have htrace : WordTrace (prefixWord ++ tailWord_713036) baseStart_713036 baseEnd_713036 := by
    simpa [prefixWord, tailWord_713036, baseEnd_713036] using wordTrace_append hprefix tailTrace_713036
  have hstable : (prefixWord ++ tailWord_713036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713036).length < 2 ^ (prefixWord ++ tailWord_713036).sum := by decide
  have hdescent : baseEnd_713036 < baseStart_713036 := by decide
  rcases family_descends (prefixWord ++ tailWord_713036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713121 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 2]
def baseStart_713121 : Nat := 118140960795 + 713121 * 2 ^ 59
def prefixEnd_713121 : Nat := 4983230072969 + 3 ^ 40 * 713121 * 2
def baseEnd_713121 : Nat := 325487855835564128451487

theorem tailTrace_713121 : CollatzResearch.WordTrace tailWord_713121 prefixEnd_713121 325487855835564128451487 := by
  unfold tailWord_713121
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009659649491883215603217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17339773099661255477068811 26009659649491883215603217)
  ·
    refine ⟨19507244737118912411702413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26009659649491883215603217 19507244737118912411702413)
    ·
      refine ⟨7315216776419592154388405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19507244737118912411702413 7315216776419592154388405)
      ·
        refine ⟨685801572789336764473913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7315216776419592154388405 685801572789336764473913)
        ·
          refine ⟨514351179592002573355435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685801572789336764473913 514351179592002573355435)
          ·
            refine ⟨771526769388003860033153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514351179592002573355435 771526769388003860033153)
            ·
              refine ⟨578645077041002895024865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771526769388003860033153 578645077041002895024865)
              ·
                refine ⟨433983807780752171268649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578645077041002895024865 433983807780752171268649)
                ·
                  refine ⟨325487855835564128451487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433983807780752171268649 325487855835564128451487)
                  ·
                    rfl

theorem cell20_713121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_713121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713121 prefixEnd_713121 := by exact prefixLift 713121
  have htrace : WordTrace (prefixWord ++ tailWord_713121) baseStart_713121 baseEnd_713121 := by
    simpa [prefixWord, tailWord_713121, baseEnd_713121] using wordTrace_append hprefix tailTrace_713121
  have hstable : (prefixWord ++ tailWord_713121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713121).length < 2 ^ (prefixWord ++ tailWord_713121).sum := by decide
  have hdescent : baseEnd_713121 < baseStart_713121 := by decide
  rcases family_descends (prefixWord ++ tailWord_713121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713122 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_713122 : Nat := 118140960795 + 713122 * 2 ^ 59
def prefixEnd_713122 : Nat := 4983230072969 + 3 ^ 40 * 713122 * 2
def baseEnd_713122 : Nat := 325488312262812569418149

theorem tailTrace_713122 : CollatzResearch.WordTrace tailWord_713122 prefixEnd_713122 325488312262812569418149 := by
  unfold tailWord_713122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502424030622065096597405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17339797414992173590926413 6502424030622065096597405)
  ·
    refine ⟨2438409011483274411224027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6502424030622065096597405 2438409011483274411224027)
    ·
      refine ⟨3657613517224911616836041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438409011483274411224027 3657613517224911616836041)
      ·
        refine ⟨2743210137918683712627031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657613517224911616836041 2743210137918683712627031)
        ·
          refine ⟨4114815206878025568940547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743210137918683712627031 4114815206878025568940547)
          ·
            refine ⟨6172222810317038353410821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114815206878025568940547 6172222810317038353410821)
            ·
              refine ⟨1157291776934444691264529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6172222810317038353410821 1157291776934444691264529)
              ·
                refine ⟨867968832700833518448397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157291776934444691264529 867968832700833518448397)
                ·
                  refine ⟨325488312262812569418149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867968832700833518448397 325488312262812569418149)
                  ·
                    rfl

theorem cell20_713122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_713122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713122 prefixEnd_713122 := by exact prefixLift 713122
  have htrace : WordTrace (prefixWord ++ tailWord_713122) baseStart_713122 baseEnd_713122 := by
    simpa [prefixWord, tailWord_713122, baseEnd_713122] using wordTrace_append hprefix tailTrace_713122
  have hstable : (prefixWord ++ tailWord_713122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713122).length < 2 ^ (prefixWord ++ tailWord_713122).sum := by decide
  have hdescent : baseEnd_713122 < baseStart_713122 := by decide
  rcases family_descends (prefixWord ++ tailWord_713122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713143 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_713143 : Nat := 118140960795 + 713143 * 2 ^ 59
def prefixEnd_713143 : Nat := 4983230072969 + 3 ^ 40 * 713143 * 2
def baseEnd_713143 : Nat := 325497897235029829718063

theorem tailTrace_713143 : CollatzResearch.WordTrace tailWord_713143 prefixEnd_713143 325497897235029829718063 := by
  unfold tailWord_713143
  simp only [CollatzResearch.WordTrace]
  refine ⟨26010462055412180972904083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17340308036941453981936055 26010462055412180972904083)
  ·
    refine ⟨39015693083118271459356125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26010462055412180972904083 39015693083118271459356125)
    ·
      refine ⟨14630884906169351797258547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39015693083118271459356125 14630884906169351797258547)
      ·
        refine ⟨21946327359254027695887821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630884906169351797258547 21946327359254027695887821)
        ·
          refine ⟨8229872759720260385957933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21946327359254027695887821 8229872759720260385957933)
          ·
            refine ⟨3086202284895097644734225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8229872759720260385957933 3086202284895097644734225)
            ·
              refine ⟨2314651713671323233550669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086202284895097644734225 2314651713671323233550669)
              ·
                refine ⟨867994392626746212581501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2314651713671323233550669 867994392626746212581501)
                ·
                  refine ⟨325497897235029829718063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867994392626746212581501 325497897235029829718063)
                  ·
                    rfl

theorem cell20_713143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_713143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713143 prefixEnd_713143 := by exact prefixLift 713143
  have htrace : WordTrace (prefixWord ++ tailWord_713143) baseStart_713143 baseEnd_713143 := by
    simpa [prefixWord, tailWord_713143, baseEnd_713143] using wordTrace_append hprefix tailTrace_713143
  have hstable : (prefixWord ++ tailWord_713143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713143).length < 2 ^ (prefixWord ++ tailWord_713143).sum := by decide
  have hdescent : baseEnd_713143 < baseStart_713143 := by decide
  rcases family_descends (prefixWord ++ tailWord_713143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713150 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_713150 : Nat := 118140960795 + 713150 * 2 ^ 59
def prefixEnd_713150 : Nat := 4983230072969 + 3 ^ 40 * 713150 * 2
def baseEnd_713150 : Nat := 325501092225768916484701

theorem tailTrace_713150 : CollatzResearch.WordTrace tailWord_713150 prefixEnd_713150 325501092225768916484701 := by
  unfold tailWord_713150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251339670798352646051113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17340478244257880778939269 3251339670798352646051113)
  ·
    refine ⟨2438504753098764484538335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3251339670798352646051113 2438504753098764484538335)
    ·
      refine ⟨3657757129648146726807503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438504753098764484538335 3657757129648146726807503)
      ·
        refine ⟨5486635694472220090211255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657757129648146726807503 5486635694472220090211255)
        ·
          refine ⟨8229953541708330135316883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486635694472220090211255 8229953541708330135316883)
          ·
            refine ⟨12344930312562495202975325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229953541708330135316883 12344930312562495202975325)
            ·
              refine ⟨4629348867210935701115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12344930312562495202975325 4629348867210935701115747)
              ·
                refine ⟨6944023300816403551673621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629348867210935701115747 6944023300816403551673621)
                ·
                  refine ⟨325501092225768916484701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6944023300816403551673621 325501092225768916484701)
                  ·
                    rfl

theorem cell20_713150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_713150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713150 prefixEnd_713150 := by exact prefixLift 713150
  have htrace : WordTrace (prefixWord ++ tailWord_713150) baseStart_713150 baseEnd_713150 := by
    simpa [prefixWord, tailWord_713150, baseEnd_713150] using wordTrace_append hprefix tailTrace_713150
  have hstable : (prefixWord ++ tailWord_713150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713150).length < 2 ^ (prefixWord ++ tailWord_713150).sum := by decide
  have hdescent : baseEnd_713150 < baseStart_713150 := by decide
  rcases family_descends (prefixWord ++ tailWord_713150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713174 : List Nat := [5, 2, 1, 1, 1, 1, 9]
def baseStart_713174 : Nat := 118140960795 + 713174 * 2 ^ 59
def prefixEnd_713174 : Nat := 4983230072969 + 3 ^ 40 * 713174 * 2
def baseEnd_713174 : Nat := 36168005164414611076067

theorem tailTrace_713174 : CollatzResearch.WordTrace tailWord_713174 prefixEnd_713174 36168005164414611076067 := by
  unfold tailWord_713174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625724544893742079205161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17341061812199915511521717 1625724544893742079205161)
  ·
    refine ⟨1219293408670306559403871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625724544893742079205161 1219293408670306559403871)
    ·
      refine ⟨1828940113005459839105807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219293408670306559403871 1828940113005459839105807)
      ·
        refine ⟨2743410169508189758658711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828940113005459839105807 2743410169508189758658711)
        ·
          refine ⟨4115115254262284637988067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743410169508189758658711 4115115254262284637988067)
          ·
            refine ⟨6172672881393426956982101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115115254262284637988067 6172672881393426956982101)
            ·
              refine ⟨36168005164414611076067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6172672881393426956982101 36168005164414611076067)
              ·
                rfl

theorem cell20_713174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_713174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713174 prefixEnd_713174 := by exact prefixLift 713174
  have htrace : WordTrace (prefixWord ++ tailWord_713174) baseStart_713174 baseEnd_713174 := by
    simpa [prefixWord, tailWord_713174, baseEnd_713174] using wordTrace_append hprefix tailTrace_713174
  have hstable : (prefixWord ++ tailWord_713174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713174).length < 2 ^ (prefixWord ++ tailWord_713174).sum := by decide
  have hdescent : baseEnd_713174 < baseStart_713174 := by decide
  rcases family_descends (prefixWord ++ tailWord_713174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713181 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_713181 : Nat := 118140960795 + 713181 * 2 ^ 59
def prefixEnd_713181 : Nat := 4983230072969 + 3 ^ 40 * 713181 * 2
def baseEnd_713181 : Nat := 325515241470470586451241

theorem tailTrace_713181 : CollatzResearch.WordTrace tailWord_713181 prefixEnd_713181 325515241470470586451241 := by
  unfold tailWord_713181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26011848029274513462787397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17341232019516342308524931 26011848029274513462787397)
  ·
    refine ⟨4877221505488971274272637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26011848029274513462787397 4877221505488971274272637)
    ·
      refine ⟨1828958064558364227852239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4877221505488971274272637 1828958064558364227852239)
      ·
        refine ⟨2743437096837546341778359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828958064558364227852239 2743437096837546341778359)
        ·
          refine ⟨4115155645256319512667539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743437096837546341778359 4115155645256319512667539)
          ·
            refine ⟨6172733467884479269001309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115155645256319512667539 6172733467884479269001309)
            ·
              refine ⟨2314775050456679725875491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6172733467884479269001309 2314775050456679725875491)
              ·
                refine ⟨3472162575685019588813237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314775050456679725875491 3472162575685019588813237)
                ·
                  refine ⟨325515241470470586451241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472162575685019588813237 325515241470470586451241)
                  ·
                    rfl

theorem cell20_713181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_713181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713181 prefixEnd_713181 := by exact prefixLift 713181
  have htrace : WordTrace (prefixWord ++ tailWord_713181) baseStart_713181 baseEnd_713181 := by
    simpa [prefixWord, tailWord_713181, baseEnd_713181] using wordTrace_append hprefix tailTrace_713181
  have hstable : (prefixWord ++ tailWord_713181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713181).length < 2 ^ (prefixWord ++ tailWord_713181).sum := by decide
  have hdescent : baseEnd_713181 < baseStart_713181 := by decide
  rcases family_descends (prefixWord ++ tailWord_713181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713218 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_713218 : Nat := 118140960795 + 713218 * 2 ^ 59
def prefixEnd_713218 : Nat := 4983230072969 + 3 ^ 40 * 713218 * 2
def baseEnd_713218 : Nat := 325532129278662902217757

theorem tailTrace_713218 : CollatzResearch.WordTrace tailWord_713218 prefixEnd_713218 325532129278662902217757 := by
  unfold tailWord_713218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503299382535117195471077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17342131686760312521256205 6503299382535117195471077)
  ·
    refine ⟨1219368634225334474150827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6503299382535117195471077 1219368634225334474150827)
    ·
      refine ⟨1829052951338001711226241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219368634225334474150827 1829052951338001711226241)
      ·
        refine ⟨1371789713503501283419681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829052951338001711226241 1371789713503501283419681)
        ·
          refine ⟨1028842285127625962564761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371789713503501283419681 1028842285127625962564761)
          ·
            refine ⟨771631713845719471923571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028842285127625962564761 771631713845719471923571)
            ·
              refine ⟨1157447570768579207885357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771631713845719471923571 1157447570768579207885357)
              ·
                refine ⟨434042839038217202957009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157447570768579207885357 434042839038217202957009)
                ·
                  refine ⟨325532129278662902217757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434042839038217202957009 325532129278662902217757)
                  ·
                    rfl

theorem cell20_713218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_713218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713218 prefixEnd_713218 := by exact prefixLift 713218
  have htrace : WordTrace (prefixWord ++ tailWord_713218) baseStart_713218 baseEnd_713218 := by
    simpa [prefixWord, tailWord_713218, baseEnd_713218] using wordTrace_append hprefix tailTrace_713218
  have hstable : (prefixWord ++ tailWord_713218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713218).length < 2 ^ (prefixWord ++ tailWord_713218).sum := by decide
  have hdescent : baseEnd_713218 < baseStart_713218 := by decide
  rcases family_descends (prefixWord ++ tailWord_713218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713229 : List Nat := [1, 7, 1, 1, 1, 1, 8]
def baseStart_713229 : Nat := 118140960795 + 713229 * 2 ^ 59
def prefixEnd_713229 : Nat := 4983230072969 + 3 ^ 40 * 713229 * 2
def baseEnd_713229 : Nat := 36170794442043972539005

theorem tailTrace_713229 : CollatzResearch.WordTrace tailWord_713229 prefixEnd_713229 36170794442043972539005 := by
  unfold tailWord_713229
  simp only [CollatzResearch.WordTrace]
  refine ⟨26013598733100617660534741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17342399155400411773689827 26013598733100617660534741)
  ·
    refine ⟨609693720307045726418783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26013598733100617660534741 609693720307045726418783)
    ·
      refine ⟨914540580460568589628175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609693720307045726418783 914540580460568589628175)
      ·
        refine ⟨1371810870690852884442263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914540580460568589628175 1371810870690852884442263)
        ·
          refine ⟨2057716306036279326663395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371810870690852884442263 2057716306036279326663395)
          ·
            refine ⟨3086574459054418989995093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057716306036279326663395 3086574459054418989995093)
            ·
              refine ⟨36170794442043972539005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3086574459054418989995093 36170794442043972539005)
              ·
                rfl

theorem cell20_713229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_713229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713229 prefixEnd_713229 := by exact prefixLift 713229
  have htrace : WordTrace (prefixWord ++ tailWord_713229) baseStart_713229 baseEnd_713229 := by
    simpa [prefixWord, tailWord_713229, baseEnd_713229] using wordTrace_append hprefix tailTrace_713229
  have hstable : (prefixWord ++ tailWord_713229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713229).length < 2 ^ (prefixWord ++ tailWord_713229).sum := by decide
  have hdescent : baseEnd_713229 < baseStart_713229 := by decide
  rcases family_descends (prefixWord ++ tailWord_713229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713236 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_713236 : Nat := 118140960795 + 713236 * 2 ^ 59
def prefixEnd_713236 : Nat := 4983230072969 + 3 ^ 40 * 713236 * 2
def baseEnd_713236 : Nat := 325540344969134839617683

theorem tailTrace_713236 : CollatzResearch.WordTrace tailWord_713236 prefixEnd_713236 325540344969134839617683 := by
  unfold tailWord_713236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006927022037628928019781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17342569362716838570693041 13006927022037628928019781)
  ·
    refine ⟨2438798816632055424003709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13006927022037628928019781 2438798816632055424003709)
    ·
      refine ⟨914549556237020784001391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2438798816632055424003709 914549556237020784001391)
      ·
        refine ⟨1371824334355531176002087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914549556237020784001391 1371824334355531176002087)
        ·
          refine ⟨2057736501533296764003131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371824334355531176002087 2057736501533296764003131)
          ·
            refine ⟨3086604752299945146004697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057736501533296764003131 3086604752299945146004697)
            ·
              refine ⟨2314953564224958859503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086604752299945146004697 2314953564224958859503523)
              ·
                refine ⟨3472430346337438289255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314953564224958859503523 3472430346337438289255285)
                ·
                  refine ⟨325540344969134839617683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472430346337438289255285 325540344969134839617683)
                  ·
                    rfl

theorem cell20_713236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_713236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713236 prefixEnd_713236 := by exact prefixLift 713236
  have htrace : WordTrace (prefixWord ++ tailWord_713236) baseStart_713236 baseEnd_713236 := by
    simpa [prefixWord, tailWord_713236, baseEnd_713236] using wordTrace_append hprefix tailTrace_713236
  have hstable : (prefixWord ++ tailWord_713236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713236).length < 2 ^ (prefixWord ++ tailWord_713236).sum := by decide
  have hdescent : baseEnd_713236 < baseStart_713236 := by decide
  rcases family_descends (prefixWord ++ tailWord_713236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713239 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 4]
def baseStart_713239 : Nat := 118140960795 + 713239 * 2 ^ 59
def prefixEnd_713239 : Nat := 4983230072969 + 3 ^ 40 * 713239 * 2
def baseEnd_713239 : Nat := 325541714250880162517671

theorem tailTrace_713239 : CollatzResearch.WordTrace tailWord_713239 prefixEnd_713239 325541714250880162517671 := by
  unfold tailWord_713239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26013963463064389368398771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17342642308709592912265847 26013963463064389368398771)
  ·
    refine ⟨39020945194596584052598157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26013963463064389368398771 39020945194596584052598157)
    ·
      refine ⟨14632854447973719019724309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39020945194596584052598157 14632854447973719019724309)
      ·
        refine ⟨685915052248768079049577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14632854447973719019724309 685915052248768079049577)
        ·
          refine ⟨514436289186576059287183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685915052248768079049577 514436289186576059287183)
          ·
            refine ⟨771654433779864088930775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514436289186576059287183 771654433779864088930775)
            ·
              refine ⟨1157481650669796133396163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771654433779864088930775 1157481650669796133396163)
              ·
                refine ⟨1736222476004694200094245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157481650669796133396163 1736222476004694200094245)
                ·
                  refine ⟨325541714250880162517671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736222476004694200094245 325541714250880162517671)
                  ·
                    rfl

theorem cell20_713239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4].length) (baseStart_713239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713239 prefixEnd_713239 := by exact prefixLift 713239
  have htrace : WordTrace (prefixWord ++ tailWord_713239) baseStart_713239 baseEnd_713239 := by
    simpa [prefixWord, tailWord_713239, baseEnd_713239] using wordTrace_append hprefix tailTrace_713239
  have hstable : (prefixWord ++ tailWord_713239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713239).length < 2 ^ (prefixWord ++ tailWord_713239).sum := by decide
  have hdescent : baseEnd_713239 < baseStart_713239 := by decide
  rcases family_descends (prefixWord ++ tailWord_713239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713284 : List Nat := [2, 3, 5, 1, 2, 7]
def baseStart_713284 : Nat := 118140960795 + 713284 * 2 ^ 59
def prefixEnd_713284 : Nat := 4983230072969 + 3 ^ 40 * 713284 * 2
def baseEnd_713284 : Nat := 12057861239891111333981

theorem tailTrace_713284 : CollatzResearch.WordTrace tailWord_713284 prefixEnd_713284 12057861239891111333981 := by
  unfold tailWord_713284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007802373950681026893453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17343736498600908035857937 13007802373950681026893453)
  ·
    refine ⟨4877925890231505385085045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13007802373950681026893453 4877925890231505385085045)
    ·
      refine ⟨457305552209203629851723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4877925890231505385085045 457305552209203629851723)
      ·
        refine ⟨685958328313805444777585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457305552209203629851723 685958328313805444777585)
        ·
          refine ⟨514468746235354083583189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685958328313805444777585 514468746235354083583189)
          ·
            refine ⟨12057861239891111333981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 514468746235354083583189 12057861239891111333981)
            ·
              rfl

theorem cell20_713284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 7].length) (baseStart_713284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713284 prefixEnd_713284 := by exact prefixLift 713284
  have htrace : WordTrace (prefixWord ++ tailWord_713284) baseStart_713284 baseEnd_713284 := by
    simpa [prefixWord, tailWord_713284, baseEnd_713284] using wordTrace_append hprefix tailTrace_713284
  have hstable : (prefixWord ++ tailWord_713284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713284).length < 2 ^ (prefixWord ++ tailWord_713284).sum := by decide
  have hdescent : baseEnd_713284 < baseStart_713284 := by decide
  rcases family_descends (prefixWord ++ tailWord_713284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713346 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_713346 : Nat := 118140960795 + 713346 * 2 ^ 59
def prefixEnd_713346 : Nat := 4983230072969 + 3 ^ 40 * 713346 * 2
def baseEnd_713346 : Nat := 325590551966463345950567

theorem tailTrace_713346 : CollatzResearch.WordTrace tailWord_713346 prefixEnd_713346 325590551966463345950567 := by
  unfold tailWord_713346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504466518419186660635973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17345244049117831095029261 6504466518419186660635973)
  ·
    refine ⟨1219587472203597498869245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6504466518419186660635973 1219587472203597498869245)
    ·
      refine ⟨457345302076349062075967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1219587472203597498869245 457345302076349062075967)
      ·
        refine ⟨686017953114523593113951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457345302076349062075967 686017953114523593113951)
        ·
          refine ⟨1029026929671785389670927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686017953114523593113951 1029026929671785389670927)
          ·
            refine ⟨1543540394507678084506391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029026929671785389670927 1543540394507678084506391)
            ·
              refine ⟨2315310591761517126759587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543540394507678084506391 2315310591761517126759587)
              ·
                refine ⟨3472965887642275690139381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315310591761517126759587 3472965887642275690139381)
                ·
                  refine ⟨325590551966463345950567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472965887642275690139381 325590551966463345950567)
                  ·
                    rfl

theorem cell20_713346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_713346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713346 prefixEnd_713346 := by exact prefixLift 713346
  have htrace : WordTrace (prefixWord ++ tailWord_713346) baseStart_713346 baseEnd_713346 := by
    simpa [prefixWord, tailWord_713346, baseEnd_713346] using wordTrace_append hprefix tailTrace_713346
  have hstable : (prefixWord ++ tailWord_713346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713346).length < 2 ^ (prefixWord ++ tailWord_713346).sum := by decide
  have hdescent : baseEnd_713346 < baseStart_713346 := by decide
  rcases family_descends (prefixWord ++ tailWord_713346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713395 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 2]
def baseStart_713395 : Nat := 118140960795 + 713395 * 2 ^ 59
def prefixEnd_713395 : Nat := 4983230072969 + 3 ^ 40 * 713395 * 2
def baseEnd_713395 : Nat := 325612916901636953317033

theorem tailTrace_713395 : CollatzResearch.WordTrace tailWord_713395 prefixEnd_713395 325612916901636953317033 := by
  unfold tailWord_713395
  simp only [CollatzResearch.WordTrace]
  refine ⟨26019653250499228011077639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17346435500332818674051759 26019653250499228011077639)
  ·
    refine ⟨39029479875748842016616459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26019653250499228011077639 39029479875748842016616459)
    ·
      refine ⟨58544219813623263024924689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39029479875748842016616459 58544219813623263024924689)
      ·
        refine ⟨43908164860217447268693517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58544219813623263024924689 43908164860217447268693517)
        ·
          refine ⟨16465561822581542725760069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43908164860217447268693517 16465561822581542725760069)
          ·
            refine ⟨3087292841734039261080013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16465561822581542725760069 3087292841734039261080013)
            ·
              refine ⟨1157734815650264722905005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3087292841734039261080013 1157734815650264722905005)
              ·
                refine ⟨434150555868849271089377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157734815650264722905005 434150555868849271089377)
                ·
                  refine ⟨325612916901636953317033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434150555868849271089377 325612916901636953317033)
                  ·
                    rfl

theorem cell20_713395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 2].length) (baseStart_713395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713395 prefixEnd_713395 := by exact prefixLift 713395
  have htrace : WordTrace (prefixWord ++ tailWord_713395) baseStart_713395 baseEnd_713395 := by
    simpa [prefixWord, tailWord_713395, baseEnd_713395] using wordTrace_append hprefix tailTrace_713395
  have hstable : (prefixWord ++ tailWord_713395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713395).length < 2 ^ (prefixWord ++ tailWord_713395).sum := by decide
  have hdescent : baseEnd_713395 < baseStart_713395 := by decide
  rcases family_descends (prefixWord ++ tailWord_713395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713398 : List Nat := [5, 1, 3, 1, 3, 1, 6]
def baseStart_713398 : Nat := 118140960795 + 713398 * 2 ^ 59
def prefixEnd_713398 : Nat := 4983230072969 + 3 ^ 40 * 713398 * 2
def baseEnd_713398 : Nat := 36179365131486919579669

theorem tailTrace_713398 : CollatzResearch.WordTrace tailWord_713398 prefixEnd_713398 36179365131486919579669 := by
  unfold tailWord_713398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626235166843022470214803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17346508446325573015624565 1626235166843022470214803)
  ·
    refine ⟨2439352750264533705322205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626235166843022470214803 2439352750264533705322205)
    ·
      refine ⟨914757281349200139495827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2439352750264533705322205 914757281349200139495827)
      ·
        refine ⟨1372135922023800209243741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914757281349200139495827 1372135922023800209243741)
        ·
          refine ⟨514550970758925078466403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372135922023800209243741 514550970758925078466403)
          ·
            refine ⟨771826456138387617699605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514550970758925078466403 771826456138387617699605)
            ·
              refine ⟨36179365131486919579669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 771826456138387617699605 36179365131486919579669)
              ·
                rfl

theorem cell20_713398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_713398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713398 prefixEnd_713398 := by exact prefixLift 713398
  have htrace : WordTrace (prefixWord ++ tailWord_713398) baseStart_713398 baseEnd_713398 := by
    simpa [prefixWord, tailWord_713398, baseEnd_713398] using wordTrace_append hprefix tailTrace_713398
  have hstable : (prefixWord ++ tailWord_713398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713398).length < 2 ^ (prefixWord ++ tailWord_713398).sum := by decide
  have hdescent : baseEnd_713398 < baseStart_713398 := by decide
  rcases family_descends (prefixWord ++ tailWord_713398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713416 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_713416 : Nat := 118140960795 + 713416 * 2 ^ 59
def prefixEnd_713416 : Nat := 4983230072969 + 3 ^ 40 * 713416 * 2
def baseEnd_713416 : Nat := 325622501873854213616947

theorem tailTrace_713416 : CollatzResearch.WordTrace tailWord_713416 prefixEnd_713416 325622501873854213616947 := by
  unfold tailWord_713416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010209591711574298796051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17346946122282099065061401 13010209591711574298796051)
  ·
    refine ⟨19515314387567361448194077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13010209591711574298796051 19515314387567361448194077)
    ·
      refine ⟨7318242895337760543072779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19515314387567361448194077 7318242895337760543072779)
      ·
        refine ⟨10977364343006640814609169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318242895337760543072779 10977364343006640814609169)
        ·
          refine ⟨8233023257254980610956877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10977364343006640814609169 8233023257254980610956877)
          ·
            refine ⟨3087383721470617729108829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8233023257254980610956877 3087383721470617729108829)
            ·
              refine ⟨1157768895551481648415811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3087383721470617729108829 1157768895551481648415811)
              ·
                refine ⟨1736653343327222472623717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157768895551481648415811 1736653343327222472623717)
                ·
                  refine ⟨325622501873854213616947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736653343327222472623717 325622501873854213616947)
                  ·
                    rfl

theorem cell20_713416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_713416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713416 prefixEnd_713416 := by exact prefixLift 713416
  have htrace : WordTrace (prefixWord ++ tailWord_713416) baseStart_713416 baseEnd_713416 := by
    simpa [prefixWord, tailWord_713416, baseEnd_713416] using wordTrace_append hprefix tailTrace_713416
  have hstable : (prefixWord ++ tailWord_713416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713416).length < 2 ^ (prefixWord ++ tailWord_713416).sum := by decide
  have hdescent : baseEnd_713416 < baseStart_713416 := by decide
  rcases family_descends (prefixWord ++ tailWord_713416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713426 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_713426 : Nat := 118140960795 + 713426 * 2 ^ 59
def prefixEnd_713426 : Nat := 4983230072969 + 3 ^ 40 * 713426 * 2
def baseEnd_713426 : Nat := 325627066146338623283573

theorem tailTrace_713426 : CollatzResearch.WordTrace tailWord_713426 prefixEnd_713426 325627066146338623283573 := by
  unfold tailWord_713426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505195978346730076364033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17347189275591280203637421 6505195978346730076364033)
  ·
    refine ⟨4878896983760047557273025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6505195978346730076364033 4878896983760047557273025)
    ·
      refine ⟨3659172737820035667954769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4878896983760047557273025 3659172737820035667954769)
      ·
        refine ⟨2744379553365026750966077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3659172737820035667954769 2744379553365026750966077)
        ·
          refine ⟨1029142332511885031612279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2744379553365026750966077 1029142332511885031612279)
          ·
            refine ⟨1543713498767827547418419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029142332511885031612279 1543713498767827547418419)
            ·
              refine ⟨2315570248151741321127629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543713498767827547418419 2315570248151741321127629)
              ·
                refine ⟨868338843056902995422861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2315570248151741321127629 868338843056902995422861)
                ·
                  refine ⟨325627066146338623283573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868338843056902995422861 325627066146338623283573)
                  ·
                    rfl

theorem cell20_713426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_713426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713426 prefixEnd_713426 := by exact prefixLift 713426
  have htrace : WordTrace (prefixWord ++ tailWord_713426) baseStart_713426 baseEnd_713426 := by
    simpa [prefixWord, tailWord_713426, baseEnd_713426] using wordTrace_append hprefix tailTrace_713426
  have hstable : (prefixWord ++ tailWord_713426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713426).length < 2 ^ (prefixWord ++ tailWord_713426).sum := by decide
  have hdescent : baseEnd_713426 < baseStart_713426 := by decide
  rcases family_descends (prefixWord ++ tailWord_713426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713460 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_713460 : Nat := 118140960795 + 713460 * 2 ^ 59
def prefixEnd_713460 : Nat := 4983230072969 + 3 ^ 40 * 713460 * 2
def baseEnd_713460 : Nat := 325642584672785616150101

theorem tailTrace_713460 : CollatzResearch.WordTrace tailWord_713460 prefixEnd_713460 325642584672785616150101 := by
  unfold tailWord_713460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011011997631872056096917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17348015996842496074795889 13011011997631872056096917)
  ·
    refine ⟨609891187388994002629543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13011011997631872056096917 609891187388994002629543)
    ·
      refine ⟨914836781083491003944315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609891187388994002629543 914836781083491003944315)
      ·
        refine ⟨1372255171625236505916473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914836781083491003944315 1372255171625236505916473)
        ·
          refine ⟨1029191378718927379437355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1372255171625236505916473 1029191378718927379437355)
          ·
            refine ⟨1543787068078391069156033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029191378718927379437355 1543787068078391069156033)
            ·
              refine ⟨1157840301058793301867025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543787068078391069156033 1157840301058793301867025)
              ·
                refine ⟨868380225794094976400269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157840301058793301867025 868380225794094976400269)
                ·
                  refine ⟨325642584672785616150101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868380225794094976400269 325642584672785616150101)
                  ·
                    rfl

theorem cell20_713460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_713460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713460 prefixEnd_713460 := by exact prefixLift 713460
  have htrace : WordTrace (prefixWord ++ tailWord_713460) baseStart_713460 baseEnd_713460 := by
    simpa [prefixWord, tailWord_713460, baseEnd_713460] using wordTrace_append hprefix tailTrace_713460
  have hstable : (prefixWord ++ tailWord_713460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713460).length < 2 ^ (prefixWord ++ tailWord_713460).sum := by decide
  have hdescent : baseEnd_713460 < baseStart_713460 := by decide
  rcases family_descends (prefixWord ++ tailWord_713460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713475 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_713475 : Nat := 118140960795 + 713475 * 2 ^ 59
def prefixEnd_713475 : Nat := 4983230072969 + 3 ^ 40 * 713475 * 2
def baseEnd_713475 : Nat := 325649431081512230650039

theorem tailTrace_713475 : CollatzResearch.WordTrace tailWord_713475 prefixEnd_713475 325649431081512230650039 := by
  unfold tailWord_713475
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022571090209401673989879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17348380726806267782659919 26022571090209401673989879)
  ·
    refine ⟨39033856635314102510984819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26022571090209401673989879 39033856635314102510984819)
    ·
      refine ⟨58550784952971153766477229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39033856635314102510984819 58550784952971153766477229)
      ·
        refine ⟨21956544357364182662428961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58550784952971153766477229 21956544357364182662428961)
        ·
          refine ⟨16467408268023136996821721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21956544357364182662428961 16467408268023136996821721)
          ·
            refine ⟨12350556201017352747616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16467408268023136996821721 12350556201017352747616291)
            ·
              refine ⟨18525834301526029121424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350556201017352747616291 18525834301526029121424437)
              ·
                refine ⟨1736796965768065230133541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18525834301526029121424437 1736796965768065230133541)
                ·
                  refine ⟨325649431081512230650039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736796965768065230133541 325649431081512230650039)
                  ·
                    rfl

theorem cell20_713475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_713475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713475 prefixEnd_713475 := by exact prefixLift 713475
  have htrace : WordTrace (prefixWord ++ tailWord_713475) baseStart_713475 baseEnd_713475 := by
    simpa [prefixWord, tailWord_713475, baseEnd_713475] using wordTrace_append hprefix tailTrace_713475
  have hstable : (prefixWord ++ tailWord_713475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713475).length < 2 ^ (prefixWord ++ tailWord_713475).sum := by decide
  have hdescent : baseEnd_713475 < baseStart_713475 := by decide
  rcases family_descends (prefixWord ++ tailWord_713475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713509 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 2]
def baseStart_713509 : Nat := 118140960795 + 713509 * 2 ^ 59
def prefixEnd_713509 : Nat := 4983230072969 + 3 ^ 40 * 713509 * 2
def baseEnd_713509 : Nat := 325664949607959223516567

theorem tailTrace_713509 : CollatzResearch.WordTrace tailWord_713509 prefixEnd_713509 325664949607959223516567 := by
  unfold tailWord_713509
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023811172086225480727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17349207448057483653818387 26023811172086225480727581)
  ·
    refine ⟨9758929189532334555272843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26023811172086225480727581 9758929189532334555272843)
    ·
      refine ⟨14638393784298501832909265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9758929189532334555272843 14638393784298501832909265)
      ·
        refine ⟨10978795338223876374681949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14638393784298501832909265 10978795338223876374681949)
        ·
          refine ⟨4117048251833953640505731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10978795338223876374681949 4117048251833953640505731)
          ·
            refine ⟨6175572377750930460758597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117048251833953640505731 6175572377750930460758597)
            ·
              refine ⟨1157919820828299461392237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6175572377750930460758597 1157919820828299461392237)
              ·
                refine ⟨434219932810612298022089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157919820828299461392237 434219932810612298022089)
                ·
                  refine ⟨325664949607959223516567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434219932810612298022089 325664949607959223516567)
                  ·
                    rfl

theorem cell20_713509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_713509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713509 prefixEnd_713509 := by exact prefixLift 713509
  have htrace : WordTrace (prefixWord ++ tailWord_713509) baseStart_713509 baseEnd_713509 := by
    simpa [prefixWord, tailWord_713509, baseEnd_713509] using wordTrace_append hprefix tailTrace_713509
  have hstable : (prefixWord ++ tailWord_713509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713509).length < 2 ^ (prefixWord ++ tailWord_713509).sum := by decide
  have hdescent : baseEnd_713509 < baseStart_713509 := by decide
  rcases family_descends (prefixWord ++ tailWord_713509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713523 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_713523 : Nat := 118140960795 + 713523 * 2 ^ 59
def prefixEnd_713523 : Nat := 4983230072969 + 3 ^ 40 * 713523 * 2
def baseEnd_713523 : Nat := 325671339589437397049843

theorem tailTrace_713523 : CollatzResearch.WordTrace tailWord_713523 prefixEnd_713523 325671339589437397049843 := by
  unfold tailWord_713523
  simp only [CollatzResearch.WordTrace]
  refine ⟨26024321794035505871737223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17349547862690337247824815 26024321794035505871737223)
  ·
    refine ⟨39036482691053258807605835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26024321794035505871737223 39036482691053258807605835)
    ·
      refine ⟨58554724036579888211408753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39036482691053258807605835 58554724036579888211408753)
      ·
        refine ⟨43916043027434916158556565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58554724036579888211408753 43916043027434916158556565)
        ·
          refine ⟨2058564516911011694932339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43916043027434916158556565 2058564516911011694932339)
          ·
            refine ⟨3087846775366517542398509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058564516911011694932339 3087846775366517542398509)
            ·
              refine ⟨1157942540762444078399441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3087846775366517542398509 1157942540762444078399441)
              ·
                refine ⟨868456905571833058799581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157942540762444078399441 868456905571833058799581)
                ·
                  refine ⟨325671339589437397049843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868456905571833058799581 325671339589437397049843)
                  ·
                    rfl

theorem cell20_713523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_713523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713523 prefixEnd_713523 := by exact prefixLift 713523
  have htrace : WordTrace (prefixWord ++ tailWord_713523) baseStart_713523 baseEnd_713523 := by
    simpa [prefixWord, tailWord_713523, baseEnd_713523] using wordTrace_append hprefix tailTrace_713523
  have hstable : (prefixWord ++ tailWord_713523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713523).length < 2 ^ (prefixWord ++ tailWord_713523).sum := by decide
  have hdescent : baseEnd_713523 < baseStart_713523 := by decide
  rcases family_descends (prefixWord ++ tailWord_713523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713526 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_713526 : Nat := 118140960795 + 713526 * 2 ^ 59
def prefixEnd_713526 : Nat := 4983230072969 + 3 ^ 40 * 713526 * 2
def baseEnd_713526 : Nat := 325672708871182719949831

theorem tailTrace_713526 : CollatzResearch.WordTrace tailWord_713526 prefixEnd_713526 325672708871182719949831 := by
  unfold tailWord_713526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626526950814039836506027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17349620808683091589397621 1626526950814039836506027)
  ·
    refine ⟨2439790426221059754759041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626526950814039836506027 2439790426221059754759041)
    ·
      refine ⟨1829842819665794816069281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2439790426221059754759041 1829842819665794816069281)
      ·
        refine ⟨1372382114749346112051961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829842819665794816069281 1372382114749346112051961)
        ·
          refine ⟨1029286586062009584038971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1372382114749346112051961 1029286586062009584038971)
          ·
            refine ⟨1543929879093014376058457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029286586062009584038971 1543929879093014376058457)
            ·
              refine ⟨1157947409319760782043843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543929879093014376058457 1157947409319760782043843)
              ·
                refine ⟨1736921113979641173065765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157947409319760782043843 1736921113979641173065765)
                ·
                  refine ⟨325672708871182719949831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736921113979641173065765 325672708871182719949831)
                  ·
                    rfl

theorem cell20_713526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_713526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713526 prefixEnd_713526 := by exact prefixLift 713526
  have htrace : WordTrace (prefixWord ++ tailWord_713526) baseStart_713526 baseEnd_713526 := by
    simpa [prefixWord, tailWord_713526, baseEnd_713526] using wordTrace_append hprefix tailTrace_713526
  have hstable : (prefixWord ++ tailWord_713526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713526).length < 2 ^ (prefixWord ++ tailWord_713526).sum := by decide
  have hdescent : baseEnd_713526 < baseStart_713526 := by decide
  rcases family_descends (prefixWord ++ tailWord_713526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713564 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_713564 : Nat := 118140960795 + 713564 * 2 ^ 59
def prefixEnd_713564 : Nat := 4983230072969 + 3 ^ 40 * 713564 * 2
def baseEnd_713564 : Nat := 325690053106623476683009

theorem tailTrace_713564 : CollatzResearch.WordTrace tailWord_713564 prefixEnd_713564 325690053106623476683009 := by
  unfold tailWord_713564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012908593443484936989873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17350544791257979915986497 13012908593443484936989873)
  ·
    refine ⟨9759681445082613702742405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13012908593443484936989873 9759681445082613702742405)
    ·
      refine ⟨1829940270952990069264201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9759681445082613702742405 1829940270952990069264201)
      ·
        refine ⟨1372455203214742551948151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829940270952990069264201 1372455203214742551948151)
        ·
          refine ⟨2058682804822113827922227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372455203214742551948151 2058682804822113827922227)
          ·
            refine ⟨3088024207233170741883341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058682804822113827922227 3088024207233170741883341)
            ·
              refine ⟨1158009077712439028206253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3088024207233170741883341 1158009077712439028206253)
              ·
                refine ⟨434253404142164635577345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1158009077712439028206253 434253404142164635577345)
                ·
                  refine ⟨325690053106623476683009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434253404142164635577345 325690053106623476683009)
                  ·
                    rfl

theorem cell20_713564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_713564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713564 prefixEnd_713564 := by exact prefixLift 713564
  have htrace : WordTrace (prefixWord ++ tailWord_713564) baseStart_713564 baseEnd_713564 := by
    simpa [prefixWord, tailWord_713564, baseEnd_713564] using wordTrace_append hprefix tailTrace_713564
  have hstable : (prefixWord ++ tailWord_713564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713564).length < 2 ^ (prefixWord ++ tailWord_713564).sum := by decide
  have hdescent : baseEnd_713564 < baseStart_713564 := by decide
  rcases family_descends (prefixWord ++ tailWord_713564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713575 : List Nat := [1, 1, 5, 1, 2, 4, 6]
def baseStart_713575 : Nat := 118140960795 + 713575 * 2 ^ 59
def prefixEnd_713575 : Nat := 4983230072969 + 3 ^ 40 * 713575 * 2
def baseEnd_713575 : Nat := 36188341534039591924033

theorem tailTrace_713575 : CollatzResearch.WordTrace tailWord_713575 prefixEnd_713575 36188341534039591924033 := by
  unfold tailWord_713575
  simp only [CollatzResearch.WordTrace]
  refine ⟨26026218389847118752630179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17350812259898079168420119 26026218389847118752630179)
  ·
    refine ⟨39039327584770678128945269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26026218389847118752630179 39039327584770678128945269)
    ·
      refine ⟨3659936961072251074588619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39039327584770678128945269 3659936961072251074588619)
      ·
        refine ⟨5489905441608376611882929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659936961072251074588619 5489905441608376611882929)
        ·
          refine ⟨4117429081206282458912197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489905441608376611882929 4117429081206282458912197)
          ·
            refine ⟨772017952726177961046037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4117429081206282458912197 772017952726177961046037)
            ·
              refine ⟨36188341534039591924033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 772017952726177961046037 36188341534039591924033)
              ·
                rfl

theorem cell20_713575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_713575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713575 prefixEnd_713575 := by exact prefixLift 713575
  have htrace : WordTrace (prefixWord ++ tailWord_713575) baseStart_713575 baseEnd_713575 := by
    simpa [prefixWord, tailWord_713575, baseEnd_713575] using wordTrace_append hprefix tailTrace_713575
  have hstable : (prefixWord ++ tailWord_713575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713575).length < 2 ^ (prefixWord ++ tailWord_713575).sum := by decide
  have hdescent : baseEnd_713575 < baseStart_713575 := by decide
  rcases family_descends (prefixWord ++ tailWord_713575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713599 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_713599 : Nat := 118140960795 + 713599 * 2 ^ 59
def prefixEnd_713599 : Nat := 4983230072969 + 3 ^ 40 * 713599 * 2
def baseEnd_713599 : Nat := 325706028060318910516199

theorem tailTrace_713599 : CollatzResearch.WordTrace tailWord_713599 prefixEnd_713599 325706028060318910516199 := by
  unfold tailWord_713599
  simp only [CollatzResearch.WordTrace]
  refine ⟨26027093741760170851503851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17351395827840113901002567 26027093741760170851503851)
  ·
    refine ⟨39040640612640256277255777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26027093741760170851503851 39040640612640256277255777)
    ·
      refine ⟨29280480459480192207941833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39040640612640256277255777 29280480459480192207941833)
      ·
        refine ⟨21960360344610144155956375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29280480459480192207941833 21960360344610144155956375)
        ·
          refine ⟨32940540516915216233934563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21960360344610144155956375 32940540516915216233934563)
          ·
            refine ⟨49410810775372824350901845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32940540516915216233934563 49410810775372824350901845)
            ·
              refine ⟨579032938773900285362131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 49410810775372824350901845 579032938773900285362131)
              ·
                refine ⟨868549408160850428043197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579032938773900285362131 868549408160850428043197)
                ·
                  refine ⟨325706028060318910516199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868549408160850428043197 325706028060318910516199)
                  ·
                    rfl

theorem cell20_713599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_713599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713599 prefixEnd_713599 := by exact prefixLift 713599
  have htrace : WordTrace (prefixWord ++ tailWord_713599) baseStart_713599 baseEnd_713599 := by
    simpa [prefixWord, tailWord_713599, baseEnd_713599] using wordTrace_append hprefix tailTrace_713599
  have hstable : (prefixWord ++ tailWord_713599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713599).length < 2 ^ (prefixWord ++ tailWord_713599).sum := by decide
  have hdescent : baseEnd_713599 < baseStart_713599 := by decide
  rcases family_descends (prefixWord ++ tailWord_713599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713644 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_713644 : Nat := 118140960795 + 713644 * 2 ^ 59
def prefixEnd_713644 : Nat := 4983230072969 + 3 ^ 40 * 713644 * 2
def baseEnd_713644 : Nat := 325726567286498754016015

theorem tailTrace_713644 : CollatzResearch.WordTrace tailWord_713644 prefixEnd_713644 325726567286498754016015 := by
  unfold tailWord_713644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014367513298571768445993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17352490017731429024594657 13014367513298571768445993)
  ·
    refine ⟨9760775634973928826334495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13014367513298571768445993 9760775634973928826334495)
    ·
      refine ⟨14641163452460893239501743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760775634973928826334495 14641163452460893239501743)
      ·
        refine ⟨21961745178691339859252615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641163452460893239501743 21961745178691339859252615)
        ·
          refine ⟨32942617768037009788878923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961745178691339859252615 32942617768037009788878923)
          ·
            refine ⟨49413926652055514683318385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32942617768037009788878923 49413926652055514683318385)
            ·
              refine ⟨37060444989041636012488789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49413926652055514683318385 37060444989041636012488789)
              ·
                refine ⟨434302089715331672021353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 37060444989041636012488789 434302089715331672021353)
                ·
                  refine ⟨325726567286498754016015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434302089715331672021353 325726567286498754016015)
                  ·
                    rfl

theorem cell20_713644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_713644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713644 prefixEnd_713644 := by exact prefixLift 713644
  have htrace : WordTrace (prefixWord ++ tailWord_713644) baseStart_713644 baseEnd_713644 := by
    simpa [prefixWord, tailWord_713644, baseEnd_713644] using wordTrace_append hprefix tailTrace_713644
  have hstable : (prefixWord ++ tailWord_713644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713644).length < 2 ^ (prefixWord ++ tailWord_713644).sum := by decide
  have hdescent : baseEnd_713644 < baseStart_713644 := by decide
  rcases family_descends (prefixWord ++ tailWord_713644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713658 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_713658 : Nat := 118140960795 + 713658 * 2 ^ 59
def prefixEnd_713658 : Nat := 4983230072969 + 3 ^ 40 * 713658 * 2
def baseEnd_713658 : Nat := 325732957267976927549291

theorem tailTrace_713658 : CollatzResearch.WordTrace tailWord_713658 prefixEnd_713658 325732957267976927549291 := by
  unfold tailWord_713658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507311412136605981975407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17352830432364282618601085 6507311412136605981975407)
  ·
    refine ⟨9760967118204908972963111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507311412136605981975407 9760967118204908972963111)
    ·
      refine ⟨14641450677307363459444667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760967118204908972963111 14641450677307363459444667)
      ·
        refine ⟨21962176015961045189167001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641450677307363459444667 21962176015961045189167001)
        ·
          refine ⟨16471632011970783891875251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21962176015961045189167001 16471632011970783891875251)
          ·
            refine ⟨24707448017956175837812877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16471632011970783891875251 24707448017956175837812877)
            ·
              refine ⟨9265293006733565939179829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24707448017956175837812877 9265293006733565939179829)
              ·
                refine ⟨868621219381271806798109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9265293006733565939179829 868621219381271806798109)
                ·
                  refine ⟨325732957267976927549291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868621219381271806798109 325732957267976927549291)
                  ·
                    rfl

theorem cell20_713658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_713658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713658 prefixEnd_713658 := by exact prefixLift 713658
  have htrace : WordTrace (prefixWord ++ tailWord_713658) baseStart_713658 baseEnd_713658 := by
    simpa [prefixWord, tailWord_713658, baseEnd_713658] using wordTrace_append hprefix tailTrace_713658
  have hstable : (prefixWord ++ tailWord_713658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713658).length < 2 ^ (prefixWord ++ tailWord_713658).sum := by decide
  have hdescent : baseEnd_713658 < baseStart_713658 := by decide
  rcases family_descends (prefixWord ++ tailWord_713658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713772 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_713772 : Nat := 118140960795 + 713772 * 2 ^ 59
def prefixEnd_713772 : Nat := 4983230072969 + 3 ^ 40 * 713772 * 2
def baseEnd_713772 : Nat := 325784989974299197748825

theorem tailTrace_713772 : CollatzResearch.WordTrace tailWord_713772 prefixEnd_713772 325784989974299197748825 := by
  unfold tailWord_713772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13016701785066710698775785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17355602380088947598367713 13016701785066710698775785)
  ·
    refine ⟨9762526338800033024081839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13016701785066710698775785 9762526338800033024081839)
    ·
      refine ⟨14643789508200049536122759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762526338800033024081839 14643789508200049536122759)
      ·
        refine ⟨21965684262300074304184139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14643789508200049536122759 21965684262300074304184139)
        ·
          refine ⟨32948526393450111456276209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21965684262300074304184139 32948526393450111456276209)
          ·
            refine ⟨24711394795087583592207157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32948526393450111456276209 24711394795087583592207157)
            ·
              refine ⟨2316693262039460961769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24711394795087583592207157 2316693262039460961769421)
              ·
                refine ⟨868759973264797860663533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2316693262039460961769421 868759973264797860663533)
                ·
                  refine ⟨325784989974299197748825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868759973264797860663533 325784989974299197748825)
                  ·
                    rfl

theorem cell20_713772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_713772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713772 prefixEnd_713772 := by exact prefixLift 713772
  have htrace : WordTrace (prefixWord ++ tailWord_713772) baseStart_713772 baseEnd_713772 := by
    simpa [prefixWord, tailWord_713772, baseEnd_713772] using wordTrace_append hprefix tailTrace_713772
  have hstable : (prefixWord ++ tailWord_713772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713772).length < 2 ^ (prefixWord ++ tailWord_713772).sum := by decide
  have hdescent : baseEnd_713772 < baseStart_713772 := by decide
  rcases family_descends (prefixWord ++ tailWord_713772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713786 : List Nat := [3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_713786 : Nat := 118140960795 + 713786 * 2 ^ 59
def prefixEnd_713786 : Nat := 4983230072969 + 3 ^ 40 * 713786 * 2
def baseEnd_713786 : Nat := 108597126651925790427367

theorem tailTrace_713786 : CollatzResearch.WordTrace tailWord_713786 prefixEnd_713786 108597126651925790427367 := by
  unfold tailWord_713786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508478548020675447140303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17355942794721801192374141 6508478548020675447140303)
  ·
    refine ⟨9762717822031013170710455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508478548020675447140303 9762717822031013170710455)
    ·
      refine ⟨14644076733046519756065683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762717822031013170710455 14644076733046519756065683)
      ·
        refine ⟨21966115099569779634098525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14644076733046519756065683 21966115099569779634098525)
        ·
          refine ⟨8237293162338667362786947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21966115099569779634098525 8237293162338667362786947)
          ·
            refine ⟨12355939743508001044180421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237293162338667362786947 12355939743508001044180421)
            ·
              refine ⟨2316738701907750195783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12355939743508001044180421 2316738701907750195783829)
              ·
                refine ⟨108597126651925790427367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2316738701907750195783829 108597126651925790427367)
                ·
                  rfl

theorem cell20_713786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_713786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713786 prefixEnd_713786 := by exact prefixLift 713786
  have htrace : WordTrace (prefixWord ++ tailWord_713786) baseStart_713786 baseEnd_713786 := by
    simpa [prefixWord, tailWord_713786, baseEnd_713786] using wordTrace_append hprefix tailTrace_713786
  have hstable : (prefixWord ++ tailWord_713786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713786).length < 2 ^ (prefixWord ++ tailWord_713786).sum := by decide
  have hdescent : baseEnd_713786 < baseStart_713786 := by decide
  rcases family_descends (prefixWord ++ tailWord_713786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713834 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_713834 : Nat := 118140960795 + 713834 * 2 ^ 59
def prefixEnd_713834 : Nat := 4983230072969 + 3 ^ 40 * 713834 * 2
def baseEnd_713834 : Nat := 325813288463702537681905

theorem tailTrace_713834 : CollatzResearch.WordTrace tailWord_713834 prefixEnd_713834 325813288463702537681905 := by
  unfold tailWord_713834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508916223977201496577139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17357109930605870657539037 6508916223977201496577139)
  ·
    refine ⟨9763374335965802244865709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508916223977201496577139 9763374335965802244865709)
    ·
      refine ⟨3661265375987175841824641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9763374335965802244865709 3661265375987175841824641)
      ·
        refine ⟨2745949031990381881368481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3661265375987175841824641 2745949031990381881368481)
        ·
          refine ⟨2059461773992786411026361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745949031990381881368481 2059461773992786411026361)
          ·
            refine ⟨1544596330494589808269771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059461773992786411026361 1544596330494589808269771)
            ·
              refine ⟨2316894495741884712404657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544596330494589808269771 2316894495741884712404657)
              ·
                refine ⟨1737670871806413534303493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316894495741884712404657 1737670871806413534303493)
                ·
                  refine ⟨325813288463702537681905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737670871806413534303493 325813288463702537681905)
                  ·
                    rfl

theorem cell20_713834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_713834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713834 prefixEnd_713834 := by exact prefixLift 713834
  have htrace : WordTrace (prefixWord ++ tailWord_713834) baseStart_713834 baseEnd_713834 := by
    simpa [prefixWord, tailWord_713834, baseEnd_713834] using wordTrace_append hprefix tailTrace_713834
  have hstable : (prefixWord ++ tailWord_713834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713834).length < 2 ^ (prefixWord ++ tailWord_713834).sum := by decide
  have hdescent : baseEnd_713834 < baseStart_713834 := by decide
  rcases family_descends (prefixWord ++ tailWord_713834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713865 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_713865 : Nat := 118140960795 + 713865 * 2 ^ 59
def prefixEnd_713865 : Nat := 4983230072969 + 3 ^ 40 * 713865 * 2
def baseEnd_713865 : Nat := 325827437708404207648445

theorem tailTrace_713865 : CollatzResearch.WordTrace tailWord_713865 prefixEnd_713865 325827437708404207648445 := by
  unfold tailWord_713865
  simp only [CollatzResearch.WordTrace]
  refine ⟨26036795558796498280687049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17357863705864332187124699 26036795558796498280687049)
  ·
    refine ⟨19527596669097373710515287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26036795558796498280687049 19527596669097373710515287)
    ·
      refine ⟨29291395003646060565772931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19527596669097373710515287 29291395003646060565772931)
      ·
        refine ⟨43937092505469090848659397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29291395003646060565772931 43937092505469090848659397)
        ·
          refine ⟨8238204844775454534123637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43937092505469090848659397 8238204844775454534123637)
          ·
            refine ⟨772331704197698862574091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8238204844775454534123637 772331704197698862574091)
            ·
              refine ⟨1158497556296548293861137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772331704197698862574091 1158497556296548293861137)
              ·
                refine ⟨868873167222411220395853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158497556296548293861137 868873167222411220395853)
                ·
                  refine ⟨325827437708404207648445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868873167222411220395853 325827437708404207648445)
                  ·
                    rfl

theorem cell20_713865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_713865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713865 prefixEnd_713865 := by exact prefixLift 713865
  have htrace : WordTrace (prefixWord ++ tailWord_713865) baseStart_713865 baseEnd_713865 := by
    simpa [prefixWord, tailWord_713865, baseEnd_713865] using wordTrace_append hprefix tailTrace_713865
  have hstable : (prefixWord ++ tailWord_713865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713865).length < 2 ^ (prefixWord ++ tailWord_713865).sum := by decide
  have hdescent : baseEnd_713865 < baseStart_713865 := by decide
  rcases family_descends (prefixWord ++ tailWord_713865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713882 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_713882 : Nat := 118140960795 + 713882 * 2 ^ 59
def prefixEnd_713882 : Nat := 4983230072969 + 3 ^ 40 * 713882 * 2
def baseEnd_713882 : Nat := 325835196971627704081709

theorem tailTrace_713882 : CollatzResearch.WordTrace tailWord_713882 prefixEnd_713882 325835196971627704081709 := by
  unfold tailWord_713882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509353899933727546013975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17358277066489940122703933 6509353899933727546013975)
  ·
    refine ⟨9764030849900591319020963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509353899933727546013975 9764030849900591319020963)
    ·
      refine ⟨14646046274850886978531445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764030849900591319020963 14646046274850886978531445)
      ·
        refine ⟨1373066838267270654237323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14646046274850886978531445 1373066838267270654237323)
        ·
          refine ⟨2059600257400905981355985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373066838267270654237323 2059600257400905981355985)
          ·
            refine ⟨1544700193050679486016989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059600257400905981355985 1544700193050679486016989)
            ·
              refine ⟨579262572394004807256371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1544700193050679486016989 579262572394004807256371)
              ·
                refine ⟨868893858591007210884557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579262572394004807256371 868893858591007210884557)
                ·
                  refine ⟨325835196971627704081709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868893858591007210884557 325835196971627704081709)
                  ·
                    rfl

theorem cell20_713882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_713882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713882 prefixEnd_713882 := by exact prefixLift 713882
  have htrace : WordTrace (prefixWord ++ tailWord_713882) baseStart_713882 baseEnd_713882 := by
    simpa [prefixWord, tailWord_713882, baseEnd_713882] using wordTrace_append hprefix tailTrace_713882
  have hstable : (prefixWord ++ tailWord_713882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713882).length < 2 ^ (prefixWord ++ tailWord_713882).sum := by decide
  have hdescent : baseEnd_713882 < baseStart_713882 := by decide
  rcases family_descends (prefixWord ++ tailWord_713882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713893 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_713893 : Nat := 118140960795 + 713893 * 2 ^ 59
def prefixEnd_713893 : Nat := 4983230072969 + 3 ^ 40 * 713893 * 2
def baseEnd_713893 : Nat := 325840217671360554714997

theorem tailTrace_713893 : CollatzResearch.WordTrace tailWord_713893 prefixEnd_713893 325840217671360554714997 := by
  unfold tailWord_713893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26037816802695059062706333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17358544535130039375137555 26037816802695059062706333)
  ·
    refine ⟨9764181301010647148514875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26037816802695059062706333 9764181301010647148514875)
    ·
      refine ⟨14646271951515970722772313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764181301010647148514875 14646271951515970722772313)
      ·
        refine ⟨10984703963636978042079235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14646271951515970722772313 10984703963636978042079235)
        ·
          refine ⟨16477055945455467063118853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984703963636978042079235 16477055945455467063118853)
          ·
            refine ⟨3089447989772900074334785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16477055945455467063118853 3089447989772900074334785)
            ·
              refine ⟨2317085992329675055751089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089447989772900074334785 2317085992329675055751089)
              ·
                refine ⟨1737814494247256291813317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317085992329675055751089 1737814494247256291813317)
                ·
                  refine ⟨325840217671360554714997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737814494247256291813317 325840217671360554714997)
                  ·
                    rfl

theorem cell20_713893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_713893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713893 prefixEnd_713893 := by exact prefixLift 713893
  have htrace : WordTrace (prefixWord ++ tailWord_713893) baseStart_713893 baseEnd_713893 := by
    simpa [prefixWord, tailWord_713893, baseEnd_713893] using wordTrace_append hprefix tailTrace_713893
  have hstable : (prefixWord ++ tailWord_713893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713893).length < 2 ^ (prefixWord ++ tailWord_713893).sum := by decide
  have hdescent : baseEnd_713893 < baseStart_713893 := by decide
  rcases family_descends (prefixWord ++ tailWord_713893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713907 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_713907 : Nat := 118140960795 + 713907 * 2 ^ 59
def prefixEnd_713907 : Nat := 4983230072969 + 3 ^ 40 * 713907 * 2
def baseEnd_713907 : Nat := 325846607652838728248273

theorem tailTrace_713907 : CollatzResearch.WordTrace tailWord_713907 prefixEnd_713907 325846607652838728248273 := by
  unfold tailWord_713907
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038327424644339453715975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17358884949762892969143983 26038327424644339453715975)
  ·
    refine ⟨39057491136966509180573963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26038327424644339453715975 39057491136966509180573963)
    ·
      refine ⟨58586236705449763770860945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39057491136966509180573963 58586236705449763770860945)
      ·
        refine ⟨43939677529087322828145709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58586236705449763770860945 43939677529087322828145709)
        ·
          refine ⟨16477379073407746060554641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43939677529087322828145709 16477379073407746060554641)
          ·
            refine ⟨12358034305055809545415981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477379073407746060554641 12358034305055809545415981)
            ·
              refine ⟨4634262864395928579530993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12358034305055809545415981 4634262864395928579530993)
              ·
                refine ⟨3475697148296946434648245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4634262864395928579530993 3475697148296946434648245)
                ·
                  refine ⟨325846607652838728248273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475697148296946434648245 325846607652838728248273)
                  ·
                    rfl

theorem cell20_713907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_713907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713907 prefixEnd_713907 := by exact prefixLift 713907
  have htrace : WordTrace (prefixWord ++ tailWord_713907) baseStart_713907 baseEnd_713907 := by
    simpa [prefixWord, tailWord_713907, baseEnd_713907] using wordTrace_append hprefix tailTrace_713907
  have hstable : (prefixWord ++ tailWord_713907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713907).length < 2 ^ (prefixWord ++ tailWord_713907).sum := by decide
  have hdescent : baseEnd_713907 < baseStart_713907 := by decide
  rcases family_descends (prefixWord ++ tailWord_713907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713933 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 3]
def baseStart_713933 : Nat := 118140960795 + 713933 * 2 ^ 59
def prefixEnd_713933 : Nat := 4983230072969 + 3 ^ 40 * 713933 * 2
def baseEnd_713933 : Nat := 325858474761298193381501

theorem tailTrace_713933 : CollatzResearch.WordTrace tailWord_713933 prefixEnd_713933 325858474761298193381501 := by
  unfold tailWord_713933
  simp only [CollatzResearch.WordTrace]
  refine ⟨26039275722550145894162453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17359517148366763929441635 26039275722550145894162453)
  ·
    refine ⟨1220591049494538088788865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26039275722550145894162453 1220591049494538088788865)
    ·
      refine ⟨915443287120903566591649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1220591049494538088788865 915443287120903566591649)
      ·
        refine ⟨686582465340677674943737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 915443287120903566591649 686582465340677674943737)
        ·
          refine ⟨514936849005508256207803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686582465340677674943737 514936849005508256207803)
          ·
            refine ⟨772405273508262384311705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514936849005508256207803 772405273508262384311705)
            ·
              refine ⟨579303955131196788233779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772405273508262384311705 579303955131196788233779)
              ·
                refine ⟨868955932696795182350669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579303955131196788233779 868955932696795182350669)
                ·
                  refine ⟨325858474761298193381501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868955932696795182350669 325858474761298193381501)
                  ·
                    rfl

theorem cell20_713933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_713933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713933 prefixEnd_713933 := by exact prefixLift 713933
  have htrace : WordTrace (prefixWord ++ tailWord_713933) baseStart_713933 baseEnd_713933 := by
    simpa [prefixWord, tailWord_713933, baseEnd_713933] using wordTrace_append hprefix tailTrace_713933
  have hstable : (prefixWord ++ tailWord_713933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713933).length < 2 ^ (prefixWord ++ tailWord_713933).sum := by decide
  have hdescent : baseEnd_713933 < baseStart_713933 := by decide
  rcases family_descends (prefixWord ++ tailWord_713933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713941 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_713941 : Nat := 118140960795 + 713941 * 2 ^ 59
def prefixEnd_713941 : Nat := 4983230072969 + 3 ^ 40 * 713941 * 2
def baseEnd_713941 : Nat := 325862126179285721114801

theorem tailTrace_713941 : CollatzResearch.WordTrace tailWord_713941 prefixEnd_713941 325862126179285721114801 := by
  unfold tailWord_713941
  simp only [CollatzResearch.WordTrace]
  refine ⟨26039567506521163260453677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17359711671014108840302451 26039567506521163260453677)
  ·
    refine ⟨9764837814945436222670129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26039567506521163260453677 9764837814945436222670129)
    ·
      refine ⟨7323628361209077167002597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9764837814945436222670129 7323628361209077167002597)
      ·
        refine ⟨1373180317726701968812987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7323628361209077167002597 1373180317726701968812987)
        ·
          refine ⟨2059770476590052953219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373180317726701968812987 2059770476590052953219481)
          ·
            refine ⟨1544827857442539714914611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059770476590052953219481 1544827857442539714914611)
            ·
              refine ⟨2317241786163809572371917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544827857442539714914611 2317241786163809572371917)
              ·
                refine ⟨868965669811428589639469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2317241786163809572371917 868965669811428589639469)
                ·
                  refine ⟨325862126179285721114801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868965669811428589639469 325862126179285721114801)
                  ·
                    rfl

theorem cell20_713941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_713941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713941 prefixEnd_713941 := by exact prefixLift 713941
  have htrace : WordTrace (prefixWord ++ tailWord_713941) baseStart_713941 baseEnd_713941 := by
    simpa [prefixWord, tailWord_713941, baseEnd_713941] using wordTrace_append hprefix tailTrace_713941
  have hstable : (prefixWord ++ tailWord_713941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713941).length < 2 ^ (prefixWord ++ tailWord_713941).sum := by decide
  have hdescent : baseEnd_713941 < baseStart_713941 := by decide
  rcases family_descends (prefixWord ++ tailWord_713941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713972 : List Nat := [2, 6, 1, 2, 9]
def baseStart_713972 : Nat := 118140960795 + 713972 * 2 ^ 59
def prefixEnd_713972 : Nat := 4983230072969 + 3 ^ 40 * 713972 * 2
def baseEnd_713972 : Nat := 4023163894123301124461

theorem tailTrace_713972 : CollatzResearch.WordTrace tailWord_713972 prefixEnd_713972 4023163894123301124461 := by
  unfold tailWord_713972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020349084704427777416085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17360465446272570369888113 13020349084704427777416085)
  ·
    refine ⟨610328863345520052066379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13020349084704427777416085 610328863345520052066379)
    ·
      refine ⟨915493295018280078099569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610328863345520052066379 915493295018280078099569)
      ·
        refine ⟨686619971263710058574677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 915493295018280078099569 686619971263710058574677)
        ·
          refine ⟨4023163894123301124461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 686619971263710058574677 4023163894123301124461)
          ·
            rfl

theorem cell20_713972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 9].length) (baseStart_713972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713972 prefixEnd_713972 := by exact prefixLift 713972
  have htrace : WordTrace (prefixWord ++ tailWord_713972) baseStart_713972 baseEnd_713972 := by
    simpa [prefixWord, tailWord_713972, baseEnd_713972] using wordTrace_append hprefix tailTrace_713972
  have hstable : (prefixWord ++ tailWord_713972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713972).length < 2 ^ (prefixWord ++ tailWord_713972).sum := by decide
  have hdescent : baseEnd_713972 < baseStart_713972 := by decide
  rcases family_descends (prefixWord ++ tailWord_713972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713982 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_713982 : Nat := 118140960795 + 713982 * 2 ^ 59
def prefixEnd_713982 : Nat := 4983230072969 + 3 ^ 40 * 713982 * 2
def baseEnd_713982 : Nat := 325880839696471800747967

theorem tailTrace_713982 : CollatzResearch.WordTrace tailWord_713982 prefixEnd_713982 325880839696471800747967 := by
  unfold tailWord_713982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255132862421578407837025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17360708599581751508464133 3255132862421578407837025)
  ·
    refine ⟨2441349646816183805877769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3255132862421578407837025 2441349646816183805877769)
    ·
      refine ⟨1831012235112137854408327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2441349646816183805877769 1831012235112137854408327)
      ·
        refine ⟨2746518352668206781612491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831012235112137854408327 2746518352668206781612491)
        ·
          refine ⟨4119777529002310172418737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746518352668206781612491 4119777529002310172418737)
          ·
            refine ⟨3089833146751732629314053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4119777529002310172418737 3089833146751732629314053)
            ·
              refine ⟨579343715015949867996385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3089833146751732629314053 579343715015949867996385)
              ·
                refine ⟨434507786261962400997289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579343715015949867996385 434507786261962400997289)
                ·
                  refine ⟨325880839696471800747967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434507786261962400997289 325880839696471800747967)
                  ·
                    rfl

theorem cell20_713982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_713982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_713982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_713982 prefixEnd_713982 := by exact prefixLift 713982
  have htrace : WordTrace (prefixWord ++ tailWord_713982) baseStart_713982 baseEnd_713982 := by
    simpa [prefixWord, tailWord_713982, baseEnd_713982] using wordTrace_append hprefix tailTrace_713982
  have hstable : (prefixWord ++ tailWord_713982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713982).length < 2 ^ (prefixWord ++ tailWord_713982).sum := by decide
  have hdescent : baseEnd_713982 < baseStart_713982 := by decide
  rcases family_descends (prefixWord ++ tailWord_713982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714007 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_714007 : Nat := 118140960795 + 714007 * 2 ^ 59
def prefixEnd_714007 : Nat := 4983230072969 + 3 ^ 40 * 714007 * 2
def baseEnd_714007 : Nat := 325892250377682824914531

theorem tailTrace_714007 : CollatzResearch.WordTrace tailWord_714007 prefixEnd_714007 325892250377682824914531 := by
  unfold tailWord_714007
  simp only [CollatzResearch.WordTrace]
  refine ⟨26041974724282056532356275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17361316482854704354904183 26041974724282056532356275)
  ·
    refine ⟨39062962086423084798534413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26041974724282056532356275 39062962086423084798534413)
    ·
      refine ⟨14648610782408656799450405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39062962086423084798534413 14648610782408656799450405)
      ·
        refine ⟨2746614521701623149896951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14648610782408656799450405 2746614521701623149896951)
        ·
          refine ⟨4119921782552434724845427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746614521701623149896951 4119921782552434724845427)
          ·
            refine ⟨6179882673828652087268141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119921782552434724845427 6179882673828652087268141)
            ·
              refine ⟨2317456002685744532725553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6179882673828652087268141 2317456002685744532725553)
              ·
                refine ⟨1738092002014308399544165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317456002685744532725553 1738092002014308399544165)
                ·
                  refine ⟨325892250377682824914531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738092002014308399544165 325892250377682824914531)
                  ·
                    rfl

theorem cell20_714007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_714007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714007 prefixEnd_714007 := by exact prefixLift 714007
  have htrace : WordTrace (prefixWord ++ tailWord_714007) baseStart_714007 baseEnd_714007 := by
    simpa [prefixWord, tailWord_714007, baseEnd_714007] using wordTrace_append hprefix tailTrace_714007
  have hstable : (prefixWord ++ tailWord_714007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714007).length < 2 ^ (prefixWord ++ tailWord_714007).sum := by decide
  have hdescent : baseEnd_714007 < baseStart_714007 := by decide
  rcases family_descends (prefixWord ++ tailWord_714007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714028 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_714028 : Nat := 118140960795 + 714028 * 2 ^ 59
def prefixEnd_714028 : Nat := 4983230072969 + 3 ^ 40 * 714028 * 2
def baseEnd_714028 : Nat := 325901835349900085214445

theorem tailTrace_714028 : CollatzResearch.WordTrace tailWord_714028 prefixEnd_714028 325901835349900085214445 := by
  unfold tailWord_714028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13021370328602988559435369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17361827104803984745913825 13021370328602988559435369)
  ·
    refine ⟨9766027746452241419576527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13021370328602988559435369 9766027746452241419576527)
    ·
      refine ⟨14649041619678362129364791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766027746452241419576527 14649041619678362129364791)
      ·
        refine ⟨21973562429517543194047187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649041619678362129364791 21973562429517543194047187)
        ·
          refine ⟨32960343644276314791070781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21973562429517543194047187 32960343644276314791070781)
          ·
            refine ⟨12360128866603618046651543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32960343644276314791070781 12360128866603618046651543)
            ·
              refine ⟨18540193299905427069977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360128866603618046651543 18540193299905427069977315)
              ·
                refine ⟨27810289949858140604965973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18540193299905427069977315 27810289949858140604965973)
                ·
                  refine ⟨325901835349900085214445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27810289949858140604965973 325901835349900085214445)
                  ·
                    rfl

theorem cell20_714028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_714028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714028 prefixEnd_714028 := by exact prefixLift 714028
  have htrace : WordTrace (prefixWord ++ tailWord_714028) baseStart_714028 baseEnd_714028 := by
    simpa [prefixWord, tailWord_714028, baseEnd_714028] using wordTrace_append hprefix tailTrace_714028
  have hstable : (prefixWord ++ tailWord_714028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714028).length < 2 ^ (prefixWord ++ tailWord_714028).sum := by decide
  have hdescent : baseEnd_714028 < baseStart_714028 := by decide
  rcases family_descends (prefixWord ++ tailWord_714028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714055 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_714055 : Nat := 118140960795 + 714055 * 2 ^ 59
def prefixEnd_714055 : Nat := 4983230072969 + 3 ^ 40 * 714055 * 2
def baseEnd_714055 : Nat := 325914158885607991314335

theorem tailTrace_714055 : CollatzResearch.WordTrace tailWord_714055 prefixEnd_714055 325914158885607991314335 := by
  unfold tailWord_714055
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043725428108160730103619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17362483618738773820069079 26043725428108160730103619)
  ·
    refine ⟨39065588142162241095155429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26043725428108160730103619 39065588142162241095155429)
    ·
      refine ⟨7324797776655420205341643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39065588142162241095155429 7324797776655420205341643)
      ·
        refine ⟨10987196664983130308012465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324797776655420205341643 10987196664983130308012465)
        ·
          refine ⟨8240397498737347731009349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10987196664983130308012465 8240397498737347731009349)
          ·
            refine ⟨1545074531013252699564253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8240397498737347731009349 1545074531013252699564253)
            ·
              refine ⟨579402949129969762336595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545074531013252699564253 579402949129969762336595)
              ·
                refine ⟨869104423694954643504893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579402949129969762336595 869104423694954643504893)
                ·
                  refine ⟨325914158885607991314335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869104423694954643504893 325914158885607991314335)
                  ·
                    rfl

theorem cell20_714055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_714055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714055 prefixEnd_714055 := by exact prefixLift 714055
  have htrace : WordTrace (prefixWord ++ tailWord_714055) baseStart_714055 baseEnd_714055 := by
    simpa [prefixWord, tailWord_714055, baseEnd_714055] using wordTrace_append hprefix tailTrace_714055
  have hstable : (prefixWord ++ tailWord_714055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714055).length < 2 ^ (prefixWord ++ tailWord_714055).sum := by decide
  have hdescent : baseEnd_714055 < baseStart_714055 := by decide
  rcases family_descends (prefixWord ++ tailWord_714055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714069 : List Nat := [1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_714069 : Nat := 118140960795 + 714069 * 2 ^ 59
def prefixEnd_714069 : Nat := 4983230072969 + 3 ^ 40 * 714069 * 2
def baseEnd_714069 : Nat := 108640182955695388282537

theorem tailTrace_714069 : CollatzResearch.WordTrace tailWord_714069 prefixEnd_714069 108640182955695388282537 := by
  unfold tailWord_714069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26044236050057441121113261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17362824033371627414075507 26044236050057441121113261)
  ·
    refine ⟨9766588518771540420417473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26044236050057441121113261 9766588518771540420417473)
    ·
      refine ⟨7324941389078655315313105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9766588518771540420417473 7324941389078655315313105)
      ·
        refine ⟨5493706041808991486484829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324941389078655315313105 5493706041808991486484829)
        ·
          refine ⟨2060139765678371807431811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5493706041808991486484829 2060139765678371807431811)
          ·
            refine ⟨3090209648517557711147717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060139765678371807431811 3090209648517557711147717)
            ·
              refine ⟨579414309097042070840197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3090209648517557711147717 579414309097042070840197)
              ·
                refine ⟨108640182955695388282537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579414309097042070840197 108640182955695388282537)
                ·
                  rfl

theorem cell20_714069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_714069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714069 prefixEnd_714069 := by exact prefixLift 714069
  have htrace : WordTrace (prefixWord ++ tailWord_714069) baseStart_714069 baseEnd_714069 := by
    simpa [prefixWord, tailWord_714069, baseEnd_714069] using wordTrace_append hprefix tailTrace_714069
  have hstable : (prefixWord ++ tailWord_714069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714069).length < 2 ^ (prefixWord ++ tailWord_714069).sum := by decide
  have hdescent : baseEnd_714069 < baseStart_714069 := by decide
  rcases family_descends (prefixWord ++ tailWord_714069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714097 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_714097 : Nat := 118140960795 + 714097 * 2 ^ 59
def prefixEnd_714097 : Nat := 4983230072969 + 3 ^ 40 * 714097 * 2
def baseEnd_714097 : Nat := 325933328830042511914163

theorem tailTrace_714097 : CollatzResearch.WordTrace tailWord_714097 prefixEnd_714097 325933328830042511914163 := by
  unfold tailWord_714097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045257293956001903132545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17363504862637334602088363 26045257293956001903132545)
  ·
    refine ⟨19533942970467001427349409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26045257293956001903132545 19533942970467001427349409)
    ·
      refine ⟨14650457227850251070512057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19533942970467001427349409 14650457227850251070512057)
      ·
        refine ⟨10987842920887688302884043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14650457227850251070512057 10987842920887688302884043)
        ·
          refine ⟨16481764381331532454326065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10987842920887688302884043 16481764381331532454326065)
          ·
            refine ⟨12361323285998649340744549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16481764381331532454326065 12361323285998649340744549)
            ·
              refine ⟨2317748116124746751389603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12361323285998649340744549 2317748116124746751389603)
              ·
                refine ⟨3476622174187120127084405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317748116124746751389603 3476622174187120127084405)
                ·
                  refine ⟨325933328830042511914163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476622174187120127084405 325933328830042511914163)
                  ·
                    rfl

theorem cell20_714097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_714097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714097 prefixEnd_714097 := by exact prefixLift 714097
  have htrace : WordTrace (prefixWord ++ tailWord_714097) baseStart_714097 baseEnd_714097 := by
    simpa [prefixWord, tailWord_714097, baseEnd_714097] using wordTrace_append hprefix tailTrace_714097
  have hstable : (prefixWord ++ tailWord_714097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714097).length < 2 ^ (prefixWord ++ tailWord_714097).sum := by decide
  have hdescent : baseEnd_714097 < baseStart_714097 := by decide
  rcases family_descends (prefixWord ++ tailWord_714097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714138 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_714138 : Nat := 118140960795 + 714138 * 2 ^ 59
def prefixEnd_714138 : Nat := 4983230072969 + 3 ^ 40 * 714138 * 2
def baseEnd_714138 : Nat := 325952042347228591547329

theorem tailTrace_714138 : CollatzResearch.WordTrace tailWord_714138 prefixEnd_714138 325952042347228591547329 := by
  unfold tailWord_714138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511688171701866476343767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17364501791204977270250045 6511688171701866476343767)
  ·
    refine ⟨9767532257552799714515651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511688171701866476343767 9767532257552799714515651)
    ·
      refine ⟨14651298386329199571773477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9767532257552799714515651 14651298386329199571773477)
      ·
        refine ⟨2747118447436724919707527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14651298386329199571773477 2747118447436724919707527)
        ·
          refine ⟨4120677671155087379561291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747118447436724919707527 4120677671155087379561291)
          ·
            refine ⟨6181016506732631069341937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120677671155087379561291 6181016506732631069341937)
            ·
              refine ⟨4635762380049473302006453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6181016506732631069341937 4635762380049473302006453)
              ·
                refine ⟨434602723129638122063105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4635762380049473302006453 434602723129638122063105)
                ·
                  refine ⟨325952042347228591547329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434602723129638122063105 325952042347228591547329)
                  ·
                    rfl

theorem cell20_714138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_714138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714138 prefixEnd_714138 := by exact prefixLift 714138
  have htrace : WordTrace (prefixWord ++ tailWord_714138) baseStart_714138 baseEnd_714138 := by
    simpa [prefixWord, tailWord_714138, baseEnd_714138] using wordTrace_append hprefix tailTrace_714138
  have hstable : (prefixWord ++ tailWord_714138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714138).length < 2 ^ (prefixWord ++ tailWord_714138).sum := by decide
  have hdescent : baseEnd_714138 < baseStart_714138 := by decide
  rcases family_descends (prefixWord ++ tailWord_714138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714187 : List Nat := [1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_714187 : Nat := 118140960795 + 714187 * 2 ^ 59
def prefixEnd_714187 : Nat := 4983230072969 + 3 ^ 40 * 714187 * 2
def baseEnd_714187 : Nat := 108658135760800732971265

theorem tailTrace_714187 : CollatzResearch.WordTrace tailWord_714187 prefixEnd_714187 108658135760800732971265 := by
  unfold tailWord_714187
  simp only [CollatzResearch.WordTrace]
  refine ⟨26048539863629947273908815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17365693242419964849272543 26048539863629947273908815)
  ·
    refine ⟨39072809795444920910863223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26048539863629947273908815 39072809795444920910863223)
    ·
      refine ⟨58609214693167381366294835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39072809795444920910863223 58609214693167381366294835)
      ·
        refine ⟨87913822039751072049442253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58609214693167381366294835 87913822039751072049442253)
        ·
          refine ⟨32967683264906652018540845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87913822039751072049442253 32967683264906652018540845)
          ·
            refine ⟨12362881224339994506952817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32967683264906652018540845 12362881224339994506952817)
            ·
              refine ⟨9272160918254995880214613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12362881224339994506952817 9272160918254995880214613)
              ·
                refine ⟨108658135760800732971265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9272160918254995880214613 108658135760800732971265)
                ·
                  rfl

theorem cell20_714187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_714187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714187 prefixEnd_714187 := by exact prefixLift 714187
  have htrace : WordTrace (prefixWord ++ tailWord_714187) baseStart_714187 baseEnd_714187 := by
    simpa [prefixWord, tailWord_714187, baseEnd_714187] using wordTrace_append hprefix tailTrace_714187
  have hstable : (prefixWord ++ tailWord_714187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714187).length < 2 ^ (prefixWord ++ tailWord_714187).sum := by decide
  have hdescent : baseEnd_714187 < baseStart_714187 := by decide
  rcases family_descends (prefixWord ++ tailWord_714187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714238 : List Nat := [4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_714238 : Nat := 118140960795 + 714238 * 2 ^ 59
def prefixEnd_714238 : Nat := 4983230072969 + 3 ^ 40 * 714238 * 2
def baseEnd_714238 : Nat := 108665895024024229404529

theorem tailTrace_714238 : CollatzResearch.WordTrace tailWord_714238 prefixEnd_714238 108665895024024229404529 := by
  unfold tailWord_714238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256299998305647873001921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17366933324296788656010245 3256299998305647873001921)
  ·
    refine ⟨2442224998729235904751441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3256299998305647873001921 2442224998729235904751441)
    ·
      refine ⟨1831668749046926928563581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2442224998729235904751441 1831668749046926928563581)
      ·
        refine ⟨686875780892597598211343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1831668749046926928563581 686875780892597598211343)
        ·
          refine ⟨1030313671338896397317015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686875780892597598211343 1030313671338896397317015)
          ·
            refine ⟨1545470507008344595975523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030313671338896397317015 1545470507008344595975523)
            ·
              refine ⟨2318205760512516893963285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545470507008344595975523 2318205760512516893963285)
              ·
                refine ⟨108665895024024229404529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2318205760512516893963285 108665895024024229404529)
                ·
                  rfl

theorem cell20_714238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_714238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714238 prefixEnd_714238 := by exact prefixLift 714238
  have htrace : WordTrace (prefixWord ++ tailWord_714238) baseStart_714238 baseEnd_714238 := by
    simpa [prefixWord, tailWord_714238, baseEnd_714238] using wordTrace_append hprefix tailTrace_714238
  have hstable : (prefixWord ++ tailWord_714238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714238).length < 2 ^ (prefixWord ++ tailWord_714238).sum := by decide
  have hdescent : baseEnd_714238 < baseStart_714238 := by decide
  rcases family_descends (prefixWord ++ tailWord_714238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714269 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 2]
def baseStart_714269 : Nat := 118140960795 + 714269 * 2 ^ 59
def prefixEnd_714269 : Nat := 4983230072969 + 3 ^ 40 * 714269 * 2
def baseEnd_714269 : Nat := 326011834316774358180127

theorem tailTrace_714269 : CollatzResearch.WordTrace tailWord_714269 prefixEnd_714269 326011834316774358180127 := by
  unfold tailWord_714269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051530649332875278393861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17367687099555250185595907 26051530649332875278393861)
  ·
    refine ⟨4884661996749914114698849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26051530649332875278393861 4884661996749914114698849)
    ·
      refine ⟨3663496497562435586024137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4884661996749914114698849 3663496497562435586024137)
      ·
        refine ⟨2747622373171826689518103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3663496497562435586024137 2747622373171826689518103)
        ·
          refine ⟨4121433559757740034277155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747622373171826689518103 4121433559757740034277155)
          ·
            refine ⟨6182150339636610051415733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121433559757740034277155 6182150339636610051415733)
            ·
              refine ⟨579576594340932192320225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6182150339636610051415733 579576594340932192320225)
              ·
                refine ⟨434682445755699144240169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579576594340932192320225 434682445755699144240169)
                ·
                  refine ⟨326011834316774358180127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434682445755699144240169 326011834316774358180127)
                  ·
                    rfl

theorem cell20_714269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_714269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714269 prefixEnd_714269 := by exact prefixLift 714269
  have htrace : WordTrace (prefixWord ++ tailWord_714269) baseStart_714269 baseEnd_714269 := by
    simpa [prefixWord, tailWord_714269, baseEnd_714269] using wordTrace_append hprefix tailTrace_714269
  have hstable : (prefixWord ++ tailWord_714269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714269).length < 2 ^ (prefixWord ++ tailWord_714269).sum := by decide
  have hdescent : baseEnd_714269 < baseStart_714269 := by decide
  rcases family_descends (prefixWord ++ tailWord_714269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714273 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_714273 : Nat := 118140960795 + 714273 * 2 ^ 59
def prefixEnd_714273 : Nat := 4983230072969 + 3 ^ 40 * 714273 * 2
def baseEnd_714273 : Nat := 326013660025768122046777

theorem tailTrace_714273 : CollatzResearch.WordTrace tailWord_714273 prefixEnd_714273 326013660025768122046777 := by
  unfold tailWord_714273
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051676541318383961539473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17367784360878922641026315 26051676541318383961539473)
  ·
    refine ⟨19538757405988787971154605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26051676541318383961539473 19538757405988787971154605)
    ·
      refine ⟨7327034027245795489182977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19538757405988787971154605 7327034027245795489182977)
      ·
        refine ⟨5495275520434346616887233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327034027245795489182977 5495275520434346616887233)
        ·
          refine ⟨4121456640325759962665425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495275520434346616887233 4121456640325759962665425)
          ·
            refine ⟨3091092480244319971999069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121456640325759962665425 3091092480244319971999069)
            ·
              refine ⟨1159159680091619989499651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3091092480244319971999069 1159159680091619989499651)
              ·
                refine ⟨1738739520137429984249477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159159680091619989499651 1738739520137429984249477)
                ·
                  refine ⟨326013660025768122046777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738739520137429984249477 326013660025768122046777)
                  ·
                    rfl

theorem cell20_714273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_714273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714273 prefixEnd_714273 := by exact prefixLift 714273
  have htrace : WordTrace (prefixWord ++ tailWord_714273) baseStart_714273 baseEnd_714273 := by
    simpa [prefixWord, tailWord_714273, baseEnd_714273] using wordTrace_append hprefix tailTrace_714273
  have hstable : (prefixWord ++ tailWord_714273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714273).length < 2 ^ (prefixWord ++ tailWord_714273).sum := by decide
  have hdescent : baseEnd_714273 < baseStart_714273 := by decide
  rcases family_descends (prefixWord ++ tailWord_714273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714376 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_714376 : Nat := 118140960795 + 714376 * 2 ^ 59
def prefixEnd_714376 : Nat := 4983230072969 + 3 ^ 40 * 714376 * 2
def baseEnd_714376 : Nat := 326060672032357541613023

theorem tailTrace_714376 : CollatzResearch.WordTrace tailWord_714376 prefixEnd_714376 326060672032357541613023 := by
  unfold tailWord_714376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13027716629972616276269491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17370288839963488368359321 13027716629972616276269491)
  ·
    refine ⟨19541574944958924414404237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13027716629972616276269491 19541574944958924414404237)
    ·
      refine ⟨7328090604359596655401589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19541574944958924414404237 7328090604359596655401589)
      ·
        refine ⟨687008494158712186443899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7328090604359596655401589 687008494158712186443899)
        ·
          refine ⟨1030512741238068279665849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687008494158712186443899 1030512741238068279665849)
          ·
            refine ⟨772884555928551209749387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030512741238068279665849 772884555928551209749387)
            ·
              refine ⟨1159326833892826814624081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772884555928551209749387 1159326833892826814624081)
              ·
                refine ⟨869495125419620110968061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159326833892826814624081 869495125419620110968061)
                ·
                  refine ⟨326060672032357541613023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869495125419620110968061 326060672032357541613023)
                  ·
                    rfl

theorem cell20_714376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_714376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714376 prefixEnd_714376 := by exact prefixLift 714376
  have htrace : WordTrace (prefixWord ++ tailWord_714376) baseStart_714376 baseEnd_714376 := by
    simpa [prefixWord, tailWord_714376, baseEnd_714376] using wordTrace_append hprefix tailTrace_714376
  have hstable : (prefixWord ++ tailWord_714376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714376).length < 2 ^ (prefixWord ++ tailWord_714376).sum := by decide
  have hdescent : baseEnd_714376 < baseStart_714376 := by decide
  rcases family_descends (prefixWord ++ tailWord_714376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714415 : List Nat := [1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_714415 : Nat := 118140960795 + 714415 * 2 ^ 59
def prefixEnd_714415 : Nat := 4983230072969 + 3 ^ 40 * 714415 * 2
def baseEnd_714415 : Nat := 108692824231682246437621

theorem tailTrace_714415 : CollatzResearch.WordTrace tailWord_714415 prefixEnd_714415 108692824231682246437621 := by
  unfold tailWord_714415
  simp only [CollatzResearch.WordTrace]
  refine ⟨26056855706803942213208699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371237137869294808805799 26056855706803942213208699)
  ·
    refine ⟨39085283560205913319813049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26056855706803942213208699 39085283560205913319813049)
    ·
      refine ⟨29313962670154434989859787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39085283560205913319813049 29313962670154434989859787)
      ·
        refine ⟨43970944005231652484789681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29313962670154434989859787 43970944005231652484789681)
        ·
          refine ⟨32978208003923739363592261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43970944005231652484789681 32978208003923739363592261)
          ·
            refine ⟨6183414000735701130673549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32978208003923739363592261 6183414000735701130673549)
            ·
              refine ⟨2318780250275887924002581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183414000735701130673549 2318780250275887924002581)
              ·
                refine ⟨108692824231682246437621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2318780250275887924002581 108692824231682246437621)
                ·
                  rfl

theorem cell20_714415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_714415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714415 prefixEnd_714415 := by exact prefixLift 714415
  have htrace : WordTrace (prefixWord ++ tailWord_714415) baseStart_714415 baseEnd_714415 := by
    simpa [prefixWord, tailWord_714415, baseEnd_714415] using wordTrace_append hprefix tailTrace_714415
  have hstable : (prefixWord ++ tailWord_714415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714415).length < 2 ^ (prefixWord ++ tailWord_714415).sum := by decide
  have hdescent : baseEnd_714415 < baseStart_714415 := by decide
  rcases family_descends (prefixWord ++ tailWord_714415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714434 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_714434 : Nat := 118140960795 + 714434 * 2 ^ 59
def prefixEnd_714434 : Nat := 4983230072969 + 3 ^ 40 * 714434 * 2
def baseEnd_714434 : Nat := 326087144812767117679453

theorem tailTrace_714434 : CollatzResearch.WordTrace tailWord_714434 prefixEnd_714434 326087144812767117679453 := by
  unfold tailWord_714434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514387173433777114537589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17371699129156738972100237 6514387173433777114537589)
  ·
    refine ⟨610723797509416604487899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6514387173433777114537589 610723797509416604487899)
    ·
      refine ⟨916085696264124906731849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610723797509416604487899 916085696264124906731849)
      ·
        refine ⟨687064272198093680048887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 916085696264124906731849 687064272198093680048887)
        ·
          refine ⟨1030596408297140520073331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687064272198093680048887 1030596408297140520073331)
          ·
            refine ⟨1545894612445710780109997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030596408297140520073331 1545894612445710780109997)
            ·
              refine ⟨579710479667141542541249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545894612445710780109997 579710479667141542541249)
              ·
                refine ⟨434782859750356156905937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579710479667141542541249 434782859750356156905937)
                ·
                  refine ⟨326087144812767117679453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434782859750356156905937 326087144812767117679453)
                  ·
                    rfl

theorem cell20_714434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_714434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714434 prefixEnd_714434 := by exact prefixLift 714434
  have htrace : WordTrace (prefixWord ++ tailWord_714434) baseStart_714434 baseEnd_714434 := by
    simpa [prefixWord, tailWord_714434, baseEnd_714434] using wordTrace_append hprefix tailTrace_714434
  have hstable : (prefixWord ++ tailWord_714434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714434).length < 2 ^ (prefixWord ++ tailWord_714434).sum := by decide
  have hdescent : baseEnd_714434 < baseStart_714434 := by decide
  rcases family_descends (prefixWord ++ tailWord_714434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714438 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_714438 : Nat := 118140960795 + 714438 * 2 ^ 59
def prefixEnd_714438 : Nat := 4983230072969 + 3 ^ 40 * 714438 * 2
def baseEnd_714438 : Nat := 326088970521760881546103

theorem tailTrace_714438 : CollatzResearch.WordTrace tailWord_714438 prefixEnd_714438 326088970521760881546103 := by
  unfold tailWord_714438
  simp only [CollatzResearch.WordTrace]
  refine ⟨814302955803769285665499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17371796390480411427530645 814302955803769285665499)
  ·
    refine ⟨1221454433705653928498249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 814302955803769285665499 1221454433705653928498249)
    ·
      refine ⟨916090825279240446373687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221454433705653928498249 916090825279240446373687)
      ·
        refine ⟨1374136237918860669560531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916090825279240446373687 1374136237918860669560531)
        ·
          refine ⟨2061204356878291004340797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374136237918860669560531 2061204356878291004340797)
          ·
            refine ⟨772951633829359126627799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2061204356878291004340797 772951633829359126627799)
            ·
              refine ⟨1159427450744038689941699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772951633829359126627799 1159427450744038689941699)
              ·
                refine ⟨1739141176116058034912549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159427450744038689941699 1739141176116058034912549)
                ·
                  refine ⟨326088970521760881546103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739141176116058034912549 326088970521760881546103)
                  ·
                    rfl

theorem cell20_714438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_714438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714438 prefixEnd_714438 := by exact prefixLift 714438
  have htrace : WordTrace (prefixWord ++ tailWord_714438) baseStart_714438 baseEnd_714438 := by
    simpa [prefixWord, tailWord_714438, baseEnd_714438] using wordTrace_append hprefix tailTrace_714438
  have hstable : (prefixWord ++ tailWord_714438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714438).length < 2 ^ (prefixWord ++ tailWord_714438).sum := by decide
  have hdescent : baseEnd_714438 < baseStart_714438 := by decide
  rcases family_descends (prefixWord ++ tailWord_714438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714439 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_714439 : Nat := 118140960795 + 714439 * 2 ^ 59
def prefixEnd_714439 : Nat := 4983230072969 + 3 ^ 40 * 714439 * 2
def baseEnd_714439 : Nat := 326089426949009322512765

theorem tailTrace_714439 : CollatzResearch.WordTrace tailWord_714439 prefixEnd_714439 326089426949009322512765 := by
  unfold tailWord_714439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057731058716994312082371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371820705811329541388247 26057731058716994312082371)
  ·
    refine ⟨39086596588075491468123557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26057731058716994312082371 39086596588075491468123557)
    ·
      refine ⟨7328736860264154650273167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39086596588075491468123557 7328736860264154650273167)
      ·
        refine ⟨10993105290396231975409751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7328736860264154650273167 10993105290396231975409751)
        ·
          refine ⟨16489657935594347963114627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10993105290396231975409751 16489657935594347963114627)
          ·
            refine ⟨24734486903391521944671941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16489657935594347963114627 24734486903391521944671941)
            ·
              refine ⟨4637716294385910364625989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24734486903391521944671941 4637716294385910364625989)
              ·
                refine ⟨869571805197358193367373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4637716294385910364625989 869571805197358193367373)
                ·
                  refine ⟨326089426949009322512765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869571805197358193367373 326089426949009322512765)
                  ·
                    rfl

theorem cell20_714439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_714439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714439 prefixEnd_714439 := by exact prefixLift 714439
  have htrace : WordTrace (prefixWord ++ tailWord_714439) baseStart_714439 baseEnd_714439 := by
    simpa [prefixWord, tailWord_714439, baseEnd_714439] using wordTrace_append hprefix tailTrace_714439
  have hstable : (prefixWord ++ tailWord_714439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714439).length < 2 ^ (prefixWord ++ tailWord_714439).sum := by decide
  have hdescent : baseEnd_714439 < baseStart_714439 := by decide
  rcases family_descends (prefixWord ++ tailWord_714439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714442 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_714442 : Nat := 118140960795 + 714442 * 2 ^ 59
def prefixEnd_714442 : Nat := 4983230072969 + 3 ^ 40 * 714442 * 2
def baseEnd_714442 : Nat := 326090796230754645412753

theorem tailTrace_714442 : CollatzResearch.WordTrace tailWord_714442 prefixEnd_714442 326090796230754645412753 := by
  unfold tailWord_714442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514460119426531456110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17371893651804083882961053 6514460119426531456110395)
  ·
    refine ⟨9771690179139797184165593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6514460119426531456110395 9771690179139797184165593)
    ·
      refine ⟨7328767634354847888124195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9771690179139797184165593 7328767634354847888124195)
      ·
        refine ⟨10993151451532271832186293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7328767634354847888124195 10993151451532271832186293)
        ·
          refine ⟨1030607948581150484267465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10993151451532271832186293 1030607948581150484267465)
          ·
            refine ⟨772955961435862863200599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030607948581150484267465 772955961435862863200599)
            ·
              refine ⟨1159433942153794294800899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772955961435862863200599 1159433942153794294800899)
              ·
                refine ⟨1739150913230691442201349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159433942153794294800899 1739150913230691442201349)
                ·
                  refine ⟨326090796230754645412753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739150913230691442201349 326090796230754645412753)
                  ·
                    rfl

theorem cell20_714442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_714442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714442 prefixEnd_714442 := by exact prefixLift 714442
  have htrace : WordTrace (prefixWord ++ tailWord_714442) baseStart_714442 baseEnd_714442 := by
    simpa [prefixWord, tailWord_714442, baseEnd_714442] using wordTrace_append hprefix tailTrace_714442
  have hstable : (prefixWord ++ tailWord_714442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714442).length < 2 ^ (prefixWord ++ tailWord_714442).sum := by decide
  have hdescent : baseEnd_714442 < baseStart_714442 := by decide
  rcases family_descends (prefixWord ++ tailWord_714442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714452 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_714452 : Nat := 118140960795 + 714452 * 2 ^ 59
def prefixEnd_714452 : Nat := 4983230072969 + 3 ^ 40 * 714452 * 2
def baseEnd_714452 : Nat := 326095360503239055079379

theorem tailTrace_714452 : CollatzResearch.WordTrace tailWord_714452 prefixEnd_714452 326095360503239055079379 := by
  unfold tailWord_714452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029102603834948766152805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17372136805113265021537073 13029102603834948766152805)
  ·
    refine ⟨2442956738219052893653651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13029102603834948766152805 2442956738219052893653651)
    ·
      refine ⟨3664435107328579340480477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2442956738219052893653651 3664435107328579340480477)
      ·
        refine ⟨1374163165248217252680179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3664435107328579340480477 1374163165248217252680179)
        ·
          refine ⟨2061244747872325879020269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374163165248217252680179 2061244747872325879020269)
          ·
            refine ⟨772966780452122204632601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2061244747872325879020269 772966780452122204632601)
            ·
              refine ⟨579725085339091653474451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772966780452122204632601 579725085339091653474451)
              ·
                refine ⟨869587628008637480211677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579725085339091653474451 869587628008637480211677)
                ·
                  refine ⟨326095360503239055079379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869587628008637480211677 326095360503239055079379)
                  ·
                    rfl

theorem cell20_714452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_714452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714452 prefixEnd_714452 := by exact prefixLift 714452
  have htrace : WordTrace (prefixWord ++ tailWord_714452) baseStart_714452 baseEnd_714452 := by
    simpa [prefixWord, tailWord_714452, baseEnd_714452] using wordTrace_append hprefix tailTrace_714452
  have hstable : (prefixWord ++ tailWord_714452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714452).length < 2 ^ (prefixWord ++ tailWord_714452).sum := by decide
  have hdescent : baseEnd_714452 < baseStart_714452 := by decide
  rcases family_descends (prefixWord ++ tailWord_714452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714522 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_714522 : Nat := 118140960795 + 714522 * 2 ^ 59
def prefixEnd_714522 : Nat := 4983230072969 + 3 ^ 40 * 714522 * 2
def baseEnd_714522 : Nat := 326127310410629922745759

theorem tailTrace_714522 : CollatzResearch.WordTrace tailWord_714522 prefixEnd_714522 326127310410629922745759 := by
  unfold tailWord_714522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515189579354074871838455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17373838878277532991569213 6515189579354074871838455)
  ·
    refine ⟨9772784369031112307757683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6515189579354074871838455 9772784369031112307757683)
    ·
      refine ⟨14659176553546668461636525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9772784369031112307757683 14659176553546668461636525)
      ·
        refine ⟨5497191207580000673113697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14659176553546668461636525 5497191207580000673113697)
        ·
          refine ⟨4122893405685000504835273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5497191207580000673113697 4122893405685000504835273)
          ·
            refine ⟨3092170054263750378626455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4122893405685000504835273 3092170054263750378626455)
            ·
              refine ⟨4638255081395625567939683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092170054263750378626455 4638255081395625567939683)
              ·
                refine ⟨6957382622093438351909525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638255081395625567939683 6957382622093438351909525)
                ·
                  refine ⟨326127310410629922745759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6957382622093438351909525 326127310410629922745759)
                  ·
                    rfl

theorem cell20_714522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_714522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714522 prefixEnd_714522 := by exact prefixLift 714522
  have htrace : WordTrace (prefixWord ++ tailWord_714522) baseStart_714522 baseEnd_714522 := by
    simpa [prefixWord, tailWord_714522, baseEnd_714522] using wordTrace_append hprefix tailTrace_714522
  have hstable : (prefixWord ++ tailWord_714522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714522).length < 2 ^ (prefixWord ++ tailWord_714522).sum := by decide
  have hdescent : baseEnd_714522 < baseStart_714522 := by decide
  rcases family_descends (prefixWord ++ tailWord_714522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714549 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_714549 : Nat := 118140960795 + 714549 * 2 ^ 59
def prefixEnd_714549 : Nat := 4983230072969 + 3 ^ 40 * 714549 * 2
def baseEnd_714549 : Nat := 326139633946337828845649

theorem tailTrace_714549 : CollatzResearch.WordTrace tailWord_714549 prefixEnd_714549 326139633946337828845649 := by
  unfold tailWord_714549
  simp only [CollatzResearch.WordTrace]
  refine ⟨26061743088318483098586701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17374495392212322065724467 26061743088318483098586701)
  ·
    refine ⟨9773153658119431161970013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26061743088318483098586701 9773153658119431161970013)
    ·
      refine ⟨3664932621794786685738755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9773153658119431161970013 3664932621794786685738755)
      ·
        refine ⟨5497398932692180028608133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664932621794786685738755 5497398932692180028608133)
        ·
          refine ⟨1030762299879783755364025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5497398932692180028608133 1030762299879783755364025)
          ·
            refine ⟨773071724909837816523019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030762299879783755364025 773071724909837816523019)
            ·
              refine ⟨1159607587364756724784529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773071724909837816523019 1159607587364756724784529)
              ·
                refine ⟨869705690523567543588397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159607587364756724784529 869705690523567543588397)
                ·
                  refine ⟨326139633946337828845649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869705690523567543588397 326139633946337828845649)
                  ·
                    rfl

theorem cell20_714549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_714549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714549 prefixEnd_714549 := by exact prefixLift 714549
  have htrace : WordTrace (prefixWord ++ tailWord_714549) baseStart_714549 baseEnd_714549 := by
    simpa [prefixWord, tailWord_714549, baseEnd_714549] using wordTrace_append hprefix tailTrace_714549
  have hstable : (prefixWord ++ tailWord_714549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714549).length < 2 ^ (prefixWord ++ tailWord_714549).sum := by decide
  have hdescent : baseEnd_714549 < baseStart_714549 := by decide
  rcases family_descends (prefixWord ++ tailWord_714549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714570 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_714570 : Nat := 118140960795 + 714570 * 2 ^ 59
def prefixEnd_714570 : Nat := 4983230072969 + 3 ^ 40 * 714570 * 2
def baseEnd_714570 : Nat := 326149218918555089145563

theorem tailTrace_714570 : CollatzResearch.WordTrace tailWord_714570 prefixEnd_714570 326149218918555089145563 := by
  unfold tailWord_714570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515627255310600921275291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17375006014161602456734109 6515627255310600921275291)
  ·
    refine ⟨9773440882965901381912937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6515627255310600921275291 9773440882965901381912937)
    ·
      refine ⟨7330080662224426036434703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9773440882965901381912937 7330080662224426036434703)
      ·
        refine ⟨10995120993336639054652055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330080662224426036434703 10995120993336639054652055)
        ·
          refine ⟨16492681490004958581978083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995120993336639054652055 16492681490004958581978083)
          ·
            refine ⟨24739022235007437872967125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16492681490004958581978083 24739022235007437872967125)
            ·
              refine ⟨579820833632986825147667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24739022235007437872967125 579820833632986825147667)
              ·
                refine ⟨869731250449480237721501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579820833632986825147667 869731250449480237721501)
                ·
                  refine ⟨326149218918555089145563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869731250449480237721501 326149218918555089145563)
                  ·
                    rfl

theorem cell20_714570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_714570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714570 prefixEnd_714570 := by exact prefixLift 714570
  have htrace : WordTrace (prefixWord ++ tailWord_714570) baseStart_714570 baseEnd_714570 := by
    simpa [prefixWord, tailWord_714570, baseEnd_714570] using wordTrace_append hprefix tailTrace_714570
  have hstable : (prefixWord ++ tailWord_714570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714570).length < 2 ^ (prefixWord ++ tailWord_714570).sum := by decide
  have hdescent : baseEnd_714570 < baseStart_714570 := by decide
  rcases family_descends (prefixWord ++ tailWord_714570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714605 : List Nat := [1, 5, 1, 1, 1, 1, 10]
def baseStart_714605 : Nat := 118140960795 + 714605 * 2 ^ 59
def prefixEnd_714605 : Nat := 4983230072969 + 3 ^ 40 * 714605 * 2
def baseEnd_714605 : Nat := 36240577096916724775417

theorem tailTrace_714605 : CollatzResearch.WordTrace tailWord_714605 prefixEnd_714605 36240577096916724775417 := by
  unfold tailWord_714605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063785576115604662625269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17375857050743736441750179 26063785576115604662625269)
  ·
    refine ⟨2443479897760837937121119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26063785576115604662625269 2443479897760837937121119)
    ·
      refine ⟨3665219846641256905681679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443479897760837937121119 3665219846641256905681679)
      ·
        refine ⟨5497829769961885358522519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665219846641256905681679 5497829769961885358522519)
        ·
          refine ⟨8246744654942828037783779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497829769961885358522519 8246744654942828037783779)
          ·
            refine ⟨12370116982414242056675669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246744654942828037783779 12370116982414242056675669)
            ·
              refine ⟨36240577096916724775417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12370116982414242056675669 36240577096916724775417)
              ·
                rfl

theorem cell20_714605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_714605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714605 prefixEnd_714605 := by exact prefixLift 714605
  have htrace : WordTrace (prefixWord ++ tailWord_714605) baseStart_714605 baseEnd_714605 := by
    simpa [prefixWord, tailWord_714605, baseEnd_714605] using wordTrace_append hprefix tailTrace_714605
  have hstable : (prefixWord ++ tailWord_714605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714605).length < 2 ^ (prefixWord ++ tailWord_714605).sum := by decide
  have hdescent : baseEnd_714605 < baseStart_714605 := by decide
  rcases family_descends (prefixWord ++ tailWord_714605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714625 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_714625 : Nat := 118140960795 + 714625 * 2 ^ 59
def prefixEnd_714625 : Nat := 4983230072969 + 3 ^ 40 * 714625 * 2
def baseEnd_714625 : Nat := 326174322417219342312005

theorem tailTrace_714625 : CollatzResearch.WordTrace tailWord_714625 prefixEnd_714625 326174322417219342312005 := by
  unfold tailWord_714625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064515036043148078353329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17376343357362098718902219 26064515036043148078353329)
  ·
    refine ⟨19548386277032361058764997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26064515036043148078353329 19548386277032361058764997)
    ·
      refine ⟨3665322426943567698518437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19548386277032361058764997 3665322426943567698518437)
      ·
        refine ⟨687247955051918943472207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3665322426943567698518437 687247955051918943472207)
        ·
          refine ⟨1030871932577878415208311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687247955051918943472207 1030871932577878415208311)
          ·
            refine ⟨1546307898866817622812467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030871932577878415208311 1546307898866817622812467)
            ·
              refine ⟨2319461848300226434218701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546307898866817622812467 2319461848300226434218701)
              ·
                refine ⟨869798193112584912832013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319461848300226434218701 869798193112584912832013)
                ·
                  refine ⟨326174322417219342312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869798193112584912832013 326174322417219342312005)
                  ·
                    rfl

theorem cell20_714625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_714625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714625 prefixEnd_714625 := by exact prefixLift 714625
  have htrace : WordTrace (prefixWord ++ tailWord_714625) baseStart_714625 baseEnd_714625 := by
    simpa [prefixWord, tailWord_714625, baseEnd_714625] using wordTrace_append hprefix tailTrace_714625
  have hstable : (prefixWord ++ tailWord_714625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714625).length < 2 ^ (prefixWord ++ tailWord_714625).sum := by decide
  have hdescent : baseEnd_714625 < baseStart_714625 := by decide
  rcases family_descends (prefixWord ++ tailWord_714625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714629 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_714629 : Nat := 118140960795 + 714629 * 2 ^ 59
def prefixEnd_714629 : Nat := 4983230072969 + 3 ^ 40 * 714629 * 2
def baseEnd_714629 : Nat := 326176148126213106178655

theorem tailTrace_714629 : CollatzResearch.WordTrace tailWord_714629 prefixEnd_714629 326176148126213106178655 := by
  unfold tailWord_714629
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064660928028656761498941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17376440618685771174332627 26064660928028656761498941)
  ·
    refine ⟨9774247848010746285562103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26064660928028656761498941 9774247848010746285562103)
    ·
      refine ⟨14661371772016119428343155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9774247848010746285562103 14661371772016119428343155)
      ·
        refine ⟨21992057658024179142514733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661371772016119428343155 21992057658024179142514733)
        ·
          refine ⟨8247021621759067178443025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21992057658024179142514733 8247021621759067178443025)
          ·
            refine ⟨6185266216319300383832269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8247021621759067178443025 6185266216319300383832269)
            ·
              refine ⟨2319474831119737643937101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6185266216319300383832269 2319474831119737643937101)
              ·
                refine ⟨869803061669901616476413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319474831119737643937101 869803061669901616476413)
                ·
                  refine ⟨326176148126213106178655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869803061669901616476413 326176148126213106178655)
                  ·
                    rfl

theorem cell20_714629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_714629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714629 prefixEnd_714629 := by exact prefixLift 714629
  have htrace : WordTrace (prefixWord ++ tailWord_714629) baseStart_714629 baseEnd_714629 := by
    simpa [prefixWord, tailWord_714629, baseEnd_714629] using wordTrace_append hprefix tailTrace_714629
  have hstable : (prefixWord ++ tailWord_714629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714629).length < 2 ^ (prefixWord ++ tailWord_714629).sum := by decide
  have hdescent : baseEnd_714629 < baseStart_714629 := by decide
  rcases family_descends (prefixWord ++ tailWord_714629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714708 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_714708 : Nat := 118140960795 + 714708 * 2 ^ 59
def prefixEnd_714708 : Nat := 4983230072969 + 3 ^ 40 * 714708 * 2
def baseEnd_714708 : Nat := 326212205878839942544999

theorem tailTrace_714708 : CollatzResearch.WordTrace tailWord_714708 prefixEnd_714708 326212205878839942544999 := by
  unfold tailWord_714708
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033771147371226626812389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17378361529828302169083185 13033771147371226626812389)
  ·
    refine ⟨2443832090132104992527323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13033771147371226626812389 2443832090132104992527323)
    ·
      refine ⟨3665748135198157488790985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443832090132104992527323 3665748135198157488790985)
      ·
        refine ⟨2749311101398618116593239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665748135198157488790985 2749311101398618116593239)
        ·
          refine ⟨4123966652097927174889859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749311101398618116593239 4123966652097927174889859)
          ·
            refine ⟨6185949978146890762334789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123966652097927174889859 6185949978146890762334789)
            ·
              refine ⟨1159865620902542017937773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6185949978146890762334789 1159865620902542017937773)
              ·
                refine ⟨434949607838453256726665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159865620902542017937773 434949607838453256726665)
                ·
                  refine ⟨326212205878839942544999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434949607838453256726665 326212205878839942544999)
                  ·
                    rfl

theorem cell20_714708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_714708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714708 prefixEnd_714708 := by exact prefixLift 714708
  have htrace : WordTrace (prefixWord ++ tailWord_714708) baseStart_714708 baseEnd_714708 := by
    simpa [prefixWord, tailWord_714708, baseEnd_714708] using wordTrace_append hprefix tailTrace_714708
  have hstable : (prefixWord ++ tailWord_714708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714708).length < 2 ^ (prefixWord ++ tailWord_714708).sum := by decide
  have hdescent : baseEnd_714708 < baseStart_714708 := by decide
  rcases family_descends (prefixWord ++ tailWord_714708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714719 : List Nat := [1, 1, 2, 3, 4, 2, 7]
def baseStart_714719 : Nat := 118140960795 + 714719 * 2 ^ 59
def prefixEnd_714719 : Nat := 4983230072969 + 3 ^ 40 * 714719 * 2
def baseEnd_714719 : Nat := 36246358508730310353143

theorem tailTrace_714719 : CollatzResearch.WordTrace tailWord_714719 prefixEnd_714719 36246358508730310353143 := by
  unfold tailWord_714719
  simp only [CollatzResearch.WordTrace]
  refine ⟨26067943497702602132275211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17378628998468401421516807 26067943497702602132275211)
  ·
    refine ⟨39101915246553903198412817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26067943497702602132275211 39101915246553903198412817)
    ·
      refine ⟨29326436434915427398809613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39101915246553903198412817 29326436434915427398809613)
      ·
        refine ⟨10997413663093285274553605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29326436434915427398809613 10997413663093285274553605)
        ·
          refine ⟨2062015061829990988978801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10997413663093285274553605 2062015061829990988978801)
          ·
            refine ⟨1546511296372493241734101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062015061829990988978801 1546511296372493241734101)
            ·
              refine ⟨36246358508730310353143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1546511296372493241734101 36246358508730310353143)
              ·
                rfl

theorem cell20_714719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_714719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714719 prefixEnd_714719 := by exact prefixLift 714719
  have htrace : WordTrace (prefixWord ++ tailWord_714719) baseStart_714719 baseEnd_714719 := by
    simpa [prefixWord, tailWord_714719, baseEnd_714719] using wordTrace_append hprefix tailTrace_714719
  have hstable : (prefixWord ++ tailWord_714719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714719).length < 2 ^ (prefixWord ++ tailWord_714719).sum := by decide
  have hdescent : baseEnd_714719 < baseStart_714719 := by decide
  rcases family_descends (prefixWord ++ tailWord_714719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714757 : List Nat := [1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_714757 : Nat := 118140960795 + 714757 * 2 ^ 59
def prefixEnd_714757 : Nat := 4983230072969 + 3 ^ 40 * 714757 * 2
def baseEnd_714757 : Nat := 108744856938004516637155

theorem tailTrace_714757 : CollatzResearch.WordTrace tailWord_714757 prefixEnd_714757 108744856938004516637155 := by
  unfold tailWord_714757
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069329471564934622158525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17379552981043289748105683 26069329471564934622158525)
  ·
    refine ⟨9775998551836850483309447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26069329471564934622158525 9775998551836850483309447)
    ·
      refine ⟨14663997827755275724964171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9775998551836850483309447 14663997827755275724964171)
      ·
        refine ⟨21995996741632913587446257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14663997827755275724964171 21995996741632913587446257)
        ·
          refine ⟨16496997556224685190584693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21995996741632913587446257 16496997556224685190584693)
          ·
            refine ⟨1546593520896064236617315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16496997556224685190584693 1546593520896064236617315)
            ·
              refine ⟨2319890281344096354925973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546593520896064236617315 2319890281344096354925973)
              ·
                refine ⟨108744856938004516637155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2319890281344096354925973 108744856938004516637155)
                ·
                  rfl

theorem cell20_714757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_714757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714757 prefixEnd_714757 := by exact prefixLift 714757
  have htrace : WordTrace (prefixWord ++ tailWord_714757) baseStart_714757 baseEnd_714757 := by
    simpa [prefixWord, tailWord_714757, baseEnd_714757] using wordTrace_append hprefix tailTrace_714757
  have hstable : (prefixWord ++ tailWord_714757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714757).length < 2 ^ (prefixWord ++ tailWord_714757).sum := by decide
  have hdescent : baseEnd_714757 < baseStart_714757 := by decide
  rcases family_descends (prefixWord ++ tailWord_714757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714764 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_714764 : Nat := 118140960795 + 714764 * 2 ^ 59
def prefixEnd_714764 : Nat := 4983230072969 + 3 ^ 40 * 714764 * 2
def baseEnd_714764 : Nat := 326237765804752636678103

theorem tailTrace_714764 : CollatzResearch.WordTrace tailWord_714764 prefixEnd_714764 326237765804752636678103 := by
  unfold tailWord_714764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034792391269787408831673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17379723188359716545108897 13034792391269787408831673)
  ·
    refine ⟨9776094293452340556623755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13034792391269787408831673 9776094293452340556623755)
    ·
      refine ⟨14664141440178510834935633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776094293452340556623755 14664141440178510834935633)
      ·
        refine ⟨10998106080133883126201725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14664141440178510834935633 10998106080133883126201725)
        ·
          refine ⟨4124289780050206172325647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10998106080133883126201725 4124289780050206172325647)
          ·
            refine ⟨6186434670075309258488471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124289780050206172325647 6186434670075309258488471)
            ·
              refine ⟨9279652005112963887732707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186434670075309258488471 9279652005112963887732707)
              ·
                refine ⟨13919478007669445831599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9279652005112963887732707 13919478007669445831599061)
                ·
                  refine ⟨326237765804752636678103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13919478007669445831599061 326237765804752636678103)
                  ·
                    rfl

theorem cell20_714764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_714764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714764 prefixEnd_714764 := by exact prefixLift 714764
  have htrace : WordTrace (prefixWord ++ tailWord_714764) baseStart_714764 baseEnd_714764 := by
    simpa [prefixWord, tailWord_714764, baseEnd_714764] using wordTrace_append hprefix tailTrace_714764
  have hstable : (prefixWord ++ tailWord_714764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714764).length < 2 ^ (prefixWord ++ tailWord_714764).sum := by decide
  have hdescent : baseEnd_714764 < baseStart_714764 := by decide
  rcases family_descends (prefixWord ++ tailWord_714764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714771 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_714771 : Nat := 118140960795 + 714771 * 2 ^ 59
def prefixEnd_714771 : Nat := 4983230072969 + 3 ^ 40 * 714771 * 2
def baseEnd_714771 : Nat := 326240960795491723444741

theorem tailTrace_714771 : CollatzResearch.WordTrace tailWord_714771 prefixEnd_714771 326240960795491723444741 := by
  unfold tailWord_714771
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069840093514215013168167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17379893395676143342112111 26069840093514215013168167)
  ·
    refine ⟨39104760140271322519752251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26069840093514215013168167 39104760140271322519752251)
    ·
      refine ⟨58657140210406983779628377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39104760140271322519752251 58657140210406983779628377)
      ·
        refine ⟨43992855157805237834721283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58657140210406983779628377 43992855157805237834721283)
        ·
          refine ⟨65989282736707856752081925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43992855157805237834721283 65989282736707856752081925)
          ·
            refine ⟨12372990513132723141015361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65989282736707856752081925 12372990513132723141015361)
            ·
              refine ⟨9279742884849542355761521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12372990513132723141015361 9279742884849542355761521)
              ·
                refine ⟨6959807163637156766821141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279742884849542355761521 6959807163637156766821141)
                ·
                  refine ⟨326240960795491723444741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6959807163637156766821141 326240960795491723444741)
                  ·
                    rfl

theorem cell20_714771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_714771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714771 prefixEnd_714771 := by exact prefixLift 714771
  have htrace : WordTrace (prefixWord ++ tailWord_714771) baseStart_714771 baseEnd_714771 := by
    simpa [prefixWord, tailWord_714771, baseEnd_714771] using wordTrace_append hprefix tailTrace_714771
  have hstable : (prefixWord ++ tailWord_714771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714771).length < 2 ^ (prefixWord ++ tailWord_714771).sum := by decide
  have hdescent : baseEnd_714771 < baseStart_714771 := by decide
  rcases family_descends (prefixWord ++ tailWord_714771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714781 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_714781 : Nat := 118140960795 + 714781 * 2 ^ 59
def prefixEnd_714781 : Nat := 4983230072969 + 3 ^ 40 * 714781 * 2
def baseEnd_714781 : Nat := 326245525067976133111367

theorem tailTrace_714781 : CollatzResearch.WordTrace tailWord_714781 prefixEnd_714781 326245525067976133111367 := by
  unfold tailWord_714781
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070204823477986721032197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17380136548985324480688131 26070204823477986721032197)
  ·
    refine ⟨4888163404402122510193537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26070204823477986721032197 4888163404402122510193537)
    ·
      refine ⟨3666122553301591882645153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4888163404402122510193537 3666122553301591882645153)
      ·
        refine ⟨2749591914976193911983865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666122553301591882645153 2749591914976193911983865)
        ·
          refine ⟨2062193936232145433987899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2749591914976193911983865 2062193936232145433987899)
          ·
            refine ⟨3093290904348218150981849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062193936232145433987899 3093290904348218150981849)
            ·
              refine ⟨2319968178261163613236387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093290904348218150981849 2319968178261163613236387)
              ·
                refine ⟨3479952267391745419854581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319968178261163613236387 3479952267391745419854581)
                ·
                  refine ⟨326245525067976133111367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3479952267391745419854581 326245525067976133111367)
                  ·
                    rfl

theorem cell20_714781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_714781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714781 prefixEnd_714781 := by exact prefixLift 714781
  have htrace : WordTrace (prefixWord ++ tailWord_714781) baseStart_714781 baseEnd_714781 := by
    simpa [prefixWord, tailWord_714781, baseEnd_714781] using wordTrace_append hprefix tailTrace_714781
  have hstable : (prefixWord ++ tailWord_714781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714781).length < 2 ^ (prefixWord ++ tailWord_714781).sum := by decide
  have hdescent : baseEnd_714781 < baseStart_714781 := by decide
  rcases family_descends (prefixWord ++ tailWord_714781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714791 : List Nat := [1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_714791 : Nat := 118140960795 + 714791 * 2 ^ 59
def prefixEnd_714791 : Nat := 4983230072969 + 3 ^ 40 * 714791 * 2
def baseEnd_714791 : Nat := 108750029780153514259331

theorem tailTrace_714791 : CollatzResearch.WordTrace tailWord_714791 prefixEnd_714791 108750029780153514259331 := by
  unfold tailWord_714791
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070569553441758428896227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17380379702294505619264151 26070569553441758428896227)
  ·
    refine ⟨39105854330162637643344341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26070569553441758428896227 39105854330162637643344341)
    ·
      refine ⟨916543460863186819765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39105854330162637643344341 916543460863186819765883)
      ·
        refine ⟨1374815191294780229648825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916543460863186819765883 1374815191294780229648825)
        ·
          refine ⟨1031111393471085172236619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374815191294780229648825 1031111393471085172236619)
          ·
            refine ⟨1546667090206627758354929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031111393471085172236619 1546667090206627758354929)
            ·
              refine ⟨1160000317654970818766197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546667090206627758354929 1160000317654970818766197)
              ·
                refine ⟨108750029780153514259331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160000317654970818766197 108750029780153514259331)
                ·
                  rfl

theorem cell20_714791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_714791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714791 prefixEnd_714791 := by exact prefixLift 714791
  have htrace : WordTrace (prefixWord ++ tailWord_714791) baseStart_714791 baseEnd_714791 := by
    simpa [prefixWord, tailWord_714791, baseEnd_714791] using wordTrace_append hprefix tailTrace_714791
  have hstable : (prefixWord ++ tailWord_714791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714791).length < 2 ^ (prefixWord ++ tailWord_714791).sum := by decide
  have hdescent : baseEnd_714791 < baseStart_714791 := by decide
  rcases family_descends (prefixWord ++ tailWord_714791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714798 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_714798 : Nat := 118140960795 + 714798 * 2 ^ 59
def prefixEnd_714798 : Nat := 4983230072969 + 3 ^ 40 * 714798 * 2
def baseEnd_714798 : Nat := 326253284331199629544631

theorem tailTrace_714798 : CollatzResearch.WordTrace tailWord_714798 prefixEnd_714798 326253284331199629544631 := by
  unfold tailWord_714798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258853108052049828050131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17380549909610932416267365 3258853108052049828050131)
  ·
    refine ⟨4888279662078074742075197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3258853108052049828050131 4888279662078074742075197)
    ·
      refine ⟨1833104873279278028278199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4888279662078074742075197 1833104873279278028278199)
      ·
        refine ⟨2749657309918917042417299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833104873279278028278199 2749657309918917042417299)
        ·
          refine ⟨4124485964878375563625949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749657309918917042417299 4124485964878375563625949)
          ·
            refine ⟨1546682236829390836359731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4124485964878375563625949 1546682236829390836359731)
            ·
              refine ⟨2320023355244086254539597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546682236829390836359731 2320023355244086254539597)
              ·
                refine ⟨870008758216532345452349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320023355244086254539597 870008758216532345452349)
                ·
                  refine ⟨326253284331199629544631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870008758216532345452349 326253284331199629544631)
                  ·
                    rfl

theorem cell20_714798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_714798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714798 prefixEnd_714798 := by exact prefixLift 714798
  have htrace : WordTrace (prefixWord ++ tailWord_714798) baseStart_714798 baseEnd_714798 := by
    simpa [prefixWord, tailWord_714798, baseEnd_714798] using wordTrace_append hprefix tailTrace_714798
  have hstable : (prefixWord ++ tailWord_714798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714798).length < 2 ^ (prefixWord ++ tailWord_714798).sum := by decide
  have hdescent : baseEnd_714798 < baseStart_714798 := by decide
  rcases family_descends (prefixWord ++ tailWord_714798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714864 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_714864 : Nat := 118140960795 + 714864 * 2 ^ 59
def prefixEnd_714864 : Nat := 4983230072969 + 3 ^ 40 * 714864 * 2
def baseEnd_714864 : Nat := 326283408529596733344361

theorem tailTrace_714864 : CollatzResearch.WordTrace tailWord_714864 prefixEnd_714864 326283408529596733344361 := by
  unfold tailWord_714864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036616041088645948151823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17382154721451527930869097 13036616041088645948151823)
  ·
    refine ⟨19554924061632968922227735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13036616041088645948151823 19554924061632968922227735)
    ·
      refine ⟨29332386092449453383341603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19554924061632968922227735 29332386092449453383341603)
      ·
        refine ⟨43998579138674180075012405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29332386092449453383341603 43998579138674180075012405)
        ·
          refine ⟨4124866794250704382032413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43998579138674180075012405 4124866794250704382032413)
          ·
            refine ⟨1546825047844014143262155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4124866794250704382032413 1546825047844014143262155)
            ·
              refine ⟨2320237571766021214893233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546825047844014143262155 2320237571766021214893233)
              ·
                refine ⟨1740178178824515911169925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320237571766021214893233 1740178178824515911169925)
                ·
                  refine ⟨326283408529596733344361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740178178824515911169925 326283408529596733344361)
                  ·
                    rfl

theorem cell20_714864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_714864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714864 prefixEnd_714864 := by exact prefixLift 714864
  have htrace : WordTrace (prefixWord ++ tailWord_714864) baseStart_714864 baseEnd_714864 := by
    simpa [prefixWord, tailWord_714864, baseEnd_714864] using wordTrace_append hprefix tailTrace_714864
  have hstable : (prefixWord ++ tailWord_714864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714864).length < 2 ^ (prefixWord ++ tailWord_714864).sum := by decide
  have hdescent : baseEnd_714864 < baseStart_714864 := by decide
  rcases family_descends (prefixWord ++ tailWord_714864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714912 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_714912 : Nat := 118140960795 + 714912 * 2 ^ 59
def prefixEnd_714912 : Nat := 4983230072969 + 3 ^ 40 * 714912 * 2
def baseEnd_714912 : Nat := 326305317037521899744165

theorem tailTrace_714912 : CollatzResearch.WordTrace tailWord_714912 prefixEnd_714912 326305317037521899744165 := by
  unfold tailWord_714912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037491393001698047025495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17383321857335597396033993 13037491393001698047025495)
  ·
    refine ⟨19556237089502547070538243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13037491393001698047025495 19556237089502547070538243)
    ·
      refine ⟨29334355634253820605807365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19556237089502547070538243 29334355634253820605807365)
      ·
        refine ⟨5500191681422591363588881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29334355634253820605807365 5500191681422591363588881)
        ·
          refine ⟨4125143761066943522691661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5500191681422591363588881 4125143761066943522691661)
          ·
            refine ⟨1546928910400103821009373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4125143761066943522691661 1546928910400103821009373)
            ·
              refine ⟨580098341400038932878515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1546928910400103821009373 580098341400038932878515)
              ·
                refine ⟨870147512100058399317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580098341400038932878515 870147512100058399317773)
                ·
                  refine ⟨326305317037521899744165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870147512100058399317773 326305317037521899744165)
                  ·
                    rfl

theorem cell20_714912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_714912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714912 prefixEnd_714912 := by exact prefixLift 714912
  have htrace : WordTrace (prefixWord ++ tailWord_714912) baseStart_714912 baseEnd_714912 := by
    simpa [prefixWord, tailWord_714912, baseEnd_714912] using wordTrace_append hprefix tailTrace_714912
  have hstable : (prefixWord ++ tailWord_714912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714912).length < 2 ^ (prefixWord ++ tailWord_714912).sum := by decide
  have hdescent : baseEnd_714912 < baseStart_714912 := by decide
  rcases family_descends (prefixWord ++ tailWord_714912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714922 : List Nat := [3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_714922 : Nat := 118140960795 + 714922 * 2 ^ 59
def prefixEnd_714922 : Nat := 4983230072969 + 3 ^ 40 * 714922 * 2
def baseEnd_714922 : Nat := 108769960436668769803597

theorem tailTrace_714922 : CollatzResearch.WordTrace tailWord_714922 prefixEnd_714922 108769960436668769803597 := by
  unfold tailWord_714922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518836878991791950478755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17383565010644778534610013 6518836878991791950478755)
  ·
    refine ⟨9778255318487687925718133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6518836878991791950478755 9778255318487687925718133)
    ·
      refine ⟨916711436108220743036075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9778255318487687925718133 916711436108220743036075)
      ·
        refine ⟨1375067154162331114554113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916711436108220743036075 1375067154162331114554113)
        ·
          refine ⟨1031300365621748335915585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375067154162331114554113 1031300365621748335915585)
          ·
            refine ⟨773475274216311251936689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031300365621748335915585 773475274216311251936689)
            ·
              refine ⟨580106455662233438952517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773475274216311251936689 580106455662233438952517)
              ·
                refine ⟨108769960436668769803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580106455662233438952517 108769960436668769803597)
                ·
                  rfl

theorem cell20_714922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_714922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714922 prefixEnd_714922 := by exact prefixLift 714922
  have htrace : WordTrace (prefixWord ++ tailWord_714922) baseStart_714922 baseEnd_714922 := by
    simpa [prefixWord, tailWord_714922, baseEnd_714922] using wordTrace_append hprefix tailTrace_714922
  have hstable : (prefixWord ++ tailWord_714922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714922).length < 2 ^ (prefixWord ++ tailWord_714922).sum := by decide
  have hdescent : baseEnd_714922 < baseStart_714922 := by decide
  rcases family_descends (prefixWord ++ tailWord_714922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714954 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_714954 : Nat := 118140960795 + 714954 * 2 ^ 59
def prefixEnd_714954 : Nat := 4983230072969 + 3 ^ 40 * 714954 * 2
def baseEnd_714954 : Nat := 326324486981956420343993

theorem tailTrace_714954 : CollatzResearch.WordTrace tailWord_714954 prefixEnd_714954 326324486981956420343993 := by
  unfold tailWord_714954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519128662962809316769979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17384343101234158178053277 6519128662962809316769979)
  ·
    refine ⟨9778692994444213975154969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519128662962809316769979 9778692994444213975154969)
    ·
      refine ⟨7334019745833160481366227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9778692994444213975154969 7334019745833160481366227)
      ·
        refine ⟨11001029618749740722049341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334019745833160481366227 11001029618749740722049341)
        ·
          refine ⟨4125386107031152770768503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11001029618749740722049341 4125386107031152770768503)
          ·
            refine ⟨6188079160546729156152755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125386107031152770768503 6188079160546729156152755)
            ·
              refine ⟨9282118740820093734229133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188079160546729156152755 9282118740820093734229133)
              ·
                refine ⟨3480794527807535150335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9282118740820093734229133 3480794527807535150335925)
                ·
                  refine ⟨326324486981956420343993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480794527807535150335925 326324486981956420343993)
                  ·
                    rfl

theorem cell20_714954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_714954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_714954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_714954 prefixEnd_714954 := by exact prefixLift 714954
  have htrace : WordTrace (prefixWord ++ tailWord_714954) baseStart_714954 baseEnd_714954 := by
    simpa [prefixWord, tailWord_714954, baseEnd_714954] using wordTrace_append hprefix tailTrace_714954
  have hstable : (prefixWord ++ tailWord_714954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714954).length < 2 ^ (prefixWord ++ tailWord_714954).sum := by decide
  have hdescent : baseEnd_714954 < baseStart_714954 := by decide
  rcases family_descends (prefixWord ++ tailWord_714954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715009 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_715009 : Nat := 118140960795 + 715009 * 2 ^ 59
def prefixEnd_715009 : Nat := 4983230072969 + 3 ^ 40 * 715009 * 2
def baseEnd_715009 : Nat := 326349590480620673510435

theorem tailTrace_715009 : CollatzResearch.WordTrace tailWord_715009 prefixEnd_715009 326349590480620673510435 := by
  unfold tailWord_715009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26078520666651981660332081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17385680444434654440221387 26078520666651981660332081)
  ·
    refine ⟨19558890499988986245249061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26078520666651981660332081 19558890499988986245249061)
    ·
      refine ⟨3667291968747934920984199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19558890499988986245249061 3667291968747934920984199)
      ·
        refine ⟨5500937953121902381476299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667291968747934920984199 5500937953121902381476299)
        ·
          refine ⟨8251406929682853572214449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500937953121902381476299 8251406929682853572214449)
          ·
            refine ⟨6188555197262140179160837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251406929682853572214449 6188555197262140179160837)
            ·
              refine ⟨1160354099486651283592657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6188555197262140179160837 1160354099486651283592657)
              ·
                refine ⟨870265574614988462694493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160354099486651283592657 870265574614988462694493)
                ·
                  refine ⟨326349590480620673510435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870265574614988462694493 326349590480620673510435)
                  ·
                    rfl

theorem cell20_715009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_715009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715009 prefixEnd_715009 := by exact prefixLift 715009
  have htrace : WordTrace (prefixWord ++ tailWord_715009) baseStart_715009 baseEnd_715009 := by
    simpa [prefixWord, tailWord_715009, baseEnd_715009] using wordTrace_append hprefix tailTrace_715009
  have hstable : (prefixWord ++ tailWord_715009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715009).length < 2 ^ (prefixWord ++ tailWord_715009).sum := by decide
  have hdescent : baseEnd_715009 < baseStart_715009 := by decide
  rcases family_descends (prefixWord ++ tailWord_715009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715012 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_715012 : Nat := 118140960795 + 715012 * 2 ^ 59
def prefixEnd_715012 : Nat := 4983230072969 + 3 ^ 40 * 715012 * 2
def baseEnd_715012 : Nat := 326350959762365996410423

theorem tailTrace_715012 : CollatzResearch.WordTrace tailWord_715012 prefixEnd_715012 326350959762365996410423 := by
  unfold tailWord_715012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039315042820556586345645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17385753390427408781794193 13039315042820556586345645)
  ·
    refine ⟨4889743141057708719879617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13039315042820556586345645 4889743141057708719879617)
    ·
      refine ⟨3667307355793281539909713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4889743141057708719879617 3667307355793281539909713)
      ·
        refine ⟨2750480516844961154932285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3667307355793281539909713 2750480516844961154932285)
        ·
          refine ⟨1031430193816860433099607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750480516844961154932285 1031430193816860433099607)
          ·
            refine ⟨1547145290725290649649411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031430193816860433099607 1547145290725290649649411)
            ·
              refine ⟨2320717936087935974474117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547145290725290649649411 2320717936087935974474117)
              ·
                refine ⟨435134613016487995213897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2320717936087935974474117 435134613016487995213897)
                ·
                  refine ⟨326350959762365996410423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435134613016487995213897 326350959762365996410423)
                  ·
                    rfl

theorem cell20_715012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_715012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715012 prefixEnd_715012 := by exact prefixLift 715012
  have htrace : WordTrace (prefixWord ++ tailWord_715012) baseStart_715012 baseEnd_715012 := by
    simpa [prefixWord, tailWord_715012, baseEnd_715012] using wordTrace_append hprefix tailTrace_715012
  have hstable : (prefixWord ++ tailWord_715012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715012).length < 2 ^ (prefixWord ++ tailWord_715012).sum := by decide
  have hdescent : baseEnd_715012 < baseStart_715012 := by decide
  rcases family_descends (prefixWord ++ tailWord_715012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715040 : List Nat := [2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_715040 : Nat := 118140960795 + 715040 * 2 ^ 59
def prefixEnd_715040 : Nat := 4983230072969 + 3 ^ 40 * 715040 * 2
def baseEnd_715040 : Nat := 108787913241774114492325

theorem tailTrace_715040 : CollatzResearch.WordTrace tailWord_715040 prefixEnd_715040 108787913241774114492325 := by
  unfold tailWord_715040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039825664769836977355287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17386434219693115969807049 13039825664769836977355287)
  ·
    refine ⟨19559738497154755466032931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13039825664769836977355287 19559738497154755466032931)
    ·
      refine ⟨29339607745732133199049397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19559738497154755466032931 29339607745732133199049397)
      ·
        refine ⟨2750588226162387487410881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29339607745732133199049397 2750588226162387487410881)
        ·
          refine ⟨2062941169621790615558161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750588226162387487410881 2062941169621790615558161)
          ·
            refine ⟨1547205877216342961668621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062941169621790615558161 1547205877216342961668621)
            ·
              refine ⟨580202203956128610625733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547205877216342961668621 580202203956128610625733)
              ·
                refine ⟨108787913241774114492325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580202203956128610625733 108787913241774114492325)
                ·
                  rfl

theorem cell20_715040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_715040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715040 prefixEnd_715040 := by exact prefixLift 715040
  have htrace : WordTrace (prefixWord ++ tailWord_715040) baseStart_715040 baseEnd_715040 := by
    simpa [prefixWord, tailWord_715040, baseEnd_715040] using wordTrace_append hprefix tailTrace_715040
  have hstable : (prefixWord ++ tailWord_715040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715040).length < 2 ^ (prefixWord ++ tailWord_715040).sum := by decide
  have hdescent : baseEnd_715040 < baseStart_715040 := by decide
  rcases family_descends (prefixWord ++ tailWord_715040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715068 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_715068 : Nat := 118140960795 + 715068 * 2 ^ 59
def prefixEnd_715068 : Nat := 4983230072969 + 3 ^ 40 * 715068 * 2
def baseEnd_715068 : Nat := 326376519688278690543527

theorem tailTrace_715068 : CollatzResearch.WordTrace tailWord_715068 prefixEnd_715068 326376519688278690543527 := by
  unfold tailWord_715068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040336286719117368364929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17387115048958823157819905 13040336286719117368364929)
  ·
    refine ⟨9780252215039338026273697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13040336286719117368364929 9780252215039338026273697)
    ·
      refine ⟨7335189161279503519705273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9780252215039338026273697 7335189161279503519705273)
      ·
        refine ⟨5501391870959627639778955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7335189161279503519705273 5501391870959627639778955)
        ·
          refine ⟨8252087806439441459668433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501391870959627639778955 8252087806439441459668433)
          ·
            refine ⟨6189065854829581094751325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252087806439441459668433 6189065854829581094751325)
            ·
              refine ⟨2320899695561092910531747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6189065854829581094751325 2320899695561092910531747)
              ·
                refine ⟨3481349543341639365797621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320899695561092910531747 3481349543341639365797621)
                ·
                  refine ⟨326376519688278690543527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481349543341639365797621 326376519688278690543527)
                  ·
                    rfl

theorem cell20_715068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_715068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715068 prefixEnd_715068 := by exact prefixLift 715068
  have htrace : WordTrace (prefixWord ++ tailWord_715068) baseStart_715068 baseEnd_715068 := by
    simpa [prefixWord, tailWord_715068, baseEnd_715068] using wordTrace_append hprefix tailTrace_715068
  have hstable : (prefixWord ++ tailWord_715068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715068).length < 2 ^ (prefixWord ++ tailWord_715068).sum := by decide
  have hdescent : baseEnd_715068 < baseStart_715068 := by decide
  rcases family_descends (prefixWord ++ tailWord_715068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715075 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_715075 : Nat := 118140960795 + 715075 * 2 ^ 59
def prefixEnd_715075 : Nat := 4983230072969 + 3 ^ 40 * 715075 * 2
def baseEnd_715075 : Nat := 326379714679017777310165

theorem tailTrace_715075 : CollatzResearch.WordTrace tailWord_715075 prefixEnd_715075 326379714679017777310165 := by
  unfold tailWord_715075
  simp only [CollatzResearch.WordTrace]
  refine ⟨26080927884412874932234679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17387285256275249954823119 26080927884412874932234679)
  ·
    refine ⟨39121391826619312398352019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26080927884412874932234679 39121391826619312398352019)
    ·
      refine ⟨58682087739928968597528029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39121391826619312398352019 58682087739928968597528029)
      ·
        refine ⟨22005782902473363224073011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58682087739928968597528029 22005782902473363224073011)
        ·
          refine ⟨33008674353710044836109517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22005782902473363224073011 33008674353710044836109517)
          ·
            refine ⟨12378252882641266813541069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33008674353710044836109517 12378252882641266813541069)
            ·
              refine ⟨4641844830990475055077901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12378252882641266813541069 4641844830990475055077901)
              ·
                refine ⟨1740691811621428145654213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4641844830990475055077901 1740691811621428145654213)
                ·
                  refine ⟨326379714679017777310165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740691811621428145654213 326379714679017777310165)
                  ·
                    rfl

theorem cell20_715075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_715075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715075 prefixEnd_715075 := by exact prefixLift 715075
  have htrace : WordTrace (prefixWord ++ tailWord_715075) baseStart_715075 baseEnd_715075 := by
    simpa [prefixWord, tailWord_715075, baseEnd_715075] using wordTrace_append hprefix tailTrace_715075
  have hstable : (prefixWord ++ tailWord_715075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715075).length < 2 ^ (prefixWord ++ tailWord_715075).sum := by decide
  have hdescent : baseEnd_715075 < baseStart_715075 := by decide
  rcases family_descends (prefixWord ++ tailWord_715075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715092 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_715092 : Nat := 118140960795 + 715092 * 2 ^ 59
def prefixEnd_715092 : Nat := 4983230072969 + 3 ^ 40 * 715092 * 2
def baseEnd_715092 : Nat := 326387473942241273743429

theorem tailTrace_715092 : CollatzResearch.WordTrace tailWord_715092 prefixEnd_715092 326387473942241273743429 := by
  unfold tailWord_715092
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040773962675643417801765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17387698616900857890402353 13040773962675643417801765)
  ·
    refine ⟨2445145118001683140837831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13040773962675643417801765 2445145118001683140837831)
    ·
      refine ⟨3667717677002524711256747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2445145118001683140837831 3667717677002524711256747)
      ·
        refine ⟨5501576515503787066885121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667717677002524711256747 5501576515503787066885121)
        ·
          refine ⟨4126182386627840300163841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5501576515503787066885121 4126182386627840300163841)
          ·
            refine ⟨3094636789970880225122881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4126182386627840300163841 3094636789970880225122881)
            ·
              refine ⟨2320977592478160168842161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094636789970880225122881 2320977592478160168842161)
              ·
                refine ⟨1740733194358620126631621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320977592478160168842161 1740733194358620126631621)
                ·
                  refine ⟨326387473942241273743429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740733194358620126631621 326387473942241273743429)
                  ·
                    rfl

theorem cell20_715092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_715092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715092 prefixEnd_715092 := by exact prefixLift 715092
  have htrace : WordTrace (prefixWord ++ tailWord_715092) baseStart_715092 baseEnd_715092 := by
    simpa [prefixWord, tailWord_715092, baseEnd_715092] using wordTrace_append hprefix tailTrace_715092
  have hstable : (prefixWord ++ tailWord_715092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715092).length < 2 ^ (prefixWord ++ tailWord_715092).sum := by decide
  have hdescent : baseEnd_715092 < baseStart_715092 := by decide
  rcases family_descends (prefixWord ++ tailWord_715092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715109 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 2]
def baseStart_715109 : Nat := 118140960795 + 715109 * 2 ^ 59
def prefixEnd_715109 : Nat := 4983230072969 + 3 ^ 40 * 715109 * 2
def baseEnd_715109 : Nat := 326395233205464770176693

theorem tailTrace_715109 : CollatzResearch.WordTrace tailWord_715109 prefixEnd_715109 326395233205464770176693 := by
  unfold tailWord_715109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082167966289698738972381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17388111977526465825981587 26082167966289698738972381)
  ·
    refine ⟨9780812987358637027114643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26082167966289698738972381 9780812987358637027114643)
    ·
      refine ⟨14671219481037955540671965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780812987358637027114643 14671219481037955540671965)
      ·
        refine ⟨5501707305389233327751987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14671219481037955540671965 5501707305389233327751987)
        ·
          refine ⟨8252560958083849991627981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501707305389233327751987 8252560958083849991627981)
          ·
            refine ⟨3094710359281443746860493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8252560958083849991627981 3094710359281443746860493)
            ·
              refine ⟨1160516384730541405072685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094710359281443746860493 1160516384730541405072685)
              ·
                refine ⟨435193644273953026902257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1160516384730541405072685 435193644273953026902257)
                ·
                  refine ⟨326395233205464770176693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435193644273953026902257 326395233205464770176693)
                  ·
                    rfl

theorem cell20_715109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_715109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715109 prefixEnd_715109 := by exact prefixLift 715109
  have htrace : WordTrace (prefixWord ++ tailWord_715109) baseStart_715109 baseEnd_715109 := by
    simpa [prefixWord, tailWord_715109, baseEnd_715109] using wordTrace_append hprefix tailTrace_715109
  have hstable : (prefixWord ++ tailWord_715109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715109).length < 2 ^ (prefixWord ++ tailWord_715109).sum := by decide
  have hdescent : baseEnd_715109 < baseStart_715109 := by decide
  rcases family_descends (prefixWord ++ tailWord_715109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715116 : List Nat := [2, 2, 1, 1, 7, 1, 6]
def baseStart_715116 : Nat := 118140960795 + 715116 * 2 ^ 59
def prefixEnd_715116 : Nat := 4983230072969 + 3 ^ 40 * 715116 * 2
def baseEnd_715116 : Nat := 36266492021800428549259

theorem tailTrace_715116 : CollatzResearch.WordTrace tailWord_715116 prefixEnd_715116 36266492021800428549259 := by
  unfold tailWord_715116
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041211638632169467238601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17388282184842892622984801 13041211638632169467238601)
  ·
    refine ⟨9780908728974127100428951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13041211638632169467238601 9780908728974127100428951)
    ·
      refine ⟨14671363093461190650643427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780908728974127100428951 14671363093461190650643427)
      ·
        refine ⟨22007044640191785975965141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671363093461190650643427 22007044640191785975965141)
        ·
          refine ⟨515790108754494983811683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22007044640191785975965141 515790108754494983811683)
          ·
            refine ⟨773685163131742475717525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515790108754494983811683 773685163131742475717525)
            ·
              refine ⟨36266492021800428549259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 773685163131742475717525 36266492021800428549259)
              ·
                rfl

theorem cell20_715116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_715116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715116 prefixEnd_715116 := by exact prefixLift 715116
  have htrace : WordTrace (prefixWord ++ tailWord_715116) baseStart_715116 baseEnd_715116 := by
    simpa [prefixWord, tailWord_715116, baseEnd_715116] using wordTrace_append hprefix tailTrace_715116
  have hstable : (prefixWord ++ tailWord_715116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715116).length < 2 ^ (prefixWord ++ tailWord_715116).sum := by decide
  have hdescent : baseEnd_715116 < baseStart_715116 := by decide
  rcases family_descends (prefixWord ++ tailWord_715116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715120 : List Nat := [2, 1, 1, 1, 4, 3, 8]
def baseStart_715120 : Nat := 118140960795 + 715120 * 2 ^ 59
def prefixEnd_715120 : Nat := 4983230072969 + 3 ^ 40 * 715120 * 2
def baseEnd_715120 : Nat := 36266694878355291201109

theorem tailTrace_715120 : CollatzResearch.WordTrace tailWord_715120 prefixEnd_715120 36266694878355291201109 := by
  unfold tailWord_715120
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041284584624923808811407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17388379446166565078415209 13041284584624923808811407)
  ·
    refine ⟨19561926876937385713217111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041284584624923808811407 19561926876937385713217111)
    ·
      refine ⟨29342890315406078569825667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19561926876937385713217111 29342890315406078569825667)
      ·
        refine ⟨44014335473109117854738501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29342890315406078569825667 44014335473109117854738501)
        ·
          refine ⟨8252687901207959597763469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44014335473109117854738501 8252687901207959597763469)
          ·
            refine ⟨3094757962952984849161301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8252687901207959597763469 3094757962952984849161301)
            ·
              refine ⟨36266694878355291201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3094757962952984849161301 36266694878355291201109)
              ·
                rfl

theorem cell20_715120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_715120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715120 prefixEnd_715120 := by exact prefixLift 715120
  have htrace : WordTrace (prefixWord ++ tailWord_715120) baseStart_715120 baseEnd_715120 := by
    simpa [prefixWord, tailWord_715120, baseEnd_715120] using wordTrace_append hprefix tailTrace_715120
  have hstable : (prefixWord ++ tailWord_715120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715120).length < 2 ^ (prefixWord ++ tailWord_715120).sum := by decide
  have hdescent : baseEnd_715120 < baseStart_715120 := by decide
  rcases family_descends (prefixWord ++ tailWord_715120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715137 : List Nat := [1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_715137 : Nat := 118140960795 + 715137 * 2 ^ 59
def prefixEnd_715137 : Nat := 4983230072969 + 3 ^ 40 * 715137 * 2
def baseEnd_715137 : Nat := 108802671056140372414415

theorem tailTrace_715137 : CollatzResearch.WordTrace tailWord_715137 prefixEnd_715137 108802671056140372414415 := by
  unfold tailWord_715137
  simp only [CollatzResearch.WordTrace]
  refine ⟨26083189210188259520991665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17388792806792173013994443 26083189210188259520991665)
  ·
    refine ⟨19562391907641194640743749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26083189210188259520991665 19562391907641194640743749)
    ·
      refine ⟨3667948482682723995139453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19562391907641194640743749 3667948482682723995139453)
      ·
        refine ⟨1375480681006021498177295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3667948482682723995139453 1375480681006021498177295)
        ·
          refine ⟨2063221021509032247265943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375480681006021498177295 2063221021509032247265943)
          ·
            refine ⟨3094831532263548370898915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063221021509032247265943 3094831532263548370898915)
            ·
              refine ⟨4642247298395322556348373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094831532263548370898915 4642247298395322556348373)
              ·
                refine ⟨108802671056140372414415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4642247298395322556348373 108802671056140372414415)
                ·
                  rfl

theorem cell20_715137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_715137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715137 prefixEnd_715137 := by exact prefixLift 715137
  have htrace : WordTrace (prefixWord ++ tailWord_715137) baseStart_715137 baseEnd_715137 := by
    simpa [prefixWord, tailWord_715137, baseEnd_715137] using wordTrace_append hprefix tailTrace_715137
  have hstable : (prefixWord ++ tailWord_715137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715137).length < 2 ^ (prefixWord ++ tailWord_715137).sum := by decide
  have hdescent : baseEnd_715137 < baseStart_715137 := by decide
  rcases family_descends (prefixWord ++ tailWord_715137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715185 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 2]
def baseStart_715185 : Nat := 118140960795 + 715185 * 2 ^ 59
def prefixEnd_715185 : Nat := 4983230072969 + 3 ^ 40 * 715185 * 2
def baseEnd_715185 : Nat := 326429921676346283643049

theorem tailTrace_715185 : CollatzResearch.WordTrace tailWord_715185 prefixEnd_715185 326429921676346283643049 := by
  unfold tailWord_715185
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084939914014363718739009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17389959942676242479159339 26084939914014363718739009)
  ·
    refine ⟨19563704935510772789054257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26084939914014363718739009 19563704935510772789054257)
    ·
      refine ⟨14672778701633079591790693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19563704935510772789054257 14672778701633079591790693)
      ·
        refine ⟨2751146006556202423460755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14672778701633079591790693 2751146006556202423460755)
        ·
          refine ⟨4126719009834303635191133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751146006556202423460755 4126719009834303635191133)
          ·
            refine ⟨1547519628687863863196675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4126719009834303635191133 1547519628687863863196675)
            ·
              refine ⟨2321279443031795794795013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547519628687863863196675 2321279443031795794795013)
              ·
                refine ⟨435239895568461711524065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2321279443031795794795013 435239895568461711524065)
                ·
                  refine ⟨326429921676346283643049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435239895568461711524065 326429921676346283643049)
                  ·
                    rfl

theorem cell20_715185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_715185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715185 prefixEnd_715185 := by exact prefixLift 715185
  have htrace : WordTrace (prefixWord ++ tailWord_715185) baseStart_715185 baseEnd_715185 := by
    simpa [prefixWord, tailWord_715185, baseEnd_715185] using wordTrace_append hprefix tailTrace_715185
  have hstable : (prefixWord ++ tailWord_715185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715185).length < 2 ^ (prefixWord ++ tailWord_715185).sum := by decide
  have hdescent : baseEnd_715185 < baseStart_715185 := by decide
  rcases family_descends (prefixWord ++ tailWord_715185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715188 : List Nat := [2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_715188 : Nat := 118140960795 + 715188 * 2 ^ 59
def prefixEnd_715188 : Nat := 4983230072969 + 3 ^ 40 * 715188 * 2
def baseEnd_715188 : Nat := 108810430319363868847679

theorem tailTrace_715188 : CollatzResearch.WordTrace tailWord_715188 prefixEnd_715188 108810430319363868847679 := by
  unfold tailWord_715188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042524666501747615549109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17390032888668996820732145 13042524666501747615549109)
  ·
    refine ⟨1222736687484538838957729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13042524666501747615549109 1222736687484538838957729)
    ·
      refine ⟨917052515613404129218297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1222736687484538838957729 917052515613404129218297)
      ·
        refine ⟨687789386710053096913723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917052515613404129218297 687789386710053096913723)
        ·
          refine ⟨1031684080065079645370585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687789386710053096913723 1031684080065079645370585)
          ·
            refine ⟨773763060048809734027939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031684080065079645370585 773763060048809734027939)
            ·
              refine ⟨1160644590073214601041909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773763060048809734027939 1160644590073214601041909)
              ·
                refine ⟨108810430319363868847679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160644590073214601041909 108810430319363868847679)
                ·
                  rfl

theorem cell20_715188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_715188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715188 prefixEnd_715188 := by exact prefixLift 715188
  have htrace : WordTrace (prefixWord ++ tailWord_715188) baseStart_715188 baseEnd_715188 := by
    simpa [prefixWord, tailWord_715188, baseEnd_715188] using wordTrace_append hprefix tailTrace_715188
  have hstable : (prefixWord ++ tailWord_715188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715188).length < 2 ^ (prefixWord ++ tailWord_715188).sum := by decide
  have hdescent : baseEnd_715188 < baseStart_715188 := by decide
  rcases family_descends (prefixWord ++ tailWord_715188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715203 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_715203 : Nat := 118140960795 + 715203 * 2 ^ 59
def prefixEnd_715203 : Nat := 4983230072969 + 3 ^ 40 * 715203 * 2
def baseEnd_715203 : Nat := 326438137366818221042975

theorem tailTrace_715203 : CollatzResearch.WordTrace tailWord_715203 prefixEnd_715203 326438137366818221042975 := by
  unfold tailWord_715203
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085596427949152792894263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17390397618632768528596175 26085596427949152792894263)
  ·
    refine ⟨39128394641923729189341395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26085596427949152792894263 39128394641923729189341395)
    ·
      refine ⟨58692591962885593784012093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39128394641923729189341395 58692591962885593784012093)
      ·
        refine ⟨22009721986082097669004535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58692591962885593784012093 22009721986082097669004535)
        ·
          refine ⟨33014582979123146503506803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22009721986082097669004535 33014582979123146503506803)
          ·
            refine ⟨49521874468684719755260205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33014582979123146503506803 49521874468684719755260205)
            ·
              refine ⟨18570702925756769908222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49521874468684719755260205 18570702925756769908222577)
              ·
                refine ⟨13928027194317577431166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570702925756769908222577 13928027194317577431166933)
                ·
                  refine ⟨326438137366818221042975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13928027194317577431166933 326438137366818221042975)
                  ·
                    rfl

theorem cell20_715203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_715203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715203 prefixEnd_715203 := by exact prefixLift 715203
  have htrace : WordTrace (prefixWord ++ tailWord_715203) baseStart_715203 baseEnd_715203 := by
    simpa [prefixWord, tailWord_715203, baseEnd_715203] using wordTrace_append hprefix tailTrace_715203
  have hstable : (prefixWord ++ tailWord_715203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715203).length < 2 ^ (prefixWord ++ tailWord_715203).sum := by decide
  have hdescent : baseEnd_715203 < baseStart_715203 := by decide
  rcases family_descends (prefixWord ++ tailWord_715203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715237 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_715237 : Nat := 118140960795 + 715237 * 2 ^ 59
def prefixEnd_715237 : Nat := 4983230072969 + 3 ^ 40 * 715237 * 2
def baseEnd_715237 : Nat := 326453655893265213909503

theorem tailTrace_715237 : CollatzResearch.WordTrace tailWord_715237 prefixEnd_715237 326453655893265213909503 := by
  unfold tailWord_715237
  simp only [CollatzResearch.WordTrace]
  refine ⟨26086836509825976599631965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17391224339883984399754643 26086836509825976599631965)
  ·
    refine ⟨9782563691184741224861987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26086836509825976599631965 9782563691184741224861987)
    ·
      refine ⟨14673845536777111837292981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9782563691184741224861987 14673845536777111837292981)
      ·
        refine ⟨1375673019072854234746217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14673845536777111837292981 1375673019072854234746217)
        ·
          refine ⟨1031754764304640676059663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375673019072854234746217 1031754764304640676059663)
          ·
            refine ⟨1547632146456961014089495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031754764304640676059663 1547632146456961014089495)
            ·
              refine ⟨2321448219685441521134243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547632146456961014089495 2321448219685441521134243)
              ·
                refine ⟨3482172329528162281701365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321448219685441521134243 3482172329528162281701365)
                ·
                  refine ⟨326453655893265213909503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482172329528162281701365 326453655893265213909503)
                  ·
                    rfl

theorem cell20_715237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_715237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715237 prefixEnd_715237 := by exact prefixLift 715237
  have htrace : WordTrace (prefixWord ++ tailWord_715237) baseStart_715237 baseEnd_715237 := by
    simpa [prefixWord, tailWord_715237, baseEnd_715237] using wordTrace_append hprefix tailTrace_715237
  have hstable : (prefixWord ++ tailWord_715237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715237).length < 2 ^ (prefixWord ++ tailWord_715237).sum := by decide
  have hdescent : baseEnd_715237 < baseStart_715237 := by decide
  rcases family_descends (prefixWord ++ tailWord_715237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715244 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_715244 : Nat := 118140960795 + 715244 * 2 ^ 59
def prefixEnd_715244 : Nat := 4983230072969 + 3 ^ 40 * 715244 * 2
def baseEnd_715244 : Nat := 326456850884004300676141

theorem tailTrace_715244 : CollatzResearch.WordTrace tailWord_715244 prefixEnd_715244 326456850884004300676141 := by
  unfold tailWord_715244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043545910400308397568393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17391394547200411196757857 13043545910400308397568393)
  ·
    refine ⟨9782659432800231298176295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13043545910400308397568393 9782659432800231298176295)
    ·
      refine ⟨14673989149200346947264443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9782659432800231298176295 14673989149200346947264443)
      ·
        refine ⟨22010983723800520420896665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14673989149200346947264443 22010983723800520420896665)
        ·
          refine ⟨16508237792850390315672499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22010983723800520420896665 16508237792850390315672499)
          ·
            refine ⟨24762356689275585473508749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508237792850390315672499 24762356689275585473508749)
            ·
              refine ⟨9285883758478344552565781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24762356689275585473508749 9285883758478344552565781)
              ·
                refine ⟨435275801178672400901521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9285883758478344552565781 435275801178672400901521)
                ·
                  refine ⟨326456850884004300676141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435275801178672400901521 326456850884004300676141)
                  ·
                    rfl

theorem cell20_715244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_715244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715244 prefixEnd_715244 := by exact prefixLift 715244
  have htrace : WordTrace (prefixWord ++ tailWord_715244) baseStart_715244 baseEnd_715244 := by
    simpa [prefixWord, tailWord_715244, baseEnd_715244] using wordTrace_append hprefix tailTrace_715244
  have hstable : (prefixWord ++ tailWord_715244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715244).length < 2 ^ (prefixWord ++ tailWord_715244).sum := by decide
  have hdescent : baseEnd_715244 < baseStart_715244 := by decide
  rcases family_descends (prefixWord ++ tailWord_715244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715254 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_715254 : Nat := 118140960795 + 715254 * 2 ^ 59
def prefixEnd_715254 : Nat := 4983230072969 + 3 ^ 40 * 715254 * 2
def baseEnd_715254 : Nat := 326461415156488710342767

theorem tailTrace_715254 : CollatzResearch.WordTrace tailWord_715254 prefixEnd_715254 326461415156488710342767 := by
  unfold tailWord_715254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630466034422774281437551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17391637700509592335333877 1630466034422774281437551)
  ·
    refine ⟨2445699051634161422156327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630466034422774281437551 2445699051634161422156327)
    ·
      refine ⟨3668548577451242133234491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2445699051634161422156327 3668548577451242133234491)
      ·
        refine ⟨5502822866176863199851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3668548577451242133234491 5502822866176863199851737)
        ·
          refine ⟨4127117149632647399888803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5502822866176863199851737 4127117149632647399888803)
          ·
            refine ⟨6190675724448971099833205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127117149632647399888803 6190675724448971099833205)
            ·
              refine ⟨580375849167091040609363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6190675724448971099833205 580375849167091040609363)
              ·
                refine ⟨870563773750636560914045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580375849167091040609363 870563773750636560914045)
                ·
                  refine ⟨326461415156488710342767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870563773750636560914045 326461415156488710342767)
                  ·
                    rfl

theorem cell20_715254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_715254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715254 prefixEnd_715254 := by exact prefixLift 715254
  have htrace : WordTrace (prefixWord ++ tailWord_715254) baseStart_715254 baseEnd_715254 := by
    simpa [prefixWord, tailWord_715254, baseEnd_715254] using wordTrace_append hprefix tailTrace_715254
  have hstable : (prefixWord ++ tailWord_715254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715254).length < 2 ^ (prefixWord ++ tailWord_715254).sum := by decide
  have hdescent : baseEnd_715254 < baseStart_715254 := by decide
  rcases family_descends (prefixWord ++ tailWord_715254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715268 : List Nat := [2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_715268 : Nat := 118140960795 + 715268 * 2 ^ 59
def prefixEnd_715268 : Nat := 4983230072969 + 3 ^ 40 * 715268 * 2
def baseEnd_715268 : Nat := 108822601712655627958681

theorem tailTrace_715268 : CollatzResearch.WordTrace tailWord_715268 prefixEnd_715268 108822601712655627958681 := by
  unfold tailWord_715268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043983586356834447005229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17391978115142445929340305 13043983586356834447005229)
  ·
    refine ⟨4891493844883812917626961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13043983586356834447005229 4891493844883812917626961)
    ·
      refine ⟨3668620383662859688220221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4891493844883812917626961 3668620383662859688220221)
      ·
        refine ⟨1375732643873572383082583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3668620383662859688220221 1375732643873572383082583)
        ·
          refine ⟨2063598965810358574623875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375732643873572383082583 2063598965810358574623875)
          ·
            refine ⟨3095398448715537861935813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063598965810358574623875 3095398448715537861935813)
            ·
              refine ⟨580387209134163349112965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3095398448715537861935813 580387209134163349112965)
              ·
                refine ⟨108822601712655627958681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580387209134163349112965 108822601712655627958681)
                ·
                  rfl

theorem cell20_715268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_715268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715268 prefixEnd_715268 := by exact prefixLift 715268
  have htrace : WordTrace (prefixWord ++ tailWord_715268) baseStart_715268 baseEnd_715268 := by
    simpa [prefixWord, tailWord_715268, baseEnd_715268] using wordTrace_append hprefix tailTrace_715268
  have hstable : (prefixWord ++ tailWord_715268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715268).length < 2 ^ (prefixWord ++ tailWord_715268).sum := by decide
  have hdescent : baseEnd_715268 < baseStart_715268 := by decide
  rcases family_descends (prefixWord ++ tailWord_715268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715278 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_715278 : Nat := 118140960795 + 715278 * 2 ^ 59
def prefixEnd_715278 : Nat := 4983230072969 + 3 ^ 40 * 715278 * 2
def baseEnd_715278 : Nat := 326472369410451293542669

theorem tailTrace_715278 : CollatzResearch.WordTrace tailWord_715278 prefixEnd_715278 326472369410451293542669 := by
  unfold tailWord_715278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261041487834680075234311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17392221268451627067916325 3261041487834680075234311)
  ·
    refine ⟨4891562231752020112851467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3261041487834680075234311 4891562231752020112851467)
    ·
      refine ⟨7337343347628030169277201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891562231752020112851467 7337343347628030169277201)
      ·
        refine ⟨5503007510721022626957901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337343347628030169277201 5503007510721022626957901)
        ·
          refine ⟨2063627816520383485109213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5503007510721022626957901 2063627816520383485109213)
          ·
            refine ⟨773860431195143806915955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2063627816520383485109213 773860431195143806915955)
            ·
              refine ⟨1160790646792715710373933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773860431195143806915955 1160790646792715710373933)
              ·
                refine ⟨435296492547268391390225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1160790646792715710373933 435296492547268391390225)
                ·
                  refine ⟨326472369410451293542669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435296492547268391390225 326472369410451293542669)
                  ·
                    rfl

theorem cell20_715278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_715278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715278 prefixEnd_715278 := by exact prefixLift 715278
  have htrace : WordTrace (prefixWord ++ tailWord_715278) baseStart_715278 baseEnd_715278 := by
    simpa [prefixWord, tailWord_715278, baseEnd_715278] using wordTrace_append hprefix tailTrace_715278
  have hstable : (prefixWord ++ tailWord_715278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715278).length < 2 ^ (prefixWord ++ tailWord_715278).sum := by decide
  have hdescent : baseEnd_715278 < baseStart_715278 := by decide
  rcases family_descends (prefixWord ++ tailWord_715278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715279 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_715279 : Nat := 118140960795 + 715279 * 2 ^ 59
def prefixEnd_715279 : Nat := 4983230072969 + 3 ^ 40 * 715279 * 2
def baseEnd_715279 : Nat := 326472825837699734509331

theorem tailTrace_715279 : CollatzResearch.WordTrace tailWord_715279 prefixEnd_715279 326472825837699734509331 := by
  unfold tailWord_715279
  simp only [CollatzResearch.WordTrace]
  refine ⟨26088368375673817772660891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17392245583782545181773927 26088368375673817772660891)
  ·
    refine ⟨39132552563510726658991337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26088368375673817772660891 39132552563510726658991337)
    ·
      refine ⟨29349414422633044994243503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39132552563510726658991337 29349414422633044994243503)
      ·
        refine ⟨44024121633949567491365255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29349414422633044994243503 44024121633949567491365255)
        ·
          refine ⟨66036182450924351237047883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44024121633949567491365255 66036182450924351237047883)
          ·
            refine ⟨99054273676386526855571825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66036182450924351237047883 99054273676386526855571825)
            ·
              refine ⟨74290705257289895141678869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99054273676386526855571825 74290705257289895141678869)
              ·
                refine ⟨3482376808935463834766197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74290705257289895141678869 3482376808935463834766197)
                ·
                  refine ⟨326472825837699734509331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482376808935463834766197 326472825837699734509331)
                  ·
                    rfl

theorem cell20_715279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_715279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715279 prefixEnd_715279 := by exact prefixLift 715279
  have htrace : WordTrace (prefixWord ++ tailWord_715279) baseStart_715279 baseEnd_715279 := by
    simpa [prefixWord, tailWord_715279, baseEnd_715279] using wordTrace_append hprefix tailTrace_715279
  have hstable : (prefixWord ++ tailWord_715279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715279).length < 2 ^ (prefixWord ++ tailWord_715279).sum := by decide
  have hdescent : baseEnd_715279 < baseStart_715279 := by decide
  rcases family_descends (prefixWord ++ tailWord_715279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715313 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_715313 : Nat := 118140960795 + 715313 * 2 ^ 59
def prefixEnd_715313 : Nat := 4983230072969 + 3 ^ 40 * 715313 * 2
def baseEnd_715313 : Nat := 326488344364146727375859

theorem tailTrace_715313 : CollatzResearch.WordTrace tailWord_715313 prefixEnd_715313 326488344364146727375859 := by
  unfold tailWord_715313
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089608457550641579398593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17393072305033761052932395 26089608457550641579398593)
  ·
    refine ⟨19567206343162981184548945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26089608457550641579398593 19567206343162981184548945)
    ·
      refine ⟨14675404757372235888411709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19567206343162981184548945 14675404757372235888411709)
      ·
        refine ⟨5503276784014588458154391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14675404757372235888411709 5503276784014588458154391)
        ·
          refine ⟨8254915176021882687231587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503276784014588458154391 8254915176021882687231587)
          ·
            refine ⟨12382372764032824030847381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254915176021882687231587 12382372764032824030847381)
            ·
              refine ⟨580423723314038626445971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12382372764032824030847381 580423723314038626445971)
              ·
                refine ⟨870635584971057939668957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580423723314038626445971 870635584971057939668957)
                ·
                  refine ⟨326488344364146727375859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870635584971057939668957 326488344364146727375859)
                  ·
                    rfl

theorem cell20_715313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_715313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715313 prefixEnd_715313 := by exact prefixLift 715313
  have htrace : WordTrace (prefixWord ++ tailWord_715313) baseStart_715313 baseEnd_715313 := by
    simpa [prefixWord, tailWord_715313, baseEnd_715313] using wordTrace_append hprefix tailTrace_715313
  have hstable : (prefixWord ++ tailWord_715313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715313).length < 2 ^ (prefixWord ++ tailWord_715313).sum := by decide
  have hdescent : baseEnd_715313 < baseStart_715313 := by decide
  rcases family_descends (prefixWord ++ tailWord_715313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715348 : List Nat := [2, 4, 1, 1, 1, 11]
def baseStart_715348 : Nat := 118140960795 + 715348 * 2 ^ 59
def prefixEnd_715348 : Nat := 4983230072969 + 3 ^ 40 * 715348 * 2
def baseEnd_715348 : Nat := 12092752567327487452187

theorem tailTrace_715348 : CollatzResearch.WordTrace tailWord_715348 prefixEnd_715348 12092752567327487452187 := by
  unfold tailWord_715348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045442506211921278461349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17393923341615895037948465 13045442506211921278461349)
  ·
    refine ⟨2446020469914735239711503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13045442506211921278461349 2446020469914735239711503)
    ·
      refine ⟨3669030704872102859567255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446020469914735239711503 3669030704872102859567255)
      ·
        refine ⟨5503546057308154289350883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669030704872102859567255 5503546057308154289350883)
        ·
          refine ⟨8255319085962231434026325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503546057308154289350883 8255319085962231434026325)
          ·
            refine ⟨12092752567327487452187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8255319085962231434026325 12092752567327487452187)
            ·
              rfl

theorem cell20_715348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 11].length) (baseStart_715348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715348 prefixEnd_715348 := by exact prefixLift 715348
  have htrace : WordTrace (prefixWord ++ tailWord_715348) baseStart_715348 baseEnd_715348 := by
    simpa [prefixWord, tailWord_715348, baseEnd_715348] using wordTrace_append hprefix tailTrace_715348
  have hstable : (prefixWord ++ tailWord_715348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715348).length < 2 ^ (prefixWord ++ tailWord_715348).sum := by decide
  have hdescent : baseEnd_715348 < baseStart_715348 := by decide
  rcases family_descends (prefixWord ++ tailWord_715348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715372 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_715372 : Nat := 118140960795 + 715372 * 2 ^ 59
def prefixEnd_715372 : Nat := 4983230072969 + 3 ^ 40 * 715372 * 2
def baseEnd_715372 : Nat := 326515273571804744408951

theorem tailTrace_715372 : CollatzResearch.WordTrace tailWord_715372 prefixEnd_715372 326515273571804744408951 := by
  unfold tailWord_715372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045880182168447327898185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17394506909557929770530913 13045880182168447327898185)
  ·
    refine ⟨9784410136626335495923639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13045880182168447327898185 9784410136626335495923639)
    ·
      refine ⟨14676615204939503243885459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9784410136626335495923639 14676615204939503243885459)
      ·
        refine ⟨22014922807409254865828189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14676615204939503243885459 22014922807409254865828189)
        ·
          refine ⟨8255596052778470574685571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22014922807409254865828189 8255596052778470574685571)
          ·
            refine ⟨12383394079167705862028357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255596052778470574685571 12383394079167705862028357)
            ·
              refine ⟨2321886389843944849130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12383394079167705862028357 2321886389843944849130317)
              ·
                refine ⟨870707396191479318423869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2321886389843944849130317 870707396191479318423869)
                ·
                  refine ⟨326515273571804744408951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870707396191479318423869 326515273571804744408951)
                  ·
                    rfl

theorem cell20_715372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_715372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715372 prefixEnd_715372 := by exact prefixLift 715372
  have htrace : WordTrace (prefixWord ++ tailWord_715372) baseStart_715372 baseEnd_715372 := by
    simpa [prefixWord, tailWord_715372, baseEnd_715372] using wordTrace_append hprefix tailTrace_715372
  have hstable : (prefixWord ++ tailWord_715372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715372).length < 2 ^ (prefixWord ++ tailWord_715372).sum := by decide
  have hdescent : baseEnd_715372 < baseStart_715372 := by decide
  rcases family_descends (prefixWord ++ tailWord_715372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715417 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_715417 : Nat := 118140960795 + 715417 * 2 ^ 59
def prefixEnd_715417 : Nat := 4983230072969 + 3 ^ 40 * 715417 * 2
def baseEnd_715417 : Nat := 326535812797984587908767

theorem tailTrace_715417 : CollatzResearch.WordTrace tailWord_715417 prefixEnd_715417 326535812797984587908767 := by
  unfold tailWord_715417
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093401649173867341184505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17395601099449244894123003 26093401649173867341184505)
  ·
    refine ⟨19570051236880400505888379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26093401649173867341184505 19570051236880400505888379)
    ·
      refine ⟨29355076855320600758832569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19570051236880400505888379 29355076855320600758832569)
      ·
        refine ⟨22016307641490450569124427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29355076855320600758832569 22016307641490450569124427)
        ·
          refine ⟨33024461462235675853686641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22016307641490450569124427 33024461462235675853686641)
          ·
            refine ⟨24768346096676756890264981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33024461462235675853686641 24768346096676756890264981)
            ·
              refine ⟨1161016223281722979231171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24768346096676756890264981 1161016223281722979231171)
              ·
                refine ⟨1741524334922584468846757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161016223281722979231171 1741524334922584468846757)
                ·
                  refine ⟨326535812797984587908767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741524334922584468846757 326535812797984587908767)
                  ·
                    rfl

theorem cell20_715417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_715417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715417 prefixEnd_715417 := by exact prefixLift 715417
  have htrace : WordTrace (prefixWord ++ tailWord_715417) baseStart_715417 baseEnd_715417 := by
    simpa [prefixWord, tailWord_715417, baseEnd_715417] using wordTrace_append hprefix tailTrace_715417
  have hstable : (prefixWord ++ tailWord_715417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715417).length < 2 ^ (prefixWord ++ tailWord_715417).sum := by decide
  have hdescent : baseEnd_715417 < baseStart_715417 := by decide
  rcases family_descends (prefixWord ++ tailWord_715417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715468 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_715468 : Nat := 118140960795 + 715468 * 2 ^ 59
def prefixEnd_715468 : Nat := 4983230072969 + 3 ^ 40 * 715468 * 2
def baseEnd_715468 : Nat := 326559090587655077208559

theorem tailTrace_715468 : CollatzResearch.WordTrace tailWord_715468 prefixEnd_715468 326559090587655077208559 := by
  unfold tailWord_715468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047630885994551525645529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17396841181326068700860705 13047630885994551525645529)
  ·
    refine ⟨9785723164495913644234147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13047630885994551525645529 9785723164495913644234147)
    ·
      refine ⟨14678584746743870466351221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785723164495913644234147 14678584746743870466351221)
      ·
        refine ⟨1376117320007237856220427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14678584746743870466351221 1376117320007237856220427)
        ·
          refine ⟨2064175980010856784330641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376117320007237856220427 2064175980010856784330641)
          ·
            refine ⟨1548131985008142588247981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064175980010856784330641 1548131985008142588247981)
            ·
              refine ⟨580549494378053470592993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548131985008142588247981 580549494378053470592993)
              ·
                refine ⟨435412120783540102944745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580549494378053470592993 435412120783540102944745)
                ·
                  refine ⟨326559090587655077208559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435412120783540102944745 326559090587655077208559)
                  ·
                    rfl

theorem cell20_715468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_715468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715468 prefixEnd_715468 := by exact prefixLift 715468
  have htrace : WordTrace (prefixWord ++ tailWord_715468) baseStart_715468 baseEnd_715468 := by
    simpa [prefixWord, tailWord_715468, baseEnd_715468] using wordTrace_append hprefix tailTrace_715468
  have hstable : (prefixWord ++ tailWord_715468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715468).length < 2 ^ (prefixWord ++ tailWord_715468).sum := by decide
  have hdescent : baseEnd_715468 < baseStart_715468 := by decide
  rcases family_descends (prefixWord ++ tailWord_715468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715527 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 2]
def baseStart_715527 : Nat := 118140960795 + 715527 * 2 ^ 59
def prefixEnd_715527 : Nat := 4983230072969 + 3 ^ 40 * 715527 * 2
def baseEnd_715527 : Nat := 326586019795313094241651

theorem tailTrace_715527 : CollatzResearch.WordTrace tailWord_715527 prefixEnd_715527 326586019795313094241651 := by
  unfold tailWord_715527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26097413678775356127688835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17398275785850237418459223 26097413678775356127688835)
  ·
    refine ⟨39146120518163034191533253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26097413678775356127688835 39146120518163034191533253)
    ·
      refine ⟨7339897597155568910912485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39146120518163034191533253 7339897597155568910912485)
      ·
        refine ⟨1376230799466669170796091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7339897597155568910912485 1376230799466669170796091)
        ·
          refine ⟨2064346199200003756194137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376230799466669170796091 2064346199200003756194137)
          ·
            refine ⟨1548259649400002817145603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064346199200003756194137 1548259649400002817145603)
            ·
              refine ⟨2322389474100004225718405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548259649400002817145603 2322389474100004225718405)
              ·
                refine ⟨435448026393750792322201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2322389474100004225718405 435448026393750792322201)
                ·
                  refine ⟨326586019795313094241651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435448026393750792322201 326586019795313094241651)
                  ·
                    rfl

theorem cell20_715527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2].length) (baseStart_715527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715527 prefixEnd_715527 := by exact prefixLift 715527
  have htrace : WordTrace (prefixWord ++ tailWord_715527) baseStart_715527 baseEnd_715527 := by
    simpa [prefixWord, tailWord_715527, baseEnd_715527] using wordTrace_append hprefix tailTrace_715527
  have hstable : (prefixWord ++ tailWord_715527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715527).length < 2 ^ (prefixWord ++ tailWord_715527).sum := by decide
  have hdescent : baseEnd_715527 < baseStart_715527 := by decide
  rcases family_descends (prefixWord ++ tailWord_715527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715607 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_715607 : Nat := 118140960795 + 715607 * 2 ^ 59
def prefixEnd_715607 : Nat := 4983230072969 + 3 ^ 40 * 715607 * 2
def baseEnd_715607 : Nat := 326622533975188371574657

theorem tailTrace_715607 : CollatzResearch.WordTrace tailWord_715607 prefixEnd_715607 326622533975188371574657 := by
  unfold tailWord_715607
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100331518485529790601075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400221012323686527067383 26100331518485529790601075)
  ·
    refine ⟨39150497277728294685901613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26100331518485529790601075 39150497277728294685901613)
    ·
      refine ⟨14681436479148110507213105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39150497277728294685901613 14681436479148110507213105)
      ·
        refine ⟨11011077359361082880409829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14681436479148110507213105 11011077359361082880409829)
        ·
          refine ⟨2064577004880203040076843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11011077359361082880409829 2064577004880203040076843)
          ·
            refine ⟨3096865507320304560115265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064577004880203040076843 3096865507320304560115265)
            ·
              refine ⟨2322649130490228420086449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096865507320304560115265 2322649130490228420086449)
              ·
                refine ⟨1741986847867671315064837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322649130490228420086449 1741986847867671315064837)
                ·
                  refine ⟨326622533975188371574657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741986847867671315064837 326622533975188371574657)
                  ·
                    rfl

theorem cell20_715607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_715607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715607 prefixEnd_715607 := by exact prefixLift 715607
  have htrace : WordTrace (prefixWord ++ tailWord_715607) baseStart_715607 baseEnd_715607 := by
    simpa [prefixWord, tailWord_715607, baseEnd_715607] using wordTrace_append hprefix tailTrace_715607
  have hstable : (prefixWord ++ tailWord_715607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715607).length < 2 ^ (prefixWord ++ tailWord_715607).sum := by decide
  have hdescent : baseEnd_715607 < baseStart_715607 := by decide
  rcases family_descends (prefixWord ++ tailWord_715607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715621 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_715621 : Nat := 118140960795 + 715621 * 2 ^ 59
def prefixEnd_715621 : Nat := 4983230072969 + 3 ^ 40 * 715621 * 2
def baseEnd_715621 : Nat := 326628923956666545107933

theorem tailTrace_715621 : CollatzResearch.WordTrace tailWord_715621 prefixEnd_715621 326628923956666545107933 := by
  unfold tailWord_715621
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100842140434810181610717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400561426956540121073811 26100842140434810181610717)
  ·
    refine ⟨9787815802663053818104019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26100842140434810181610717 9787815802663053818104019)
    ·
      refine ⟨14681723703994580727156029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9787815802663053818104019 14681723703994580727156029)
      ·
        refine ⟨5505646388997967772683511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14681723703994580727156029 5505646388997967772683511)
        ·
          refine ⟨8258469583496951659025267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505646388997967772683511 8258469583496951659025267)
          ·
            refine ⟨12387704375245427488537901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258469583496951659025267 12387704375245427488537901)
            ·
              refine ⟨4645389140717035308201713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12387704375245427488537901 4645389140717035308201713)
              ·
                refine ⟨3484041855537776481151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645389140717035308201713 3484041855537776481151285)
                ·
                  refine ⟨326628923956666545107933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3484041855537776481151285 326628923956666545107933)
                  ·
                    rfl

theorem cell20_715621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_715621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715621 prefixEnd_715621 := by exact prefixLift 715621
  have htrace : WordTrace (prefixWord ++ tailWord_715621) baseStart_715621 baseEnd_715621 := by
    simpa [prefixWord, tailWord_715621, baseEnd_715621] using wordTrace_append hprefix tailTrace_715621
  have hstable : (prefixWord ++ tailWord_715621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715621).length < 2 ^ (prefixWord ++ tailWord_715621).sum := by decide
  have hdescent : baseEnd_715621 < baseStart_715621 := by decide
  rcases family_descends (prefixWord ++ tailWord_715621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715635 : List Nat := [1, 1, 1, 2, 2, 1, 12]
def baseStart_715635 : Nat := 118140960795 + 715635 * 2 ^ 59
def prefixEnd_715635 : Nat := 4983230072969 + 3 ^ 40 * 715635 * 2
def baseEnd_715635 : Nat := 36292812659793857626801

theorem tailTrace_715635 : CollatzResearch.WordTrace tailWord_715635 prefixEnd_715635 36292812659793857626801 := by
  unfold tailWord_715635
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101352762384090572620359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400901841589393715080239 26101352762384090572620359)
  ·
    refine ⟨39152029143576135858930539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26101352762384090572620359 39152029143576135858930539)
    ·
      refine ⟨58728043715364203788395809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39152029143576135858930539 58728043715364203788395809)
      ·
        refine ⟨44046032786523152841296857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58728043715364203788395809 44046032786523152841296857)
        ·
          refine ⟨33034524589892364630972643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44046032786523152841296857 33034524589892364630972643)
          ·
            refine ⟨49551786884838546946458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33034524589892364630972643 49551786884838546946458965)
            ·
              refine ⟨36292812659793857626801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49551786884838546946458965 36292812659793857626801)
              ·
                rfl

theorem cell20_715635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_715635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715635 prefixEnd_715635 := by exact prefixLift 715635
  have htrace : WordTrace (prefixWord ++ tailWord_715635) baseStart_715635 baseEnd_715635 := by
    simpa [prefixWord, tailWord_715635, baseEnd_715635] using wordTrace_append hprefix tailTrace_715635
  have hstable : (prefixWord ++ tailWord_715635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715635).length < 2 ^ (prefixWord ++ tailWord_715635).sum := by decide
  have hdescent : baseEnd_715635 < baseStart_715635 := by decide
  rcases family_descends (prefixWord ++ tailWord_715635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715641 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 2]
def baseStart_715641 : Nat := 118140960795 + 715641 * 2 ^ 59
def prefixEnd_715641 : Nat := 4983230072969 + 3 ^ 40 * 715641 * 2
def baseEnd_715641 : Nat := 326638052501635364441185

theorem tailTrace_715641 : CollatzResearch.WordTrace tailWord_715641 prefixEnd_715641 326638052501635364441185 := by
  unfold tailWord_715641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101571600362353597338777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17401047733574902398225851 26101571600362353597338777)
  ·
    refine ⟨19576178700271765198004083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26101571600362353597338777 19576178700271765198004083)
    ·
      refine ⟨29364268050407647797006125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19576178700271765198004083 29364268050407647797006125)
      ·
        refine ⟨11011600518902867923877297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29364268050407647797006125 11011600518902867923877297)
        ·
          refine ⟨8258700389177150942907973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011600518902867923877297 8258700389177150942907973)
          ·
            refine ⟨1548506322970715801795245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8258700389177150942907973 1548506322970715801795245)
            ·
              refine ⟨580689871114018425673217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548506322970715801795245 580689871114018425673217)
              ·
                refine ⟨435517403335513819254913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580689871114018425673217 435517403335513819254913)
                ·
                  refine ⟨326638052501635364441185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435517403335513819254913 326638052501635364441185)
                  ·
                    rfl

theorem cell20_715641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_715641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715641 prefixEnd_715641 := by exact prefixLift 715641
  have htrace : WordTrace (prefixWord ++ tailWord_715641) baseStart_715641 baseEnd_715641 := by
    simpa [prefixWord, tailWord_715641, baseEnd_715641] using wordTrace_append hprefix tailTrace_715641
  have hstable : (prefixWord ++ tailWord_715641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715641).length < 2 ^ (prefixWord ++ tailWord_715641).sum := by decide
  have hdescent : baseEnd_715641 < baseStart_715641 := by decide
  rcases family_descends (prefixWord ++ tailWord_715641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715645 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_715645 : Nat := 118140960795 + 715645 * 2 ^ 59
def prefixEnd_715645 : Nat := 4983230072969 + 3 ^ 40 * 715645 * 2
def baseEnd_715645 : Nat := 326639878210629128307835

theorem tailTrace_715645 : CollatzResearch.WordTrace tailWord_715645 prefixEnd_715645 326639878210629128307835 := by
  unfold tailWord_715645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101717492347862280484389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17401144994898574853656259 26101717492347862280484389)
  ·
    refine ⟨4894072029815224177590823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26101717492347862280484389 4894072029815224177590823)
    ·
      refine ⟨7341108044722836266386235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894072029815224177590823 7341108044722836266386235)
      ·
        refine ⟨11011662067084254399579353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7341108044722836266386235 11011662067084254399579353)
        ·
          refine ⟨8258746550313190799684515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011662067084254399579353 8258746550313190799684515)
          ·
            refine ⟨12388119825469786199526773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258746550313190799684515 12388119825469786199526773)
            ·
              refine ⟨1161386233637792456205635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12388119825469786199526773 1161386233637792456205635)
              ·
                refine ⟨1742079350456688684308453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161386233637792456205635 1742079350456688684308453)
                ·
                  refine ⟨326639878210629128307835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742079350456688684308453 326639878210629128307835)
                  ·
                    rfl

theorem cell20_715645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_715645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715645 prefixEnd_715645 := by exact prefixLift 715645
  have htrace : WordTrace (prefixWord ++ tailWord_715645) baseStart_715645 baseEnd_715645 := by
    simpa [prefixWord, tailWord_715645, baseEnd_715645] using wordTrace_append hprefix tailTrace_715645
  have hstable : (prefixWord ++ tailWord_715645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715645).length < 2 ^ (prefixWord ++ tailWord_715645).sum := by decide
  have hdescent : baseEnd_715645 < baseStart_715645 := by decide
  rcases family_descends (prefixWord ++ tailWord_715645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715655 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_715655 : Nat := 118140960795 + 715655 * 2 ^ 59
def prefixEnd_715655 : Nat := 4983230072969 + 3 ^ 40 * 715655 * 2
def baseEnd_715655 : Nat := 326644442483113537974461

theorem tailTrace_715655 : CollatzResearch.WordTrace tailWord_715655 prefixEnd_715655 326644442483113537974461 := by
  unfold tailWord_715655
  simp only [CollatzResearch.WordTrace]
  refine ⟨26102082222311633988348419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17401388148207755992232279 26102082222311633988348419)
  ·
    refine ⟨39153123333467450982522629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26102082222311633988348419 39153123333467450982522629)
    ·
      refine ⟨7341210625025147059222993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39153123333467450982522629 7341210625025147059222993)
      ·
        refine ⟨5505907968768860294417245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7341210625025147059222993 5505907968768860294417245)
        ·
          refine ⟨2064715488288322610406467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5505907968768860294417245 2064715488288322610406467)
          ·
            refine ⟨3097073232432483915609701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064715488288322610406467 3097073232432483915609701)
            ·
              refine ⟨580701231081090734176819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3097073232432483915609701 580701231081090734176819)
              ·
                refine ⟨871051846621636101265229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580701231081090734176819 871051846621636101265229)
                ·
                  refine ⟨326644442483113537974461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871051846621636101265229 326644442483113537974461)
                  ·
                    rfl

theorem cell20_715655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_715655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715655 prefixEnd_715655 := by exact prefixLift 715655
  have htrace : WordTrace (prefixWord ++ tailWord_715655) baseStart_715655 baseEnd_715655 := by
    simpa [prefixWord, tailWord_715655, baseEnd_715655] using wordTrace_append hprefix tailTrace_715655
  have hstable : (prefixWord ++ tailWord_715655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715655).length < 2 ^ (prefixWord ++ tailWord_715655).sum := by decide
  have hdescent : baseEnd_715655 < baseStart_715655 := by decide
  rcases family_descends (prefixWord ++ tailWord_715655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715711 : List Nat := [1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_715711 : Nat := 118140960795 + 715711 * 2 ^ 59
def prefixEnd_715711 : Nat := 4983230072969 + 3 ^ 40 * 715711 * 2
def baseEnd_715711 : Nat := 108890000803008744035855

theorem tailTrace_715711 : CollatzResearch.WordTrace tailWord_715711 prefixEnd_715711 108890000803008744035855 := by
  unfold tailWord_715711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26104124710108755552386987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17402749806739170368257991 26104124710108755552386987)
  ·
    refine ⟨39156187065163133328580481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26104124710108755552386987 39156187065163133328580481)
    ·
      refine ⟨29367140298872349996435361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39156187065163133328580481 29367140298872349996435361)
      ·
        refine ⟨22025355224154262497326521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29367140298872349996435361 22025355224154262497326521)
        ·
          refine ⟨16519016418115696872994891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22025355224154262497326521 16519016418115696872994891)
          ·
            refine ⟨24778524627173545309492337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16519016418115696872994891 24778524627173545309492337)
            ·
              refine ⟨18583893470380158982119253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24778524627173545309492337 18583893470380158982119253)
              ·
                refine ⟨108890000803008744035855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18583893470380158982119253 108890000803008744035855)
                ·
                  rfl

theorem cell20_715711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_715711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715711 prefixEnd_715711 := by exact prefixLift 715711
  have htrace : WordTrace (prefixWord ++ tailWord_715711) baseStart_715711 baseEnd_715711 := by
    simpa [prefixWord, tailWord_715711, baseEnd_715711] using wordTrace_append hprefix tailTrace_715711
  have hstable : (prefixWord ++ tailWord_715711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715711).length < 2 ^ (prefixWord ++ tailWord_715711).sum := by decide
  have hdescent : baseEnd_715711 < baseStart_715711 := by decide
  rcases family_descends (prefixWord ++ tailWord_715711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715734 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_715734 : Nat := 118140960795 + 715734 * 2 ^ 59
def prefixEnd_715734 : Nat := 4983230072969 + 3 ^ 40 * 715734 * 2
def baseEnd_715734 : Nat := 326680500235740374340805

theorem tailTrace_715734 : CollatzResearch.WordTrace tailWord_715734 prefixEnd_715734 326680500235740374340805 := by
  unfold tailWord_715734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631560224314089405029641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17403309059350286986982837 1631560224314089405029641)
  ·
    refine ⟨1223670168235567053772231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1631560224314089405029641 1223670168235567053772231)
    ·
      refine ⟨1835505252353350580658347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223670168235567053772231 1835505252353350580658347)
      ·
        refine ⟨2753257878530025870987521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835505252353350580658347 2753257878530025870987521)
        ·
          refine ⟨2064943408897519403240641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753257878530025870987521 2064943408897519403240641)
          ·
            refine ⟨1548707556673139552430481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064943408897519403240641 1548707556673139552430481)
            ·
              refine ⟨1161530667504854664322861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548707556673139552430481 1161530667504854664322861)
              ·
                refine ⟨435574000314320499121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161530667504854664322861 435574000314320499121073)
                ·
                  refine ⟨326680500235740374340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435574000314320499121073 326680500235740374340805)
                  ·
                    rfl

theorem cell20_715734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_715734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715734 prefixEnd_715734 := by exact prefixLift 715734
  have htrace : WordTrace (prefixWord ++ tailWord_715734) baseStart_715734 baseEnd_715734 := by
    simpa [prefixWord, tailWord_715734, baseEnd_715734] using wordTrace_append hprefix tailTrace_715734
  have hstable : (prefixWord ++ tailWord_715734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715734).length < 2 ^ (prefixWord ++ tailWord_715734).sum := by decide
  have hdescent : baseEnd_715734 < baseStart_715734 := by decide
  rcases family_descends (prefixWord ++ tailWord_715734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715738 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_715738 : Nat := 118140960795 + 715738 * 2 ^ 59
def prefixEnd_715738 : Nat := 4983230072969 + 3 ^ 40 * 715738 * 2
def baseEnd_715738 : Nat := 326682325944734138207455

theorem tailTrace_715738 : CollatzResearch.WordTrace tailWord_715738 prefixEnd_715738 326682325944734138207455 := by
  unfold tailWord_715738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526277370252734790904967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17403406320673959442413245 6526277370252734790904967)
  ·
    refine ⟨9789416055379102186357451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6526277370252734790904967 9789416055379102186357451)
    ·
      refine ⟨14684124083068653279536177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789416055379102186357451 14684124083068653279536177)
      ·
        refine ⟨11013093062301489959652133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14684124083068653279536177 11013093062301489959652133)
        ·
          refine ⟨2064954949181529367434775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11013093062301489959652133 2064954949181529367434775)
          ·
            refine ⟨3097432423772294051152163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064954949181529367434775 3097432423772294051152163)
            ·
              refine ⟨4646148635658441076728245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097432423772294051152163 4646148635658441076728245)
              ·
                refine ⟨435576434592978850943273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4646148635658441076728245 435576434592978850943273)
                ·
                  refine ⟨326682325944734138207455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435576434592978850943273 326682325944734138207455)
                  ·
                    rfl

theorem cell20_715738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_715738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715738 prefixEnd_715738 := by exact prefixLift 715738
  have htrace : WordTrace (prefixWord ++ tailWord_715738) baseStart_715738 baseEnd_715738 := by
    simpa [prefixWord, tailWord_715738, baseEnd_715738] using wordTrace_append hprefix tailTrace_715738
  have hstable : (prefixWord ++ tailWord_715738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715738).length < 2 ^ (prefixWord ++ tailWord_715738).sum := by decide
  have hdescent : baseEnd_715738 < baseStart_715738 := by decide
  rcases family_descends (prefixWord ++ tailWord_715738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715752 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_715752 : Nat := 118140960795 + 715752 * 2 ^ 59
def prefixEnd_715752 : Nat := 4983230072969 + 3 ^ 40 * 715752 * 2
def baseEnd_715752 : Nat := 326688715926212311740731

theorem tailTrace_715752 : CollatzResearch.WordTrace tailWord_715752 prefixEnd_715752 326688715926212311740731 := by
  unfold tailWord_715752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052810051480109777314755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17403746735306813036419673 13052810051480109777314755)
  ·
    refine ⟨19579215077220164665972133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13052810051480109777314755 19579215077220164665972133)
    ·
      refine ⟨3671102826978780874869775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19579215077220164665972133 3671102826978780874869775)
      ·
        refine ⟨5506654240468171312304663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671102826978780874869775 5506654240468171312304663)
        ·
          refine ⟨8259981360702256968456995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506654240468171312304663 8259981360702256968456995)
          ·
            refine ⟨12389972041053385452685493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8259981360702256968456995 12389972041053385452685493)
            ·
              refine ⟨1161559878848754886189265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12389972041053385452685493 1161559878848754886189265)
              ·
                refine ⟨871169909136566164641949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161559878848754886189265 871169909136566164641949)
                ·
                  refine ⟨326688715926212311740731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871169909136566164641949 326688715926212311740731)
                  ·
                    rfl

theorem cell20_715752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_715752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715752 prefixEnd_715752 := by exact prefixLift 715752
  have htrace : WordTrace (prefixWord ++ tailWord_715752) baseStart_715752 baseEnd_715752 := by
    simpa [prefixWord, tailWord_715752, baseEnd_715752] using wordTrace_append hprefix tailTrace_715752
  have hstable : (prefixWord ++ tailWord_715752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715752).length < 2 ^ (prefixWord ++ tailWord_715752).sum := by decide
  have hdescent : baseEnd_715752 < baseStart_715752 := by decide
  rcases family_descends (prefixWord ++ tailWord_715752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715759 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_715759 : Nat := 118140960795 + 715759 * 2 ^ 59
def prefixEnd_715759 : Nat := 4983230072969 + 3 ^ 40 * 715759 * 2
def baseEnd_715759 : Nat := 326691910916951398507369

theorem tailTrace_715759 : CollatzResearch.WordTrace tailWord_715759 prefixEnd_715759 326691910916951398507369 := by
  unfold tailWord_715759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26105875413934859750134331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17403916942623239833422887 26105875413934859750134331)
  ·
    refine ⟨39158813120902289625201497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26105875413934859750134331 39158813120902289625201497)
    ·
      refine ⟨29369109840676717218901123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39158813120902289625201497 29369109840676717218901123)
      ·
        refine ⟨44053664761015075828351685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29369109840676717218901123 44053664761015075828351685)
        ·
          refine ⟨8260062142690326717815941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44053664761015075828351685 8260062142690326717815941)
          ·
            refine ⟨1548761651754436259590489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8260062142690326717815941 1548761651754436259590489)
            ·
              refine ⟨1161571238815827194692867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548761651754436259590489 1161571238815827194692867)
              ·
                refine ⟨1742356858223740792039301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161571238815827194692867 1742356858223740792039301)
                ·
                  refine ⟨326691910916951398507369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742356858223740792039301 326691910916951398507369)
                  ·
                    rfl

theorem cell20_715759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_715759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715759 prefixEnd_715759 := by exact prefixLift 715759
  have htrace : WordTrace (prefixWord ++ tailWord_715759) baseStart_715759 baseEnd_715759 := by
    simpa [prefixWord, tailWord_715759, baseEnd_715759] using wordTrace_append hprefix tailTrace_715759
  have hstable : (prefixWord ++ tailWord_715759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715759).length < 2 ^ (prefixWord ++ tailWord_715759).sum := by decide
  have hdescent : baseEnd_715759 < baseStart_715759 := by decide
  rcases family_descends (prefixWord ++ tailWord_715759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715765 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_715765 : Nat := 118140960795 + 715765 * 2 ^ 59
def prefixEnd_715765 : Nat := 4983230072969 + 3 ^ 40 * 715765 * 2
def baseEnd_715765 : Nat := 326694649480442044307345

theorem tailTrace_715765 : CollatzResearch.WordTrace tailWord_715765 prefixEnd_715765 326694649480442044307345 := by
  unfold tailWord_715765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26106094251913122774852749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17404062834608748516568499 26106094251913122774852749)
  ·
    refine ⟨9789785344467421040569781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26106094251913122774852749 9789785344467421040569781)
    ·
      refine ⟨917792376043820722553417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9789785344467421040569781 917792376043820722553417)
      ·
        refine ⟨688344282032865541915063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917792376043820722553417 688344282032865541915063)
        ·
          refine ⟨1032516423049298312872595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688344282032865541915063 1032516423049298312872595)
          ·
            refine ⟨1548774634573947469308893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032516423049298312872595 1548774634573947469308893)
            ·
              refine ⟨580790487965230300990835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548774634573947469308893 580790487965230300990835)
              ·
                refine ⟨871185731947845451486253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580790487965230300990835 871185731947845451486253)
                ·
                  refine ⟨326694649480442044307345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871185731947845451486253 326694649480442044307345)
                  ·
                    rfl

theorem cell20_715765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_715765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715765 prefixEnd_715765 := by exact prefixLift 715765
  have htrace : WordTrace (prefixWord ++ tailWord_715765) baseStart_715765 baseEnd_715765 := by
    simpa [prefixWord, tailWord_715765, baseEnd_715765] using wordTrace_append hprefix tailTrace_715765
  have hstable : (prefixWord ++ tailWord_715765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715765).length < 2 ^ (prefixWord ++ tailWord_715765).sum := by decide
  have hdescent : baseEnd_715765 < baseStart_715765 := by decide
  rcases family_descends (prefixWord ++ tailWord_715765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715811 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_715811 : Nat := 118140960795 + 715811 * 2 ^ 59
def prefixEnd_715811 : Nat := 4983230072969 + 3 ^ 40 * 715811 * 2
def baseEnd_715811 : Nat := 326715645133870328773823

theorem tailTrace_715811 : CollatzResearch.WordTrace tailWord_715811 prefixEnd_715811 326715645133870328773823 := by
  unfold tailWord_715811
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107772009746472631027287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17405181339830981754018191 26107772009746472631027287)
  ·
    refine ⟨39161658014619708946540931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26107772009746472631027287 39161658014619708946540931)
    ·
      refine ⟨58742487021929563419811397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39161658014619708946540931 58742487021929563419811397)
      ·
        refine ⟨11014216316611793141214637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58742487021929563419811397 11014216316611793141214637)
        ·
          refine ⟨4130331118729422427955489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11014216316611793141214637 4130331118729422427955489)
          ·
            refine ⟨3097748339047066820966617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130331118729422427955489 3097748339047066820966617)
            ·
              refine ⟨2323311254285300115724963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097748339047066820966617 2323311254285300115724963)
              ·
                refine ⟨3484966881427950173587445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323311254285300115724963 3484966881427950173587445)
                ·
                  refine ⟨326715645133870328773823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3484966881427950173587445 326715645133870328773823)
                  ·
                    rfl

theorem cell20_715811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_715811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715811 prefixEnd_715811 := by exact prefixLift 715811
  have htrace : WordTrace (prefixWord ++ tailWord_715811) baseStart_715811 baseEnd_715811 := by
    simpa [prefixWord, tailWord_715811, baseEnd_715811] using wordTrace_append hprefix tailTrace_715811
  have hstable : (prefixWord ++ tailWord_715811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715811).length < 2 ^ (prefixWord ++ tailWord_715811).sum := by decide
  have hdescent : baseEnd_715811 < baseStart_715811 := by decide
  rcases family_descends (prefixWord ++ tailWord_715811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715887 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_715887 : Nat := 118140960795 + 715887 * 2 ^ 59
def prefixEnd_715887 : Nat := 4983230072969 + 3 ^ 40 * 715887 * 2
def baseEnd_715887 : Nat := 326750333604751842240179

theorem tailTrace_715887 : CollatzResearch.WordTrace tailWord_715887 prefixEnd_715887 326750333604751842240179 := by
  unfold tailWord_715887
  simp only [CollatzResearch.WordTrace]
  refine ⟨26110543957471137610793915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407029304980758407195943 26110543957471137610793915)
  ·
    refine ⟨39165815936206706416190873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26110543957471137610793915 39165815936206706416190873)
    ·
      refine ⟨29374361952155029812143155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39165815936206706416190873 29374361952155029812143155)
      ·
        refine ⟨44061542928232544718214733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29374361952155029812143155 44061542928232544718214733)
        ·
          refine ⟨16523078598087204269330525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44061542928232544718214733 16523078598087204269330525)
          ·
            refine ⟨6196154474282701600998947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16523078598087204269330525 6196154474282701600998947)
            ·
              refine ⟨9294231711424052401498421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196154474282701600998947 9294231711424052401498421)
              ·
                refine ⟨871334222946004912640477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9294231711424052401498421 871334222946004912640477)
                ·
                  refine ⟨326750333604751842240179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871334222946004912640477 326750333604751842240179)
                  ·
                    rfl

theorem cell20_715887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_715887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715887 prefixEnd_715887 := by exact prefixLift 715887
  have htrace : WordTrace (prefixWord ++ tailWord_715887) baseStart_715887 baseEnd_715887 := by
    simpa [prefixWord, tailWord_715887, baseEnd_715887] using wordTrace_append hprefix tailTrace_715887
  have hstable : (prefixWord ++ tailWord_715887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715887).length < 2 ^ (prefixWord ++ tailWord_715887).sum := by decide
  have hdescent : baseEnd_715887 < baseStart_715887 := by decide
  rcases family_descends (prefixWord ++ tailWord_715887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715897 : List Nat := [1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_715897 : Nat := 118140960795 + 715897 * 2 ^ 59
def prefixEnd_715897 : Nat := 4983230072969 + 3 ^ 40 * 715897 * 2
def baseEnd_715897 : Nat := 108918299292412083968935

theorem tailTrace_715897 : CollatzResearch.WordTrace tailWord_715897 prefixEnd_715897 108918299292412083968935 := by
  unfold tailWord_715897
  simp only [CollatzResearch.WordTrace]
  refine ⟨26110908687434909318657945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407272458289939545771963 26110908687434909318657945)
  ·
    refine ⟨19583181515576181988993459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26110908687434909318657945 19583181515576181988993459)
    ·
      refine ⟨29374772273364272983490189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19583181515576181988993459 29374772273364272983490189)
      ·
        refine ⟨11015539602511602368808821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29374772273364272983490189 11015539602511602368808821)
        ·
          refine ⟨1032706837735462722075827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11015539602511602368808821 1032706837735462722075827)
          ·
            refine ⟨1549060256603194083113741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032706837735462722075827 1549060256603194083113741)
            ·
              refine ⟨580897596226197781167653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1549060256603194083113741 580897596226197781167653)
              ·
                refine ⟨108918299292412083968935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580897596226197781167653 108918299292412083968935)
                ·
                  rfl

theorem cell20_715897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_715897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715897 prefixEnd_715897 := by exact prefixLift 715897
  have htrace : WordTrace (prefixWord ++ tailWord_715897) baseStart_715897 baseEnd_715897 := by
    simpa [prefixWord, tailWord_715897, baseEnd_715897] using wordTrace_append hprefix tailTrace_715897
  have hstable : (prefixWord ++ tailWord_715897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715897).length < 2 ^ (prefixWord ++ tailWord_715897).sum := by decide
  have hdescent : baseEnd_715897 < baseStart_715897 := by decide
  rcases family_descends (prefixWord ++ tailWord_715897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715918 : List Nat := [4, 1, 1, 3, 2, 2, 7]
def baseStart_715918 : Nat := 118140960795 + 715918 * 2 ^ 59
def prefixEnd_715918 : Nat := 4983230072969 + 3 ^ 40 * 715918 * 2
def baseEnd_715918 : Nat := 36307164761050390245191

theorem tailTrace_715918 : CollatzResearch.WordTrace tailWord_715918 prefixEnd_715918 36307164761050390245191 := by
  unfold tailWord_715918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263959327544853738146551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17407783080239219936781605 3263959327544853738146551)
  ·
    refine ⟨4895938991317280607219827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263959327544853738146551 4895938991317280607219827)
    ·
      refine ⟨7343908486975920910829741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895938991317280607219827 7343908486975920910829741)
      ·
        refine ⟨2753965682615970341561153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7343908486975920910829741 2753965682615970341561153)
        ·
          refine ⟨2065474261961977756170865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753965682615970341561153 2065474261961977756170865)
          ·
            refine ⟨1549105696471483317128149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2065474261961977756170865 1549105696471483317128149)
            ·
              refine ⟨36307164761050390245191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1549105696471483317128149 36307164761050390245191)
              ·
                rfl

theorem cell20_715918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_715918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715918 prefixEnd_715918 := by exact prefixLift 715918
  have htrace : WordTrace (prefixWord ++ tailWord_715918) baseStart_715918 baseEnd_715918 := by
    simpa [prefixWord, tailWord_715918, baseEnd_715918] using wordTrace_append hprefix tailTrace_715918
  have hstable : (prefixWord ++ tailWord_715918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715918).length < 2 ^ (prefixWord ++ tailWord_715918).sum := by decide
  have hdescent : baseEnd_715918 < baseStart_715918 := by decide
  rcases family_descends (prefixWord ++ tailWord_715918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715925 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_715925 : Nat := 118140960795 + 715925 * 2 ^ 59
def prefixEnd_715925 : Nat := 4983230072969 + 3 ^ 40 * 715925 * 2
def baseEnd_715925 : Nat := 326767677840192598973357

theorem tailTrace_715925 : CollatzResearch.WordTrace tailWord_715925 prefixEnd_715925 326767677840192598973357 := by
  unfold tailWord_715925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111929931333470100677229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407953287555646733784819 26111929931333470100677229)
  ·
    refine ⟨9791973724250051287753961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26111929931333470100677229 9791973724250051287753961)
    ·
      refine ⟨7343980293187538465815471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9791973724250051287753961 7343980293187538465815471)
      ·
        refine ⟨11015970439781307698723207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7343980293187538465815471 11015970439781307698723207)
        ·
          refine ⟨16523955659671961548084811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015970439781307698723207 16523955659671961548084811)
          ·
            refine ⟨24785933489507942322127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16523955659671961548084811 24785933489507942322127217)
            ·
              refine ⟨18589450117130956741595413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24785933489507942322127217 18589450117130956741595413)
              ·
                refine ⟨871380474240513597262285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18589450117130956741595413 871380474240513597262285)
                ·
                  refine ⟨326767677840192598973357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871380474240513597262285 326767677840192598973357)
                  ·
                    rfl

theorem cell20_715925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_715925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715925 prefixEnd_715925 := by exact prefixLift 715925
  have htrace : WordTrace (prefixWord ++ tailWord_715925) baseStart_715925 baseEnd_715925 := by
    simpa [prefixWord, tailWord_715925, baseEnd_715925] using wordTrace_append hprefix tailTrace_715925
  have hstable : (prefixWord ++ tailWord_715925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715925).length < 2 ^ (prefixWord ++ tailWord_715925).sum := by decide
  have hdescent : baseEnd_715925 < baseStart_715925 := by decide
  rcases family_descends (prefixWord ++ tailWord_715925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715928 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_715928 : Nat := 118140960795 + 715928 * 2 ^ 59
def prefixEnd_715928 : Nat := 4983230072969 + 3 ^ 40 * 715928 * 2
def baseEnd_715928 : Nat := 326769047121937921873345

theorem tailTrace_715928 : CollatzResearch.WordTrace tailWord_715928 prefixEnd_715928 326769047121937921873345 := by
  unfold tailWord_715928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13056019675161300806518219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17408026233548401075357625 13056019675161300806518219)
  ·
    refine ⟨19584029512741951209777329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13056019675161300806518219 19584029512741951209777329)
    ·
      refine ⟨14688022134556463407332997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19584029512741951209777329 14688022134556463407332997)
      ·
        refine ⟨2754004150229336888874937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14688022134556463407332997 2754004150229336888874937)
        ·
          refine ⟨2065503112672002666656203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754004150229336888874937 2065503112672002666656203)
          ·
            refine ⟨3098254669008003999984305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065503112672002666656203 3098254669008003999984305)
            ·
              refine ⟨2323691001756002999988229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098254669008003999984305 2323691001756002999988229)
              ·
                refine ⟨435692062829250562497793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2323691001756002999988229 435692062829250562497793)
                ·
                  refine ⟨326769047121937921873345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435692062829250562497793 326769047121937921873345)
                  ·
                    rfl

theorem cell20_715928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_715928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715928 prefixEnd_715928 := by exact prefixLift 715928
  have htrace : WordTrace (prefixWord ++ tailWord_715928) baseStart_715928 baseEnd_715928 := by
    simpa [prefixWord, tailWord_715928, baseEnd_715928] using wordTrace_append hprefix tailTrace_715928
  have hstable : (prefixWord ++ tailWord_715928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715928).length < 2 ^ (prefixWord ++ tailWord_715928).sum := by decide
  have hdescent : baseEnd_715928 < baseStart_715928 := by decide
  rcases family_descends (prefixWord ++ tailWord_715928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715938 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_715938 : Nat := 118140960795 + 715938 * 2 ^ 59
def prefixEnd_715938 : Nat := 4983230072969 + 3 ^ 40 * 715938 * 2
def baseEnd_715938 : Nat := 326773611394422331539971

theorem tailTrace_715938 : CollatzResearch.WordTrace tailWord_715938 prefixEnd_715938 326773611394422331539971 := by
  unfold tailWord_715938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528101020071593330225117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17408269386857582213933645 6528101020071593330225117)
  ·
    refine ⟨2448037882526847498834419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6528101020071593330225117 2448037882526847498834419)
    ·
      refine ⟨3672056823790271248251629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448037882526847498834419 3672056823790271248251629)
      ·
        refine ⟨1377021308921351718094361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3672056823790271248251629 1377021308921351718094361)
        ·
          refine ⟨1032765981691013788570771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377021308921351718094361 1032765981691013788570771)
          ·
            refine ⟨1549148972536520682856157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032765981691013788570771 1549148972536520682856157)
            ·
              refine ⟨580930864701195256071059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1549148972536520682856157 580930864701195256071059)
              ·
                refine ⟨871396297051792884106589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580930864701195256071059 871396297051792884106589)
                ·
                  refine ⟨326773611394422331539971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871396297051792884106589 326773611394422331539971)
                  ·
                    rfl

theorem cell20_715938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_715938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715938 prefixEnd_715938 := by exact prefixLift 715938
  have htrace : WordTrace (prefixWord ++ tailWord_715938) baseStart_715938 baseEnd_715938 := by
    simpa [prefixWord, tailWord_715938, baseEnd_715938] using wordTrace_append hprefix tailTrace_715938
  have hstable : (prefixWord ++ tailWord_715938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715938).length < 2 ^ (prefixWord ++ tailWord_715938).sum := by decide
  have hdescent : baseEnd_715938 < baseStart_715938 := by decide
  rcases family_descends (prefixWord ++ tailWord_715938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715958 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_715958 : Nat := 118140960795 + 715958 * 2 ^ 59
def prefixEnd_715958 : Nat := 4983230072969 + 3 ^ 40 * 715958 * 2
def baseEnd_715958 : Nat := 326782739939391150873223

theorem tailTrace_715958 : CollatzResearch.WordTrace tailWord_715958 prefixEnd_715958 326782739939391150873223 := by
  unfold tailWord_715958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632070846263369796039283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17408755693475944491085685 1632070846263369796039283)
  ·
    refine ⟨2448106269395054694058925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632070846263369796039283 2448106269395054694058925)
    ·
      refine ⟨918039851023145510272097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2448106269395054694058925 918039851023145510272097)
      ·
        refine ⟨688529888267359132704073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918039851023145510272097 688529888267359132704073)
        ·
          refine ⟨516397416200519349528055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688529888267359132704073 516397416200519349528055)
          ·
            refine ⟨774596124300779024292083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516397416200519349528055 774596124300779024292083)
            ·
              refine ⟨1161894186451168536438125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774596124300779024292083 1161894186451168536438125)
              ·
                refine ⟨435710319919188201164297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161894186451168536438125 435710319919188201164297)
                ·
                  refine ⟨326782739939391150873223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435710319919188201164297 326782739939391150873223)
                  ·
                    rfl

theorem cell20_715958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_715958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715958 prefixEnd_715958 := by exact prefixLift 715958
  have htrace : WordTrace (prefixWord ++ tailWord_715958) baseStart_715958 baseEnd_715958 := by
    simpa [prefixWord, tailWord_715958, baseEnd_715958] using wordTrace_append hprefix tailTrace_715958
  have hstable : (prefixWord ++ tailWord_715958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715958).length < 2 ^ (prefixWord ++ tailWord_715958).sum := by decide
  have hdescent : baseEnd_715958 < baseStart_715958 := by decide
  rcases family_descends (prefixWord ++ tailWord_715958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715990 : List Nat := [5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_715990 : Nat := 118140960795 + 715990 * 2 ^ 59
def prefixEnd_715990 : Nat := 4983230072969 + 3 ^ 40 * 715990 * 2
def baseEnd_715990 : Nat := 108932448537113753935475

theorem tailTrace_715990 : CollatzResearch.WordTrace tailWord_715990 prefixEnd_715990 108932448537113753935475 := by
  unfold tailWord_715990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632143792256124137612089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17409533784065324134528949 1632143792256124137612089)
  ·
    refine ⟨1224107844192093103209067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1632143792256124137612089 1224107844192093103209067)
    ·
      refine ⟨1836161766288139654813601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224107844192093103209067 1836161766288139654813601)
      ·
        refine ⟨1377121324716104741110201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1836161766288139654813601 1377121324716104741110201)
        ·
          refine ⟨1032840993537078555832651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377121324716104741110201 1032840993537078555832651)
          ·
            refine ⟨1549261490305617833748977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032840993537078555832651 1549261490305617833748977)
            ·
              refine ⟨1161946117729213375311733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549261490305617833748977 1161946117729213375311733)
              ·
                refine ⟨108932448537113753935475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1161946117729213375311733 108932448537113753935475)
                ·
                  rfl

theorem cell20_715990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_715990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715990 prefixEnd_715990 := by exact prefixLift 715990
  have htrace : WordTrace (prefixWord ++ tailWord_715990) baseStart_715990 baseEnd_715990 := by
    simpa [prefixWord, tailWord_715990, baseEnd_715990] using wordTrace_append hprefix tailTrace_715990
  have hstable : (prefixWord ++ tailWord_715990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715990).length < 2 ^ (prefixWord ++ tailWord_715990).sum := by decide
  have hdescent : baseEnd_715990 < baseStart_715990 := by decide
  rcases family_descends (prefixWord ++ tailWord_715990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715997 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_715997 : Nat := 118140960795 + 715997 * 2 ^ 59
def prefixEnd_715997 : Nat := 4983230072969 + 3 ^ 40 * 715997 * 2
def baseEnd_715997 : Nat := 326800540602080348573063

theorem tailTrace_715997 : CollatzResearch.WordTrace tailWord_715997 prefixEnd_715997 326800540602080348573063 := by
  unfold tailWord_715997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114555987072626397298245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17409703991381750931532163 26114555987072626397298245)
  ·
    refine ⟨4896479247576117449493421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26114555987072626397298245 4896479247576117449493421)
    ·
      refine ⟨1836179717841044043560033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4896479247576117449493421 1836179717841044043560033)
      ·
        refine ⟨1377134788380783032670025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1836179717841044043560033 1377134788380783032670025)
        ·
          refine ⟨1032851091285587274502519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377134788380783032670025 1032851091285587274502519)
          ·
            refine ⟨1549276636928380911753779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032851091285587274502519 1549276636928380911753779)
            ·
              refine ⟨2323914955392571367630669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549276636928380911753779 2323914955392571367630669)
              ·
                refine ⟨871468108272214262861501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323914955392571367630669 871468108272214262861501)
                ·
                  refine ⟨326800540602080348573063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871468108272214262861501 326800540602080348573063)
                  ·
                    rfl

theorem cell20_715997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_715997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_715997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_715997 prefixEnd_715997 := by exact prefixLift 715997
  have htrace : WordTrace (prefixWord ++ tailWord_715997) baseStart_715997 baseEnd_715997 := by
    simpa [prefixWord, tailWord_715997, baseEnd_715997] using wordTrace_append hprefix tailTrace_715997
  have hstable : (prefixWord ++ tailWord_715997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715997).length < 2 ^ (prefixWord ++ tailWord_715997).sum := by decide
  have hdescent : baseEnd_715997 < baseStart_715997 := by decide
  rcases family_descends (prefixWord ++ tailWord_715997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716008 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_716008 : Nat := 118140960795 + 716008 * 2 ^ 59
def prefixEnd_716008 : Nat := 4983230072969 + 3 ^ 40 * 716008 * 2
def baseEnd_716008 : Nat := 326805561301813199206351

theorem tailTrace_716008 : CollatzResearch.WordTrace tailWord_716008 prefixEnd_716008 326805561301813199206351 := by
  unfold tailWord_716008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057478595016387637974339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17409971460021850183965785 13057478595016387637974339)
  ·
    refine ⟨19586217892524581456961509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13057478595016387637974339 19586217892524581456961509)
    ·
      refine ⟨3672415854848359023180283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19586217892524581456961509 3672415854848359023180283)
      ·
        refine ⟨5508623782272538534770425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672415854848359023180283 5508623782272538534770425)
        ·
          refine ⟨4131467836704403901077819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5508623782272538534770425 4131467836704403901077819)
          ·
            refine ⟨6197201755056605851616729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131467836704403901077819 6197201755056605851616729)
            ·
              refine ⟨4647901316292454388712547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197201755056605851616729 4647901316292454388712547)
              ·
                refine ⟨6971851974438681583068821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647901316292454388712547 6971851974438681583068821)
                ·
                  refine ⟨326805561301813199206351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6971851974438681583068821 326805561301813199206351)
                  ·
                    rfl

theorem cell20_716008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_716008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716008 prefixEnd_716008 := by exact prefixLift 716008
  have htrace : WordTrace (prefixWord ++ tailWord_716008) baseStart_716008 baseEnd_716008 := by
    simpa [prefixWord, tailWord_716008, baseEnd_716008] using wordTrace_append hprefix tailTrace_716008
  have hstable : (prefixWord ++ tailWord_716008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716008).length < 2 ^ (prefixWord ++ tailWord_716008).sum := by decide
  have hdescent : baseEnd_716008 < baseStart_716008 := by decide
  rcases family_descends (prefixWord ++ tailWord_716008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716025 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 2]
def baseStart_716025 : Nat := 118140960795 + 716025 * 2 ^ 59
def prefixEnd_716025 : Nat := 4983230072969 + 3 ^ 40 * 716025 * 2
def baseEnd_716025 : Nat := 326813320565036695639615

theorem tailTrace_716025 : CollatzResearch.WordTrace tailWord_716025 prefixEnd_716025 326813320565036695639615 := by
  unfold tailWord_716025
  simp only [CollatzResearch.WordTrace]
  refine ⟨26115577230971187179317529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17410384820647458119545019 26115577230971187179317529)
  ·
    refine ⟨19586682923228390384488147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26115577230971187179317529 19586682923228390384488147)
    ·
      refine ⟨29380024384842585576732221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19586682923228390384488147 29380024384842585576732221)
      ·
        refine ⟨11017509144315969591274583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29380024384842585576732221 11017509144315969591274583)
        ·
          refine ⟨16526263716473954386911875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11017509144315969591274583 16526263716473954386911875)
          ·
            refine ⟨24789395574710931580367813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16526263716473954386911875 24789395574710931580367813)
            ·
              refine ⟨4648011670258299671318965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24789395574710931580367813 4648011670258299671318965)
              ·
                refine ⟨435751094086715594186153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4648011670258299671318965 435751094086715594186153)
                ·
                  refine ⟨326813320565036695639615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435751094086715594186153 326813320565036695639615)
                  ·
                    rfl

theorem cell20_716025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_716025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716025 prefixEnd_716025 := by exact prefixLift 716025
  have htrace : WordTrace (prefixWord ++ tailWord_716025) baseStart_716025 baseEnd_716025 := by
    simpa [prefixWord, tailWord_716025, baseEnd_716025] using wordTrace_append hprefix tailTrace_716025
  have hstable : (prefixWord ++ tailWord_716025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716025).length < 2 ^ (prefixWord ++ tailWord_716025).sum := by decide
  have hdescent : baseEnd_716025 < baseStart_716025 := by decide
  rcases family_descends (prefixWord ++ tailWord_716025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716063 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_716063 : Nat := 118140960795 + 716063 * 2 ^ 59
def prefixEnd_716063 : Nat := 4983230072969 + 3 ^ 40 * 716063 * 2
def baseEnd_716063 : Nat := 326830664800477452372793

theorem tailTrace_716063 : CollatzResearch.WordTrace tailWord_716063 prefixEnd_716063 326830664800477452372793 := by
  unfold tailWord_716063
  simp only [CollatzResearch.WordTrace]
  refine ⟨26116963204833519669200843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17411308803222346446133895 26116963204833519669200843)
  ·
    refine ⟨39175444807250279503801265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26116963204833519669200843 39175444807250279503801265)
    ·
      refine ⟨29381583605437709627850949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39175444807250279503801265 29381583605437709627850949)
      ·
        refine ⟨5509046926019570555222053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29381583605437709627850949 5509046926019570555222053)
        ·
          refine ⟨1032946298628669479104135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5509046926019570555222053 1032946298628669479104135)
          ·
            refine ⟨1549419447943004218656203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032946298628669479104135 1549419447943004218656203)
            ·
              refine ⟨2324129171914506327984305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549419447943004218656203 2324129171914506327984305)
              ·
                refine ⟨1743096878935879745988229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324129171914506327984305 1743096878935879745988229)
                ·
                  refine ⟨326830664800477452372793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743096878935879745988229 326830664800477452372793)
                  ·
                    rfl

theorem cell20_716063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_716063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716063 prefixEnd_716063 := by exact prefixLift 716063
  have htrace : WordTrace (prefixWord ++ tailWord_716063) baseStart_716063 baseEnd_716063 := by
    simpa [prefixWord, tailWord_716063, baseEnd_716063] using wordTrace_append hprefix tailTrace_716063
  have hstable : (prefixWord ++ tailWord_716063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716063).length < 2 ^ (prefixWord ++ tailWord_716063).sum := by decide
  have hdescent : baseEnd_716063 < baseStart_716063 := by decide
  rcases family_descends (prefixWord ++ tailWord_716063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716122 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_716122 : Nat := 118140960795 + 716122 * 2 ^ 59
def prefixEnd_716122 : Nat := 4983230072969 + 3 ^ 40 * 716122 * 2
def baseEnd_716122 : Nat := 326857594008135469405885

theorem tailTrace_716122 : CollatzResearch.WordTrace tailWord_716122 prefixEnd_716122 326857594008135469405885 := by
  unfold tailWord_716122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529778777904943186399655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17412743407746515163732413 6529778777904943186399655)
  ·
    refine ⟨9794668166857414779599483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6529778777904943186399655 9794668166857414779599483)
    ·
      refine ⟨14692002250286122169399225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9794668166857414779599483 14692002250286122169399225)
      ·
        refine ⟨11019001687714591627049419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14692002250286122169399225 11019001687714591627049419)
        ·
          refine ⟨16528502531571887440574129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019001687714591627049419 16528502531571887440574129)
          ·
            refine ⟨12396376898678915580430597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16528502531571887440574129 12396376898678915580430597)
            ·
              refine ⟨2324320668502296671330737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12396376898678915580430597 2324320668502296671330737)
              ·
                refine ⟨1743240501376722503498053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324320668502296671330737 1743240501376722503498053)
                ·
                  refine ⟨326857594008135469405885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743240501376722503498053 326857594008135469405885)
                  ·
                    rfl

theorem cell20_716122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_716122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716122 prefixEnd_716122 := by exact prefixLift 716122
  have htrace : WordTrace (prefixWord ++ tailWord_716122) baseStart_716122 baseEnd_716122 := by
    simpa [prefixWord, tailWord_716122, baseEnd_716122] using wordTrace_append hprefix tailTrace_716122
  have hstable : (prefixWord ++ tailWord_716122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716122).length < 2 ^ (prefixWord ++ tailWord_716122).sum := by decide
  have hdescent : baseEnd_716122 < baseStart_716122 := by decide
  rcases family_descends (prefixWord ++ tailWord_716122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716135 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 2]
def baseStart_716135 : Nat := 118140960795 + 716135 * 2 ^ 59
def prefixEnd_716135 : Nat := 4983230072969 + 3 ^ 40 * 716135 * 2
def baseEnd_716135 : Nat := 326863527562365201972499

theorem tailTrace_716135 : CollatzResearch.WordTrace tailWord_716135 prefixEnd_716135 326863527562365201972499 := by
  unfold tailWord_716135
  simp only [CollatzResearch.WordTrace]
  refine ⟨26119589260572675965821859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17413059507048450643881239 26119589260572675965821859)
  ·
    refine ⟨39179383890859013948732789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26119589260572675965821859 39179383890859013948732789)
    ·
      refine ⟨3673067239768032557693699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39179383890859013948732789 3673067239768032557693699)
      ·
        refine ⟨5509600859652048836540549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673067239768032557693699 5509600859652048836540549)
        ·
          refine ⟨1033050161184759156851353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5509600859652048836540549 1033050161184759156851353)
          ·
            refine ⟨774787620888569367638515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033050161184759156851353 774787620888569367638515)
            ·
              refine ⟨1162181431332854051457773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774787620888569367638515 1162181431332854051457773)
              ·
                refine ⟨435818036749820269296665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162181431332854051457773 435818036749820269296665)
                ·
                  refine ⟨326863527562365201972499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435818036749820269296665 326863527562365201972499)
                  ·
                    rfl

theorem cell20_716135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2].length) (baseStart_716135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716135 prefixEnd_716135 := by exact prefixLift 716135
  have htrace : WordTrace (prefixWord ++ tailWord_716135) baseStart_716135 baseEnd_716135 := by
    simpa [prefixWord, tailWord_716135, baseEnd_716135] using wordTrace_append hprefix tailTrace_716135
  have hstable : (prefixWord ++ tailWord_716135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716135).length < 2 ^ (prefixWord ++ tailWord_716135).sum := by decide
  have hdescent : baseEnd_716135 < baseStart_716135 := by decide
  rcases family_descends (prefixWord ++ tailWord_716135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716142 : List Nat := [4, 1, 2, 4, 2, 1, 6]
def baseStart_716142 : Nat := 118140960795 + 716142 * 2 ^ 59
def prefixEnd_716142 : Nat := 4983230072969 + 3 ^ 40 * 716142 * 2
def baseEnd_716142 : Nat := 36318524728122698748793

theorem tailTrace_716142 : CollatzResearch.WordTrace tailWord_716142 prefixEnd_716142 36318524728122698748793 := by
  unfold tailWord_716142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264980571443414520165835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17413229714364877440884453 3264980571443414520165835)
  ·
    refine ⟨4897470857165121780248753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3264980571443414520165835 4897470857165121780248753)
    ·
      refine ⟨3673103142873841335186565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4897470857165121780248753 3673103142873841335186565)
      ·
        refine ⟨688706839288845250347481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3673103142873841335186565 688706839288845250347481)
        ·
          refine ⟨516530129466633937760611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688706839288845250347481 516530129466633937760611)
          ·
            refine ⟨774795194199950906640917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516530129466633937760611 774795194199950906640917)
            ·
              refine ⟨36318524728122698748793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 774795194199950906640917 36318524728122698748793)
              ·
                rfl

theorem cell20_716142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_716142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716142 prefixEnd_716142 := by exact prefixLift 716142
  have htrace : WordTrace (prefixWord ++ tailWord_716142) baseStart_716142 baseEnd_716142 := by
    simpa [prefixWord, tailWord_716142, baseEnd_716142] using wordTrace_append hprefix tailTrace_716142
  have hstable : (prefixWord ++ tailWord_716142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716142).length < 2 ^ (prefixWord ++ tailWord_716142).sum := by decide
  have hdescent : baseEnd_716142 < baseStart_716142 := by decide
  rcases family_descends (prefixWord ++ tailWord_716142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716156 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_716156 : Nat := 118140960795 + 716156 * 2 ^ 59
def prefixEnd_716156 : Nat := 4983230072969 + 3 ^ 40 * 716156 * 2
def baseEnd_716156 : Nat := 326873112534582462272413

theorem tailTrace_716156 : CollatzResearch.WordTrace tailWord_716156 prefixEnd_716156 326873112534582462272413 := by
  unfold tailWord_716156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060177596748298276168161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17413570128997731034890881 13060177596748298276168161)
  ·
    refine ⟨9795133197561223707126121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13060177596748298276168161 9795133197561223707126121)
    ·
      refine ⟨7346349898170917780344591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9795133197561223707126121 7346349898170917780344591)
      ·
        refine ⟨11019524847256376670516887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346349898170917780344591 11019524847256376670516887)
        ·
          refine ⟨16529287270884565005775331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019524847256376670516887 16529287270884565005775331)
          ·
            refine ⟨24793930906326847508662997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16529287270884565005775331 24793930906326847508662997)
            ·
              refine ⟨581107755617035488484289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24793930906326847508662997 581107755617035488484289)
              ·
                refine ⟨435830816712776616363217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581107755617035488484289 435830816712776616363217)
                ·
                  refine ⟨326873112534582462272413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435830816712776616363217 326873112534582462272413)
                  ·
                    rfl

theorem cell20_716156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_716156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716156 prefixEnd_716156 := by exact prefixLift 716156
  have htrace : WordTrace (prefixWord ++ tailWord_716156) baseStart_716156 baseEnd_716156 := by
    simpa [prefixWord, tailWord_716156, baseEnd_716156] using wordTrace_append hprefix tailTrace_716156
  have hstable : (prefixWord ++ tailWord_716156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716156).length < 2 ^ (prefixWord ++ tailWord_716156).sum := by decide
  have hdescent : baseEnd_716156 < baseStart_716156 := by decide
  rcases family_descends (prefixWord ++ tailWord_716156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716167 : List Nat := [1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_716167 : Nat := 118140960795 + 716167 * 2 ^ 59
def prefixEnd_716167 : Nat := 4983230072969 + 3 ^ 40 * 716167 * 2
def baseEnd_716167 : Nat := 108959377744771770968567

theorem tailTrace_716167 : CollatzResearch.WordTrace tailWord_716167 prefixEnd_716167 108959377744771770968567 := by
  unfold tailWord_716167
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120756396456745430986755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17413837597637830287324503 26120756396456745430986755)
  ·
    refine ⟨39181134594685118146480133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26120756396456745430986755 39181134594685118146480133)
    ·
      refine ⟨7346462736503459652465025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39181134594685118146480133 7346462736503459652465025)
      ·
        refine ⟨5509847052377594739348769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7346462736503459652465025 5509847052377594739348769)
        ·
          refine ⟨4132385289283196054511577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5509847052377594739348769 4132385289283196054511577)
          ·
            refine ⟨3099288966962397040883683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4132385289283196054511577 3099288966962397040883683)
            ·
              refine ⟨4648933450443595561325525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099288966962397040883683 4648933450443595561325525)
              ·
                refine ⟨108959377744771770968567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4648933450443595561325525 108959377744771770968567)
                ·
                  rfl

theorem cell20_716167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_716167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716167 prefixEnd_716167 := by exact prefixLift 716167
  have htrace : WordTrace (prefixWord ++ tailWord_716167) baseStart_716167 baseEnd_716167 := by
    simpa [prefixWord, tailWord_716167, baseEnd_716167] using wordTrace_append hprefix tailTrace_716167
  have hstable : (prefixWord ++ tailWord_716167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716167).length < 2 ^ (prefixWord ++ tailWord_716167).sum := by decide
  have hdescent : baseEnd_716167 < baseStart_716167 := by decide
  rcases family_descends (prefixWord ++ tailWord_716167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716215 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 2]
def baseStart_716215 : Nat := 118140960795 + 716215 * 2 ^ 59
def prefixEnd_716215 : Nat := 4983230072969 + 3 ^ 40 * 716215 * 2
def baseEnd_716215 : Nat := 326900041742240479305505

theorem tailTrace_716215 : CollatzResearch.WordTrace tailWord_716215 prefixEnd_716215 326900041742240479305505 := by
  unfold tailWord_716215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122507100282849628734099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17415004733521899752489399 26122507100282849628734099)
  ·
    refine ⟨39183760650424274443101149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26122507100282849628734099 39183760650424274443101149)
    ·
      refine ⟨14693910243909102916162931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39183760650424274443101149 14693910243909102916162931)
      ·
        refine ⟨22040865365863654374244397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14693910243909102916162931 22040865365863654374244397)
        ·
          refine ⟨8265324512198870390341649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22040865365863654374244397 8265324512198870390341649)
          ·
            refine ⟨6198993384149152792756237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8265324512198870390341649 6198993384149152792756237)
            ·
              refine ⟨2324622519055932297283589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6198993384149152792756237 2324622519055932297283589)
              ·
                refine ⟨435866722322987305740673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2324622519055932297283589 435866722322987305740673)
                ·
                  refine ⟨326900041742240479305505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435866722322987305740673 326900041742240479305505)
                  ·
                    rfl

theorem cell20_716215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2].length) (baseStart_716215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716215 prefixEnd_716215 := by exact prefixLift 716215
  have htrace : WordTrace (prefixWord ++ tailWord_716215) baseStart_716215 baseEnd_716215 := by
    simpa [prefixWord, tailWord_716215, baseEnd_716215] using wordTrace_append hprefix tailTrace_716215
  have hstable : (prefixWord ++ tailWord_716215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716215).length < 2 ^ (prefixWord ++ tailWord_716215).sum := by decide
  have hdescent : baseEnd_716215 < baseStart_716215 := by decide
  rcases family_descends (prefixWord ++ tailWord_716215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716236 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_716236 : Nat := 118140960795 + 716236 * 2 ^ 59
def prefixEnd_716236 : Nat := 4983230072969 + 3 ^ 40 * 716236 * 2
def baseEnd_716236 : Nat := 326909626714457739605419

theorem tailTrace_716236 : CollatzResearch.WordTrace tailWord_716236 prefixEnd_716236 326909626714457739605419 := by
  unfold tailWord_716236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061636516603385107624281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17415515355471180143499041 13061636516603385107624281)
  ·
    refine ⟨9796227387452538830718211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13061636516603385107624281 9796227387452538830718211)
    ·
      refine ⟨14694341081178808246077317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9796227387452538830718211 14694341081178808246077317)
      ·
        refine ⟨2755188952721026546139497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14694341081178808246077317 2755188952721026546139497)
        ·
          refine ⟨2066391714540769909604623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755188952721026546139497 2066391714540769909604623)
          ·
            refine ⟨3099587571811154864406935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066391714540769909604623 3099587571811154864406935)
            ·
              refine ⟨4649381357716732296610403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099587571811154864406935 4649381357716732296610403)
              ·
                refine ⟨6974072036575098444915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649381357716732296610403 6974072036575098444915605)
                ·
                  refine ⟨326909626714457739605419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6974072036575098444915605 326909626714457739605419)
                  ·
                    rfl

theorem cell20_716236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_716236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716236 prefixEnd_716236 := by exact prefixLift 716236
  have htrace : WordTrace (prefixWord ++ tailWord_716236) baseStart_716236 baseEnd_716236 := by
    simpa [prefixWord, tailWord_716236, baseEnd_716236] using wordTrace_append hprefix tailTrace_716236
  have hstable : (prefixWord ++ tailWord_716236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716236).length < 2 ^ (prefixWord ++ tailWord_716236).sum := by decide
  have hdescent : baseEnd_716236 < baseStart_716236 := by decide
  rcases family_descends (prefixWord ++ tailWord_716236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716298 : List Nat := [3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_716298 : Nat := 118140960795 + 716298 * 2 ^ 59
def prefixEnd_716298 : Nat := 4983230072969 + 3 ^ 40 * 716298 * 2
def baseEnd_716298 : Nat := 108979308401287026512833

theorem tailTrace_716298 : CollatzResearch.WordTrace tailWord_716298 prefixEnd_716298 108979308401287026512833 := by
  unfold tailWord_716298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531383589745538701001387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17417022905988103202670365 6531383589745538701001387)
  ·
    refine ⟨9797075384618308051502081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6531383589745538701001387 9797075384618308051502081)
    ·
      refine ⟨7347806538463731038626561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9797075384618308051502081 7347806538463731038626561)
      ·
        refine ⟨5510854903847798278969921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7347806538463731038626561 5510854903847798278969921)
        ·
          refine ⟨4133141177885848709227441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5510854903847798278969921 4133141177885848709227441)
          ·
            refine ⟨3099855883414386531920581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4133141177885848709227441 3099855883414386531920581)
            ·
              refine ⟨581222978140197474735109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3099855883414386531920581 581222978140197474735109)
              ·
                refine ⟨108979308401287026512833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581222978140197474735109 108979308401287026512833)
                ·
                  rfl

theorem cell20_716298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_716298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716298 prefixEnd_716298 := by exact prefixLift 716298
  have htrace : WordTrace (prefixWord ++ tailWord_716298) baseStart_716298 baseEnd_716298 := by
    simpa [prefixWord, tailWord_716298, baseEnd_716298] using wordTrace_append hprefix tailTrace_716298
  have hstable : (prefixWord ++ tailWord_716298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716298).length < 2 ^ (prefixWord ++ tailWord_716298).sum := by decide
  have hdescent : baseEnd_716298 < baseStart_716298 := by decide
  rcases family_descends (prefixWord ++ tailWord_716298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716343 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_716343 : Nat := 118140960795 + 716343 * 2 ^ 59
def prefixEnd_716343 : Nat := 4983230072969 + 3 ^ 40 * 716343 * 2
def baseEnd_716343 : Nat := 326958464430040923038315

theorem tailTrace_716343 : CollatzResearch.WordTrace tailWord_716343 prefixEnd_716343 326958464430040923038315 := by
  unfold tailWord_716343
  simp only [CollatzResearch.WordTrace]
  refine ⟨26127175643819127489393683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17418117095879418326262455 26127175643819127489393683)
  ·
    refine ⟨39190763465728691234090525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26127175643819127489393683 39190763465728691234090525)
    ·
      refine ⟨14696536299648259212783947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39190763465728691234090525 14696536299648259212783947)
      ·
        refine ⟨22044804449472388819175921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14696536299648259212783947 22044804449472388819175921)
        ·
          refine ⟨16533603337104291614381941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22044804449472388819175921 16533603337104291614381941)
          ·
            refine ⟨1550025312853527338848307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16533603337104291614381941 1550025312853527338848307)
            ·
              refine ⟨2325037969280291008272461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550025312853527338848307 2325037969280291008272461)
              ·
                refine ⟨871889238480109128102173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2325037969280291008272461 871889238480109128102173)
                ·
                  refine ⟨326958464430040923038315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871889238480109128102173 326958464430040923038315)
                  ·
                    rfl

theorem cell20_716343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_716343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716343 prefixEnd_716343 := by exact prefixLift 716343
  have htrace : WordTrace (prefixWord ++ tailWord_716343) baseStart_716343 baseEnd_716343 := by
    simpa [prefixWord, tailWord_716343, baseEnd_716343] using wordTrace_append hprefix tailTrace_716343
  have hstable : (prefixWord ++ tailWord_716343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716343).length < 2 ^ (prefixWord ++ tailWord_716343).sum := by decide
  have hdescent : baseEnd_716343 < baseStart_716343 := by decide
  rcases family_descends (prefixWord ++ tailWord_716343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716405 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_716405 : Nat := 118140960795 + 716405 * 2 ^ 59
def prefixEnd_716405 : Nat := 4983230072969 + 3 ^ 40 * 716405 * 2
def baseEnd_716405 : Nat := 326986762919444262971395

theorem tailTrace_716405 : CollatzResearch.WordTrace tailWord_716405 prefixEnd_716405 326986762919444262971395 := by
  unfold tailWord_716405
  simp only [CollatzResearch.WordTrace]
  refine ⟨26129436969594512078150669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17419624646396341385433779 26129436969594512078150669)
  ·
    refine ⟨9798538863597942029306501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26129436969594512078150669 9798538863597942029306501)
    ·
      refine ⟨1837226036924614130494969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9798538863597942029306501 1837226036924614130494969)
      ·
        refine ⟨1377919527693460597871227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1837226036924614130494969 1377919527693460597871227)
        ·
          refine ⟨2066879291540190896806841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377919527693460597871227 2066879291540190896806841)
          ·
            refine ⟨1550159468655143172605131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066879291540190896806841 1550159468655143172605131)
            ·
              refine ⟨2325239202982714758907697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550159468655143172605131 2325239202982714758907697)
              ·
                refine ⟨1743929402237036069180773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325239202982714758907697 1743929402237036069180773)
                ·
                  refine ⟨326986762919444262971395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743929402237036069180773 326986762919444262971395)
                  ·
                    rfl

theorem cell20_716405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_716405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716405 prefixEnd_716405 := by exact prefixLift 716405
  have htrace : WordTrace (prefixWord ++ tailWord_716405) baseStart_716405 baseEnd_716405 := by
    simpa [prefixWord, tailWord_716405, baseEnd_716405] using wordTrace_append hprefix tailTrace_716405
  have hstable : (prefixWord ++ tailWord_716405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716405).length < 2 ^ (prefixWord ++ tailWord_716405).sum := by decide
  have hdescent : baseEnd_716405 < baseStart_716405 := by decide
  rcases family_descends (prefixWord ++ tailWord_716405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716436 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_716436 : Nat := 118140960795 + 716436 * 2 ^ 59
def prefixEnd_716436 : Nat := 4983230072969 + 3 ^ 40 * 716436 * 2
def baseEnd_716436 : Nat := 327000912164145932937935

theorem tailTrace_716436 : CollatzResearch.WordTrace tailWord_716436 prefixEnd_716436 327000912164145932937935 := by
  unfold tailWord_716436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065283816241102186264581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17420378421654802915019441 13065283816241102186264581)
  ·
    refine ⟨2449740715545206659924609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13065283816241102186264581 2449740715545206659924609)
    ·
      refine ⟨1837305536658904994943457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449740715545206659924609 1837305536658904994943457)
      ·
        refine ⟨1377979152494178746207593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1837305536658904994943457 1377979152494178746207593)
        ·
          refine ⟨1033484364370634059655695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377979152494178746207593 1033484364370634059655695)
          ·
            refine ⟨1550226546555951089483543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033484364370634059655695 1550226546555951089483543)
            ·
              refine ⟨2325339819833926634225315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550226546555951089483543 2325339819833926634225315)
              ·
                refine ⟨3488009729750889951337973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325339819833926634225315 3488009729750889951337973)
                ·
                  refine ⟨327000912164145932937935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488009729750889951337973 327000912164145932937935)
                  ·
                    rfl

theorem cell20_716436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_716436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716436 prefixEnd_716436 := by exact prefixLift 716436
  have htrace : WordTrace (prefixWord ++ tailWord_716436) baseStart_716436 baseEnd_716436 := by
    simpa [prefixWord, tailWord_716436, baseEnd_716436] using wordTrace_append hprefix tailTrace_716436
  have hstable : (prefixWord ++ tailWord_716436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716436).length < 2 ^ (prefixWord ++ tailWord_716436).sum := by decide
  have hdescent : baseEnd_716436 < baseStart_716436 := by decide
  rcases family_descends (prefixWord ++ tailWord_716436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716471 : List Nat := [1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_716471 : Nat := 118140960795 + 716471 * 2 ^ 59
def prefixEnd_716471 : Nat := 4983230072969 + 3 ^ 40 * 716471 * 2
def baseEnd_716471 : Nat := 109005629039280455590375

theorem tailTrace_716471 : CollatzResearch.WordTrace tailWord_716471 prefixEnd_716471 109005629039280455590375 := by
  unfold tailWord_716471
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131844187355405350053267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17421229458236936900035511 26131844187355405350053267)
  ·
    refine ⟨39197766281033108025079901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26131844187355405350053267 39197766281033108025079901)
    ·
      refine ⟨14699162355387415509404963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39197766281033108025079901 14699162355387415509404963)
      ·
        refine ⟨22048743533081123264107445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14699162355387415509404963 22048743533081123264107445)
        ·
          refine ⟨2067069706226355306010073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22048743533081123264107445 2067069706226355306010073)
          ·
            refine ⟨1550302279669766479507555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067069706226355306010073 1550302279669766479507555)
            ·
              refine ⟨2325453419504649719261333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550302279669766479507555 2325453419504649719261333)
              ·
                refine ⟨109005629039280455590375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2325453419504649719261333 109005629039280455590375)
                ·
                  rfl

theorem cell20_716471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_716471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716471 prefixEnd_716471 := by exact prefixLift 716471
  have htrace : WordTrace (prefixWord ++ tailWord_716471) baseStart_716471 baseEnd_716471 := by
    simpa [prefixWord, tailWord_716471, baseEnd_716471] using wordTrace_append hprefix tailTrace_716471
  have hstable : (prefixWord ++ tailWord_716471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716471).length < 2 ^ (prefixWord ++ tailWord_716471).sum := by decide
  have hdescent : baseEnd_716471 < baseStart_716471 := by decide
  rcases family_descends (prefixWord ++ tailWord_716471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716508 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_716508 : Nat := 118140960795 + 716508 * 2 ^ 59
def prefixEnd_716508 : Nat := 4983230072969 + 3 ^ 40 * 716508 * 2
def baseEnd_716508 : Nat := 327033774926033682537641

theorem tailTrace_716508 : CollatzResearch.WordTrace tailWord_716508 prefixEnd_716508 327033774926033682537641 := by
  unfold tailWord_716508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066596844110680334575089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17422129125480907112766785 13066596844110680334575089)
  ·
    refine ⟨9799947633083010250931317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13066596844110680334575089 9799947633083010250931317)
    ·
      refine ⟨918745090601532211024811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9799947633083010250931317 918745090601532211024811)
      ·
        refine ⟨1378117635902298316537217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918745090601532211024811 1378117635902298316537217)
        ·
          refine ⟨1033588226926723737402913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378117635902298316537217 1033588226926723737402913)
          ·
            refine ⟨775191170195042803052185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033588226926723737402913 775191170195042803052185)
            ·
              refine ⟨581393377646282102289139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775191170195042803052185 581393377646282102289139)
              ·
                refine ⟨872090066469423153433709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581393377646282102289139 872090066469423153433709)
                ·
                  refine ⟨327033774926033682537641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872090066469423153433709 327033774926033682537641)
                  ·
                    rfl

theorem cell20_716508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_716508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716508 prefixEnd_716508 := by exact prefixLift 716508
  have htrace : WordTrace (prefixWord ++ tailWord_716508) baseStart_716508 baseEnd_716508 := by
    simpa [prefixWord, tailWord_716508, baseEnd_716508] using wordTrace_append hprefix tailTrace_716508
  have hstable : (prefixWord ++ tailWord_716508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716508).length < 2 ^ (prefixWord ++ tailWord_716508).sum := by decide
  have hdescent : baseEnd_716508 < baseStart_716508 := by decide
  rcases family_descends (prefixWord ++ tailWord_716508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716523 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_716523 : Nat := 118140960795 + 716523 * 2 ^ 59
def prefixEnd_716523 : Nat := 4983230072969 + 3 ^ 40 * 716523 * 2
def baseEnd_716523 : Nat := 327040621334760297037579

theorem tailTrace_716523 : CollatzResearch.WordTrace tailWord_716523 prefixEnd_716523 327040621334760297037579 := by
  unfold tailWord_716523
  simp only [CollatzResearch.WordTrace]
  refine ⟨26133740783167018230946223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17422493855444678820630815 26133740783167018230946223)
  ·
    refine ⟨39200611174750527346419335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26133740783167018230946223 39200611174750527346419335)
    ·
      refine ⟨58800916762125791019629003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39200611174750527346419335 58800916762125791019629003)
      ·
        refine ⟨88201375143188686529443505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58800916762125791019629003 88201375143188686529443505)
        ·
          refine ⟨66151031357391514897082629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88201375143188686529443505 66151031357391514897082629)
          ·
            refine ⟨12403318379510909043202993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66151031357391514897082629 12403318379510909043202993)
            ·
              refine ⟨9302488784633181782402245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12403318379510909043202993 9302488784633181782402245)
              ·
                refine ⟨1744216647118721584200421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9302488784633181782402245 1744216647118721584200421)
                ·
                  refine ⟨327040621334760297037579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744216647118721584200421 327040621334760297037579)
                  ·
                    rfl

theorem cell20_716523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_716523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716523 prefixEnd_716523 := by exact prefixLift 716523
  have htrace : WordTrace (prefixWord ++ tailWord_716523) baseStart_716523 baseEnd_716523 := by
    simpa [prefixWord, tailWord_716523, baseEnd_716523] using wordTrace_append hprefix tailTrace_716523
  have hstable : (prefixWord ++ tailWord_716523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716523).length < 2 ^ (prefixWord ++ tailWord_716523).sum := by decide
  have hdescent : baseEnd_716523 < baseStart_716523 := by decide
  rcases family_descends (prefixWord ++ tailWord_716523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716561 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_716561 : Nat := 118140960795 + 716561 * 2 ^ 59
def prefixEnd_716561 : Nat := 4983230072969 + 3 ^ 40 * 716561 * 2
def baseEnd_716561 : Nat := 327057965570201053770757

theorem tailTrace_716561 : CollatzResearch.WordTrace tailWord_716561 prefixEnd_716561 327057965570201053770757 := by
  unfold tailWord_716561
  simp only [CollatzResearch.WordTrace]
  refine ⟨26135126757029350720829537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17423417838019567147219691 26135126757029350720829537)
  ·
    refine ⟨19601345067772013040622153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26135126757029350720829537 19601345067772013040622153)
    ·
      refine ⟨14701008800829009780466615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19601345067772013040622153 14701008800829009780466615)
      ·
        refine ⟨22051513201243514670699923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14701008800829009780466615 22051513201243514670699923)
        ·
          refine ⟨33077269801865272006049885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22051513201243514670699923 33077269801865272006049885)
          ·
            refine ⟨12403976175699477002268707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33077269801865272006049885 12403976175699477002268707)
            ·
              refine ⟨18605964263549215503403061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12403976175699477002268707 18605964263549215503403061)
              ·
                refine ⟨1744309149707738953444037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18605964263549215503403061 1744309149707738953444037)
                ·
                  refine ⟨327057965570201053770757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744309149707738953444037 327057965570201053770757)
                  ·
                    rfl

theorem cell20_716561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_716561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716561 prefixEnd_716561 := by exact prefixLift 716561
  have htrace : WordTrace (prefixWord ++ tailWord_716561) baseStart_716561 baseEnd_716561 := by
    simpa [prefixWord, tailWord_716561, baseEnd_716561] using wordTrace_append hprefix tailTrace_716561
  have hstable : (prefixWord ++ tailWord_716561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716561).length < 2 ^ (prefixWord ++ tailWord_716561).sum := by decide
  have hdescent : baseEnd_716561 < baseStart_716561 := by decide
  rcases family_descends (prefixWord ++ tailWord_716561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716578 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_716578 : Nat := 118140960795 + 716578 * 2 ^ 59
def prefixEnd_716578 : Nat := 4983230072969 + 3 ^ 40 * 716578 * 2
def baseEnd_716578 : Nat := 327065724833424550204021

theorem tailTrace_716578 : CollatzResearch.WordTrace tailWord_716578 prefixEnd_716578 327065724833424550204021 := by
  unfold tailWord_716578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533936699491940656049597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17423831198645175082798925 6533936699491940656049597)
  ·
    refine ⟨2450226262309477746018599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6533936699491940656049597 2450226262309477746018599)
    ·
      refine ⟨3675339393464216619027899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450226262309477746018599 3675339393464216619027899)
      ·
        refine ⟨5513009090196324928541849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675339393464216619027899 5513009090196324928541849)
        ·
          refine ⟨4134756817647243696406387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5513009090196324928541849 4134756817647243696406387)
          ·
            refine ⟨6202135226470865544609581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134756817647243696406387 6202135226470865544609581)
            ·
              refine ⟨2325800709926574579228593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6202135226470865544609581 2325800709926574579228593)
              ·
                refine ⟨1744350532444930934421445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325800709926574579228593 1744350532444930934421445)
                ·
                  refine ⟨327065724833424550204021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744350532444930934421445 327065724833424550204021)
                  ·
                    rfl

theorem cell20_716578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_716578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716578 prefixEnd_716578 := by exact prefixLift 716578
  have htrace : WordTrace (prefixWord ++ tailWord_716578) baseStart_716578 baseEnd_716578 := by
    simpa [prefixWord, tailWord_716578, baseEnd_716578] using wordTrace_append hprefix tailTrace_716578
  have hstable : (prefixWord ++ tailWord_716578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716578).length < 2 ^ (prefixWord ++ tailWord_716578).sum := by decide
  have hdescent : baseEnd_716578 < baseStart_716578 := by decide
  rcases family_descends (prefixWord ++ tailWord_716578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716616 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_716616 : Nat := 118140960795 + 716616 * 2 ^ 59
def prefixEnd_716616 : Nat := 4983230072969 + 3 ^ 40 * 716616 * 2
def baseEnd_716616 : Nat := 327083069068865306937199

theorem tailTrace_716616 : CollatzResearch.WordTrace tailWord_716616 prefixEnd_716616 327083069068865306937199 := by
  unfold tailWord_716616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068566385915047557040851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17424755181220063409387801 13068566385915047557040851)
  ·
    refine ⟨19602849578872571335561277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13068566385915047557040851 19602849578872571335561277)
    ·
      refine ⟨7351068592077214250835479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19602849578872571335561277 7351068592077214250835479)
      ·
        refine ⟨11026602888115821376253219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7351068592077214250835479 11026602888115821376253219)
        ·
          refine ⟨16539904332173732064379829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026602888115821376253219 16539904332173732064379829)
          ·
            refine ⟨1550616031141287381035609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16539904332173732064379829 1550616031141287381035609)
            ·
              refine ⟨1162962023355965535776707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550616031141287381035609 1162962023355965535776707)
              ·
                refine ⟨1744443035033948303665061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162962023355965535776707 1744443035033948303665061)
                ·
                  refine ⟨327083069068865306937199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744443035033948303665061 327083069068865306937199)
                  ·
                    rfl

theorem cell20_716616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_716616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716616 prefixEnd_716616 := by exact prefixLift 716616
  have htrace : WordTrace (prefixWord ++ tailWord_716616) baseStart_716616 baseEnd_716616 := by
    simpa [prefixWord, tailWord_716616, baseEnd_716616] using wordTrace_append hprefix tailTrace_716616
  have hstable : (prefixWord ++ tailWord_716616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716616).length < 2 ^ (prefixWord ++ tailWord_716616).sum := by decide
  have hdescent : baseEnd_716616 < baseStart_716616 := by decide
  rcases family_descends (prefixWord ++ tailWord_716616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716626 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_716626 : Nat := 118140960795 + 716626 * 2 ^ 59
def prefixEnd_716626 : Nat := 4983230072969 + 3 ^ 40 * 716626 * 2
def baseEnd_716626 : Nat := 327087633341349716603825

theorem tailTrace_716626 : CollatzResearch.WordTrace tailWord_716626 prefixEnd_716626 327087633341349716603825 := by
  unfold tailWord_716626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534374375448466705486433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17424998334529244547963821 6534374375448466705486433)
  ·
    refine ⟨4900780781586350029114825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6534374375448466705486433 4900780781586350029114825)
    ·
      refine ⟨3675585586189762521836119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4900780781586350029114825 3675585586189762521836119)
      ·
        refine ⟨5513378379284643782754179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675585586189762521836119 5513378379284643782754179)
        ·
          refine ⟨8270067568926965674131269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513378379284643782754179 8270067568926965674131269)
          ·
            refine ⟨1550637669173806063899613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8270067568926965674131269 1550637669173806063899613)
            ·
              refine ⟨581489125940177273962355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1550637669173806063899613 581489125940177273962355)
              ·
                refine ⟨872233688910265910943533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581489125940177273962355 872233688910265910943533)
                ·
                  refine ⟨327087633341349716603825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872233688910265910943533 327087633341349716603825)
                  ·
                    rfl

theorem cell20_716626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_716626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716626 prefixEnd_716626 := by exact prefixLift 716626
  have htrace : WordTrace (prefixWord ++ tailWord_716626) baseStart_716626 baseEnd_716626 := by
    simpa [prefixWord, tailWord_716626, baseEnd_716626] using wordTrace_append hprefix tailTrace_716626
  have hstable : (prefixWord ++ tailWord_716626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716626).length < 2 ^ (prefixWord ++ tailWord_716626).sum := by decide
  have hdescent : baseEnd_716626 < baseStart_716626 := by decide
  rcases family_descends (prefixWord ++ tailWord_716626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716636 : List Nat := [2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_716636 : Nat := 118140960795 + 716636 * 2 ^ 59
def prefixEnd_716636 : Nat := 4983230072969 + 3 ^ 40 * 716636 * 2
def baseEnd_716636 : Nat := 109030732537944708756817

theorem tailTrace_716636 : CollatzResearch.WordTrace tailWord_716636 prefixEnd_716636 109030732537944708756817 := by
  unfold tailWord_716636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068931115878819264904881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17425241487838425686539841 13068931115878819264904881)
  ·
    refine ⟨9801698336909114448678661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13068931115878819264904881 9801698336909114448678661)
    ·
      refine ⟨1837818438170458959127249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9801698336909114448678661 1837818438170458959127249)
      ·
        refine ⟨1378363828627844219345437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1837818438170458959127249 1378363828627844219345437)
        ·
          refine ⟨516886435735441582254539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1378363828627844219345437 516886435735441582254539)
          ·
            refine ⟨775329653603162373381809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516886435735441582254539 775329653603162373381809)
            ·
              refine ⟨581497240202371780036357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775329653603162373381809 581497240202371780036357)
              ·
                refine ⟨109030732537944708756817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581497240202371780036357 109030732537944708756817)
                ·
                  rfl

theorem cell20_716636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_716636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716636 prefixEnd_716636 := by exact prefixLift 716636
  have htrace : WordTrace (prefixWord ++ tailWord_716636) baseStart_716636 baseEnd_716636 := by
    simpa [prefixWord, tailWord_716636, baseEnd_716636] using wordTrace_append hprefix tailTrace_716636
  have hstable : (prefixWord ++ tailWord_716636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716636).length < 2 ^ (prefixWord ++ tailWord_716636).sum := by decide
  have hdescent : baseEnd_716636 < baseStart_716636 := by decide
  rcases family_descends (prefixWord ++ tailWord_716636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716640 : List Nat := [2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_716640 : Nat := 118140960795 + 716640 * 2 ^ 59
def prefixEnd_716640 : Nat := 4983230072969 + 3 ^ 40 * 716640 * 2
def baseEnd_716640 : Nat := 109031341107609296712367

theorem tailTrace_716640 : CollatzResearch.WordTrace tailWord_716640 prefixEnd_716640 109031341107609296712367 := by
  unfold tailWord_716640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069004061871573606477687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17425338749162098141970249 13069004061871573606477687)
  ·
    refine ⟨19603506092807360409716531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13069004061871573606477687 19603506092807360409716531)
    ·
      refine ⟨29405259139211040614574797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19603506092807360409716531 29405259139211040614574797)
      ·
        refine ⟨11026972177204140230465549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29405259139211040614574797 11026972177204140230465549)
        ·
          refine ⟨4135114566451552586424581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11026972177204140230465549 4135114566451552586424581)
          ·
            refine ⟨775333981209666109954609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4135114566451552586424581 775333981209666109954609)
            ·
              refine ⟨581500485907249582465957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775333981209666109954609 581500485907249582465957)
              ·
                refine ⟨109031341107609296712367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581500485907249582465957 109031341107609296712367)
                ·
                  rfl

theorem cell20_716640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_716640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716640 prefixEnd_716640 := by exact prefixLift 716640
  have htrace : WordTrace (prefixWord ++ tailWord_716640) baseStart_716640 baseEnd_716640 := by
    simpa [prefixWord, tailWord_716640, baseEnd_716640] using wordTrace_append hprefix tailTrace_716640
  have hstable : (prefixWord ++ tailWord_716640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716640).length < 2 ^ (prefixWord ++ tailWord_716640).sum := by decide
  have hdescent : baseEnd_716640 < baseStart_716640 := by decide
  rcases family_descends (prefixWord ++ tailWord_716640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716718 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_716718 : Nat := 118140960795 + 716718 * 2 ^ 59
def prefixEnd_716718 : Nat := 4983230072969 + 3 ^ 40 * 716718 * 2
def baseEnd_716718 : Nat := 327129624648206285536783

theorem tailTrace_716718 : CollatzResearch.WordTrace tailWord_716718 prefixEnd_716718 327129624648206285536783 := by
  unfold tailWord_716718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267606627182570816786851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17427235344973711022863205 3267606627182570816786851)
  ·
    refine ⟨4901409940773856225180277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267606627182570816786851 4901409940773856225180277)
    ·
      refine ⟨459507181947549021110651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4901409940773856225180277 459507181947549021110651)
      ·
        refine ⟨689260772921323531665977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459507181947549021110651 689260772921323531665977)
        ·
          refine ⟨516945579690992648749483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689260772921323531665977 516945579690992648749483)
          ·
            refine ⟨775418369536488973124225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516945579690992648749483 775418369536488973124225)
            ·
              refine ⟨581563777152366729843169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775418369536488973124225 581563777152366729843169)
              ·
                refine ⟨436172832864275047382377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581563777152366729843169 436172832864275047382377)
                ·
                  refine ⟨327129624648206285536783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436172832864275047382377 327129624648206285536783)
                  ·
                    rfl

theorem cell20_716718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_716718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716718 prefixEnd_716718 := by exact prefixLift 716718
  have htrace : WordTrace (prefixWord ++ tailWord_716718) baseStart_716718 baseEnd_716718 := by
    simpa [prefixWord, tailWord_716718, baseEnd_716718] using wordTrace_append hprefix tailTrace_716718
  have hstable : (prefixWord ++ tailWord_716718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716718).length < 2 ^ (prefixWord ++ tailWord_716718).sum := by decide
  have hdescent : baseEnd_716718 < baseStart_716718 := by decide
  rcases family_descends (prefixWord ++ tailWord_716718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716751 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_716751 : Nat := 118140960795 + 716751 * 2 ^ 59
def prefixEnd_716751 : Nat := 4983230072969 + 3 ^ 40 * 716751 * 2
def baseEnd_716751 : Nat := 327144686747404837436647

theorem tailTrace_716751 : CollatzResearch.WordTrace tailWord_716751 prefixEnd_716751 327144686747404837436647 := by
  unfold tailWord_716751
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142056626341013170246107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17428037750894008780164071 26142056626341013170246107)
  ·
    refine ⟨39213084939511519755369161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26142056626341013170246107 39213084939511519755369161)
    ·
      refine ⟨29409813704633639816526871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39213084939511519755369161 29409813704633639816526871)
      ·
        refine ⟨44114720556950459724790307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29409813704633639816526871 44114720556950459724790307)
        ·
          refine ⟨66172080835425689587185461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44114720556950459724790307 66172080835425689587185461)
          ·
            refine ⟨6203632578321158398798637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66172080835425689587185461 6203632578321158398798637)
            ·
              refine ⟨2326362216870434399549489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203632578321158398798637 2326362216870434399549489)
              ·
                refine ⟨1744771662652825799662117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326362216870434399549489 1744771662652825799662117)
                ·
                  refine ⟨327144686747404837436647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744771662652825799662117 327144686747404837436647)
                  ·
                    rfl

theorem cell20_716751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_716751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716751 prefixEnd_716751 := by exact prefixLift 716751
  have htrace : WordTrace (prefixWord ++ tailWord_716751) baseStart_716751 baseEnd_716751 := by
    simpa [prefixWord, tailWord_716751, baseEnd_716751] using wordTrace_append hprefix tailTrace_716751
  have hstable : (prefixWord ++ tailWord_716751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716751).length < 2 ^ (prefixWord ++ tailWord_716751).sum := by decide
  have hdescent : baseEnd_716751 < baseStart_716751 := by decide
  rcases family_descends (prefixWord ++ tailWord_716751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716775 : List Nat := [1, 1, 5, 2, 3, 1, 7]
def baseStart_716775 : Nat := 118140960795 + 716775 * 2 ^ 59
def prefixEnd_716775 : Nat := 4983230072969 + 3 ^ 40 * 716775 * 2
def baseEnd_716775 : Nat := 36350626777929713404061

theorem tailTrace_716775 : CollatzResearch.WordTrace tailWord_716775 prefixEnd_716775 36350626777929713404061 := by
  unfold tailWord_716775
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142931978254065269119779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17428621318836043512746519 26142931978254065269119779)
  ·
    refine ⟨39214397967381097903679669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26142931978254065269119779 39214397967381097903679669)
    ·
      refine ⟨3676349809441977928469969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39214397967381097903679669 3676349809441977928469969)
      ·
        refine ⟨2757262357081483446352477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3676349809441977928469969 2757262357081483446352477)
        ·
          refine ⟨1033973383905556292382179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2757262357081483446352477 1033973383905556292382179)
          ·
            refine ⟨1550960075858334438573269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033973383905556292382179 1550960075858334438573269)
            ·
              refine ⟨36350626777929713404061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1550960075858334438573269 36350626777929713404061)
              ·
                rfl

theorem cell20_716775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_716775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716775 prefixEnd_716775 := by exact prefixLift 716775
  have htrace : WordTrace (prefixWord ++ tailWord_716775) baseStart_716775 baseEnd_716775 := by
    simpa [prefixWord, tailWord_716775, baseEnd_716775] using wordTrace_append hprefix tailTrace_716775
  have hstable : (prefixWord ++ tailWord_716775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716775).length < 2 ^ (prefixWord ++ tailWord_716775).sum := by decide
  have hdescent : baseEnd_716775 < baseStart_716775 := by decide
  rcases family_descends (prefixWord ++ tailWord_716775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716796 : List Nat := [2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_716796 : Nat := 118140960795 + 716796 * 2 ^ 59
def prefixEnd_716796 : Nat := 4983230072969 + 3 ^ 40 * 716796 * 2
def baseEnd_716796 : Nat := 109055075324528226978821

theorem tailTrace_716796 : CollatzResearch.WordTrace tailWord_716796 prefixEnd_716796 109055075324528226978821 := by
  unfold tailWord_716796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071848955588992927817121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17429131940785323903756161 13071848955588992927817121)
  ·
    refine ⟨9803886716691744695862841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13071848955588992927817121 9803886716691744695862841)
    ·
      refine ⟨7352915037518808521897131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9803886716691744695862841 7352915037518808521897131)
      ·
        refine ⟨11029372556278212782845697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352915037518808521897131 11029372556278212782845697)
        ·
          refine ⟨8272029417208659587134273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11029372556278212782845697 8272029417208659587134273)
          ·
            refine ⟨6204022062906494690350705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8272029417208659587134273 6204022062906494690350705)
            ·
              refine ⟨4653016547179871017763029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6204022062906494690350705 4653016547179871017763029)
              ·
                refine ⟨109055075324528226978821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4653016547179871017763029 109055075324528226978821)
                ·
                  rfl

theorem cell20_716796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_716796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716796 prefixEnd_716796 := by exact prefixLift 716796
  have htrace : WordTrace (prefixWord ++ tailWord_716796) baseStart_716796 baseEnd_716796 := by
    simpa [prefixWord, tailWord_716796, baseEnd_716796] using wordTrace_append hprefix tailTrace_716796
  have hstable : (prefixWord ++ tailWord_716796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716796).length < 2 ^ (prefixWord ++ tailWord_716796).sum := by decide
  have hdescent : baseEnd_716796 < baseStart_716796 := by decide
  rcases family_descends (prefixWord ++ tailWord_716796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716840 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_716840 : Nat := 118140960795 + 716840 * 2 ^ 59
def prefixEnd_716840 : Nat := 4983230072969 + 3 ^ 40 * 716840 * 2
def baseEnd_716840 : Nat := 327185308772516083469617

theorem tailTrace_716840 : CollatzResearch.WordTrace tailWord_716840 prefixEnd_716840 327185308772516083469617 := by
  unfold tailWord_716840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13072651361509290685117987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17430201815345720913490649 13072651361509290685117987)
  ·
    refine ⟨19608977042263936027676981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13072651361509290685117987 19608977042263936027676981)
    ·
      refine ⟨1838341597712244002594717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19608977042263936027676981 1838341597712244002594717)
      ·
        refine ⟨689378099142091500973019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1838341597712244002594717 689378099142091500973019)
        ·
          refine ⟨1034067148713137251459529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689378099142091500973019 1034067148713137251459529)
          ·
            refine ⟨775550361534852938594647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034067148713137251459529 775550361534852938594647)
            ·
              refine ⟨1163325542302279407891971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775550361534852938594647 1163325542302279407891971)
              ·
                refine ⟨1744988313453419111837957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163325542302279407891971 1744988313453419111837957)
                ·
                  refine ⟨327185308772516083469617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744988313453419111837957 327185308772516083469617)
                  ·
                    rfl

theorem cell20_716840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_716840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716840 prefixEnd_716840 := by exact prefixLift 716840
  have htrace : WordTrace (prefixWord ++ tailWord_716840) baseStart_716840 baseEnd_716840 := by
    simpa [prefixWord, tailWord_716840, baseEnd_716840] using wordTrace_append hprefix tailTrace_716840
  have hstable : (prefixWord ++ tailWord_716840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716840).length < 2 ^ (prefixWord ++ tailWord_716840).sum := by decide
  have hdescent : baseEnd_716840 < baseStart_716840 := by decide
  rcases family_descends (prefixWord ++ tailWord_716840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716896 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_716896 : Nat := 118140960795 + 716896 * 2 ^ 59
def prefixEnd_716896 : Nat := 4983230072969 + 3 ^ 40 * 716896 * 2
def baseEnd_716896 : Nat := 327210868698428777602721

theorem tailTrace_716896 : CollatzResearch.WordTrace tailWord_716896 prefixEnd_716896 327210868698428777602721 := by
  unfold tailWord_716896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073672605407851467137271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17431563473877135289516361 13073672605407851467137271)
  ·
    refine ⟨19610508908111777200705907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13073672605407851467137271 19610508908111777200705907)
    ·
      refine ⟨29415763362167665801058861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19610508908111777200705907 29415763362167665801058861)
      ·
        refine ⟨11030911260812874675397073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29415763362167665801058861 11030911260812874675397073)
        ·
          refine ⟨8273183445609656006547805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11030911260812874675397073 8273183445609656006547805)
          ·
            refine ⟨3102443792103621002455427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8273183445609656006547805 3102443792103621002455427)
            ·
              refine ⟨4653665688155431503683141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102443792103621002455427 4653665688155431503683141)
              ·
                refine ⟨872562316529143406940589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4653665688155431503683141 872562316529143406940589)
                ·
                  refine ⟨327210868698428777602721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872562316529143406940589 327210868698428777602721)
                  ·
                    rfl

theorem cell20_716896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_716896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716896 prefixEnd_716896 := by exact prefixLift 716896
  have htrace : WordTrace (prefixWord ++ tailWord_716896) baseStart_716896 baseEnd_716896 := by
    simpa [prefixWord, tailWord_716896, baseEnd_716896] using wordTrace_append hprefix tailTrace_716896
  have hstable : (prefixWord ++ tailWord_716896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716896).length < 2 ^ (prefixWord ++ tailWord_716896).sum := by decide
  have hdescent : baseEnd_716896 < baseStart_716896 := by decide
  rcases family_descends (prefixWord ++ tailWord_716896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716899 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 2]
def baseStart_716899 : Nat := 118140960795 + 716899 * 2 ^ 59
def prefixEnd_716899 : Nat := 4983230072969 + 3 ^ 40 * 716899 * 2
def baseEnd_716899 : Nat := 327212237980174100502709

theorem tailTrace_716899 : CollatzResearch.WordTrace tailWord_716899 prefixEnd_716899 327212237980174100502709 := by
  unfold tailWord_716899
  simp only [CollatzResearch.WordTrace]
  refine ⟨26147454629804834446633751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17431636419869889631089167 26147454629804834446633751)
  ·
    refine ⟨39221181944707251669950627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26147454629804834446633751 39221181944707251669950627)
    ·
      refine ⟨58831772917060877504925941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39221181944707251669950627 58831772917060877504925941)
      ·
        refine ⟨5515478710974457266086807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58831772917060877504925941 5515478710974457266086807)
        ·
          refine ⟨8273218066461685899130211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515478710974457266086807 8273218066461685899130211)
          ·
            refine ⟨12409827099692528848695317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273218066461685899130211 12409827099692528848695317)
            ·
              refine ⟨581710645298087289782593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12409827099692528848695317 581710645298087289782593)
              ·
                refine ⟨436282983973565467336945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581710645298087289782593 436282983973565467336945)
                ·
                  refine ⟨327212237980174100502709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436282983973565467336945 327212237980174100502709)
                  ·
                    rfl

theorem cell20_716899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2].length) (baseStart_716899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716899 prefixEnd_716899 := by exact prefixLift 716899
  have htrace : WordTrace (prefixWord ++ tailWord_716899) baseStart_716899 baseEnd_716899 := by
    simpa [prefixWord, tailWord_716899, baseEnd_716899] using wordTrace_append hprefix tailTrace_716899
  have hstable : (prefixWord ++ tailWord_716899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716899).length < 2 ^ (prefixWord ++ tailWord_716899).sum := by decide
  have hdescent : baseEnd_716899 < baseStart_716899 := by decide
  rcases family_descends (prefixWord ++ tailWord_716899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716903 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_716903 : Nat := 118140960795 + 716903 * 2 ^ 59
def prefixEnd_716903 : Nat := 4983230072969 + 3 ^ 40 * 716903 * 2
def baseEnd_716903 : Nat := 327214063689167864369359

theorem tailTrace_716903 : CollatzResearch.WordTrace tailWord_716903 prefixEnd_716903 327214063689167864369359 := by
  unfold tailWord_716903
  simp only [CollatzResearch.WordTrace]
  refine ⟨26147600521790343129779363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17431733681193562086519575 26147600521790343129779363)
  ·
    refine ⟨39221400782685514694669045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26147600521790343129779363 39221400782685514694669045)
    ·
      refine ⟨3677006323376767002625223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39221400782685514694669045 3677006323376767002625223)
      ·
        refine ⟨5515509485065150503937835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677006323376767002625223 5515509485065150503937835)
        ·
          refine ⟨8273264227597725755906753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515509485065150503937835 8273264227597725755906753)
          ·
            refine ⟨6204948170698294316930065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273264227597725755906753 6204948170698294316930065)
            ·
              refine ⟨4653711128023720737697549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6204948170698294316930065 4653711128023720737697549)
              ·
                refine ⟨1745141673008895276636581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4653711128023720737697549 1745141673008895276636581)
                ·
                  refine ⟨327214063689167864369359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745141673008895276636581 327214063689167864369359)
                  ·
                    rfl

theorem cell20_716903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_716903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716903 prefixEnd_716903 := by exact prefixLift 716903
  have htrace : WordTrace (prefixWord ++ tailWord_716903) baseStart_716903 baseEnd_716903 := by
    simpa [prefixWord, tailWord_716903, baseEnd_716903] using wordTrace_append hprefix tailTrace_716903
  have hstable : (prefixWord ++ tailWord_716903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716903).length < 2 ^ (prefixWord ++ tailWord_716903).sum := by decide
  have hdescent : baseEnd_716903 < baseStart_716903 := by decide
  rcases family_descends (prefixWord ++ tailWord_716903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716906 : List Nat := [3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_716906 : Nat := 118140960795 + 716906 * 2 ^ 59
def prefixEnd_716906 : Nat := 4983230072969 + 3 ^ 40 * 716906 * 2
def baseEnd_716906 : Nat := 109071810990304395756449

theorem tailTrace_716906 : CollatzResearch.WordTrace tailWord_716906 prefixEnd_716906 109071810990304395756449 := by
  unfold tailWord_716906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536927485194868660534643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17431806627186316428092381 6536927485194868660534643)
  ·
    refine ⟨9805391227792302990801965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536927485194868660534643 9805391227792302990801965)
    ·
      refine ⟨3677021710422113621550737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9805391227792302990801965 3677021710422113621550737)
      ·
        refine ⟨2757766282816585216163053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677021710422113621550737 2757766282816585216163053)
        ·
          refine ⟨1034162356056219456061145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2757766282816585216163053 1034162356056219456061145)
          ·
            refine ⟨775621767042164592045859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034162356056219456061145 775621767042164592045859)
            ·
              refine ⟨1163432650563246888068789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775621767042164592045859 1163432650563246888068789)
              ·
                refine ⟨109071810990304395756449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1163432650563246888068789 109071810990304395756449)
                ·
                  rfl

theorem cell20_716906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_716906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716906 prefixEnd_716906 := by exact prefixLift 716906
  have htrace : WordTrace (prefixWord ++ tailWord_716906) baseStart_716906 baseEnd_716906 := by
    simpa [prefixWord, tailWord_716906, baseEnd_716906] using wordTrace_append hprefix tailTrace_716906
  have hstable : (prefixWord ++ tailWord_716906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716906).length < 2 ^ (prefixWord ++ tailWord_716906).sum := by decide
  have hdescent : baseEnd_716906 < baseStart_716906 := by decide
  rcases family_descends (prefixWord ++ tailWord_716906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716950 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_716950 : Nat := 118140960795 + 716950 * 2 ^ 59
def prefixEnd_716950 : Nat := 4983230072969 + 3 ^ 40 * 716950 * 2
def baseEnd_716950 : Nat := 327235515769844589802501

theorem tailTrace_716950 : CollatzResearch.WordTrace tailWord_716950 prefixEnd_716950 327235515769844589802501 := by
  unfold tailWord_716950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634332172038754384796269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17432876501746713437826869 1634332172038754384796269)
  ·
    refine ⟨612874564514532894298601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1634332172038754384796269 612874564514532894298601)
    ·
      refine ⟨459655923385899670723951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612874564514532894298601 459655923385899670723951)
      ·
        refine ⟨689483885078849506085927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459655923385899670723951 689483885078849506085927)
        ·
          refine ⟨1034225827618274259128891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689483885078849506085927 1034225827618274259128891)
          ·
            refine ⟨1551338741427411388693337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034225827618274259128891 1551338741427411388693337)
            ·
              refine ⟨1163504056070558541520003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551338741427411388693337 1163504056070558541520003)
              ·
                refine ⟨1745256084105837812280005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163504056070558541520003 1745256084105837812280005)
                ·
                  refine ⟨327235515769844589802501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745256084105837812280005 327235515769844589802501)
                  ·
                    rfl

theorem cell20_716950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_716950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_716950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_716950 prefixEnd_716950 := by exact prefixLift 716950
  have htrace : WordTrace (prefixWord ++ tailWord_716950) baseStart_716950 baseEnd_716950 := by
    simpa [prefixWord, tailWord_716950, baseEnd_716950] using wordTrace_append hprefix tailTrace_716950
  have hstable : (prefixWord ++ tailWord_716950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716950).length < 2 ^ (prefixWord ++ tailWord_716950).sum := by decide
  have hdescent : baseEnd_716950 < baseStart_716950 := by decide
  rcases family_descends (prefixWord ++ tailWord_716950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717010 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_717010 : Nat := 118140960795 + 717010 * 2 ^ 59
def prefixEnd_717010 : Nat := 4983230072969 + 3 ^ 40 * 717010 * 2
def baseEnd_717010 : Nat := 327262901404751047802255

theorem tailTrace_717010 : CollatzResearch.WordTrace tailWord_717010 prefixEnd_717010 327262901404751047802255 := by
  unfold tailWord_717010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537875783100675100981121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17434335421601800269282989 6537875783100675100981121)
  ·
    refine ⟨4903406837325506325735841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6537875783100675100981121 4903406837325506325735841)
    ·
      refine ⟨3677555127994129744301881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903406837325506325735841 3677555127994129744301881)
      ·
        refine ⟨2758166345995597308226411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677555127994129744301881 2758166345995597308226411)
        ·
          refine ⟨4137249518993395962339617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758166345995597308226411 4137249518993395962339617)
          ·
            refine ⟨3102937139245046971754713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137249518993395962339617 3102937139245046971754713)
            ·
              refine ⟨2327202854433785228816035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102937139245046971754713 2327202854433785228816035)
              ·
                refine ⟨3490804281650677843224053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327202854433785228816035 3490804281650677843224053)
                ·
                  refine ⟨327262901404751047802255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3490804281650677843224053 327262901404751047802255)
                  ·
                    rfl

theorem cell20_717010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_717010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717010 prefixEnd_717010 := by exact prefixLift 717010
  have htrace : WordTrace (prefixWord ++ tailWord_717010) baseStart_717010 baseEnd_717010 := by
    simpa [prefixWord, tailWord_717010, baseEnd_717010] using wordTrace_append hprefix tailTrace_717010
  have hstable : (prefixWord ++ tailWord_717010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717010).length < 2 ^ (prefixWord ++ tailWord_717010).sum := by decide
  have hdescent : baseEnd_717010 < baseStart_717010 := by decide
  rcases family_descends (prefixWord ++ tailWord_717010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717013 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_717013 : Nat := 118140960795 + 717013 * 2 ^ 59
def prefixEnd_717013 : Nat := 4983230072969 + 3 ^ 40 * 717013 * 2
def baseEnd_717013 : Nat := 327264270686496370702243

theorem tailTrace_717013 : CollatzResearch.WordTrace tailWord_717013 prefixEnd_717013 327264270686496370702243 := by
  unfold tailWord_717013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151612551391831916283693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17434408367594554610855795 26151612551391831916283693)
  ·
    refine ⟨9806854706771936968606385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26151612551391831916283693 9806854706771936968606385)
    ·
      refine ⟨7355141030078952726454789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9806854706771936968606385 7355141030078952726454789)
      ·
        refine ⟨1379088943139803636210273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7355141030078952726454789 1379088943139803636210273)
        ·
          refine ⟨1034316707354852727157705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379088943139803636210273 1034316707354852727157705)
          ·
            refine ⟨775737530516139545368279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034316707354852727157705 775737530516139545368279)
            ·
              refine ⟨1163606295774209318052419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775737530516139545368279 1163606295774209318052419)
              ·
                refine ⟨1745409443661313977078629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163606295774209318052419 1745409443661313977078629)
                ·
                  refine ⟨327264270686496370702243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745409443661313977078629 327264270686496370702243)
                  ·
                    rfl

theorem cell20_717013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_717013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717013 prefixEnd_717013 := by exact prefixLift 717013
  have htrace : WordTrace (prefixWord ++ tailWord_717013) baseStart_717013 baseEnd_717013 := by
    simpa [prefixWord, tailWord_717013, baseEnd_717013] using wordTrace_append hprefix tailTrace_717013
  have hstable : (prefixWord ++ tailWord_717013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717013).length < 2 ^ (prefixWord ++ tailWord_717013).sum := by decide
  have hdescent : baseEnd_717013 < baseStart_717013 := by decide
  rcases family_descends (prefixWord ++ tailWord_717013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717017 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_717017 : Nat := 118140960795 + 717017 * 2 ^ 59
def prefixEnd_717017 : Nat := 4983230072969 + 3 ^ 40 * 717017 * 2
def baseEnd_717017 : Nat := 327266096395490134568893

theorem tailTrace_717017 : CollatzResearch.WordTrace tailWord_717017 prefixEnd_717017 327266096395490134568893 := by
  unfold tailWord_717017
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151758443377340599429305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17434505628918227066286203 26151758443377340599429305)
  ·
    refine ⟨19613818832533005449571979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26151758443377340599429305 19613818832533005449571979)
    ·
      refine ⟨29420728248799508174357969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19613818832533005449571979 29420728248799508174357969)
      ·
        refine ⟨22065546186599631130768477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29420728248799508174357969 22065546186599631130768477)
        ·
          refine ⟨8274579819974861674038179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22065546186599631130768477 8274579819974861674038179)
          ·
            refine ⟨12411869729962292511057269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274579819974861674038179 12411869729962292511057269)
            ·
              refine ⟨1163612787183964922911619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12411869729962292511057269 1163612787183964922911619)
              ·
                refine ⟨1745419180775947384367429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163612787183964922911619 1745419180775947384367429)
                ·
                  refine ⟨327266096395490134568893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745419180775947384367429 327266096395490134568893)
                  ·
                    rfl

theorem cell20_717017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_717017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717017 prefixEnd_717017 := by exact prefixLift 717017
  have htrace : WordTrace (prefixWord ++ tailWord_717017) baseStart_717017 baseEnd_717017 := by
    simpa [prefixWord, tailWord_717017, baseEnd_717017] using wordTrace_append hprefix tailTrace_717017
  have hstable : (prefixWord ++ tailWord_717017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717017).length < 2 ^ (prefixWord ++ tailWord_717017).sum := by decide
  have hdescent : baseEnd_717017 < baseStart_717017 := by decide
  rcases family_descends (prefixWord ++ tailWord_717017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717024 : List Nat := [2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_717024 : Nat := 118140960795 + 717024 * 2 ^ 59
def prefixEnd_717024 : Nat := 4983230072969 + 3 ^ 40 * 717024 * 2
def baseEnd_717024 : Nat := 109089763795409740445177

theorem tailTrace_717024 : CollatzResearch.WordTrace tailWord_717024 prefixEnd_717024 109089763795409740445177 := by
  unfold tailWord_717024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076006877175990397467063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17434675836234653863289417 13076006877175990397467063)
  ·
    refine ⟨19614010315763985596200595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13076006877175990397467063 19614010315763985596200595)
    ·
      refine ⟨29421015473645978394300893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19614010315763985596200595 29421015473645978394300893)
      ·
        refine ⟨11032880802617241897862835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29421015473645978394300893 11032880802617241897862835)
        ·
          refine ⟨16549321203925862846794253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032880802617241897862835 16549321203925862846794253)
          ·
            refine ⟨6205995451472198567547845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16549321203925862846794253 6205995451472198567547845)
            ·
              refine ⟨1163624147151037231415221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6205995451472198567547845 1163624147151037231415221)
              ·
                refine ⟨109089763795409740445177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1163624147151037231415221 109089763795409740445177)
                ·
                  rfl

theorem cell20_717024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_717024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717024 prefixEnd_717024 := by exact prefixLift 717024
  have htrace : WordTrace (prefixWord ++ tailWord_717024) baseStart_717024 baseEnd_717024 := by
    simpa [prefixWord, tailWord_717024, baseEnd_717024] using wordTrace_append hprefix tailTrace_717024
  have hstable : (prefixWord ++ tailWord_717024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717024).length < 2 ^ (prefixWord ++ tailWord_717024).sum := by decide
  have hdescent : baseEnd_717024 < baseStart_717024 := by decide
  rcases family_descends (prefixWord ++ tailWord_717024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717079 : List Nat := [1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_717079 : Nat := 118140960795 + 717079 * 2 ^ 59
def prefixEnd_717079 : Nat := 4983230072969 + 3 ^ 40 * 717079 * 2
def baseEnd_717079 : Nat := 109098131628297824833991

theorem tailTrace_717079 : CollatzResearch.WordTrace tailWord_717079 prefixEnd_717079 109098131628297824833991 := by
  unfold tailWord_717079
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154019769152725188186291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17436013179435150125457527 26154019769152725188186291)
  ·
    refine ⟨39231029653729087782279437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26154019769152725188186291 39231029653729087782279437)
    ·
      refine ⟨14711636120148407918354789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39231029653729087782279437 14711636120148407918354789)
      ·
        refine ⟨2758431772527826484691523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14711636120148407918354789 2758431772527826484691523)
        ·
          refine ⟨4137647658791739727037285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758431772527826484691523 4137647658791739727037285)
          ·
            refine ⟨775808936023451198819491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4137647658791739727037285 775808936023451198819491)
            ·
              refine ⟨1163713404035176798229237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775808936023451198819491 1163713404035176798229237)
              ·
                refine ⟨109098131628297824833991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1163713404035176798229237 109098131628297824833991)
                ·
                  rfl

theorem cell20_717079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_717079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717079 prefixEnd_717079 := by exact prefixLift 717079
  have htrace : WordTrace (prefixWord ++ tailWord_717079) baseStart_717079 baseEnd_717079 := by
    simpa [prefixWord, tailWord_717079, baseEnd_717079] using wordTrace_append hprefix tailTrace_717079
  have hstable : (prefixWord ++ tailWord_717079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717079).length < 2 ^ (prefixWord ++ tailWord_717079).sum := by decide
  have hdescent : baseEnd_717079 < baseStart_717079 := by decide
  rcases family_descends (prefixWord ++ tailWord_717079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717096 : List Nat := [2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_717096 : Nat := 118140960795 + 717096 * 2 ^ 59
def prefixEnd_717096 : Nat := 4983230072969 + 3 ^ 40 * 717096 * 2
def baseEnd_717096 : Nat := 109100718049372323645079

theorem tailTrace_717096 : CollatzResearch.WordTrace tailWord_717096 prefixEnd_717096 109100718049372323645079 := by
  unfold tailWord_717096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077319905045568545777571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17436426540060758061036761 13077319905045568545777571)
  ·
    refine ⟨19615979857568352818666357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13077319905045568545777571 19615979857568352818666357)
    ·
      refine ⟨1838998111647033076749971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19615979857568352818666357 1838998111647033076749971)
      ·
        refine ⟨2758497167470549615124957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838998111647033076749971 2758497167470549615124957)
        ·
          refine ⟨1034436437801456105671859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2758497167470549615124957 1034436437801456105671859)
          ·
            refine ⟨1551654656702184158507789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034436437801456105671859 1551654656702184158507789)
            ·
              refine ⟨581870496263319059440421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1551654656702184158507789 581870496263319059440421)
              ·
                refine ⟨109100718049372323645079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581870496263319059440421 109100718049372323645079)
                ·
                  rfl

theorem cell20_717096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_717096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717096 prefixEnd_717096 := by exact prefixLift 717096
  have htrace : WordTrace (prefixWord ++ tailWord_717096) baseStart_717096 baseEnd_717096 := by
    simpa [prefixWord, tailWord_717096, baseEnd_717096] using wordTrace_append hprefix tailTrace_717096
  have hstable : (prefixWord ++ tailWord_717096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717096).length < 2 ^ (prefixWord ++ tailWord_717096).sum := by decide
  have hdescent : baseEnd_717096 < baseStart_717096 := by decide
  rcases family_descends (prefixWord ++ tailWord_717096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717107 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_717107 : Nat := 118140960795 + 717107 * 2 ^ 59
def prefixEnd_717107 : Nat := 4983230072969 + 3 ^ 40 * 717107 * 2
def baseEnd_717107 : Nat := 327307174847849821568525

theorem tailTrace_717107 : CollatzResearch.WordTrace tailWord_717107 prefixEnd_717107 327307174847849821568525 := by
  unfold tailWord_717107
  simp only [CollatzResearch.WordTrace]
  refine ⟨26155041013051285970205575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17436694008700857313470383 26155041013051285970205575)
  ·
    refine ⟨39232561519576928955308363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26155041013051285970205575 39232561519576928955308363)
    ·
      refine ⟨58848842279365393432962545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39232561519576928955308363 58848842279365393432962545)
      ·
        refine ⟨44136631709524045074721909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58848842279365393432962545 44136631709524045074721909)
        ·
          refine ⟨4137809222767879225755179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44136631709524045074721909 4137809222767879225755179)
          ·
            refine ⟨6206713834151818838632769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137809222767879225755179 6206713834151818838632769)
            ·
              refine ⟨4655035375613864128974577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6206713834151818838632769 4655035375613864128974577)
              ·
                refine ⟨3491276531710398096730933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655035375613864128974577 3491276531710398096730933)
                ·
                  refine ⟨327307174847849821568525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491276531710398096730933 327307174847849821568525)
                  ·
                    rfl

theorem cell20_717107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_717107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717107 prefixEnd_717107 := by exact prefixLift 717107
  have htrace : WordTrace (prefixWord ++ tailWord_717107) baseStart_717107 baseEnd_717107 := by
    simpa [prefixWord, tailWord_717107, baseEnd_717107] using wordTrace_append hprefix tailTrace_717107
  have hstable : (prefixWord ++ tailWord_717107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717107).length < 2 ^ (prefixWord ++ tailWord_717107).sum := by decide
  have hdescent : baseEnd_717107 < baseStart_717107 := by decide
  rcases family_descends (prefixWord ++ tailWord_717107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717162 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_717162 : Nat := 118140960795 + 717162 * 2 ^ 59
def prefixEnd_717162 : Nat := 4983230072969 + 3 ^ 40 * 717162 * 2
def baseEnd_717162 : Nat := 327332278346514074734967

theorem tailTrace_717162 : CollatzResearch.WordTrace tailWord_717162 prefixEnd_717162 327332278346514074734967 := by
  unfold tailWord_717162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539261756963007590864435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17438031351901353575638493 6539261756963007590864435)
  ·
    refine ⟨9808892635444511386296653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6539261756963007590864435 9808892635444511386296653)
    ·
      refine ⟨3678334738291691769861245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9808892635444511386296653 3678334738291691769861245)
      ·
        refine ⟨1379375526859384413697967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3678334738291691769861245 1379375526859384413697967)
        ·
          refine ⟨2069063290289076620546951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379375526859384413697967 2069063290289076620546951)
          ·
            refine ⟨3103594935433614930820427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069063290289076620546951 3103594935433614930820427)
            ·
              refine ⟨4655392403150422396230641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103594935433614930820427 4655392403150422396230641)
              ·
                refine ⟨3491544302362816797172981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655392403150422396230641 3491544302362816797172981)
                ·
                  refine ⟨327332278346514074734967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491544302362816797172981 327332278346514074734967)
                  ·
                    rfl

theorem cell20_717162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_717162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717162 prefixEnd_717162 := by exact prefixLift 717162
  have htrace : WordTrace (prefixWord ++ tailWord_717162) baseStart_717162 baseEnd_717162 := by
    simpa [prefixWord, tailWord_717162, baseEnd_717162] using wordTrace_append hprefix tailTrace_717162
  have hstable : (prefixWord ++ tailWord_717162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717162).length < 2 ^ (prefixWord ++ tailWord_717162).sum := by decide
  have hdescent : baseEnd_717162 < baseStart_717162 := by decide
  rcases family_descends (prefixWord ++ tailWord_717162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717237 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 2]
def baseStart_717237 : Nat := 118140960795 + 717237 * 2 ^ 59
def prefixEnd_717237 : Nat := 4983230072969 + 3 ^ 40 * 717237 * 2
def baseEnd_717237 : Nat := 327366510390147147234661

theorem tailTrace_717237 : CollatzResearch.WordTrace tailWord_717237 prefixEnd_717237 327366510390147147234661 := by
  unfold tailWord_717237
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159782502580318172437965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17439855001720212114958643 26159782502580318172437965)
  ·
    refine ⟨9809918438467619314664237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26159782502580318172437965 9809918438467619314664237)
    ·
      refine ⟨3678719414425357242999089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9809918438467619314664237 3678719414425357242999089)
      ·
        refine ⟨2759039560819017932249317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678719414425357242999089 2759039560819017932249317)
        ·
          refine ⟨517319917653565862296747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2759039560819017932249317 517319917653565862296747)
          ·
            refine ⟨775979876480348793445121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517319917653565862296747 775979876480348793445121)
            ·
              refine ⟨581984907360261595083841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775979876480348793445121 581984907360261595083841)
              ·
                refine ⟨436488680520196196312881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581984907360261595083841 436488680520196196312881)
                ·
                  refine ⟨327366510390147147234661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436488680520196196312881 327366510390147147234661)
                  ·
                    rfl

theorem cell20_717237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_717237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717237 prefixEnd_717237 := by exact prefixLift 717237
  have htrace : WordTrace (prefixWord ++ tailWord_717237) baseStart_717237 baseEnd_717237 := by
    simpa [prefixWord, tailWord_717237, baseEnd_717237] using wordTrace_append hprefix tailTrace_717237
  have hstable : (prefixWord ++ tailWord_717237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717237).length < 2 ^ (prefixWord ++ tailWord_717237).sum := by decide
  have hdescent : baseEnd_717237 < baseStart_717237 := by decide
  rcases family_descends (prefixWord ++ tailWord_717237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717241 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 2]
def baseStart_717241 : Nat := 118140960795 + 717241 * 2 ^ 59
def prefixEnd_717241 : Nat := 4983230072969 + 3 ^ 40 * 717241 * 2
def baseEnd_717241 : Nat := 327368336099140911101311

theorem tailTrace_717241 : CollatzResearch.WordTrace tailWord_717241 prefixEnd_717241 327368336099140911101311 := by
  unfold tailWord_717241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159928394565826855583577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17439952263043884570389051 26159928394565826855583577)
  ·
    refine ⟨19619946295924370141687683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26159928394565826855583577 19619946295924370141687683)
    ·
      refine ⟨29429919443886555212531525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619946295924370141687683 29429919443886555212531525)
      ·
        refine ⟨5518109895728729102349661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29429919443886555212531525 5518109895728729102349661)
        ·
          refine ⟨2069291210898273413381123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5518109895728729102349661 2069291210898273413381123)
          ·
            refine ⟨3103936816347410120071685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069291210898273413381123 3103936816347410120071685)
            ·
              refine ⟨581988153065139397513441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3103936816347410120071685 581988153065139397513441)
              ·
                refine ⟨436491114798854548135081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581988153065139397513441 436491114798854548135081)
                ·
                  refine ⟨327368336099140911101311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436491114798854548135081 327368336099140911101311)
                  ·
                    rfl

theorem cell20_717241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_717241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717241 prefixEnd_717241 := by exact prefixLift 717241
  have htrace : WordTrace (prefixWord ++ tailWord_717241) baseStart_717241 baseEnd_717241 := by
    simpa [prefixWord, tailWord_717241, baseEnd_717241] using wordTrace_append hprefix tailTrace_717241
  have hstable : (prefixWord ++ tailWord_717241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717241).length < 2 ^ (prefixWord ++ tailWord_717241).sum := by decide
  have hdescent : baseEnd_717241 < baseStart_717241 := by decide
  rcases family_descends (prefixWord ++ tailWord_717241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717269 : List Nat := [1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_717269 : Nat := 118140960795 + 717269 * 2 ^ 59
def prefixEnd_717269 : Nat := 4983230072969 + 3 ^ 40 * 717269 * 2
def baseEnd_717269 : Nat := 109127038687365752722621

theorem tailTrace_717269 : CollatzResearch.WordTrace tailWord_717269 prefixEnd_717269 109127038687365752722621 := by
  unfold tailWord_717269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160949638464387637602861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17440633092309591758401907 26160949638464387637602861)
  ·
    refine ⟨9810356114424145364101073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26160949638464387637602861 9810356114424145364101073)
    ·
      refine ⟨7357767085818109023075805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9810356114424145364101073 7357767085818109023075805)
      ·
        refine ⟨2759162657181790883653427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7357767085818109023075805 2759162657181790883653427)
        ·
          refine ⟨4138743985772686325480141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759162657181790883653427 4138743985772686325480141)
          ·
            refine ⟨1552028994664757372055053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4138743985772686325480141 1552028994664757372055053)
            ·
              refine ⟨582010872999284014520645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552028994664757372055053 582010872999284014520645)
              ·
                refine ⟨109127038687365752722621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582010872999284014520645 109127038687365752722621)
                ·
                  rfl

theorem cell20_717269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_717269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717269 prefixEnd_717269 := by exact prefixLift 717269
  have htrace : WordTrace (prefixWord ++ tailWord_717269) baseStart_717269 baseEnd_717269 := by
    simpa [prefixWord, tailWord_717269, baseEnd_717269] using wordTrace_append hprefix tailTrace_717269
  have hstable : (prefixWord ++ tailWord_717269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717269).length < 2 ^ (prefixWord ++ tailWord_717269).sum := by decide
  have hdescent : baseEnd_717269 < baseStart_717269 := by decide
  rcases family_descends (prefixWord ++ tailWord_717269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717290 : List Nat := [3, 1, 3, 1, 3, 2, 7]
def baseStart_717290 : Nat := 118140960795 + 717290 * 2 ^ 59
def prefixEnd_717290 : Nat := 4983230072969 + 3 ^ 40 * 717290 * 2
def baseEnd_717290 : Nat := 36376744559368279829753

theorem tailTrace_717290 : CollatzResearch.WordTrace tailWord_717290 prefixEnd_717290 36376744559368279829753 := by
  unfold tailWord_717290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540428892847077056029331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17441143714258872149411549 6540428892847077056029331)
  ·
    refine ⟨9810643339270615584043997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540428892847077056029331 9810643339270615584043997)
    ·
      refine ⟨3678991252226480844016499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9810643339270615584043997 3678991252226480844016499)
      ·
        refine ⟨5518486878339721266024749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678991252226480844016499 5518486878339721266024749)
        ·
          refine ⟨2069432579377395474759281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5518486878339721266024749 2069432579377395474759281)
          ·
            refine ⟨1552074434533046606069461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069432579377395474759281 1552074434533046606069461)
            ·
              refine ⟨36376744559368279829753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1552074434533046606069461 36376744559368279829753)
              ·
                rfl

theorem cell20_717290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_717290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717290 prefixEnd_717290 := by exact prefixLift 717290
  have htrace : WordTrace (prefixWord ++ tailWord_717290) baseStart_717290 baseEnd_717290 := by
    simpa [prefixWord, tailWord_717290, baseEnd_717290] using wordTrace_append hprefix tailTrace_717290
  have hstable : (prefixWord ++ tailWord_717290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717290).length < 2 ^ (prefixWord ++ tailWord_717290).sum := by decide
  have hdescent : baseEnd_717290 < baseStart_717290 := by decide
  rcases family_descends (prefixWord ++ tailWord_717290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717293 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_717293 : Nat := 118140960795 + 717293 * 2 ^ 59
def prefixEnd_717293 : Nat := 4983230072969 + 3 ^ 40 * 717293 * 2
def baseEnd_717293 : Nat := 327392070316059841367765

theorem tailTrace_717293 : CollatzResearch.WordTrace tailWord_717293 prefixEnd_717293 327392070316059841367765 := by
  unfold tailWord_717293
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161824990377439736476533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17441216660251626490984355 26161824990377439736476533)
  ·
    refine ⟨2452671092847884975294675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26161824990377439736476533 2452671092847884975294675)
    ·
      refine ⟨3679006639271827462942013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452671092847884975294675 3679006639271827462942013)
      ·
        refine ⟨1379627489726935298603255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3679006639271827462942013 1379627489726935298603255)
        ·
          refine ⟨2069441234590402947904883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379627489726935298603255 2069441234590402947904883)
          ·
            refine ⟨3104161851885604421857325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069441234590402947904883 3104161851885604421857325)
            ·
              refine ⟨1164060694457101658196497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3104161851885604421857325 1164060694457101658196497)
              ·
                refine ⟨873045520842826243647373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164060694457101658196497 873045520842826243647373)
                ·
                  refine ⟨327392070316059841367765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873045520842826243647373 327392070316059841367765)
                  ·
                    rfl

theorem cell20_717293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_717293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717293 prefixEnd_717293 := by exact prefixLift 717293
  have htrace : WordTrace (prefixWord ++ tailWord_717293) baseStart_717293 baseEnd_717293 := by
    simpa [prefixWord, tailWord_717293, baseEnd_717293] using wordTrace_append hprefix tailTrace_717293
  have hstable : (prefixWord ++ tailWord_717293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717293).length < 2 ^ (prefixWord ++ tailWord_717293).sum := by decide
  have hdescent : baseEnd_717293 < baseStart_717293 := by decide
  rcases family_descends (prefixWord ++ tailWord_717293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717297 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_717297 : Nat := 118140960795 + 717297 * 2 ^ 59
def prefixEnd_717297 : Nat := 4983230072969 + 3 ^ 40 * 717297 * 2
def baseEnd_717297 : Nat := 327393896025053605234415

theorem tailTrace_717297 : CollatzResearch.WordTrace tailWord_717297 prefixEnd_717297 327393896025053605234415 := by
  unfold tailWord_717297
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161970882362948419622145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17441313921575298946414763 26161970882362948419622145)
  ·
    refine ⟨19621478161772211314716609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26161970882362948419622145 19621478161772211314716609)
    ·
      refine ⟨14716108621329158486037457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19621478161772211314716609 14716108621329158486037457)
      ·
        refine ⟨11037081465996868864528093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716108621329158486037457 11037081465996868864528093)
        ·
          refine ⟨4138905549748825824198035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11037081465996868864528093 4138905549748825824198035)
          ·
            refine ⟨6208358324623238736297053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138905549748825824198035 6208358324623238736297053)
            ·
              refine ⟨2328134371733714526111395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6208358324623238736297053 2328134371733714526111395)
              ·
                refine ⟨3492201557600571789167093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328134371733714526111395 3492201557600571789167093)
                ·
                  refine ⟨327393896025053605234415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3492201557600571789167093 327393896025053605234415)
                  ·
                    rfl

theorem cell20_717297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_717297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717297 prefixEnd_717297 := by exact prefixLift 717297
  have htrace : WordTrace (prefixWord ++ tailWord_717297) baseStart_717297 baseEnd_717297 := by
    simpa [prefixWord, tailWord_717297, baseEnd_717297] using wordTrace_append hprefix tailTrace_717297
  have hstable : (prefixWord ++ tailWord_717297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717297).length < 2 ^ (prefixWord ++ tailWord_717297).sum := by decide
  have hdescent : baseEnd_717297 < baseStart_717297 := by decide
  rcases family_descends (prefixWord ++ tailWord_717297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717311 : List Nat := [1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_717311 : Nat := 118140960795 + 717311 * 2 ^ 59
def prefixEnd_717311 : Nat := 4983230072969 + 3 ^ 40 * 717311 * 2
def baseEnd_717311 : Nat := 109133428668843926255897

theorem tailTrace_717311 : CollatzResearch.WordTrace tailWord_717311 prefixEnd_717311 109133428668843926255897 := by
  unfold tailWord_717311
  simp only [CollatzResearch.WordTrace]
  refine ⟨26162481504312228810631787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17441654336208152540421191 26162481504312228810631787)
  ·
    refine ⟨39243722256468343215947681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26162481504312228810631787 39243722256468343215947681)
    ·
      refine ⟨29432791692351257411960761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39243722256468343215947681 29432791692351257411960761)
      ·
        refine ⟨22074593769263443058970571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29432791692351257411960761 22074593769263443058970571)
        ·
          refine ⟨33111890653895164588455857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22074593769263443058970571 33111890653895164588455857)
          ·
            refine ⟨24833917990421373441341893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33111890653895164588455857 24833917990421373441341893)
            ·
              refine ⟨4656359623204007520251605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24833917990421373441341893 4656359623204007520251605)
              ·
                refine ⟨109133428668843926255897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4656359623204007520251605 109133428668843926255897)
                ·
                  rfl

theorem cell20_717311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_717311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717311 prefixEnd_717311 := by exact prefixLift 717311
  have htrace : WordTrace (prefixWord ++ tailWord_717311) baseStart_717311 baseEnd_717311 := by
    simpa [prefixWord, tailWord_717311, baseEnd_717311] using wordTrace_append hprefix tailTrace_717311
  have hstable : (prefixWord ++ tailWord_717311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717311).length < 2 ^ (prefixWord ++ tailWord_717311).sum := by decide
  have hdescent : baseEnd_717311 < baseStart_717311 := by decide
  rcases family_descends (prefixWord ++ tailWord_717311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717338 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_717338 : Nat := 118140960795 + 717338 * 2 ^ 59
def prefixEnd_717338 : Nat := 4983230072969 + 3 ^ 40 * 717338 * 2
def baseEnd_717338 : Nat := 327412609542239684867581

theorem tailTrace_717338 : CollatzResearch.WordTrace tailWord_717338 prefixEnd_717338 327412609542239684867581 := by
  unfold tailWord_717338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540866568803603105466167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17442310850142941614576445 6540866568803603105466167)
  ·
    refine ⟨9811299853205404658199251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540866568803603105466167 9811299853205404658199251)
    ·
      refine ⟨14716949779808106987298877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811299853205404658199251 14716949779808106987298877)
      ·
        refine ⟨5518856167428040120237079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14716949779808106987298877 5518856167428040120237079)
        ·
          refine ⟨8278284251142060180355619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518856167428040120237079 8278284251142060180355619)
          ·
            refine ⟨12417426376713090270533429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278284251142060180355619 12417426376713090270533429)
            ·
              refine ⟨1164133722816852212862509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12417426376713090270533429 1164133722816852212862509)
              ·
                refine ⟨436550146056319579823441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164133722816852212862509 436550146056319579823441)
                ·
                  refine ⟨327412609542239684867581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436550146056319579823441 327412609542239684867581)
                  ·
                    rfl

theorem cell20_717338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_717338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717338 prefixEnd_717338 := by exact prefixLift 717338
  have htrace : WordTrace (prefixWord ++ tailWord_717338) baseStart_717338 baseEnd_717338 := by
    simpa [prefixWord, tailWord_717338, baseEnd_717338] using wordTrace_append hprefix tailTrace_717338
  have hstable : (prefixWord ++ tailWord_717338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717338).length < 2 ^ (prefixWord ++ tailWord_717338).sum := by decide
  have hdescent : baseEnd_717338 < baseStart_717338 := by decide
  rcases family_descends (prefixWord ++ tailWord_717338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717349 : List Nat := [1, 3, 1, 2, 2, 1, 10]
def baseStart_717349 : Nat := 118140960795 + 717349 * 2 ^ 59
def prefixEnd_717349 : Nat := 4983230072969 + 3 ^ 40 * 717349 * 2
def baseEnd_717349 : Nat := 36379736693552503944541

theorem tailTrace_717349 : CollatzResearch.WordTrace tailWord_717349 prefixEnd_717349 36379736693552503944541 := by
  unfold tailWord_717349
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163867478174561300515101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17442578318783040867010067 26163867478174561300515101)
  ·
    refine ⟨9811450304315460487693163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26163867478174561300515101 9811450304315460487693163)
    ·
      refine ⟨14717175456473190731539745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811450304315460487693163 14717175456473190731539745)
      ·
        refine ⟨11037881592354893048654809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14717175456473190731539745 11037881592354893048654809)
        ·
          refine ⟨8278411194266169786491107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11037881592354893048654809 8278411194266169786491107)
          ·
            refine ⟨12417616791399254679736661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278411194266169786491107 12417616791399254679736661)
            ·
              refine ⟨36379736693552503944541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12417616791399254679736661 36379736693552503944541)
              ·
                rfl

theorem cell20_717349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_717349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717349 prefixEnd_717349 := by exact prefixLift 717349
  have htrace : WordTrace (prefixWord ++ tailWord_717349) baseStart_717349 baseEnd_717349 := by
    simpa [prefixWord, tailWord_717349, baseEnd_717349] using wordTrace_append hprefix tailTrace_717349
  have hstable : (prefixWord ++ tailWord_717349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717349).length < 2 ^ (prefixWord ++ tailWord_717349).sum := by decide
  have hdescent : baseEnd_717349 < baseStart_717349 := by decide
  rcases family_descends (prefixWord ++ tailWord_717349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717351 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 2]
def baseStart_717351 : Nat := 118140960795 + 717351 * 2 ^ 59
def prefixEnd_717351 : Nat := 4983230072969 + 3 ^ 40 * 717351 * 2
def baseEnd_717351 : Nat := 327418543096469417434195

theorem tailTrace_717351 : CollatzResearch.WordTrace tailWord_717351 prefixEnd_717351 327418543096469417434195 := by
  unfold tailWord_717351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163940424167315642087907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17442626949444877094725271 26163940424167315642087907)
  ·
    refine ⟨39245910636250973463131861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26163940424167315642087907 39245910636250973463131861)
    ·
      refine ⟨919826030537132190542153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39245910636250973463131861 919826030537132190542153)
      ·
        refine ⟨689869522902849142906615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919826030537132190542153 689869522902849142906615)
        ·
          refine ⟨1034804284354273714359923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689869522902849142906615 1034804284354273714359923)
          ·
            refine ⟨1552206426531410571539885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034804284354273714359923 1552206426531410571539885)
            ·
              refine ⟨582077409949278964327457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552206426531410571539885 582077409949278964327457)
              ·
                refine ⟨436558057461959223245593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582077409949278964327457 436558057461959223245593)
                ·
                  refine ⟨327418543096469417434195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436558057461959223245593 327418543096469417434195)
                  ·
                    rfl

theorem cell20_717351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2].length) (baseStart_717351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717351 prefixEnd_717351 := by exact prefixLift 717351
  have htrace : WordTrace (prefixWord ++ tailWord_717351) baseStart_717351 baseEnd_717351 := by
    simpa [prefixWord, tailWord_717351, baseEnd_717351] using wordTrace_append hprefix tailTrace_717351
  have hstable : (prefixWord ++ tailWord_717351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717351).length < 2 ^ (prefixWord ++ tailWord_717351).sum := by decide
  have hdescent : baseEnd_717351 < baseStart_717351 := by decide
  rcases family_descends (prefixWord ++ tailWord_717351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717352 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_717352 : Nat := 118140960795 + 717352 * 2 ^ 59
def prefixEnd_717352 : Nat := 4983230072969 + 3 ^ 40 * 717352 * 2
def baseEnd_717352 : Nat := 327418999523717858400857

theorem tailTrace_717352 : CollatzResearch.WordTrace tailWord_717352 prefixEnd_717352 327418999523717858400857 := by
  unfold tailWord_717352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081988448581846406437155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17442651264775795208582873 13081988448581846406437155)
  ·
    refine ⟨19622982672872769609655733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081988448581846406437155 19622982672872769609655733)
    ·
      refine ⟨1839654625581822150905225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19622982672872769609655733 1839654625581822150905225)
      ·
        refine ⟨1379740969186366613178919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839654625581822150905225 1379740969186366613178919)
        ·
          refine ⟨2069611453779549919768379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379740969186366613178919 2069611453779549919768379)
          ·
            refine ⟨3104417180669324879652569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069611453779549919768379 3104417180669324879652569)
            ·
              refine ⟨2328312885501993659739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104417180669324879652569 2328312885501993659739427)
              ·
                refine ⟨3492469328252990489609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328312885501993659739427 3492469328252990489609141)
                ·
                  refine ⟨327418999523717858400857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3492469328252990489609141 327418999523717858400857)
                  ·
                    rfl

theorem cell20_717352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_717352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717352 prefixEnd_717352 := by exact prefixLift 717352
  have htrace : WordTrace (prefixWord ++ tailWord_717352) baseStart_717352 baseEnd_717352 := by
    simpa [prefixWord, tailWord_717352, baseEnd_717352] using wordTrace_append hprefix tailTrace_717352
  have hstable : (prefixWord ++ tailWord_717352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717352).length < 2 ^ (prefixWord ++ tailWord_717352).sum := by decide
  have hdescent : baseEnd_717352 < baseStart_717352 := by decide
  rcases family_descends (prefixWord ++ tailWord_717352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717387 : List Nat := [1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_717387 : Nat := 118140960795 + 717387 * 2 ^ 59
def prefixEnd_717387 : Nat := 4983230072969 + 3 ^ 40 * 717387 * 2
def baseEnd_717387 : Nat := 109144991492471097411349

theorem tailTrace_717387 : CollatzResearch.WordTrace tailWord_717387 prefixEnd_717387 109144991492471097411349 := by
  unfold tailWord_717387
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165253452036893790398415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17443502301357929193598943 26165253452036893790398415)
  ·
    refine ⟨39247880178055340685597623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26165253452036893790398415 39247880178055340685597623)
    ·
      refine ⟨58871820267083011028396435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39247880178055340685597623 58871820267083011028396435)
      ·
        refine ⟨88307730400624516542594653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58871820267083011028396435 88307730400624516542594653)
        ·
          refine ⟨33115398900234193703472995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88307730400624516542594653 33115398900234193703472995)
          ·
            refine ⟨49673098350351290555209493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33115398900234193703472995 49673098350351290555209493)
            ·
              refine ⟨2328426485172716744775445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49673098350351290555209493 2328426485172716744775445)
              ·
                refine ⟨109144991492471097411349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2328426485172716744775445 109144991492471097411349)
                ·
                  rfl

theorem cell20_717387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_717387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717387 prefixEnd_717387 := by exact prefixLift 717387
  have htrace : WordTrace (prefixWord ++ tailWord_717387) baseStart_717387 baseEnd_717387 := by
    simpa [prefixWord, tailWord_717387, baseEnd_717387] using wordTrace_append hprefix tailTrace_717387
  have hstable : (prefixWord ++ tailWord_717387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717387).length < 2 ^ (prefixWord ++ tailWord_717387).sum := by decide
  have hdescent : baseEnd_717387 < baseStart_717387 := by decide
  rcases family_descends (prefixWord ++ tailWord_717387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717404 : List Nat := [2, 2, 4, 1, 3, 8]
def baseStart_717404 : Nat := 118140960795 + 717404 * 2 ^ 59
def prefixEnd_717404 : Nat := 4983230072969 + 3 ^ 40 * 717404 * 2
def baseEnd_717404 : Nat := 12127508657060621802493

theorem tailTrace_717404 : CollatzResearch.WordTrace tailWord_717404 prefixEnd_717404 12127508657060621802493 := by
  unfold tailWord_717404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082936746487652846883633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17443915661983537129178177 13082936746487652846883633)
  ·
    refine ⟨9812202559865739635162725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13082936746487652846883633 9812202559865739635162725)
    ·
      refine ⟨1839787979974826181593011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9812202559865739635162725 1839787979974826181593011)
      ·
        refine ⟨2759681969962239272389517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839787979974826181593011 2759681969962239272389517)
        ·
          refine ⟨1034880738735839727146069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2759681969962239272389517 1034880738735839727146069)
          ·
            refine ⟨12127508657060621802493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1034880738735839727146069 12127508657060621802493)
            ·
              rfl

theorem cell20_717404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 8].length) (baseStart_717404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717404 prefixEnd_717404 := by exact prefixLift 717404
  have htrace : WordTrace (prefixWord ++ tailWord_717404) baseStart_717404 baseEnd_717404 := by
    simpa [prefixWord, tailWord_717404, baseEnd_717404] using wordTrace_append hprefix tailTrace_717404
  have hstable : (prefixWord ++ tailWord_717404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717404).length < 2 ^ (prefixWord ++ tailWord_717404).sum := by decide
  have hdescent : baseEnd_717404 < baseStart_717404 := by decide
  rcases family_descends (prefixWord ++ tailWord_717404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717410 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_717410 : Nat := 118140960795 + 717410 * 2 ^ 59
def prefixEnd_717410 : Nat := 4983230072969 + 3 ^ 40 * 717410 * 2
def baseEnd_717410 : Nat := 327445472304127434467287

theorem tailTrace_717410 : CollatzResearch.WordTrace tailWord_717410 prefixEnd_717410 327445472304127434467287 := by
  unfold tailWord_717410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541523082738392179621421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17444061553969045812323789 6541523082738392179621421)
  ·
    refine ⟨2453071156026897067358033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6541523082738392179621421 2453071156026897067358033)
    ·
      refine ⟨1839803367020172800518525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2453071156026897067358033 1839803367020172800518525)
      ·
        refine ⟨689926262632564800194447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1839803367020172800518525 689926262632564800194447)
        ·
          refine ⟨1034889393948847200291671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689926262632564800194447 1034889393948847200291671)
          ·
            refine ⟨1552334090923270800437507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034889393948847200291671 1552334090923270800437507)
            ·
              refine ⟨2328501136384906200656261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552334090923270800437507 2328501136384906200656261)
              ·
                refine ⟨436593963072169912623049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2328501136384906200656261 436593963072169912623049)
                ·
                  refine ⟨327445472304127434467287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436593963072169912623049 327445472304127434467287)
                  ·
                    rfl

theorem cell20_717410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_717410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717410 prefixEnd_717410 := by exact prefixLift 717410
  have htrace : WordTrace (prefixWord ++ tailWord_717410) baseStart_717410 baseEnd_717410 := by
    simpa [prefixWord, tailWord_717410, baseEnd_717410] using wordTrace_append hprefix tailTrace_717410
  have hstable : (prefixWord ++ tailWord_717410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717410).length < 2 ^ (prefixWord ++ tailWord_717410).sum := by decide
  have hdescent : baseEnd_717410 < baseStart_717410 := by decide
  rcases family_descends (prefixWord ++ tailWord_717410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717421 : List Nat := [1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_717421 : Nat := 118140960795 + 717421 * 2 ^ 59
def prefixEnd_717421 : Nat := 4983230072969 + 3 ^ 40 * 717421 * 2
def baseEnd_717421 : Nat := 109150164334620095033525

theorem tailTrace_717421 : CollatzResearch.WordTrace tailWord_717421 prefixEnd_717421 109150164334620095033525 := by
  unfold tailWord_717421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26166493533913717597136117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17444329022609145064757411 26166493533913717597136117)
  ·
    refine ⟨2453108768804411024731511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26166493533913717597136117 2453108768804411024731511)
    ·
      refine ⟨3679663153206616537097267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453108768804411024731511 3679663153206616537097267)
      ·
        refine ⟨5519494729809924805645901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679663153206616537097267 5519494729809924805645901)
        ·
          refine ⟨2069810523678721802117213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5519494729809924805645901 2069810523678721802117213)
          ·
            refine ⟨776178946379520675793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2069810523678721802117213 776178946379520675793955)
            ·
              refine ⟨1164268419569281013690933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776178946379520675793955 1164268419569281013690933)
              ·
                refine ⟨109150164334620095033525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1164268419569281013690933 109150164334620095033525)
                ·
                  rfl

theorem cell20_717421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_717421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717421 prefixEnd_717421 := by exact prefixLift 717421
  have htrace : WordTrace (prefixWord ++ tailWord_717421) baseStart_717421 baseEnd_717421 := by
    simpa [prefixWord, tailWord_717421, baseEnd_717421] using wordTrace_append hprefix tailTrace_717421
  have hstable : (prefixWord ++ tailWord_717421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717421).length < 2 ^ (prefixWord ++ tailWord_717421).sum := by decide
  have hdescent : baseEnd_717421 < baseStart_717421 := by decide
  rcases family_descends (prefixWord ++ tailWord_717421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717463 : List Nat := [1, 1, 3, 3, 2, 1, 9]
def baseStart_717463 : Nat := 118140960795 + 717463 * 2 ^ 59
def prefixEnd_717463 : Nat := 4983230072969 + 3 ^ 40 * 717463 * 2
def baseEnd_717463 : Nat := 36385518105366089522267

theorem tailTrace_717463 : CollatzResearch.WordTrace tailWord_717463 prefixEnd_717463 36385518105366089522267 := by
  unfold tailWord_717463
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168025399761558770165043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17445350266507705846776695 26168025399761558770165043)
  ·
    refine ⟨39252038099642338155247565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26168025399761558770165043 39252038099642338155247565)
    ·
      refine ⟨14719514287365876808217837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39252038099642338155247565 14719514287365876808217837)
      ·
        refine ⟨5519817857762203803081689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14719514287365876808217837 5519817857762203803081689)
        ·
          refine ⟨4139863393321652852311267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519817857762203803081689 4139863393321652852311267)
          ·
            refine ⟨6209795089982479278466901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139863393321652852311267 6209795089982479278466901)
            ·
              refine ⟨36385518105366089522267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6209795089982479278466901 36385518105366089522267)
              ·
                rfl

theorem cell20_717463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_717463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717463 prefixEnd_717463 := by exact prefixLift 717463
  have htrace : WordTrace (prefixWord ++ tailWord_717463) baseStart_717463 baseEnd_717463 := by
    simpa [prefixWord, tailWord_717463, baseEnd_717463] using wordTrace_append hprefix tailTrace_717463
  have hstable : (prefixWord ++ tailWord_717463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717463).length < 2 ^ (prefixWord ++ tailWord_717463).sum := by decide
  have hdescent : baseEnd_717463 < baseStart_717463 := by decide
  rcases family_descends (prefixWord ++ tailWord_717463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717511 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 2]
def baseStart_717511 : Nat := 118140960795 + 717511 * 2 ^ 59
def prefixEnd_717511 : Nat := 4983230072969 + 3 ^ 40 * 717511 * 2
def baseEnd_717511 : Nat := 327491571456219972100207

theorem tailTrace_717511 : CollatzResearch.WordTrace tailWord_717511 prefixEnd_717511 327491571456219972100207 := by
  unfold tailWord_717511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169776103587662967912387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17446517402391775311941591 26169776103587662967912387)
  ·
    refine ⟨39254664155381494451868581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26169776103587662967912387 39254664155381494451868581)
    ·
      refine ⟨7360249529134030209725359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39254664155381494451868581 7360249529134030209725359)
      ·
        refine ⟨11040374293701045314588039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7360249529134030209725359 11040374293701045314588039)
        ·
          refine ⟨16560561440551567971882059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040374293701045314588039 16560561440551567971882059)
          ·
            refine ⟨24840842160827351957823089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16560561440551567971882059 24840842160827351957823089)
            ·
              refine ⟨18630631620620513968367317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24840842160827351957823089 18630631620620513968367317)
              ·
                refine ⟨436655428608293296133609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18630631620620513968367317 436655428608293296133609)
                ·
                  refine ⟨327491571456219972100207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436655428608293296133609 327491571456219972100207)
                  ·
                    rfl

theorem cell20_717511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2].length) (baseStart_717511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717511 prefixEnd_717511 := by exact prefixLift 717511
  have htrace : WordTrace (prefixWord ++ tailWord_717511) baseStart_717511 baseEnd_717511 := by
    simpa [prefixWord, tailWord_717511, baseEnd_717511] using wordTrace_append hprefix tailTrace_717511
  have hstable : (prefixWord ++ tailWord_717511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717511).length < 2 ^ (prefixWord ++ tailWord_717511).sum := by decide
  have hdescent : baseEnd_717511 < baseStart_717511 := by decide
  rcases family_descends (prefixWord ++ tailWord_717511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717518 : List Nat := [4, 1, 1, 1, 3, 4, 6]
def baseStart_717518 : Nat := 118140960795 + 717518 * 2 ^ 59
def prefixEnd_717518 : Nat := 4983230072969 + 3 ^ 40 * 717518 * 2
def baseEnd_717518 : Nat := 36388307382995450985205

theorem tailTrace_717518 : CollatzResearch.WordTrace tailWord_717518 prefixEnd_717518 36388307382995450985205 := by
  unfold tailWord_717518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3271253926820287895427151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17446687609708202108944805 3271253926820287895427151)
  ·
    refine ⟨4906880890230431843140727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3271253926820287895427151 4906880890230431843140727)
    ·
      refine ⟨7360321335345647764711091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4906880890230431843140727 7360321335345647764711091)
      ·
        refine ⟨11040482003018471647066637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7360321335345647764711091 11040482003018471647066637)
        ·
          refine ⟨4140180751131926867649989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11040482003018471647066637 4140180751131926867649989)
          ·
            refine ⟨776283890837236287684373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4140180751131926867649989 776283890837236287684373)
            ·
              refine ⟨36388307382995450985205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 776283890837236287684373 36388307382995450985205)
              ·
                rfl

theorem cell20_717518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_717518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717518 prefixEnd_717518 := by exact prefixLift 717518
  have htrace : WordTrace (prefixWord ++ tailWord_717518) baseStart_717518 baseEnd_717518 := by
    simpa [prefixWord, tailWord_717518, baseEnd_717518] using wordTrace_append hprefix tailTrace_717518
  have hstable : (prefixWord ++ tailWord_717518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717518).length < 2 ^ (prefixWord ++ tailWord_717518).sum := by decide
  have hdescent : baseEnd_717518 < baseStart_717518 := by decide
  rcases family_descends (prefixWord ++ tailWord_717518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717524 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_717524 : Nat := 118140960795 + 717524 * 2 ^ 59
def prefixEnd_717524 : Nat := 4983230072969 + 3 ^ 40 * 717524 * 2
def baseEnd_717524 : Nat := 327497505010449704666821

theorem tailTrace_717524 : CollatzResearch.WordTrace tailWord_717524 prefixEnd_717524 327497505010449704666821 := by
  unfold tailWord_717524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13085125126270283094067813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17446833501693710792090417 13085125126270283094067813)
  ·
    refine ⟨2453460961175678080137715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13085125126270283094067813 2453460961175678080137715)
    ·
      refine ⟨3680191441763517120206573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453460961175678080137715 3680191441763517120206573)
      ·
        refine ⟨1380071790661318920077465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3680191441763517120206573 1380071790661318920077465)
        ·
          refine ⟨1035053842995989190058099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380071790661318920077465 1035053842995989190058099)
          ·
            refine ⟨1552580764493983785087149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035053842995989190058099 1552580764493983785087149)
            ·
              refine ⟨582217786685243919407681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552580764493983785087149 582217786685243919407681)
              ·
                refine ⟨436663340013932939555761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582217786685243919407681 436663340013932939555761)
                ·
                  refine ⟨327497505010449704666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436663340013932939555761 327497505010449704666821)
                  ·
                    rfl

theorem cell20_717524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_717524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717524 prefixEnd_717524 := by exact prefixLift 717524
  have htrace : WordTrace (prefixWord ++ tailWord_717524) baseStart_717524 baseEnd_717524 := by
    simpa [prefixWord, tailWord_717524, baseEnd_717524] using wordTrace_append hprefix tailTrace_717524
  have hstable : (prefixWord ++ tailWord_717524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717524).length < 2 ^ (prefixWord ++ tailWord_717524).sum := by decide
  have hdescent : baseEnd_717524 < baseStart_717524 := by decide
  rcases family_descends (prefixWord ++ tailWord_717524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717587 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 2]
def baseStart_717587 : Nat := 118140960795 + 717587 * 2 ^ 59
def prefixEnd_717587 : Nat := 4983230072969 + 3 ^ 40 * 717587 * 2
def baseEnd_717587 : Nat := 327526259927101485566563

theorem tailTrace_717587 : CollatzResearch.WordTrace tailWord_717587 prefixEnd_717587 327526259927101485566563 := by
  unfold tailWord_717587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26172548051312327947679015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17448365367541551965119343 26172548051312327947679015)
  ·
    refine ⟨39258822076968491921518523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26172548051312327947679015 39258822076968491921518523)
    ·
      refine ⟨58888233115452737882277785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39258822076968491921518523 58888233115452737882277785)
      ·
        refine ⟨44166174836589553411708339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58888233115452737882277785 44166174836589553411708339)
        ·
          refine ⟨66249262254884330117562509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44166174836589553411708339 66249262254884330117562509)
          ·
            refine ⟨24843473345581623794085941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66249262254884330117562509 24843473345581623794085941)
            ·
              refine ⟨2329075626148277230695557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24843473345581623794085941 2329075626148277230695557)
              ·
                refine ⟨436701679902801980755417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2329075626148277230695557 436701679902801980755417)
                ·
                  refine ⟨327526259927101485566563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436701679902801980755417 327526259927101485566563)
                  ·
                    rfl

theorem cell20_717587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2].length) (baseStart_717587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717587 prefixEnd_717587 := by exact prefixLift 717587
  have htrace : WordTrace (prefixWord ++ tailWord_717587) baseStart_717587 baseEnd_717587 := by
    simpa [prefixWord, tailWord_717587, baseEnd_717587] using wordTrace_append hprefix tailTrace_717587
  have hstable : (prefixWord ++ tailWord_717587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717587).length < 2 ^ (prefixWord ++ tailWord_717587).sum := by decide
  have hdescent : baseEnd_717587 < baseStart_717587 := by decide
  rcases family_descends (prefixWord ++ tailWord_717587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717601 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_717601 : Nat := 118140960795 + 717601 * 2 ^ 59
def prefixEnd_717601 : Nat := 4983230072969 + 3 ^ 40 * 717601 * 2
def baseEnd_717601 : Nat := 327532649908579659099839

theorem tailTrace_717601 : CollatzResearch.WordTrace tailWord_717601 prefixEnd_717601 327532649908579659099839 := by
  unfold tailWord_717601
  simp only [CollatzResearch.WordTrace]
  refine ⟨26173058673261608338688657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17448705782174405559125771 26173058673261608338688657)
  ·
    refine ⟨19629794004946206254016493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26173058673261608338688657 19629794004946206254016493)
    ·
      refine ⟨7361172751854827345256185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19629794004946206254016493 7361172751854827345256185)
      ·
        refine ⟨5520879563891120508942139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361172751854827345256185 5520879563891120508942139)
        ·
          refine ⟨8281319345836680763413209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520879563891120508942139 8281319345836680763413209)
          ·
            refine ⟨6210989509377510572559907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8281319345836680763413209 6210989509377510572559907)
            ·
              refine ⟨9316484264066265858839861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210989509377510572559907 9316484264066265858839861)
              ·
                refine ⟨873420399756212424266237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9316484264066265858839861 873420399756212424266237)
                ·
                  refine ⟨327532649908579659099839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873420399756212424266237 327532649908579659099839)
                  ·
                    rfl

theorem cell20_717601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_717601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717601 prefixEnd_717601 := by exact prefixLift 717601
  have htrace : WordTrace (prefixWord ++ tailWord_717601) baseStart_717601 baseEnd_717601 := by
    simpa [prefixWord, tailWord_717601, baseEnd_717601] using wordTrace_append hprefix tailTrace_717601
  have hstable : (prefixWord ++ tailWord_717601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717601).length < 2 ^ (prefixWord ++ tailWord_717601).sum := by decide
  have hdescent : baseEnd_717601 < baseStart_717601 := by decide
  rcases family_descends (prefixWord ++ tailWord_717601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717653 : List Nat := [1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_717653 : Nat := 118140960795 + 717653 * 2 ^ 59
def prefixEnd_717653 : Nat := 4983230072969 + 3 ^ 40 * 717653 * 2
def baseEnd_717653 : Nat := 109185461375166196455431

theorem tailTrace_717653 : CollatzResearch.WordTrace tailWord_717653 prefixEnd_717653 109185461375166196455431 := by
  unfold tailWord_717653
  simp only [CollatzResearch.WordTrace]
  refine ⟨26174955269073221219581613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17449970179382147479721075 26174955269073221219581613)
  ·
    refine ⟨9815608225902457957343105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26174955269073221219581613 9815608225902457957343105)
    ·
      refine ⟨7361706169426843468007329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9815608225902457957343105 7361706169426843468007329)
      ·
        refine ⟨5521279627070132601005497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361706169426843468007329 5521279627070132601005497)
        ·
          refine ⟨4140959720302599450754123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5521279627070132601005497 4140959720302599450754123)
          ·
            refine ⟨6211439580453899176131185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140959720302599450754123 6211439580453899176131185)
            ·
              refine ⟨4658579685340424382098389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211439580453899176131185 4658579685340424382098389)
              ·
                refine ⟨109185461375166196455431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4658579685340424382098389 109185461375166196455431)
                ·
                  rfl

theorem cell20_717653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_717653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717653 prefixEnd_717653 := by exact prefixLift 717653
  have htrace : WordTrace (prefixWord ++ tailWord_717653) baseStart_717653 baseEnd_717653 := by
    simpa [prefixWord, tailWord_717653, baseEnd_717653] using wordTrace_append hprefix tailTrace_717653
  have hstable : (prefixWord ++ tailWord_717653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717653).length < 2 ^ (prefixWord ++ tailWord_717653).sum := by decide
  have hdescent : baseEnd_717653 < baseStart_717653 := by decide
  rcases family_descends (prefixWord ++ tailWord_717653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717666 : List Nat := [3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_717666 : Nat := 118140960795 + 717666 * 2 ^ 59
def prefixEnd_717666 : Nat := 4983230072969 + 3 ^ 40 * 717666 * 2
def baseEnd_717666 : Nat := 109187439226576107310969

theorem tailTrace_717666 : CollatzResearch.WordTrace tailWord_717666 prefixEnd_717666 109187439226576107310969 := by
  unfold tailWord_717666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6543857354506531109951213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17450286278684082959869901 6543857354506531109951213)
  ·
    refine ⟨2453946507939949166231705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6543857354506531109951213 2453946507939949166231705)
    ·
      refine ⟨1840459880954961874673779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2453946507939949166231705 1840459880954961874673779)
      ·
        refine ⟨2760689821432442812010669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840459880954961874673779 2760689821432442812010669)
        ·
          refine ⟨1035258683037166054504001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2760689821432442812010669 1035258683037166054504001)
          ·
            refine ⟨776444012277874540878001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035258683037166054504001 776444012277874540878001)
            ·
              refine ⟨582333009208405905658501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776444012277874540878001 582333009208405905658501)
              ·
                refine ⟨109187439226576107310969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582333009208405905658501 109187439226576107310969)
                ·
                  rfl

theorem cell20_717666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_717666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717666 prefixEnd_717666 := by exact prefixLift 717666
  have htrace : WordTrace (prefixWord ++ tailWord_717666) baseStart_717666 baseEnd_717666 := by
    simpa [prefixWord, tailWord_717666, baseEnd_717666] using wordTrace_append hprefix tailTrace_717666
  have hstable : (prefixWord ++ tailWord_717666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717666).length < 2 ^ (prefixWord ++ tailWord_717666).sum := by decide
  have hdescent : baseEnd_717666 < baseStart_717666 := by decide
  rcases family_descends (prefixWord ++ tailWord_717666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717701 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_717701 : Nat := 118140960795 + 717701 * 2 ^ 59
def prefixEnd_717701 : Nat := 4983230072969 + 3 ^ 40 * 717701 * 2
def baseEnd_717701 : Nat := 327578292633423755766097

theorem tailTrace_717701 : CollatzResearch.WordTrace tailWord_717701 prefixEnd_717701 327578292633423755766097 := by
  unfold tailWord_717701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176705972899325417328957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17451137315266216944885971 26176705972899325417328957)
  ·
    refine ⟨9816264739837247031498359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26176705972899325417328957 9816264739837247031498359)
    ·
      refine ⟨14724397109755870547247539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816264739837247031498359 14724397109755870547247539)
      ·
        refine ⟨22086595664633805820871309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14724397109755870547247539 22086595664633805820871309)
        ·
          refine ⟨8282473374237677182826741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22086595664633805820871309 8282473374237677182826741)
          ·
            refine ⟨776481878834782235890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8282473374237677182826741 776481878834782235890007)
            ·
              refine ⟨1164722818252173353835011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776481878834782235890007 1164722818252173353835011)
              ·
                refine ⟨1747084227378260030752517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164722818252173353835011 1747084227378260030752517)
                ·
                  refine ⟨327578292633423755766097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747084227378260030752517 327578292633423755766097)
                  ·
                    rfl

theorem cell20_717701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_717701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717701 prefixEnd_717701 := by exact prefixLift 717701
  have htrace : WordTrace (prefixWord ++ tailWord_717701) baseStart_717701 baseEnd_717701 := by
    simpa [prefixWord, tailWord_717701, baseEnd_717701] using wordTrace_append hprefix tailTrace_717701
  have hstable : (prefixWord ++ tailWord_717701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717701).length < 2 ^ (prefixWord ++ tailWord_717701).sum := by decide
  have hdescent : baseEnd_717701 < baseStart_717701 := by decide
  rcases family_descends (prefixWord ++ tailWord_717701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717743 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_717743 : Nat := 118140960795 + 717743 * 2 ^ 59
def prefixEnd_717743 : Nat := 4983230072969 + 3 ^ 40 * 717743 * 2
def baseEnd_717743 : Nat := 327597462577858276365925

theorem tailTrace_717743 : CollatzResearch.WordTrace tailWord_717743 prefixEnd_717743 327597462577858276365925 := by
  unfold tailWord_717743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26178237838747166590357883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17452158559164777726905255 26178237838747166590357883)
  ·
    refine ⟨39267356758120749885536825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26178237838747166590357883 39267356758120749885536825)
    ·
      refine ⟨29450517568590562414152619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39267356758120749885536825 29450517568590562414152619)
      ·
        refine ⟨44175776352885843621228929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29450517568590562414152619 44175776352885843621228929)
        ·
          refine ⟨33131832264664382715921697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44175776352885843621228929 33131832264664382715921697)
          ·
            refine ⟨24848874198498287036941273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33131832264664382715921697 24848874198498287036941273)
            ·
              refine ⟨18636655648873715277705955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24848874198498287036941273 18636655648873715277705955)
              ·
                refine ⟨27954983473310572916558933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636655648873715277705955 27954983473310572916558933)
                ·
                  refine ⟨327597462577858276365925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27954983473310572916558933 327597462577858276365925)
                  ·
                    rfl

theorem cell20_717743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_717743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717743 prefixEnd_717743 := by exact prefixLift 717743
  have htrace : WordTrace (prefixWord ++ tailWord_717743) baseStart_717743 baseEnd_717743 := by
    simpa [prefixWord, tailWord_717743, baseEnd_717743] using wordTrace_append hprefix tailTrace_717743
  have hstable : (prefixWord ++ tailWord_717743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717743).length < 2 ^ (prefixWord ++ tailWord_717743).sum := by decide
  have hdescent : baseEnd_717743 < baseStart_717743 := by decide
  rcases family_descends (prefixWord ++ tailWord_717743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717753 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_717753 : Nat := 118140960795 + 717753 * 2 ^ 59
def prefixEnd_717753 : Nat := 4983230072969 + 3 ^ 40 * 717753 * 2
def baseEnd_717753 : Nat := 327602026850342686032551

theorem tailTrace_717753 : CollatzResearch.WordTrace tailWord_717753 prefixEnd_717753 327602026850342686032551 := by
  unfold tailWord_717753
  simp only [CollatzResearch.WordTrace]
  refine ⟨26178602568710938298221913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17452401712473958865481275 26178602568710938298221913)
  ·
    refine ⟨19633951926533203723666435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26178602568710938298221913 19633951926533203723666435)
    ·
      refine ⟨29450927889799805585499653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19633951926533203723666435 29450927889799805585499653)
      ·
        refine ⟨5522048979337463547281185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29450927889799805585499653 5522048979337463547281185)
        ·
          refine ⟨4141536734503097660460889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522048979337463547281185 4141536734503097660460889)
          ·
            refine ⟨3106152550877323245345667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141536734503097660460889 3106152550877323245345667)
            ·
              refine ⟨4659228826315984868018501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106152550877323245345667 4659228826315984868018501)
              ·
                refine ⟨873605404934247162753469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4659228826315984868018501 873605404934247162753469)
                ·
                  refine ⟨327602026850342686032551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873605404934247162753469 327602026850342686032551)
                  ·
                    rfl

theorem cell20_717753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_717753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717753 prefixEnd_717753 := by exact prefixLift 717753
  have htrace : WordTrace (prefixWord ++ tailWord_717753) baseStart_717753 baseEnd_717753 := by
    simpa [prefixWord, tailWord_717753, baseEnd_717753] using wordTrace_append hprefix tailTrace_717753
  have hstable : (prefixWord ++ tailWord_717753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717753).length < 2 ^ (prefixWord ++ tailWord_717753).sum := by decide
  have hdescent : baseEnd_717753 < baseStart_717753 := by decide
  rcases family_descends (prefixWord ++ tailWord_717753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717767 : List Nat := [1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_717767 : Nat := 118140960795 + 717767 * 2 ^ 59
def prefixEnd_717767 : Nat := 4983230072969 + 3 ^ 40 * 717767 * 2
def baseEnd_717767 : Nat := 109202805610606953188609

theorem tailTrace_717767 : CollatzResearch.WordTrace tailWord_717767 prefixEnd_717767 109202805610606953188609 := by
  unfold tailWord_717767
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179113190660218689231555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17452742127106812459487703 26179113190660218689231555)
  ·
    refine ⟨39268669785990328033847333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26179113190660218689231555 39268669785990328033847333)
    ·
      refine ⟨7362875584873186506346375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39268669785990328033847333 7362875584873186506346375)
      ·
        refine ⟨11044313377309779759519563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7362875584873186506346375 11044313377309779759519563)
        ·
          refine ⟨16566470065964669639279345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11044313377309779759519563 16566470065964669639279345)
          ·
            refine ⟨12424852549473502229459509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16566470065964669639279345 12424852549473502229459509)
            ·
              refine ⟨1164829926513140834011829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12424852549473502229459509 1164829926513140834011829)
              ·
                refine ⟨109202805610606953188609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1164829926513140834011829 109202805610606953188609)
                ·
                  rfl

theorem cell20_717767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_717767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717767 prefixEnd_717767 := by exact prefixLift 717767
  have htrace : WordTrace (prefixWord ++ tailWord_717767) baseStart_717767 baseEnd_717767 := by
    simpa [prefixWord, tailWord_717767, baseEnd_717767] using wordTrace_append hprefix tailTrace_717767
  have hstable : (prefixWord ++ tailWord_717767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717767).length < 2 ^ (prefixWord ++ tailWord_717767).sum := by decide
  have hdescent : baseEnd_717767 < baseStart_717767 := by decide
  rcases family_descends (prefixWord ++ tailWord_717767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717784 : List Nat := [2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_717784 : Nat := 118140960795 + 717784 * 2 ^ 59
def prefixEnd_717784 : Nat := 4983230072969 + 3 ^ 40 * 717784 * 2
def baseEnd_717784 : Nat := 109205392031681451999697

theorem tailTrace_717784 : CollatzResearch.WordTrace tailWord_717784 prefixEnd_717784 109205392031681451999697 := by
  unfold tailWord_717784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089866615799315296300203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17453155487732420395066937 13089866615799315296300203)
  ·
    refine ⟨19634799923698972944450305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13089866615799315296300203 19634799923698972944450305)
    ·
      refine ⟨14726099942774229708337729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19634799923698972944450305 14726099942774229708337729)
      ·
        refine ⟨11044574957080672281253297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14726099942774229708337729 11044574957080672281253297)
        ·
          refine ⟨8283431217810504210939973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11044574957080672281253297 8283431217810504210939973)
          ·
            refine ⟨1553143353339469539551245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8283431217810504210939973 1553143353339469539551245)
            ·
              refine ⟨582428757502301077331717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1553143353339469539551245 582428757502301077331717)
              ·
                refine ⟨109205392031681451999697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582428757502301077331717 109205392031681451999697)
                ·
                  rfl

theorem cell20_717784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_717784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717784 prefixEnd_717784 := by exact prefixLift 717784
  have htrace : WordTrace (prefixWord ++ tailWord_717784) baseStart_717784 baseEnd_717784 := by
    simpa [prefixWord, tailWord_717784, baseEnd_717784] using wordTrace_append hprefix tailTrace_717784
  have hstable : (prefixWord ++ tailWord_717784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717784).length < 2 ^ (prefixWord ++ tailWord_717784).sum := by decide
  have hdescent : baseEnd_717784 < baseStart_717784 := by decide
  rcases family_descends (prefixWord ++ tailWord_717784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717836 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_717836 : Nat := 118140960795 + 717836 * 2 ^ 59
def prefixEnd_717836 : Nat := 4983230072969 + 3 ^ 40 * 717836 * 2
def baseEnd_717836 : Nat := 327639910311963286265545

theorem tailTrace_717836 : CollatzResearch.WordTrace tailWord_717836 prefixEnd_717836 327639910311963286265545 := by
  unfold tailWord_717836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090814913705121736746681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17454419884940162315662241 13090814913705121736746681)
  ·
    refine ⟨9818111185278841302560011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13090814913705121736746681 9818111185278841302560011)
    ·
      refine ⟨14727166777918261953840017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9818111185278841302560011 14727166777918261953840017)
      ·
        refine ⟨11045375083438696465380013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14727166777918261953840017 11045375083438696465380013)
        ·
          refine ⟨4142015656289511174517505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11045375083438696465380013 4142015656289511174517505)
          ·
            refine ⟨3106511742217133380888129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142015656289511174517505 3106511742217133380888129)
            ·
              refine ⟨2329883806662850035666097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106511742217133380888129 2329883806662850035666097)
              ·
                refine ⟨1747412854997137526749573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329883806662850035666097 1747412854997137526749573)
                ·
                  refine ⟨327639910311963286265545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747412854997137526749573 327639910311963286265545)
                  ·
                    rfl

theorem cell20_717836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_717836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717836 prefixEnd_717836 := by exact prefixLift 717836
  have htrace : WordTrace (prefixWord ++ tailWord_717836) baseStart_717836 baseEnd_717836 := by
    simpa [prefixWord, tailWord_717836, baseEnd_717836] using wordTrace_append hprefix tailTrace_717836
  have hstable : (prefixWord ++ tailWord_717836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717836).length < 2 ^ (prefixWord ++ tailWord_717836).sum := by decide
  have hdescent : baseEnd_717836 < baseStart_717836 := by decide
  rcases family_descends (prefixWord ++ tailWord_717836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717850 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_717850 : Nat := 118140960795 + 717850 * 2 ^ 59
def prefixEnd_717850 : Nat := 4983230072969 + 3 ^ 40 * 717850 * 2
def baseEnd_717850 : Nat := 327646300293441459798821

theorem tailTrace_717850 : CollatzResearch.WordTrace tailWord_717850 prefixEnd_717850 327646300293441459798821 := by
  unfold tailWord_717850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545535112339880966125751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17454760299573015909668669 6545535112339880966125751)
  ·
    refine ⟨9818302668509821449188627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6545535112339880966125751 9818302668509821449188627)
    ·
      refine ⟨14727454002764732173782941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9818302668509821449188627 14727454002764732173782941)
      ·
        refine ⟨5522795251036774565168603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14727454002764732173782941 5522795251036774565168603)
        ·
          refine ⟨8284192876555161847752905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5522795251036774565168603 8284192876555161847752905)
          ·
            refine ⟨6213144657416371385814679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8284192876555161847752905 6213144657416371385814679)
            ·
              refine ⟨9319716986124557078722019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213144657416371385814679 9319716986124557078722019)
              ·
                refine ⟨13979575479186835618083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319716986124557078722019 13979575479186835618083029)
                ·
                  refine ⟨327646300293441459798821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13979575479186835618083029 327646300293441459798821)
                  ·
                    rfl

theorem cell20_717850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_717850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717850 prefixEnd_717850 := by exact prefixLift 717850
  have htrace : WordTrace (prefixWord ++ tailWord_717850) baseStart_717850 baseEnd_717850 := by
    simpa [prefixWord, tailWord_717850, baseEnd_717850] using wordTrace_append hprefix tailTrace_717850
  have hstable : (prefixWord ++ tailWord_717850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717850).length < 2 ^ (prefixWord ++ tailWord_717850).sum := by decide
  have hdescent : baseEnd_717850 < baseStart_717850 := by decide
  rcases family_descends (prefixWord ++ tailWord_717850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717860 : List Nat := [2, 3, 1, 4, 1, 3, 6]
def baseStart_717860 : Nat := 118140960795 + 717860 * 2 ^ 59
def prefixEnd_717860 : Nat := 4983230072969 + 3 ^ 40 * 717860 * 2
def baseEnd_717860 : Nat := 36405651618436207718383

theorem tailTrace_717860 : CollatzResearch.WordTrace tailWord_717860 prefixEnd_717860 36405651618436207718383 := by
  unfold tailWord_717860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091252589661647786183517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17455003452882197048244689 13091252589661647786183517)
  ·
    refine ⟨4909219721123117919818819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13091252589661647786183517 4909219721123117919818819)
    ·
      refine ⟨7363829581684676879728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909219721123117919818819 7363829581684676879728229)
      ·
        refine ⟨1380718046565876914949043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7363829581684676879728229 1380718046565876914949043)
        ·
          refine ⟨2071077069848815372423565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380718046565876914949043 2071077069848815372423565)
          ·
            refine ⟨776653901193305764658837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2071077069848815372423565 776653901193305764658837)
            ·
              refine ⟨36405651618436207718383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 776653901193305764658837 36405651618436207718383)
              ·
                rfl

theorem cell20_717860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_717860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717860 prefixEnd_717860 := by exact prefixLift 717860
  have htrace : WordTrace (prefixWord ++ tailWord_717860) baseStart_717860 baseEnd_717860 := by
    simpa [prefixWord, tailWord_717860, baseEnd_717860] using wordTrace_append hprefix tailTrace_717860
  have hstable : (prefixWord ++ tailWord_717860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717860).length < 2 ^ (prefixWord ++ tailWord_717860).sum := by decide
  have hdescent : baseEnd_717860 < baseStart_717860 := by decide
  rcases family_descends (prefixWord ++ tailWord_717860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717881 : List Nat := [1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_717881 : Nat := 118140960795 + 717881 * 2 ^ 59
def prefixEnd_717881 : Nat := 4983230072969 + 3 ^ 40 * 717881 * 2
def baseEnd_717881 : Nat := 109220149846047709921787

theorem tailTrace_717881 : CollatzResearch.WordTrace tailWord_717881 prefixEnd_717881 109220149846047709921787 := by
  unfold tailWord_717881
  simp only [CollatzResearch.WordTrace]
  refine ⟨26183271112247216158881497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17455514074831477439254331 26183271112247216158881497)
  ·
    refine ⟨19637453334185412119161123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26183271112247216158881497 19637453334185412119161123)
    ·
      refine ⟨29456180001278118178741685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19637453334185412119161123 29456180001278118178741685)
      ·
        refine ⟨2761516875119823579257033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29456180001278118178741685 2761516875119823579257033)
        ·
          refine ⟨2071137656339867684442775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761516875119823579257033 2071137656339867684442775)
          ·
            refine ⟨3106706484509801526664163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071137656339867684442775 3106706484509801526664163)
            ·
              refine ⟨4660059726764702289996245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106706484509801526664163 4660059726764702289996245)
              ·
                refine ⟨109220149846047709921787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4660059726764702289996245 109220149846047709921787)
                ·
                  rfl

theorem cell20_717881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_717881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717881 prefixEnd_717881 := by exact prefixLift 717881
  have htrace : WordTrace (prefixWord ++ tailWord_717881) baseStart_717881 baseEnd_717881 := by
    simpa [prefixWord, tailWord_717881, baseEnd_717881] using wordTrace_append hprefix tailTrace_717881
  have hstable : (prefixWord ++ tailWord_717881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717881).length < 2 ^ (prefixWord ++ tailWord_717881).sum := by decide
  have hdescent : baseEnd_717881 < baseStart_717881 := by decide
  rcases family_descends (prefixWord ++ tailWord_717881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717884 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_717884 : Nat := 118140960795 + 717884 * 2 ^ 59
def prefixEnd_717884 : Nat := 4983230072969 + 3 ^ 40 * 717884 * 2
def baseEnd_717884 : Nat := 327661818819888452665349

theorem tailTrace_717884 : CollatzResearch.WordTrace tailWord_717884 prefixEnd_717884 327661818819888452665349 := by
  unfold tailWord_717884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091690265618173835620353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17455587020824231780827137 13091690265618173835620353)
  ·
    refine ⟨9818767699213630376715265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13091690265618173835620353 9818767699213630376715265)
    ·
      refine ⟨7364075774410222782536449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9818767699213630376715265 7364075774410222782536449)
      ·
        refine ⟨5523056830807667086902337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7364075774410222782536449 5523056830807667086902337)
        ·
          refine ⟨4142292623105750315176753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523056830807667086902337 4142292623105750315176753)
          ·
            refine ⟨3106719467329312736382565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142292623105750315176753 3106719467329312736382565)
            ·
              refine ⟨582509900124246138071731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3106719467329312736382565 582509900124246138071731)
              ·
                refine ⟨873764850186369207107597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582509900124246138071731 873764850186369207107597)
                ·
                  refine ⟨327661818819888452665349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873764850186369207107597 327661818819888452665349)
                  ·
                    rfl

theorem cell20_717884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_717884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717884 prefixEnd_717884 := by exact prefixLift 717884
  have htrace : WordTrace (prefixWord ++ tailWord_717884) baseStart_717884 baseEnd_717884 := by
    simpa [prefixWord, tailWord_717884, baseEnd_717884] using wordTrace_append hprefix tailTrace_717884
  have hstable : (prefixWord ++ tailWord_717884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717884).length < 2 ^ (prefixWord ++ tailWord_717884).sum := by decide
  have hdescent : baseEnd_717884 < baseStart_717884 := by decide
  rcases family_descends (prefixWord ++ tailWord_717884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717918 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_717918 : Nat := 118140960795 + 717918 * 2 ^ 59
def prefixEnd_717918 : Nat := 4983230072969 + 3 ^ 40 * 717918 * 2
def baseEnd_717918 : Nat := 327677337346335445531877

theorem tailTrace_717918 : CollatzResearch.WordTrace tailWord_717918 prefixEnd_717918 327677337346335445531877 := by
  unfold tailWord_717918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273077576639146434747301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17456413742075447651985605 3273077576639146434747301)
  ·
    refine ⟨613702045619839956515119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3273077576639146434747301 613702045619839956515119)
    ·
      refine ⟨920553068429759934772679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613702045619839956515119 920553068429759934772679)
      ·
        refine ⟨1380829602644639902159019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920553068429759934772679 1380829602644639902159019)
        ·
          refine ⟨2071244403966959853238529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380829602644639902159019 2071244403966959853238529)
          ·
            refine ⟨1553433302975219889928897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071244403966959853238529 1553433302975219889928897)
            ·
              refine ⟨1165074977231414917446673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553433302975219889928897 1165074977231414917446673)
              ·
                refine ⟨873806232923561188085005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165074977231414917446673 873806232923561188085005)
                ·
                  refine ⟨327677337346335445531877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873806232923561188085005 327677337346335445531877)
                  ·
                    rfl

theorem cell20_717918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_717918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717918 prefixEnd_717918 := by exact prefixLift 717918
  have htrace : WordTrace (prefixWord ++ tailWord_717918) baseStart_717918 baseEnd_717918 := by
    simpa [prefixWord, tailWord_717918, baseEnd_717918] using wordTrace_append hprefix tailTrace_717918
  have hstable : (prefixWord ++ tailWord_717918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717918).length < 2 ^ (prefixWord ++ tailWord_717918).sum := by decide
  have hdescent : baseEnd_717918 < baseStart_717918 := by decide
  rcases family_descends (prefixWord ++ tailWord_717918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717922 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_717922 : Nat := 118140960795 + 717922 * 2 ^ 59
def prefixEnd_717922 : Nat := 4983230072969 + 3 ^ 40 * 717922 * 2
def baseEnd_717922 : Nat := 327679163055329209398527

theorem tailTrace_717922 : CollatzResearch.WordTrace tailWord_717922 prefixEnd_717922 327679163055329209398527 := by
  unfold tailWord_717922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546191626274670040281005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17456511003399120107416013 6546191626274670040281005)
  ·
    refine ⟨2454821859853001265105377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6546191626274670040281005 2454821859853001265105377)
    ·
      refine ⟨1841116394889750948829033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2454821859853001265105377 1841116394889750948829033)
      ·
        refine ⟨1380837296167313211621775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841116394889750948829033 1380837296167313211621775)
        ·
          refine ⟨2071255944250969817432663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380837296167313211621775 2071255944250969817432663)
          ·
            refine ⟨3106883916376454726148995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071255944250969817432663 3106883916376454726148995)
            ·
              refine ⟨4660325874564682089223493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106883916376454726148995 4660325874564682089223493)
              ·
                refine ⟨873811101480877891729405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4660325874564682089223493 873811101480877891729405)
                ·
                  refine ⟨327679163055329209398527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873811101480877891729405 327679163055329209398527)
                  ·
                    rfl

theorem cell20_717922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_717922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717922 prefixEnd_717922 := by exact prefixLift 717922
  have htrace : WordTrace (prefixWord ++ tailWord_717922) baseStart_717922 baseEnd_717922 := by
    simpa [prefixWord, tailWord_717922, baseEnd_717922] using wordTrace_append hprefix tailTrace_717922
  have hstable : (prefixWord ++ tailWord_717922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717922).length < 2 ^ (prefixWord ++ tailWord_717922).sum := by decide
  have hdescent : baseEnd_717922 < baseStart_717922 := by decide
  rcases family_descends (prefixWord ++ tailWord_717922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717929 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 2]
def baseStart_717929 : Nat := 118140960795 + 717929 * 2 ^ 59
def prefixEnd_717929 : Nat := 4983230072969 + 3 ^ 40 * 717929 * 2
def baseEnd_717929 : Nat := 327682358046068296165165

theorem tailTrace_717929 : CollatzResearch.WordTrace tailWord_717929 prefixEnd_717929 327682358046068296165165 := by
  unfold tailWord_717929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26185021816073320356628841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17456681210715546904419227 26185021816073320356628841)
  ·
    refine ⟨19638766362054990267471631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26185021816073320356628841 19638766362054990267471631)
    ·
      refine ⟨29458149543082485401207447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19638766362054990267471631 29458149543082485401207447)
      ·
        refine ⟨44187224314623728101811171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29458149543082485401207447 44187224314623728101811171)
        ·
          refine ⟨66280836471935592152716757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44187224314623728101811171 66280836471935592152716757)
          ·
            refine ⟨1553457104810990441079299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66280836471935592152716757 1553457104810990441079299)
            ·
              refine ⟨2330185657216485661618949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553457104810990441079299 2330185657216485661618949)
              ·
                refine ⟨436909810728091061553553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2330185657216485661618949 436909810728091061553553)
                ·
                  refine ⟨327682358046068296165165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436909810728091061553553 327682358046068296165165)
                  ·
                    rfl

theorem cell20_717929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_717929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717929 prefixEnd_717929 := by exact prefixLift 717929
  have htrace : WordTrace (prefixWord ++ tailWord_717929) baseStart_717929 baseEnd_717929 := by
    simpa [prefixWord, tailWord_717929, baseEnd_717929] using wordTrace_append hprefix tailTrace_717929
  have hstable : (prefixWord ++ tailWord_717929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717929).length < 2 ^ (prefixWord ++ tailWord_717929).sum := by decide
  have hdescent : baseEnd_717929 < baseStart_717929 := by decide
  rcases family_descends (prefixWord ++ tailWord_717929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717988 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_717988 : Nat := 118140960795 + 717988 * 2 ^ 59
def prefixEnd_717988 : Nat := 4983230072969 + 3 ^ 40 * 717988 * 2
def baseEnd_717988 : Nat := 327709287253726313198257

theorem tailTrace_717988 : CollatzResearch.WordTrace tailWord_717988 prefixEnd_717988 327709287253726313198257 := by
  unfold tailWord_717988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093586861429786716513309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17458115815239715622017745 13093586861429786716513309)
  ·
    refine ⟨4910095073036170018692491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13093586861429786716513309 4910095073036170018692491)
    ·
      refine ⟨7365142609554255028038737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910095073036170018692491 7365142609554255028038737)
      ·
        refine ⟨5523856957165691271029053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365142609554255028038737 5523856957165691271029053)
        ·
          refine ⟨2071446358937134226635895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5523856957165691271029053 2071446358937134226635895)
          ·
            refine ⟨3107169538405701339953843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071446358937134226635895 3107169538405701339953843)
            ·
              refine ⟨4660754307608552009930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107169538405701339953843 4660754307608552009930765)
              ·
                refine ⟨1747782865353207003724037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4660754307608552009930765 1747782865353207003724037)
                ·
                  refine ⟨327709287253726313198257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747782865353207003724037 327709287253726313198257)
                  ·
                    rfl

theorem cell20_717988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_717988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_717988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_717988 prefixEnd_717988 := by exact prefixLift 717988
  have htrace : WordTrace (prefixWord ++ tailWord_717988) baseStart_717988 baseEnd_717988 := by
    simpa [prefixWord, tailWord_717988, baseEnd_717988] using wordTrace_append hprefix tailTrace_717988
  have hstable : (prefixWord ++ tailWord_717988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717988).length < 2 ^ (prefixWord ++ tailWord_717988).sum := by decide
  have hdescent : baseEnd_717988 < baseStart_717988 := by decide
  rcases family_descends (prefixWord ++ tailWord_717988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718012 : List Nat := [2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_718012 : Nat := 118140960795 + 718012 * 2 ^ 59
def prefixEnd_718012 : Nat := 4983230072969 + 3 ^ 40 * 718012 * 2
def baseEnd_718012 : Nat := 109240080502562965466053

theorem tailTrace_718012 : CollatzResearch.WordTrace tailWord_718012 prefixEnd_718012 109240080502562965466053 := by
  unfold tailWord_718012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094024537386312765950145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17458699383181750354600193 13094024537386312765950145)
  ·
    refine ⟨9820518403039734574462609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13094024537386312765950145 9820518403039734574462609)
    ·
      refine ⟨7365388802279800930846957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9820518403039734574462609 7365388802279800930846957)
      ·
        refine ⟨2762020800854925349067609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7365388802279800930846957 2762020800854925349067609)
        ·
          refine ⟨2071515600641194011800707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2762020800854925349067609 2071515600641194011800707)
          ·
            refine ⟨3107273400961791017701061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071515600641194011800707 3107273400961791017701061)
            ·
              refine ⟨582613762680335815818949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3107273400961791017701061 582613762680335815818949)
              ·
                refine ⟨109240080502562965466053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582613762680335815818949 109240080502562965466053)
                ·
                  rfl

theorem cell20_718012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_718012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718012 prefixEnd_718012 := by exact prefixLift 718012
  have htrace : WordTrace (prefixWord ++ tailWord_718012) baseStart_718012 baseEnd_718012 := by
    simpa [prefixWord, tailWord_718012, baseEnd_718012] using wordTrace_append hprefix tailTrace_718012
  have hstable : (prefixWord ++ tailWord_718012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718012).length < 2 ^ (prefixWord ++ tailWord_718012).sum := by decide
  have hdescent : baseEnd_718012 < baseStart_718012 := by decide
  rcases family_descends (prefixWord ++ tailWord_718012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718053 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_718053 : Nat := 118140960795 + 718053 * 2 ^ 59
def prefixEnd_718053 : Nat := 4983230072969 + 3 ^ 40 * 718053 * 2
def baseEnd_718053 : Nat := 327738955024874976031325

theorem tailTrace_718053 : CollatzResearch.WordTrace tailWord_718053 prefixEnd_718053 327738955024874976031325 := by
  unfold tailWord_718053
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189544467624089534142813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17459696311749393022761875 26189544467624089534142813)
  ·
    refine ⟨9821079175359033575303555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26189544467624089534142813 9821079175359033575303555)
    ·
      refine ⟨14731618763038550362955333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821079175359033575303555 14731618763038550362955333)
      ·
        refine ⟨2762178518069728193054125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14731618763038550362955333 2762178518069728193054125)
        ·
          refine ⟨1035816944276148072395297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762178518069728193054125 1035816944276148072395297)
          ·
            refine ⟨776862708207111054296473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035816944276148072395297 776862708207111054296473)
            ·
              refine ⟨582647031155333290722355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776862708207111054296473 582647031155333290722355)
              ·
                refine ⟨873970546732999936083533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582647031155333290722355 873970546732999936083533)
                ·
                  refine ⟨327738955024874976031325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873970546732999936083533 327738955024874976031325)
                  ·
                    rfl

theorem cell20_718053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_718053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718053 prefixEnd_718053 := by exact prefixLift 718053
  have htrace : WordTrace (prefixWord ++ tailWord_718053) baseStart_718053 baseEnd_718053 := by
    simpa [prefixWord, tailWord_718053, baseEnd_718053] using wordTrace_append hprefix tailTrace_718053
  have hstable : (prefixWord ++ tailWord_718053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718053).length < 2 ^ (prefixWord ++ tailWord_718053).sum := by decide
  have hdescent : baseEnd_718053 < baseStart_718053 := by decide
  rcases family_descends (prefixWord ++ tailWord_718053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718092 : List Nat := [2, 2, 1, 2, 2, 11]
def baseStart_718092 : Nat := 118140960795 + 718092 * 2 ^ 59
def prefixEnd_718092 : Nat := 4983230072969 + 3 ^ 40 * 718092 * 2
def baseEnd_718092 : Nat := 12139139099539413841895

theorem tailTrace_718092 : CollatzResearch.WordTrace tailWord_718092 prefixEnd_718092 12139139099539413841895 := by
  unfold tailWord_718092
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095483457241399597406265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17460644609655199463208353 13095483457241399597406265)
  ·
    refine ⟨9821612592931049698054699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13095483457241399597406265 9821612592931049698054699)
    ·
      refine ⟨14732418889396574547082049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821612592931049698054699 14732418889396574547082049)
      ·
        refine ⟨11049314167047430910311537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14732418889396574547082049 11049314167047430910311537)
        ·
          refine ⟨8286985625285573182733653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11049314167047430910311537 8286985625285573182733653)
          ·
            refine ⟨12139139099539413841895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8286985625285573182733653 12139139099539413841895)
            ·
              rfl

theorem cell20_718092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 11].length) (baseStart_718092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718092 prefixEnd_718092 := by exact prefixLift 718092
  have htrace : WordTrace (prefixWord ++ tailWord_718092) baseStart_718092 baseEnd_718092 := by
    simpa [prefixWord, tailWord_718092, baseEnd_718092] using wordTrace_append hprefix tailTrace_718092
  have hstable : (prefixWord ++ tailWord_718092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718092).length < 2 ^ (prefixWord ++ tailWord_718092).sum := by decide
  have hdescent : baseEnd_718092 < baseStart_718092 := by decide
  rcases family_descends (prefixWord ++ tailWord_718092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718168 : List Nat := [2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_718168 : Nat := 118140960795 + 718168 * 2 ^ 59
def prefixEnd_718168 : Nat := 4983230072969 + 3 ^ 40 * 718168 * 2
def baseEnd_718168 : Nat := 109263814719481895732507

theorem tailTrace_718168 : CollatzResearch.WordTrace tailWord_718168 prefixEnd_718168 109263814719481895732507 := by
  unfold tailWord_718168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096869431103732087289579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17462492574804976116386105 13096869431103732087289579)
  ·
    refine ⟨19645304146655598130934369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13096869431103732087289579 19645304146655598130934369)
    ·
      refine ⟨14733978109991698598200777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19645304146655598130934369 14733978109991698598200777)
      ·
        refine ⟨11050483582493773948650583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14733978109991698598200777 11050483582493773948650583)
        ·
          refine ⟨16575725373740660922975875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050483582493773948650583 16575725373740660922975875)
          ·
            refine ⟨24863588060610991384463813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16575725373740660922975875 24863588060610991384463813)
            ·
              refine ⟨4661922761364560884586965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24863588060610991384463813 4661922761364560884586965)
              ·
                refine ⟨109263814719481895732507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4661922761364560884586965 109263814719481895732507)
                ·
                  rfl

theorem cell20_718168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_718168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718168 prefixEnd_718168 := by exact prefixLift 718168
  have htrace : WordTrace (prefixWord ++ tailWord_718168) baseStart_718168 baseEnd_718168 := by
    simpa [prefixWord, tailWord_718168, baseEnd_718168] using wordTrace_append hprefix tailTrace_718168
  have hstable : (prefixWord ++ tailWord_718168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718168).length < 2 ^ (prefixWord ++ tailWord_718168).sum := by decide
  have hdescent : baseEnd_718168 < baseStart_718168 := by decide
  rcases family_descends (prefixWord ++ tailWord_718168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
