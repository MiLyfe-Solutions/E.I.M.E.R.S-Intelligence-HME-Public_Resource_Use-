import V185TrunkScan23Chunk1343

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7959495 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_7959495 : Nat := 118140960795 + 7959495 * 2 ^ 59
def prefixEnd_7959495 : Nat := 4983230072969 + 3 ^ 40 * 7959495 * 2
def baseEnd_7959495 : Nat := 4087046702058441172907455

theorem tailTrace_7959495 : CollatzResearch.WordTrace tailWord_7959495 prefixEnd_7959495 4087046702058441172907455 := by
  unfold tailWord_7959495
  simp only [CollatzResearch.WordTrace]
  refine ⟨290306632299116463365855939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193537754866077642243903959 290306632299116463365855939)
  ·
    refine ⟨435459948448674695048783909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290306632299116463365855939 435459948448674695048783909)
    ·
      refine ⟨81648740334126505321646983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435459948448674695048783909 81648740334126505321646983)
      ·
        refine ⟨122473110501189757982470475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81648740334126505321646983 122473110501189757982470475)
        ·
          refine ⟨183709665751784636973705713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122473110501189757982470475 183709665751784636973705713)
          ·
            refine ⟨137782249313838477730279285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183709665751784636973705713 137782249313838477730279285)
            ·
              refine ⟨12917085873172357287213683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137782249313838477730279285 12917085873172357287213683)
              ·
                refine ⟨19375628809758535930820525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12917085873172357287213683 19375628809758535930820525)
                ·
                  refine ⟨7265860803659450974057697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19375628809758535930820525 7265860803659450974057697)
                  ·
                    refine ⟨5449395602744588230543273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7265860803659450974057697 5449395602744588230543273)
                    ·
                      refine ⟨4087046702058441172907455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449395602744588230543273 4087046702058441172907455)
                      ·
                        rfl

theorem cell23_7959495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_7959495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959495 prefixEnd_7959495 := by exact prefixLift 7959495
  have htrace : WordTrace (prefixWord ++ tailWord_7959495) baseStart_7959495 baseEnd_7959495 := by
    simpa [prefixWord, tailWord_7959495, baseEnd_7959495] using wordTrace_append hprefix tailTrace_7959495
  have hstable : (prefixWord ++ tailWord_7959495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959495).length < 2 ^ (prefixWord ++ tailWord_7959495).sum := by decide
  have hdescent : baseEnd_7959495 < baseStart_7959495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_7959504 : Nat := 118140960795 + 7959504 * 2 ^ 59
def prefixEnd_7959504 : Nat := 4983230072969 + 3 ^ 40 * 7959504 * 2
def baseEnd_7959504 : Nat := 4087051323384331637694913

theorem tailTrace_7959504 : CollatzResearch.WordTrace tailWord_7959504 prefixEnd_7959504 4087051323384331637694913 := by
  unfold tailWord_7959504
  simp only [CollatzResearch.WordTrace]
  refine ⟨145153480278041928951466783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193537973704055905268622377 145153480278041928951466783)
  ·
    refine ⟨217730220417062893427200175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145153480278041928951466783 217730220417062893427200175)
    ·
      refine ⟨326595330625594340140800263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217730220417062893427200175 326595330625594340140800263)
      ·
        refine ⟨489892995938391510211200395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326595330625594340140800263 489892995938391510211200395)
        ·
          refine ⟨734839493907587265316800593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489892995938391510211200395 734839493907587265316800593)
          ·
            refine ⟨551129620430690448987600445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734839493907587265316800593 551129620430690448987600445)
            ·
              refine ⟨206673607661508918370350167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551129620430690448987600445 206673607661508918370350167)
              ·
                refine ⟨310010411492263377555525251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206673607661508918370350167 310010411492263377555525251)
                ·
                  refine ⟨465015617238395066333287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310010411492263377555525251 465015617238395066333287877)
                  ·
                    refine ⟨87190428232199074937491477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465015617238395066333287877 87190428232199074937491477)
                    ·
                      refine ⟨4087051323384331637694913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87190428232199074937491477 4087051323384331637694913)
                      ·
                        rfl

theorem cell23_7959504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_7959504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959504 prefixEnd_7959504 := by exact prefixLift 7959504
  have htrace : WordTrace (prefixWord ++ tailWord_7959504) baseStart_7959504 baseEnd_7959504 := by
    simpa [prefixWord, tailWord_7959504, baseEnd_7959504] using wordTrace_append hprefix tailTrace_7959504
  have hstable : (prefixWord ++ tailWord_7959504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959504).length < 2 ^ (prefixWord ++ tailWord_7959504).sum := by decide
  have hdescent : baseEnd_7959504 < baseStart_7959504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959525 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7959525 : Nat := 118140960795 + 7959525 * 2 ^ 59
def prefixEnd_7959525 : Nat := 4983230072969 + 3 ^ 40 * 7959525 * 2
def baseEnd_7959525 : Nat := 4087062106478076055532317

theorem tailTrace_7959525 : CollatzResearch.WordTrace tailWord_7959525 prefixEnd_7959525 4087062106478076055532317 := by
  unfold tailWord_7959525
  simp only [CollatzResearch.WordTrace]
  refine ⟨290307726489007778489448029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193538484326005185659632019 290307726489007778489448029)
  ·
    refine ⟨108865397433377916933543011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290307726489007778489448029 108865397433377916933543011)
    ·
      refine ⟨163298096150066875400314517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108865397433377916933543011 163298096150066875400314517)
      ·
        refine ⟨7654598257034384784389743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163298096150066875400314517 7654598257034384784389743)
        ·
          refine ⟨11481897385551577176584615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654598257034384784389743 11481897385551577176584615)
          ·
            refine ⟨17222846078327365764876923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481897385551577176584615 17222846078327365764876923)
            ·
              refine ⟨25834269117491048647315385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222846078327365764876923 25834269117491048647315385)
              ·
                refine ⟨19375701838118286485486539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25834269117491048647315385 19375701838118286485486539)
                ·
                  refine ⟨29063552757177429728229809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19375701838118286485486539 29063552757177429728229809)
                  ·
                    refine ⟨21797664567883072296172357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29063552757177429728229809 21797664567883072296172357)
                    ·
                      refine ⟨4087062106478076055532317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21797664567883072296172357 4087062106478076055532317)
                      ·
                        rfl

theorem cell23_7959525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7959525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959525 prefixEnd_7959525 := by exact prefixLift 7959525
  have htrace : WordTrace (prefixWord ++ tailWord_7959525) baseStart_7959525 baseEnd_7959525 := by
    simpa [prefixWord, tailWord_7959525, baseEnd_7959525] using wordTrace_append hprefix tailTrace_7959525
  have hstable : (prefixWord ++ tailWord_7959525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959525).length < 2 ^ (prefixWord ++ tailWord_7959525).sum := by decide
  have hdescent : baseEnd_7959525 < baseStart_7959525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959528 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7959528 : Nat := 118140960795 + 7959528 * 2 ^ 59
def prefixEnd_7959528 : Nat := 4983230072969 + 3 ^ 40 * 7959528 * 2
def baseEnd_7959528 : Nat := 4087063646920039543794803

theorem tailTrace_7959528 : CollatzResearch.WordTrace tailWord_7959528 prefixEnd_7959528 4087063646920039543794803 := by
  unfold tailWord_7959528
  simp only [CollatzResearch.WordTrace]
  refine ⟨145153917953998455000903619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193538557271997940001204825 145153917953998455000903619)
  ·
    refine ⟨217730876930997682501355429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145153917953998455000903619 217730876930997682501355429)
    ·
      refine ⟨40824539424562065469004143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217730876930997682501355429 40824539424562065469004143)
      ·
        refine ⟨61236809136843098203506215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40824539424562065469004143 61236809136843098203506215)
        ·
          refine ⟨91855213705264647305259323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61236809136843098203506215 91855213705264647305259323)
          ·
            refine ⟨137782820557896970957888985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91855213705264647305259323 137782820557896970957888985)
            ·
              refine ⟨103337115418422728218416739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137782820557896970957888985 103337115418422728218416739)
              ·
                refine ⟨155005673127634092327625109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103337115418422728218416739 155005673127634092327625109)
                ·
                  refine ⟨7265890927857848077857427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155005673127634092327625109 7265890927857848077857427)
                  ·
                    refine ⟨10898836391786772116786141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265890927857848077857427 10898836391786772116786141)
                    ·
                      refine ⟨4087063646920039543794803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898836391786772116786141 4087063646920039543794803)
                      ·
                        rfl

theorem cell23_7959528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7959528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959528 prefixEnd_7959528 := by exact prefixLift 7959528
  have htrace : WordTrace (prefixWord ++ tailWord_7959528) baseStart_7959528 baseEnd_7959528 := by
    simpa [prefixWord, tailWord_7959528, baseEnd_7959528] using wordTrace_append hprefix tailTrace_7959528
  have hstable : (prefixWord ++ tailWord_7959528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959528).length < 2 ^ (prefixWord ++ tailWord_7959528).sum := by decide
  have hdescent : baseEnd_7959528 < baseStart_7959528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959545 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_7959545 : Nat := 118140960795 + 7959545 * 2 ^ 59
def prefixEnd_7959545 : Nat := 4983230072969 + 3 ^ 40 * 7959545 * 2
def baseEnd_7959545 : Nat := 4087072376091165977282225

theorem tailTrace_7959545 : CollatzResearch.WordTrace tailWord_7959545 prefixEnd_7959545 4087072376091165977282225 := by
  unfold tailWord_7959545
  simp only [CollatzResearch.WordTrace]
  refine ⟨290308455948935321905176089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193538970632623547936784059 290308455948935321905176089)
  ·
    refine ⟨217731341961701491428882067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290308455948935321905176089 217731341961701491428882067)
    ·
      refine ⟨326597012942552237143323101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217731341961701491428882067 326597012942552237143323101)
      ·
        refine ⟨122473879853457088928746163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326597012942552237143323101 122473879853457088928746163)
        ·
          refine ⟨183710819780185633393119245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122473879853457088928746163 183710819780185633393119245)
          ·
            refine ⟨68891557417569612522419717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183710819780185633393119245 68891557417569612522419717)
            ·
              refine ⟨12917167015794302347953697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68891557417569612522419717 12917167015794302347953697)
              ·
                refine ⟨9687875261845726760965273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917167015794302347953697 9687875261845726760965273)
                ·
                  refine ⟨7265906446384295070723955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9687875261845726760965273 7265906446384295070723955)
                  ·
                    refine ⟨10898859669576442606085933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265906446384295070723955 10898859669576442606085933)
                    ·
                      refine ⟨4087072376091165977282225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898859669576442606085933 4087072376091165977282225)
                      ·
                        rfl

theorem cell23_7959545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_7959545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959545 prefixEnd_7959545 := by exact prefixLift 7959545
  have htrace : WordTrace (prefixWord ++ tailWord_7959545) baseStart_7959545 baseEnd_7959545 := by
    simpa [prefixWord, tailWord_7959545, baseEnd_7959545] using wordTrace_append hprefix tailTrace_7959545
  have hstable : (prefixWord ++ tailWord_7959545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959545).length < 2 ^ (prefixWord ++ tailWord_7959545).sum := by decide
  have hdescent : baseEnd_7959545 < baseStart_7959545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959571 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3]
def baseStart_7959571 : Nat := 118140960795 + 7959571 * 2 ^ 59
def prefixEnd_7959571 : Nat := 4983230072969 + 3 ^ 40 * 7959571 * 2
def baseEnd_7959571 : Nat := 4087085726588182875557105

theorem tailTrace_7959571 : CollatzResearch.WordTrace tailWord_7959571 prefixEnd_7959571 4087085726588182875557105 := by
  unfold tailWord_7959571
  simp only [CollatzResearch.WordTrace]
  refine ⟨290309404246841128345622567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193539602831227418897081711 290309404246841128345622567)
  ·
    refine ⟨435464106370261692518433851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290309404246841128345622567 435464106370261692518433851)
    ·
      refine ⟨653196159555392538777650777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435464106370261692518433851 653196159555392538777650777)
      ·
        refine ⟨489897119666544404083238083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653196159555392538777650777 489897119666544404083238083)
        ·
          refine ⟨734845679499816606124857125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489897119666544404083238083 734845679499816606124857125)
          ·
            refine ⟨137783564906215613648410711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 734845679499816606124857125 137783564906215613648410711)
            ·
              refine ⟨206675347359323420472616067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137783564906215613648410711 206675347359323420472616067)
              ·
                refine ⟨310013021038985130708924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206675347359323420472616067 310013021038985130708924101)
                ·
                  refine ⟨58127441444809712007923269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310013021038985130708924101 58127441444809712007923269)
                  ·
                    refine ⟨10898895270901821001485613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58127441444809712007923269 10898895270901821001485613)
                    ·
                      refine ⟨4087085726588182875557105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898895270901821001485613 4087085726588182875557105)
                      ·
                        rfl

theorem cell23_7959571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_7959571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959571 prefixEnd_7959571 := by exact prefixLift 7959571
  have htrace : WordTrace (prefixWord ++ tailWord_7959571) baseStart_7959571 baseEnd_7959571 := by
    simpa [prefixWord, tailWord_7959571, baseEnd_7959571] using wordTrace_append hprefix tailTrace_7959571
  have hstable : (prefixWord ++ tailWord_7959571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959571).length < 2 ^ (prefixWord ++ tailWord_7959571).sum := by decide
  have hdescent : baseEnd_7959571 < baseStart_7959571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959585 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7959585 : Nat := 118140960795 + 7959585 * 2 ^ 59
def prefixEnd_7959585 : Nat := 4983230072969 + 3 ^ 40 * 7959585 * 2
def baseEnd_7959585 : Nat := 4087092915317345820782041

theorem tailTrace_7959585 : CollatzResearch.WordTrace tailWord_7959585 prefixEnd_7959585 4087092915317345820782041 := by
  unfold tailWord_7959585
  simp only [CollatzResearch.WordTrace]
  refine ⟨290309914868790408736632209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193539943245860272491088139 290309914868790408736632209)
  ·
    refine ⟨217732436151592806552474157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290309914868790408736632209 217732436151592806552474157)
    ·
      refine ⟨81649663556847302457177809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217732436151592806552474157 81649663556847302457177809)
      ·
        refine ⟨61237247667635476842883357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81649663556847302457177809 61237247667635476842883357)
        ·
          refine ⟨22963967875363303816081259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61237247667635476842883357 22963967875363303816081259)
          ·
            refine ⟨34445951813044955724121889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22963967875363303816081259 34445951813044955724121889)
            ·
              refine ⟨25834463859783716793091417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34445951813044955724121889 25834463859783716793091417)
              ·
                refine ⟨19375847894837787594818563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25834463859783716793091417 19375847894837787594818563)
                ·
                  refine ⟨29063771842256681392227845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19375847894837787594818563 29063771842256681392227845)
                  ·
                    refine ⟨5449457220423127761042721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29063771842256681392227845 5449457220423127761042721)
                    ·
                      refine ⟨4087092915317345820782041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449457220423127761042721 4087092915317345820782041)
                      ·
                        rfl

theorem cell23_7959585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7959585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959585 prefixEnd_7959585 := by exact prefixLift 7959585
  have htrace : WordTrace (prefixWord ++ tailWord_7959585) baseStart_7959585 baseEnd_7959585 := by
    simpa [prefixWord, tailWord_7959585, baseEnd_7959585] using wordTrace_append hprefix tailTrace_7959585
  have hstable : (prefixWord ++ tailWord_7959585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959585).length < 2 ^ (prefixWord ++ tailWord_7959585).sum := by decide
  have hdescent : baseEnd_7959585 < baseStart_7959585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959598 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7959598 : Nat := 118140960795 + 7959598 * 2 ^ 59
def prefixEnd_7959598 : Nat := 4983230072969 + 3 ^ 40 * 7959598 * 2
def baseEnd_7959598 : Nat := 4087099590565854269919481

theorem tailTrace_7959598 : CollatzResearch.WordTrace tailWord_7959598 prefixEnd_7959598 4087099590565854269919481 := by
  unfold tailWord_7959598
  simp only [CollatzResearch.WordTrace]
  refine ⟨36288798627217913994606931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193540259345162207971236965 36288798627217913994606931)
  ·
    refine ⟨54433197940826870991910397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36288798627217913994606931 54433197940826870991910397)
    ·
      refine ⟨20412449227810076621966399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54433197940826870991910397 20412449227810076621966399)
      ·
        refine ⟨30618673841715114932949599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20412449227810076621966399 30618673841715114932949599)
        ·
          refine ⟨45928010762572672399424399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30618673841715114932949599 45928010762572672399424399)
          ·
            refine ⟨68892016143859008599136599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45928010762572672399424399 68892016143859008599136599)
            ·
              refine ⟨103338024215788512898704899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68892016143859008599136599 103338024215788512898704899)
              ·
                refine ⟨155007036323682769348057349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103338024215788512898704899 155007036323682769348057349)
                ·
                  refine ⟨29063819310690519252760753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155007036323682769348057349 29063819310690519252760753)
                  ·
                    refine ⟨21797864483017889439570565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29063819310690519252760753 21797864483017889439570565)
                    ·
                      refine ⟨4087099590565854269919481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21797864483017889439570565 4087099590565854269919481)
                      ·
                        rfl

theorem cell23_7959598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7959598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959598 prefixEnd_7959598 := by exact prefixLift 7959598
  have htrace : WordTrace (prefixWord ++ tailWord_7959598) baseStart_7959598 baseEnd_7959598 := by
    simpa [prefixWord, tailWord_7959598, baseEnd_7959598] using wordTrace_append hprefix tailTrace_7959598
  have hstable : (prefixWord ++ tailWord_7959598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959598).length < 2 ^ (prefixWord ++ tailWord_7959598).sum := by decide
  have hdescent : baseEnd_7959598 < baseStart_7959598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959608 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 7]
def baseStart_7959608 : Nat := 118140960795 + 7959608 * 2 ^ 59
def prefixEnd_7959608 : Nat := 4983230072969 + 3 ^ 40 * 7959608 * 2
def baseEnd_7959608 : Nat := 454122747263599914532715

theorem tailTrace_7959608 : CollatzResearch.WordTrace tailWord_7959608 prefixEnd_7959608 454122747263599914532715 := by
  unfold tailWord_7959608
  simp only [CollatzResearch.WordTrace]
  refine ⟨145155376873853541832359739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193540502498471389109812985 145155376873853541832359739)
  ·
    refine ⟨217733065310780312748539609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145155376873853541832359739 217733065310780312748539609)
    ·
      refine ⟨163299798983085234561404707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217733065310780312748539609 163299798983085234561404707)
      ·
        refine ⟨244949698474627851842107061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163299798983085234561404707 244949698474627851842107061)
        ·
          refine ⟨22964034231996361110197537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244949698474627851842107061 22964034231996361110197537)
          ·
            refine ⟨17223025673997270832648153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22964034231996361110197537 17223025673997270832648153)
            ·
              refine ⟨12917269255497953124486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17223025673997270832648153 12917269255497953124486115)
              ·
                refine ⟨19375903883246929686729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12917269255497953124486115 19375903883246929686729173)
                ·
                  refine ⟨454122747263599914532715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19375903883246929686729173 454122747263599914532715)
                  ·
                    rfl

theorem cell23_7959608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_7959608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959608 prefixEnd_7959608 := by exact prefixLift 7959608
  have htrace : WordTrace (prefixWord ++ tailWord_7959608) baseStart_7959608 baseEnd_7959608 := by
    simpa [prefixWord, tailWord_7959608, baseEnd_7959608] using wordTrace_append hprefix tailTrace_7959608
  have hstable : (prefixWord ++ tailWord_7959608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959608).length < 2 ^ (prefixWord ++ tailWord_7959608).sum := by decide
  have hdescent : baseEnd_7959608 < baseStart_7959608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959621 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_7959621 : Nat := 118140960795 + 7959621 * 2 ^ 59
def prefixEnd_7959621 : Nat := 4983230072969 + 3 ^ 40 * 7959621 * 2
def baseEnd_7959621 : Nat := 1362370466873635893310625

theorem tailTrace_7959621 : CollatzResearch.WordTrace tailWord_7959621 prefixEnd_7959621 1362370466873635893310625 := by
  unfold tailWord_7959621
  simp only [CollatzResearch.WordTrace]
  refine ⟨290311227896659986884942717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193540818597773324589961811 290311227896659986884942717)
  ·
    refine ⟨108866710461247495081853519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290311227896659986884942717 108866710461247495081853519)
    ·
      refine ⟨163300065691871242622780279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108866710461247495081853519 163300065691871242622780279)
      ·
        refine ⟨244950098537806863934170419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163300065691871242622780279 244950098537806863934170419)
        ·
          refine ⟨367425147806710295901255629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244950098537806863934170419 367425147806710295901255629)
          ·
            refine ⟨137784430427516360962970861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367425147806710295901255629 137784430427516360962970861)
            ·
              refine ⟨51669161410318635361114073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137784430427516360962970861 51669161410318635361114073)
              ·
                refine ⟨38751871057738976520835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51669161410318635361114073 38751871057738976520835555)
                ·
                  refine ⟨58127806586608464781253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38751871057738976520835555 58127806586608464781253333)
                  ·
                    refine ⟨1362370466873635893310625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58127806586608464781253333 1362370466873635893310625)
                    ·
                      rfl

theorem cell23_7959621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_7959621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959621 prefixEnd_7959621 := by exact prefixLift 7959621
  have htrace : WordTrace (prefixWord ++ tailWord_7959621) baseStart_7959621 baseEnd_7959621 := by
    simpa [prefixWord, tailWord_7959621, baseEnd_7959621] using wordTrace_append hprefix tailTrace_7959621
  have hstable : (prefixWord ++ tailWord_7959621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959621).length < 2 ^ (prefixWord ++ tailWord_7959621).sum := by decide
  have hdescent : baseEnd_7959621 < baseStart_7959621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959719 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7959719 : Nat := 118140960795 + 7959719 * 2 ^ 59
def prefixEnd_7959719 : Nat := 4983230072969 + 3 ^ 40 * 7959719 * 2
def baseEnd_7959719 : Nat := 1362387240575016098835475

theorem tailTrace_7959719 : CollatzResearch.WordTrace tailWord_7959719 prefixEnd_7959719 1362387240575016098835475 := by
  unfold tailWord_7959719
  simp only [CollatzResearch.WordTrace]
  refine ⟨290314802250304949622010211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193543201500203299748006807 290314802250304949622010211)
  ·
    refine ⟨435472203375457424433015317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290314802250304949622010211 435472203375457424433015317)
    ·
      refine ⟨20412759533224566770297593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435472203375457424433015317 20412759533224566770297593)
      ·
        refine ⟨15309569649918425077723195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20412759533224566770297593 15309569649918425077723195)
        ·
          refine ⟨22964354474877637616584793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309569649918425077723195 22964354474877637616584793)
          ·
            refine ⟨17223265856158228212438595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22964354474877637616584793 17223265856158228212438595)
            ·
              refine ⟨25834898784237342318657893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17223265856158228212438595 25834898784237342318657893)
              ·
                refine ⟨4844043522044501684748355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25834898784237342318657893 4844043522044501684748355)
                ·
                  refine ⟨7266065283066752527122533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844043522044501684748355 7266065283066752527122533)
                  ·
                    refine ⟨1362387240575016098835475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7266065283066752527122533 1362387240575016098835475)
                    ·
                      rfl

theorem cell23_7959719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7959719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959719 prefixEnd_7959719 := by exact prefixLift 7959719
  have htrace : WordTrace (prefixWord ++ tailWord_7959719) baseStart_7959719 baseEnd_7959719 := by
    simpa [prefixWord, tailWord_7959719, baseEnd_7959719] using wordTrace_append hprefix tailTrace_7959719
  have hstable : (prefixWord ++ tailWord_7959719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959719).length < 2 ^ (prefixWord ++ tailWord_7959719).sum := by decide
  have hdescent : baseEnd_7959719 < baseStart_7959719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959735 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_7959735 : Nat := 118140960795 + 7959735 * 2 ^ 59
def prefixEnd_7959735 : Nat := 4983230072969 + 3 ^ 40 * 7959735 * 2
def baseEnd_7959735 : Nat := 4087169937415520233906351

theorem tailTrace_7959735 : CollatzResearch.WordTrace tailWord_7959735 prefixEnd_7959735 4087169937415520233906351 := by
  unfold tailWord_7959735
  simp only [CollatzResearch.WordTrace]
  refine ⟨290315385818246984354592659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193543590545497989569728439 290315385818246984354592659)
  ·
    refine ⟨435473078727370476531888989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290315385818246984354592659 435473078727370476531888989)
    ·
      refine ⟨163302404522763928699458371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435473078727370476531888989 163302404522763928699458371)
      ·
        refine ⟨244953606784145893049187557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163302404522763928699458371 244953606784145893049187557)
        ·
          refine ⟨45928801272027354946722667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244953606784145893049187557 45928801272027354946722667)
          ·
            refine ⟨68893201908041032420084001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45928801272027354946722667 68893201908041032420084001)
            ·
              refine ⟨51669901431030774315063001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68893201908041032420084001 51669901431030774315063001)
              ·
                refine ⟨38752426073273080736297251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51669901431030774315063001 38752426073273080736297251)
                ·
                  refine ⟨58128639109909621104445877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38752426073273080736297251 58128639109909621104445877)
                  ·
                    refine ⟨5449559916554026978541801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58128639109909621104445877 5449559916554026978541801)
                    ·
                      refine ⟨4087169937415520233906351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449559916554026978541801 4087169937415520233906351)
                      ·
                        rfl

theorem cell23_7959735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_7959735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959735 prefixEnd_7959735 := by exact prefixLift 7959735
  have htrace : WordTrace (prefixWord ++ tailWord_7959735) baseStart_7959735 baseEnd_7959735 := by
    simpa [prefixWord, tailWord_7959735, baseEnd_7959735] using wordTrace_append hprefix tailTrace_7959735
  have hstable : (prefixWord ++ tailWord_7959735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959735).length < 2 ^ (prefixWord ++ tailWord_7959735).sum := by decide
  have hdescent : baseEnd_7959735 < baseStart_7959735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959742 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_7959742 : Nat := 118140960795 + 7959742 * 2 ^ 59
def prefixEnd_7959742 : Nat := 4983230072969 + 3 ^ 40 * 7959742 * 2
def baseEnd_7959742 : Nat := 4087173531780101706518819

theorem tailTrace_7959742 : CollatzResearch.WordTrace tailWord_7959742 prefixEnd_7959742 4087173531780101706518819 := by
  unfold tailWord_7959742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289455141152703068762185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193543760752814416366731653 36289455141152703068762185)
  ·
    refine ⟨27217091355864527301571639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36289455141152703068762185 27217091355864527301571639)
    ·
      refine ⟨40825637033796790952357459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27217091355864527301571639 40825637033796790952357459)
      ·
        refine ⟨61238455550695186428536189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40825637033796790952357459 61238455550695186428536189)
        ·
          refine ⟨22964420831510694910701071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61238455550695186428536189 22964420831510694910701071)
          ·
            refine ⟨34446631247266042366051607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964420831510694910701071 34446631247266042366051607)
            ·
              refine ⟨51669946870899063549077411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34446631247266042366051607 51669946870899063549077411)
              ·
                refine ⟨77504920306348595323616117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51669946870899063549077411 77504920306348595323616117)
                ·
                  refine ⟨7266086278720180811589011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77504920306348595323616117 7266086278720180811589011)
                  ·
                    refine ⟨10899129418080271217383517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7266086278720180811589011 10899129418080271217383517)
                    ·
                      refine ⟨4087173531780101706518819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10899129418080271217383517 4087173531780101706518819)
                      ·
                        rfl

theorem cell23_7959742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_7959742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959742 prefixEnd_7959742 := by exact prefixLift 7959742
  have htrace : WordTrace (prefixWord ++ tailWord_7959742) baseStart_7959742 baseEnd_7959742 := by
    simpa [prefixWord, tailWord_7959742, baseEnd_7959742] using wordTrace_append hprefix tailTrace_7959742
  have hstable : (prefixWord ++ tailWord_7959742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959742).length < 2 ^ (prefixWord ++ tailWord_7959742).sum := by decide
  have hdescent : baseEnd_7959742 < baseStart_7959742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959752 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_7959752 : Nat := 118140960795 + 7959752 * 2 ^ 59
def prefixEnd_7959752 : Nat := 4983230072969 + 3 ^ 40 * 7959752 * 2
def baseEnd_7959752 : Nat := 4087178666586646667393773

theorem tailTrace_7959752 : CollatzResearch.WordTrace tailWord_7959752 prefixEnd_7959752 4087178666586646667393773 := by
  unfold tailWord_7959752
  simp only [CollatzResearch.WordTrace]
  refine ⟨145158002929592698128980755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193544003906123597505307673 145158002929592698128980755)
  ·
    refine ⟨217737004394389047193471133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145158002929592698128980755 217737004394389047193471133)
    ·
      refine ⟨81651376647895892697551675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217737004394389047193471133 81651376647895892697551675)
      ·
        refine ⟨122477064971843839046327513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81651376647895892697551675 122477064971843839046327513)
        ·
          refine ⟨91857798728882879284745635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122477064971843839046327513 91857798728882879284745635)
          ·
            refine ⟨137786698093324318927118453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91857798728882879284745635 137786698093324318927118453)
            ·
              refine ⟨12917502946249154899417355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137786698093324318927118453 12917502946249154899417355)
              ·
                refine ⟨19376254419373732349126033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12917502946249154899417355 19376254419373732349126033)
                ·
                  refine ⟨14532190814530299261844525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19376254419373732349126033 14532190814530299261844525)
                  ·
                    refine ⟨5449571555448862223191697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14532190814530299261844525 5449571555448862223191697)
                    ·
                      refine ⟨4087178666586646667393773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449571555448862223191697 4087178666586646667393773)
                      ·
                        rfl

theorem cell23_7959752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_7959752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959752 prefixEnd_7959752 := by exact prefixLift 7959752
  have htrace : WordTrace (prefixWord ++ tailWord_7959752) baseStart_7959752 baseEnd_7959752 := by
    simpa [prefixWord, tailWord_7959752, baseEnd_7959752] using wordTrace_append hprefix tailTrace_7959752
  have hstable : (prefixWord ++ tailWord_7959752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959752).length < 2 ^ (prefixWord ++ tailWord_7959752).sum := by decide
  have hdescent : baseEnd_7959752 < baseStart_7959752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959766 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_7959766 : Nat := 118140960795 + 7959766 * 2 ^ 59
def prefixEnd_7959766 : Nat := 4983230072969 + 3 ^ 40 * 7959766 * 2
def baseEnd_7959766 : Nat := 454131761701756623624301

theorem tailTrace_7959766 : CollatzResearch.WordTrace tailWord_7959766 prefixEnd_7959766 454131761701756623624301 := by
  unfold tailWord_7959766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144782280070917290560697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193544344320756451099314101 18144782280070917290560697)
  ·
    refine ⟨13608586710053187967920523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18144782280070917290560697 13608586710053187967920523)
    ·
      refine ⟨20412880065079781951880785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13608586710053187967920523 20412880065079781951880785)
      ·
        refine ⟨15309660048809836463910589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20412880065079781951880785 15309660048809836463910589)
        ·
          refine ⟨5741122518303688673966471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15309660048809836463910589 5741122518303688673966471)
          ·
            refine ⟨8611683777455533010949707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741122518303688673966471 8611683777455533010949707)
            ·
              refine ⟨12917525666183299516424561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611683777455533010949707 12917525666183299516424561)
              ·
                refine ⟨9688144249637474637318421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917525666183299516424561 9688144249637474637318421)
                ·
                  refine ⟨454131761701756623624301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9688144249637474637318421 454131761701756623624301)
                  ·
                    rfl

theorem cell23_7959766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_7959766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959766 prefixEnd_7959766 := by exact prefixLift 7959766
  have htrace : WordTrace (prefixWord ++ tailWord_7959766) baseStart_7959766 baseEnd_7959766 := by
    simpa [prefixWord, tailWord_7959766, baseEnd_7959766] using wordTrace_append hprefix tailTrace_7959766
  have hstable : (prefixWord ++ tailWord_7959766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959766).length < 2 ^ (prefixWord ++ tailWord_7959766).sum := by decide
  have hdescent : baseEnd_7959766 < baseStart_7959766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959795 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4]
def baseStart_7959795 : Nat := 118140960795 + 7959795 * 2 ^ 59
def prefixEnd_7959795 : Nat := 4983230072969 + 3 ^ 40 * 7959795 * 2
def baseEnd_7959795 : Nat := 4087200746254789999156075

theorem tailTrace_7959795 : CollatzResearch.WordTrace tailWord_7959795 prefixEnd_7959795 4087200746254789999156075 := by
  unfold tailWord_7959795
  simp only [CollatzResearch.WordTrace]
  refine ⟨290317574198029614601776839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193545049465353076401184559 290317574198029614601776839)
  ·
    refine ⟨435476361297044421902665259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290317574198029614601776839 435476361297044421902665259)
    ·
      refine ⟨653214541945566632853997889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435476361297044421902665259 653214541945566632853997889)
      ·
        refine ⟨489910906459174974640498417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653214541945566632853997889 489910906459174974640498417)
        ·
          refine ⟨367433179844381230980373813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489910906459174974640498417 367433179844381230980373813)
          ·
            refine ⟨34446860610410740404410045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367433179844381230980373813 34446860610410740404410045)
            ·
              refine ⟨12917572728904027651653767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34446860610410740404410045 12917572728904027651653767)
              ·
                refine ⟨19376359093356041477480651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12917572728904027651653767 19376359093356041477480651)
                ·
                  refine ⟨29064538640034062216220977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19376359093356041477480651 29064538640034062216220977)
                  ·
                    refine ⟨21798403980025546662165733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29064538640034062216220977 21798403980025546662165733)
                    ·
                      refine ⟨4087200746254789999156075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21798403980025546662165733 4087200746254789999156075)
                      ·
                        rfl

theorem cell23_7959795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_7959795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959795 prefixEnd_7959795 := by exact prefixLift 7959795
  have htrace : WordTrace (prefixWord ++ tailWord_7959795) baseStart_7959795 baseEnd_7959795 := by
    simpa [prefixWord, tailWord_7959795, baseEnd_7959795] using wordTrace_append hprefix tailTrace_7959795
  have hstable : (prefixWord ++ tailWord_7959795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959795).length < 2 ^ (prefixWord ++ tailWord_7959795).sum := by decide
  have hdescent : baseEnd_7959795 < baseStart_7959795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959802 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_7959802 : Nat := 118140960795 + 7959802 * 2 ^ 59
def prefixEnd_7959802 : Nat := 4983230072969 + 3 ^ 40 * 7959802 * 2
def baseEnd_7959802 : Nat := 4087204340619371471768543

theorem tailTrace_7959802 : CollatzResearch.WordTrace tailWord_7959802 prefixEnd_7959802 4087204340619371471768543 := by
  unfold tailWord_7959802
  simp only [CollatzResearch.WordTrace]
  refine ⟨72579457377251063699320415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193545219672669503198187773 72579457377251063699320415)
  ·
    refine ⟨108869186065876595548980623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72579457377251063699320415 108869186065876595548980623)
    ·
      refine ⟨163303779098814893323470935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108869186065876595548980623 163303779098814893323470935)
      ·
        refine ⟨244955668648222339985206403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163303779098814893323470935 244955668648222339985206403)
        ·
          refine ⟨367433502972333509977809605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244955668648222339985206403 367433502972333509977809605)
          ·
            refine ⟨68893781807312533120839301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367433502972333509977809605 68893781807312533120839301)
            ·
              refine ⟨12917584088871099960157369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68893781807312533120839301 12917584088871099960157369)
              ·
                refine ⟨9688188066653324970118027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917584088871099960157369 9688188066653324970118027)
                ·
                  refine ⟨14532282099979987455177041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688188066653324970118027 14532282099979987455177041)
                  ·
                    refine ⟨10899211574984990591382781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14532282099979987455177041 10899211574984990591382781)
                    ·
                      refine ⟨4087204340619371471768543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10899211574984990591382781 4087204340619371471768543)
                      ·
                        rfl

theorem cell23_7959802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_7959802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959802 prefixEnd_7959802 := by exact prefixLift 7959802
  have htrace : WordTrace (prefixWord ++ tailWord_7959802) baseStart_7959802 baseEnd_7959802 := by
    simpa [prefixWord, tailWord_7959802, baseEnd_7959802] using wordTrace_append hprefix tailTrace_7959802
  have hstable : (prefixWord ++ tailWord_7959802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959802).length < 2 ^ (prefixWord ++ tailWord_7959802).sum := by decide
  have hdescent : baseEnd_7959802 < baseStart_7959802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959810 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_7959810 : Nat := 118140960795 + 7959810 * 2 ^ 59
def prefixEnd_7959810 : Nat := 4983230072969 + 3 ^ 40 * 7959810 * 2
def baseEnd_7959810 : Nat := 4087208448464607440468507

theorem tailTrace_7959810 : CollatzResearch.WordTrace tailWord_7959810 prefixEnd_7959810 4087208448464607440468507 := by
  unfold tailWord_7959810
  simp only [CollatzResearch.WordTrace]
  refine ⟨72579530323243818040893221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193545414195316848109048589 72579530323243818040893221)
  ·
    refine ⟨13608661935608215882667479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72579530323243818040893221 13608661935608215882667479)
    ·
      refine ⟨20412992903412323824001219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13608661935608215882667479 20412992903412323824001219)
      ·
        refine ⟨30619489355118485736001829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20412992903412323824001219 30619489355118485736001829)
        ·
          refine ⟨5741154254084716075500343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30619489355118485736001829 5741154254084716075500343)
          ·
            refine ⟨8611731381127074113250515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741154254084716075500343 8611731381127074113250515)
            ·
              refine ⟨12917597071690611169875773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8611731381127074113250515 12917597071690611169875773)
              ·
                refine ⟨4844098901883979188703415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12917597071690611169875773 4844098901883979188703415)
                ·
                  refine ⟨7266148352825968783055123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844098901883979188703415 7266148352825968783055123)
                  ·
                    refine ⟨10899222529238953174582685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7266148352825968783055123 10899222529238953174582685)
                    ·
                      refine ⟨4087208448464607440468507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10899222529238953174582685 4087208448464607440468507)
                      ·
                        rfl

theorem cell23_7959810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_7959810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959810 prefixEnd_7959810 := by exact prefixLift 7959810
  have htrace : WordTrace (prefixWord ++ tailWord_7959810) baseStart_7959810 baseEnd_7959810 := by
    simpa [prefixWord, tailWord_7959810, baseEnd_7959810] using wordTrace_append hprefix tailTrace_7959810
  have hstable : (prefixWord ++ tailWord_7959810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959810).length < 2 ^ (prefixWord ++ tailWord_7959810).sum := by decide
  have hdescent : baseEnd_7959810 < baseStart_7959810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959818 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_7959818 : Nat := 118140960795 + 7959818 * 2 ^ 59
def prefixEnd_7959818 : Nat := 4983230072969 + 3 ^ 40 * 7959818 * 2
def baseEnd_7959818 : Nat := 1362404185436614469722823

theorem tailTrace_7959818 : CollatzResearch.WordTrace tailWord_7959818 prefixEnd_7959818 1362404185436614469722823 := by
  unfold tailWord_7959818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72579603269236572382466027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193545608717964193019909405 72579603269236572382466027)
  ·
    refine ⟨108869404903854858573699041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72579603269236572382466027 108869404903854858573699041)
    ·
      refine ⟨81652053677891143930274281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108869404903854858573699041 81652053677891143930274281)
      ·
        refine ⟨61239040258418357947705711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81652053677891143930274281 61239040258418357947705711)
        ·
          refine ⟨91858560387627536921558567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61239040258418357947705711 91858560387627536921558567)
          ·
            refine ⟨137787840581441305382337851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91858560387627536921558567 137787840581441305382337851)
            ·
              refine ⟨206681760872161958073506777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137787840581441305382337851 206681760872161958073506777)
              ·
                refine ⟨155011320654121468555130083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206681760872161958073506777 155011320654121468555130083)
                ·
                  refine ⟨232516980981182202832695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155011320654121468555130083 232516980981182202832695125)
                  ·
                    refine ⟨1362404185436614469722823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232516980981182202832695125 1362404185436614469722823)
                    ·
                      rfl

theorem cell23_7959818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_7959818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959818 prefixEnd_7959818 := by exact prefixLift 7959818
  have htrace : WordTrace (prefixWord ++ tailWord_7959818) baseStart_7959818 baseEnd_7959818 := by
    simpa [prefixWord, tailWord_7959818, baseEnd_7959818] using wordTrace_append hprefix tailTrace_7959818
  have hstable : (prefixWord ++ tailWord_7959818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959818).length < 2 ^ (prefixWord ++ tailWord_7959818).sum := by decide
  have hdescent : baseEnd_7959818 < baseStart_7959818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959832 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_7959832 : Nat := 118140960795 + 7959832 * 2 ^ 59
def prefixEnd_7959832 : Nat := 4983230072969 + 3 ^ 40 * 7959832 * 2
def baseEnd_7959832 : Nat := 4087219745039006354393405

theorem tailTrace_7959832 : CollatzResearch.WordTrace tailWord_7959832 prefixEnd_7959832 4087219745039006354393405 := by
  unfold tailWord_7959832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145159461849447784960436875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193545949132597046613915833 145159461849447784960436875)
  ·
    refine ⟨217739192774171677440655313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145159461849447784960436875 217739192774171677440655313)
    ·
      refine ⟨163304394580628758080491485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217739192774171677440655313 163304394580628758080491485)
      ·
        refine ⟨61239147967735784280184307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163304394580628758080491485 61239147967735784280184307)
        ·
          refine ⟨91858721951603676420276461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61239147967735784280184307 91858721951603676420276461)
          ·
            refine ⟨34447020731851378657603673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91858721951603676420276461 34447020731851378657603673)
            ·
              refine ⟨25835265548888533993202755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34447020731851378657603673 25835265548888533993202755)
              ·
                refine ⟨38752898323332800989804133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25835265548888533993202755 38752898323332800989804133)
                ·
                  refine ⟨7266168435624900185588275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38752898323332800989804133 7266168435624900185588275)
                  ·
                    refine ⟨10899252653437350278382413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7266168435624900185588275 10899252653437350278382413)
                    ·
                      refine ⟨4087219745039006354393405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10899252653437350278382413 4087219745039006354393405)
                      ·
                        rfl

theorem cell23_7959832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_7959832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959832 prefixEnd_7959832 := by exact prefixLift 7959832
  have htrace : WordTrace (prefixWord ++ tailWord_7959832) baseStart_7959832 baseEnd_7959832 := by
    simpa [prefixWord, tailWord_7959832, baseEnd_7959832] using wordTrace_append hprefix tailTrace_7959832
  have hstable : (prefixWord ++ tailWord_7959832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959832).length < 2 ^ (prefixWord ++ tailWord_7959832).sum := by decide
  have hdescent : baseEnd_7959832 < baseStart_7959832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959859 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 1, 3, 2]
def baseStart_7959859 : Nat := 118140960795 + 7959859 * 2 ^ 59
def prefixEnd_7959859 : Nat := 4983230072969 + 3 ^ 40 * 7959859 * 2
def baseEnd_7959859 : Nat := 4087233609016677748755781

theorem tailTrace_7959859 : CollatzResearch.WordTrace tailWord_7959859 prefixEnd_7959859 4087233609016677748755781 := by
  unfold tailWord_7959859
  simp only [CollatzResearch.WordTrace]
  refine ⟨290319908469797753532106631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193546605646531835688071087 290319908469797753532106631)
  ·
    refine ⟨435479862704696630298159947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290319908469797753532106631 435479862704696630298159947)
    ·
      refine ⟨653219794057044945447239921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435479862704696630298159947 653219794057044945447239921)
      ·
        refine ⟨489914845542783709085429941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653219794057044945447239921 489914845542783709085429941)
        ·
          refine ⟨45929516769635972726759057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489914845542783709085429941 45929516769635972726759057)
          ·
            refine ⟨34447137577226979545069293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45929516769635972726759057 34447137577226979545069293)
            ·
              refine ⟨12917676591460117329400985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34447137577226979545069293 12917676591460117329400985)
              ·
                refine ⟨9688257443595087997050739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12917676591460117329400985 9688257443595087997050739)
                ·
                  refine ⟨14532386165392631995576109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688257443595087997050739 14532386165392631995576109)
                  ·
                    refine ⟨5449644812022236998341041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14532386165392631995576109 5449644812022236998341041)
                    ·
                      refine ⟨4087233609016677748755781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449644812022236998341041 4087233609016677748755781)
                      ·
                        rfl

theorem cell23_7959859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3, 2].length) (baseStart_7959859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959859 prefixEnd_7959859 := by exact prefixLift 7959859
  have htrace : WordTrace (prefixWord ++ tailWord_7959859) baseStart_7959859 baseEnd_7959859 := by
    simpa [prefixWord, tailWord_7959859, baseEnd_7959859] using wordTrace_append hprefix tailTrace_7959859
  have hstable : (prefixWord ++ tailWord_7959859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959859).length < 2 ^ (prefixWord ++ tailWord_7959859).sum := by decide
  have hdescent : baseEnd_7959859 < baseStart_7959859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959872 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2]
def baseStart_7959872 : Nat := 118140960795 + 7959872 * 2 ^ 59
def prefixEnd_7959872 : Nat := 4983230072969 + 3 ^ 40 * 7959872 * 2
def baseEnd_7959872 : Nat := 4087240284265186197893221

theorem tailTrace_7959872 : CollatzResearch.WordTrace tailWord_7959872 prefixEnd_7959872 4087240284265186197893221 := by
  unfold tailWord_7959872
  simp only [CollatzResearch.WordTrace]
  refine ⟨145160191309375328376164935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193546921745833771168219913 145160191309375328376164935)
  ·
    refine ⟨217740286964062992564247403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145160191309375328376164935 217740286964062992564247403)
    ·
      refine ⟨326610430446094488846371105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217740286964062992564247403 326610430446094488846371105)
      ·
        refine ⟨244957822834570866634778329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326610430446094488846371105 244957822834570866634778329)
        ·
          refine ⟨183718367125928149976083747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244957822834570866634778329 183718367125928149976083747)
          ·
            refine ⟨275577550688892224964125621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183718367125928149976083747 275577550688892224964125621)
            ·
              refine ⟨25835395377083646090386777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275577550688892224964125621 25835395377083646090386777)
              ·
                refine ⟨19376546532812734567790083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25835395377083646090386777 19376546532812734567790083)
                ·
                  refine ⟨29064819799219101851685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19376546532812734567790083 29064819799219101851685125)
                  ·
                    refine ⟨5449653712353581597190961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29064819799219101851685125 5449653712353581597190961)
                    ·
                      refine ⟨4087240284265186197893221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449653712353581597190961 4087240284265186197893221)
                      ·
                        rfl

theorem cell23_7959872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_7959872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959872 prefixEnd_7959872 := by exact prefixLift 7959872
  have htrace : WordTrace (prefixWord ++ tailWord_7959872) baseStart_7959872 baseEnd_7959872 := by
    simpa [prefixWord, tailWord_7959872, baseEnd_7959872] using wordTrace_append hprefix tailTrace_7959872
  have hstable : (prefixWord ++ tailWord_7959872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959872).length < 2 ^ (prefixWord ++ tailWord_7959872).sum := by decide
  have hdescent : baseEnd_7959872 < baseStart_7959872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959906 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7959906 : Nat := 118140960795 + 7959906 * 2 ^ 59
def prefixEnd_7959906 : Nat := 4983230072969 + 3 ^ 40 * 7959906 * 2
def baseEnd_7959906 : Nat := 4087257742607439064868065

theorem tailTrace_7959906 : CollatzResearch.WordTrace tailWord_7959906 prefixEnd_7959906 4087257742607439064868065 := by
  unfold tailWord_7959906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72580405675156870139766893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193547748467084987039378381 72580405675156870139766893)
  ·
    refine ⟨27217652128183826302412585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72580405675156870139766893 27217652128183826302412585)
    ·
      refine ⟨20413239096137869726809439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27217652128183826302412585 20413239096137869726809439)
      ·
        refine ⟨30619858644206804590214159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20413239096137869726809439 30619858644206804590214159)
        ·
          refine ⟨45929787966310206885321239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30619858644206804590214159 45929787966310206885321239)
          ·
            refine ⟨68894681949465310327981859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45929787966310206885321239 68894681949465310327981859)
            ·
              refine ⟨103342022924197965491972789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68894681949465310327981859 103342022924197965491972789)
              ·
                refine ⟨9688314649143559264872449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103342022924197965491972789 9688314649143559264872449)
                ·
                  refine ⟨7266235986857669448654337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9688314649143559264872449 7266235986857669448654337)
                  ·
                    refine ⟨5449676990143252086490753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7266235986857669448654337 5449676990143252086490753)
                    ·
                      refine ⟨4087257742607439064868065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449676990143252086490753 4087257742607439064868065)
                      ·
                        rfl

theorem cell23_7959906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7959906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959906 prefixEnd_7959906 := by exact prefixLift 7959906
  have htrace : WordTrace (prefixWord ++ tailWord_7959906) baseStart_7959906 baseEnd_7959906 := by
    simpa [prefixWord, tailWord_7959906, baseEnd_7959906] using wordTrace_append hprefix tailTrace_7959906
  have hstable : (prefixWord ++ tailWord_7959906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959906).length < 2 ^ (prefixWord ++ tailWord_7959906).sum := by decide
  have hdescent : baseEnd_7959906 < baseStart_7959906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959912 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 7]
def baseStart_7959912 : Nat := 118140960795 + 7959912 * 2 ^ 59
def prefixEnd_7959912 : Nat := 4983230072969 + 3 ^ 40 * 7959912 * 2
def baseEnd_7959912 : Nat := 454140091499040671265893

theorem tailTrace_7959912 : CollatzResearch.WordTrace tailWord_7959912 prefixEnd_7959912 454140091499040671265893 := by
  unfold tailWord_7959912
  simp only [CollatzResearch.WordTrace]
  refine ⟨145160920769302871791892995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193547894359070495722523993 145160920769302871791892995)
  ·
    refine ⟨217741381153954307687839493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145160920769302871791892995 217741381153954307687839493)
    ·
      refine ⟨40826508966366432691469905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217741381153954307687839493 40826508966366432691469905)
      ·
        refine ⟨30619881724774824518602429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40826508966366432691469905 30619881724774824518602429)
        ·
          refine ⟨11482455646790559194475911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30619881724774824518602429 11482455646790559194475911)
          ·
            refine ⟨17223683470185838791713867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482455646790559194475911 17223683470185838791713867)
            ·
              refine ⟨25835525205278758187570801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17223683470185838791713867 25835525205278758187570801)
              ·
                refine ⟨19376643903959068640678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25835525205278758187570801 19376643903959068640678101)
                ·
                  refine ⟨454140091499040671265893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19376643903959068640678101 454140091499040671265893)
                  ·
                    rfl

theorem cell23_7959912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_7959912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959912 prefixEnd_7959912 := by exact prefixLift 7959912
  have htrace : WordTrace (prefixWord ++ tailWord_7959912) baseStart_7959912 baseEnd_7959912 := by
    simpa [prefixWord, tailWord_7959912, baseEnd_7959912] using wordTrace_append hprefix tailTrace_7959912
  have hstable : (prefixWord ++ tailWord_7959912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959912).length < 2 ^ (prefixWord ++ tailWord_7959912).sum := by decide
  have hdescent : baseEnd_7959912 < baseStart_7959912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959985 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 10]
def baseStart_7959985 : Nat := 118140960795 + 7959985 * 2 ^ 59
def prefixEnd_7959985 : Nat := 4983230072969 + 3 ^ 40 * 7959985 * 2
def baseEnd_7959985 : Nat := 454144256397682695086689

theorem tailTrace_7959985 : CollatzResearch.WordTrace tailWord_7959985 prefixEnd_7959985 454144256397682695086689 := by
  unfold tailWord_7959985
  simp only [CollatzResearch.WordTrace]
  refine ⟨290324504067341277051193409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193549669378227518034128939 290324504067341277051193409)
  ·
    refine ⟨217743378050505957788395057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290324504067341277051193409 217743378050505957788395057)
    ·
      refine ⟨163307533537879468341296293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217743378050505957788395057 163307533537879468341296293)
      ·
        refine ⟨30620162538352400313993055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163307533537879468341296293 30620162538352400313993055)
        ·
          refine ⟨45930243807528600470989583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30620162538352400313993055 45930243807528600470989583)
          ·
            refine ⟨68895365711292900706484375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45930243807528600470989583 68895365711292900706484375)
            ·
              refine ⟨103343048566939351059726563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68895365711292900706484375 103343048566939351059726563)
              ·
                refine ⟨155014572850409026589589845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103343048566939351059726563 155014572850409026589589845)
                ·
                  refine ⟨454144256397682695086689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155014572850409026589589845 454144256397682695086689)
                  ·
                    rfl

theorem cell23_7959985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_7959985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959985 prefixEnd_7959985 := by exact prefixLift 7959985
  have htrace : WordTrace (prefixWord ++ tailWord_7959985) baseStart_7959985 baseEnd_7959985 := by
    simpa [prefixWord, tailWord_7959985, baseEnd_7959985] using wordTrace_append hprefix tailTrace_7959985
  have hstable : (prefixWord ++ tailWord_7959985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959985).length < 2 ^ (prefixWord ++ tailWord_7959985).sum := by decide
  have hdescent : baseEnd_7959985 < baseStart_7959985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960032 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_7960032 : Nat := 118140960795 + 7960032 * 2 ^ 59
def prefixEnd_7960032 : Nat := 4983230072969 + 3 ^ 40 * 7960032 * 2
def baseEnd_7960032 : Nat := 1362440813723301857297495

theorem tailTrace_7960032 : CollatzResearch.WordTrace tailWord_7960032 prefixEnd_7960032 1362440813723301857297495 := by
  unfold tailWord_7960032
  simp only [CollatzResearch.WordTrace]
  refine ⟨145163109149085502039077175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193550812198780669385436233 145163109149085502039077175)
  ·
    refine ⟨217744663723628253058615763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145163109149085502039077175 217744663723628253058615763)
    ·
      refine ⟨326616995585442379587923645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217744663723628253058615763 326616995585442379587923645)
      ·
        refine ⟨122481373344540892345471367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326616995585442379587923645 122481373344540892345471367)
        ·
          refine ⟨183722060016811338518207051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122481373344540892345471367 183722060016811338518207051)
          ·
            refine ⟨275583090025217007777310577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183722060016811338518207051 275583090025217007777310577)
            ·
              refine ⟨206687317518912755832982933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275583090025217007777310577 206687317518912755832982933)
              ·
                refine ⟨9688468008699035429671075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206687317518912755832982933 9688468008699035429671075)
                ·
                  refine ⟨14532702013048553144506613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688468008699035429671075 14532702013048553144506613)
                  ·
                    refine ⟨1362440813723301857297495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14532702013048553144506613 1362440813723301857297495)
                    ·
                      rfl

theorem cell23_7960032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_7960032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960032 prefixEnd_7960032 := by exact prefixLift 7960032
  have htrace : WordTrace (prefixWord ++ tailWord_7960032) baseStart_7960032 baseEnd_7960032 := by
    simpa [prefixWord, tailWord_7960032, baseEnd_7960032] using wordTrace_append hprefix tailTrace_7960032
  have hstable : (prefixWord ++ tailWord_7960032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960032).length < 2 ^ (prefixWord ++ tailWord_7960032).sum := by decide
  have hdescent : baseEnd_7960032 < baseStart_7960032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960072 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_7960072 : Nat := 118140960795 + 7960072 * 2 ^ 59
def prefixEnd_7960072 : Nat := 4983230072969 + 3 ^ 40 * 7960072 * 2
def baseEnd_7960072 : Nat := 4087342980396085415392301

theorem tailTrace_7960072 : CollatzResearch.WordTrace tailWord_7960072 prefixEnd_7960072 4087342980396085415392301 := by
  unfold tailWord_7960072
  simp only [CollatzResearch.WordTrace]
  refine ⟨145163838609013045454805235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193551784812017393939740313 145163838609013045454805235)
  ·
    refine ⟨217745757913519568182207853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145163838609013045454805235 217745757913519568182207853)
    ·
      refine ⟨81654659217569838068327945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217745757913519568182207853 81654659217569838068327945)
      ·
        refine ⟨61240994413177378551245959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81654659217569838068327945 61240994413177378551245959)
        ·
          refine ⟨91861491619766067826868939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61240994413177378551245959 91861491619766067826868939)
          ·
            refine ⟨137792237429649101740303409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91861491619766067826868939 137792237429649101740303409)
            ·
              refine ⟨103344178072236826305227557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137792237429649101740303409 103344178072236826305227557)
              ·
                refine ⟨19377033388544404932230167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103344178072236826305227557 19377033388544404932230167)
                ·
                  refine ⟨29065550082816607398345251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19377033388544404932230167 29065550082816607398345251)
                  ·
                    refine ⟨43598325124224911097517877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29065550082816607398345251 43598325124224911097517877)
                    ·
                      refine ⟨4087342980396085415392301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43598325124224911097517877 4087342980396085415392301)
                      ·
                        rfl

theorem cell23_7960072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_7960072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960072 prefixEnd_7960072 := by exact prefixLift 7960072
  have htrace : WordTrace (prefixWord ++ tailWord_7960072) baseStart_7960072 baseEnd_7960072 := by
    simpa [prefixWord, tailWord_7960072, baseEnd_7960072] using wordTrace_append hprefix tailTrace_7960072
  have hstable : (prefixWord ++ tailWord_7960072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960072).length < 2 ^ (prefixWord ++ tailWord_7960072).sum := by decide
  have hdescent : baseEnd_7960072 < baseStart_7960072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960106 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7960106 : Nat := 118140960795 + 7960106 * 2 ^ 59
def prefixEnd_7960106 : Nat := 4983230072969 + 3 ^ 40 * 7960106 * 2
def baseEnd_7960106 : Nat := 4087360438738338282367145

theorem tailTrace_7960106 : CollatzResearch.WordTrace tailWord_7960106 prefixEnd_7960106 4087360438738338282367145 := by
  unfold tailWord_7960106
  simp only [CollatzResearch.WordTrace]
  refine ⟨72582229324975728679087043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193552611533268609810898781 72582229324975728679087043)
  ·
    refine ⟨108873343987463593018630565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72582229324975728679087043 108873343987463593018630565)
    ·
      refine ⟨20413751997649423690993231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108873343987463593018630565 20413751997649423690993231)
      ·
        refine ⟨30620627996474135536489847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20413751997649423690993231 30620627996474135536489847)
        ·
          refine ⟨45930941994711203304734771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30620627996474135536489847 45930941994711203304734771)
          ·
            refine ⟨68896412992066804957102157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45930941994711203304734771 68896412992066804957102157)
            ·
              refine ⟨25836154872025051858913309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68896412992066804957102157 25836154872025051858913309)
              ·
                refine ⟨9688558077009394447092491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25836154872025051858913309 9688558077009394447092491)
                ·
                  refine ⟨14532837115514091670638737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688558077009394447092491 14532837115514091670638737)
                  ·
                    refine ⟨10899627836635568752979053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14532837115514091670638737 10899627836635568752979053)
                    ·
                      refine ⟨4087360438738338282367145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10899627836635568752979053 4087360438738338282367145)
                      ·
                        rfl

theorem cell23_7960106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7960106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960106 prefixEnd_7960106 := by exact prefixLift 7960106
  have htrace : WordTrace (prefixWord ++ tailWord_7960106) baseStart_7960106 baseEnd_7960106 := by
    simpa [prefixWord, tailWord_7960106, baseEnd_7960106] using wordTrace_append hprefix tailTrace_7960106
  have hstable : (prefixWord ++ tailWord_7960106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960106).length < 2 ^ (prefixWord ++ tailWord_7960106).sum := by decide
  have hdescent : baseEnd_7960106 < baseStart_7960106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960229 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_7960229 : Nat := 118140960795 + 7960229 * 2 ^ 59
def prefixEnd_7960229 : Nat := 4983230072969 + 3 ^ 40 * 7960229 * 2
def baseEnd_7960229 : Nat := 1362474532286280433709693

theorem tailTrace_7960229 : CollatzResearch.WordTrace tailWord_7960229 prefixEnd_7960229 1362474532286280433709693 := by
  unfold tailWord_7960229
  simp only [CollatzResearch.WordTrace]
  refine ⟨290333403478457306723075741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193555602318971537815383827 290333403478457306723075741)
  ·
    refine ⟨108875026304421490021153403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290333403478457306723075741 108875026304421490021153403)
    ·
      refine ⟨163312539456632235031730105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108875026304421490021153403 163312539456632235031730105)
      ·
        refine ⟨122484404592474176273797579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163312539456632235031730105 122484404592474176273797579)
        ·
          refine ⟨183726606888711264410696369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122484404592474176273797579 183726606888711264410696369)
          ·
            refine ⟨137794955166533448308022277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183726606888711264410696369 137794955166533448308022277)
            ·
              refine ⟨25836554093725021557754177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137794955166533448308022277 25836554093725021557754177)
              ·
                refine ⟨19377415570293766168315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25836554093725021557754177 19377415570293766168315633)
                ·
                  refine ⟨14533061677720324626236725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19377415570293766168315633 14533061677720324626236725)
                  ·
                    refine ⟨1362474532286280433709693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14533061677720324626236725 1362474532286280433709693)
                    ·
                      rfl

theorem cell23_7960229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_7960229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960229 prefixEnd_7960229 := by exact prefixLift 7960229
  have htrace : WordTrace (prefixWord ++ tailWord_7960229) baseStart_7960229 baseEnd_7960229 := by
    simpa [prefixWord, tailWord_7960229, baseEnd_7960229] using wordTrace_append hprefix tailTrace_7960229
  have hstable : (prefixWord ++ tailWord_7960229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960229).length < 2 ^ (prefixWord ++ tailWord_7960229).sum := by decide
  have hdescent : baseEnd_7960229 < baseStart_7960229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960249 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7960249 : Nat := 118140960795 + 7960249 * 2 ^ 59
def prefixEnd_7960249 : Nat := 4983230072969 + 3 ^ 40 * 7960249 * 2
def baseEnd_7960249 : Nat := 4087433866471931222878987

theorem tailTrace_7960249 : CollatzResearch.WordTrace tailWord_7960249 prefixEnd_7960249 4087433866471931222878987 := by
  unfold tailWord_7960249
  simp only [CollatzResearch.WordTrace]
  refine ⟨290334132938384850138803801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193556088625589900092535867 290334132938384850138803801)
  ·
    refine ⟨217750599703788637604102851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290334132938384850138803801 217750599703788637604102851)
    ·
      refine ⟨326625899555682956406154277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217750599703788637604102851 326625899555682956406154277)
      ·
        refine ⟨61242356166690554326153927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326625899555682956406154277 61242356166690554326153927)
        ·
          refine ⟨91863534250035831489230891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61242356166690554326153927 91863534250035831489230891)
          ·
            refine ⟨137795301375053747233846337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91863534250035831489230891 137795301375053747233846337)
            ·
              refine ⟨103346476031290310425384753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137795301375053747233846337 103346476031290310425384753)
              ·
                refine ⟨77509857023467732819038565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103346476031290310425384753 77509857023467732819038565)
                ·
                  refine ⟨14533098191900199903569731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77509857023467732819038565 14533098191900199903569731)
                  ·
                    refine ⟨21799647287850299855354597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14533098191900199903569731 21799647287850299855354597)
                    ·
                      refine ⟨4087433866471931222878987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21799647287850299855354597 4087433866471931222878987)
                      ·
                        rfl

theorem cell23_7960249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7960249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960249 prefixEnd_7960249 := by exact prefixLift 7960249
  have htrace : WordTrace (prefixWord ++ tailWord_7960249) baseStart_7960249 baseEnd_7960249 := by
    simpa [prefixWord, tailWord_7960249, baseEnd_7960249] using wordTrace_append hprefix tailTrace_7960249
  have hstable : (prefixWord ++ tailWord_7960249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960249).length < 2 ^ (prefixWord ++ tailWord_7960249).sum := by decide
  have hdescent : baseEnd_7960249 < baseStart_7960249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960266 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_7960266 : Nat := 118140960795 + 7960266 * 2 ^ 59
def prefixEnd_7960266 : Nat := 4983230072969 + 3 ^ 40 * 7960266 * 2
def baseEnd_7960266 : Nat := 4087442595643057656366409

theorem tailTrace_7960266 : CollatzResearch.WordTrace tailWord_7960266 prefixEnd_7960266 4087442595643057656366409 := by
  unfold tailWord_7960266
  simp only [CollatzResearch.WordTrace]
  refine ⟨72583688244830815510543163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193556501986215508028115101 72583688244830815510543163)
  ·
    refine ⟨108875532367246223265814745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72583688244830815510543163 108875532367246223265814745)
    ·
      refine ⟨81656649275434667449361059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108875532367246223265814745 81656649275434667449361059)
      ·
        refine ⟨122484973913152001174041589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81656649275434667449361059 122484973913152001174041589)
        ·
          refine ⟨11482966304358000110066399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122484973913152001174041589 11482966304358000110066399)
          ·
            refine ⟨17224449456537000165099599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482966304358000110066399 17224449456537000165099599)
            ·
              refine ⟨25836674184805500247649399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17224449456537000165099599 25836674184805500247649399)
              ·
                refine ⟨38755011277208250371474099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25836674184805500247649399 38755011277208250371474099)
                ·
                  refine ⟨58132516915812375557211149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38755011277208250371474099 58132516915812375557211149)
                  ·
                    refine ⟨21799693843429640833954181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58132516915812375557211149 21799693843429640833954181)
                    ·
                      refine ⟨4087442595643057656366409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21799693843429640833954181 4087442595643057656366409)
                      ·
                        rfl

theorem cell23_7960266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_7960266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960266 prefixEnd_7960266 := by exact prefixLift 7960266
  have htrace : WordTrace (prefixWord ++ tailWord_7960266) baseStart_7960266 baseEnd_7960266 := by
    simpa [prefixWord, tailWord_7960266, baseEnd_7960266] using wordTrace_append hprefix tailTrace_7960266
  have hstable : (prefixWord ++ tailWord_7960266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960266).length < 2 ^ (prefixWord ++ tailWord_7960266).sum := by decide
  have hdescent : baseEnd_7960266 < baseStart_7960266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960293 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_7960293 : Nat := 118140960795 + 7960293 * 2 ^ 59
def prefixEnd_7960293 : Nat := 4983230072969 + 3 ^ 40 * 7960293 * 2
def baseEnd_7960293 : Nat := 1362485486540243016909595

theorem tailTrace_7960293 : CollatzResearch.WordTrace tailWord_7960293 prefixEnd_7960293 1362485486540243016909595 := by
  unfold tailWord_7960293
  simp only [CollatzResearch.WordTrace]
  refine ⟨290335737750225445653405533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193557158500150297102270355 290335737750225445653405533)
  ·
    refine ⟨108875901656334542120027075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290335737750225445653405533 108875901656334542120027075)
    ·
      refine ⟨163313852484501813180040613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108875901656334542120027075 163313852484501813180040613)
      ·
        refine ⟨30621347340844089971257615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163313852484501813180040613 30621347340844089971257615)
        ·
          refine ⟨45932021011266134956886423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30621347340844089971257615 45932021011266134956886423)
          ·
            refine ⟨68898031516899202435329635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45932021011266134956886423 68898031516899202435329635)
            ·
              refine ⟨103347047275348803652994453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68898031516899202435329635 103347047275348803652994453)
              ·
                refine ⟨4844392841031975171234115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103347047275348803652994453 4844392841031975171234115)
                ·
                  refine ⟨7266589261547962756851173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844392841031975171234115 7266589261547962756851173)
                  ·
                    refine ⟨1362485486540243016909595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7266589261547962756851173 1362485486540243016909595)
                    ·
                      rfl

theorem cell23_7960293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_7960293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960293 prefixEnd_7960293 := by exact prefixLift 7960293
  have htrace : WordTrace (prefixWord ++ tailWord_7960293) baseStart_7960293 baseEnd_7960293 := by
    simpa [prefixWord, tailWord_7960293, baseEnd_7960293] using wordTrace_append hprefix tailTrace_7960293
  have hstable : (prefixWord ++ tailWord_7960293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960293).length < 2 ^ (prefixWord ++ tailWord_7960293).sum := by decide
  have hdescent : baseEnd_7960293 < baseStart_7960293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960319 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 3, 5]
def baseStart_7960319 : Nat := 118140960795 + 7960319 * 2 ^ 59
def prefixEnd_7960319 : Nat := 4983230072969 + 3 ^ 40 * 7960319 * 2
def baseEnd_7960319 : Nat := 1362489936705915316334555

theorem tailTrace_7960319 : CollatzResearch.WordTrace tailWord_7960319 prefixEnd_7960319 1362489936705915316334555 := by
  unfold tailWord_7960319
  simp only [CollatzResearch.WordTrace]
  refine ⟨290336686048131252093852011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193557790698754168062568007 290336686048131252093852011)
  ·
    refine ⟨435505029072196878140778017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290336686048131252093852011 435505029072196878140778017)
    ·
      refine ⟨326628771804147658605583513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435505029072196878140778017 326628771804147658605583513)
      ·
        refine ⟨244971578853110743954187635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326628771804147658605583513 244971578853110743954187635)
        ·
          refine ⟨367457368279666115931281453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244971578853110743954187635 367457368279666115931281453)
          ·
            refine ⟨137796513104874793474230545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367457368279666115931281453 137796513104874793474230545)
            ·
              refine ⟨103347384828656095105672909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137796513104874793474230545 103347384828656095105672909)
              ·
                refine ⟨38755269310746035664627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103347384828656095105672909 38755269310746035664627341)
                ·
                  refine ⟨14533225991529763374235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38755269310746035664627341 14533225991529763374235253)
                  ·
                    refine ⟨1362489936705915316334555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14533225991529763374235253 1362489936705915316334555)
                    ·
                      rfl

theorem cell23_7960319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_7960319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960319 prefixEnd_7960319 := by exact prefixLift 7960319
  have htrace : WordTrace (prefixWord ++ tailWord_7960319) baseStart_7960319 baseEnd_7960319 := by
    simpa [prefixWord, tailWord_7960319, baseEnd_7960319] using wordTrace_append hprefix tailTrace_7960319
  have hstable : (prefixWord ++ tailWord_7960319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960319).length < 2 ^ (prefixWord ++ tailWord_7960319).sum := by decide
  have hdescent : baseEnd_7960319 < baseStart_7960319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960327 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 1, 4]
def baseStart_7960327 : Nat := 118140960795 + 7960327 * 2 ^ 59
def prefixEnd_7960327 : Nat := 4983230072969 + 3 ^ 40 * 7960327 * 2
def baseEnd_7960327 : Nat := 1362491305987660639234543

theorem tailTrace_7960327 : CollatzResearch.WordTrace tailWord_7960327 prefixEnd_7960327 1362491305987660639234543 := by
  unfold tailWord_7960327
  simp only [CollatzResearch.WordTrace]
  refine ⟨290336977832102269460143235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193557985221401512973428823 290336977832102269460143235)
  ·
    refine ⟨435505466748153404190214853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290336977832102269460143235 435505466748153404190214853)
    ·
      refine ⟨81657275015278763285665285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435505466748153404190214853 81657275015278763285665285)
      ·
        refine ⟨15310739065364768116062241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81657275015278763285665285 15310739065364768116062241)
        ·
          refine ⟨11483054299023576087046681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15310739065364768116062241 11483054299023576087046681)
          ·
            refine ⟨8612290724267682065285011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483054299023576087046681 8612290724267682065285011)
            ·
              refine ⟨12918436086401523097927517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612290724267682065285011 12918436086401523097927517)
              ·
                refine ⟨4844413532400571161722819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12918436086401523097927517 4844413532400571161722819)
                ·
                  refine ⟨7266620298600856742584229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844413532400571161722819 7266620298600856742584229)
                  ·
                    refine ⟨1362491305987660639234543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7266620298600856742584229 1362491305987660639234543)
                    ·
                      rfl

theorem cell23_7960327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_7960327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960327 prefixEnd_7960327 := by exact prefixLift 7960327
  have htrace : WordTrace (prefixWord ++ tailWord_7960327) baseStart_7960327 baseEnd_7960327 := by
    simpa [prefixWord, tailWord_7960327, baseEnd_7960327] using wordTrace_append hprefix tailTrace_7960327
  have hstable : (prefixWord ++ tailWord_7960327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960327).length < 2 ^ (prefixWord ++ tailWord_7960327).sum := by decide
  have hdescent : baseEnd_7960327 < baseStart_7960327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960343 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7960343 : Nat := 118140960795 + 7960343 * 2 ^ 59
def prefixEnd_7960343 : Nat := 4983230072969 + 3 ^ 40 * 7960343 * 2
def baseEnd_7960343 : Nat := 4087482133653453855103555

theorem tailTrace_7960343 : CollatzResearch.WordTrace tailWord_7960343 prefixEnd_7960343 4087482133653453855103555 := by
  unfold tailWord_7960343
  simp only [CollatzResearch.WordTrace]
  refine ⟨290337561400044304192725683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193558374266696202795150455 290337561400044304192725683)
  ·
    refine ⟨435506342100066456289088525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290337561400044304192725683 435506342100066456289088525)
    ·
      refine ⟨163314878287524921108408197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435506342100066456289088525 163314878287524921108408197)
      ·
        refine ⟨30621539678910922707826537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163314878287524921108408197 30621539678910922707826537)
        ·
          refine ⟨22966154759183192030869903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30621539678910922707826537 22966154759183192030869903)
          ·
            refine ⟨34449232138774788046304855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22966154759183192030869903 34449232138774788046304855)
            ·
              refine ⟨51673848208162182069457283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34449232138774788046304855 51673848208162182069457283)
              ·
                refine ⟨77510772312243273104185925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51673848208162182069457283 77510772312243273104185925)
                ·
                  refine ⟨14533269808545613707034861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77510772312243273104185925 14533269808545613707034861)
                  ·
                    refine ⟨5449976178204605140138073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14533269808545613707034861 5449976178204605140138073)
                    ·
                      refine ⟨4087482133653453855103555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449976178204605140138073 4087482133653453855103555)
                      ·
                        rfl

theorem cell23_7960343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7960343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960343 prefixEnd_7960343 := by exact prefixLift 7960343
  have htrace : WordTrace (prefixWord ++ tailWord_7960343) baseStart_7960343 baseEnd_7960343 := by
    simpa [prefixWord, tailWord_7960343, baseEnd_7960343] using wordTrace_append hprefix tailTrace_7960343
  have hstable : (prefixWord ++ tailWord_7960343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960343).length < 2 ^ (prefixWord ++ tailWord_7960343).sum := by decide
  have hdescent : baseEnd_7960343 < baseStart_7960343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960373 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_7960373 : Nat := 118140960795 + 7960373 * 2 ^ 59
def prefixEnd_7960373 : Nat := 4983230072969 + 3 ^ 40 * 7960373 * 2
def baseEnd_7960373 : Nat := 4087497538073088737728417

theorem tailTrace_7960373 : CollatzResearch.WordTrace tailWord_7960373 prefixEnd_7960373 4087497538073088737728417 := by
  unfold tailWord_7960373
  simp only [CollatzResearch.WordTrace]
  refine ⟨290338655589935619316317773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193559103726623746210878515 290338655589935619316317773)
  ·
    refine ⟨108876995846225857243619165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290338655589935619316317773 108876995846225857243619165)
    ·
      refine ⟨40828873442334696466357187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108876995846225857243619165 40828873442334696466357187)
      ·
        refine ⟨61243310163502044699535781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40828873442334696466357187 61243310163502044699535781)
        ·
          refine ⟨11483120655656633381162959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61243310163502044699535781 11483120655656633381162959)
          ·
            refine ⟨17224680983484950071744439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483120655656633381162959 17224680983484950071744439)
            ·
              refine ⟨25837021475227425107616659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17224680983484950071744439 25837021475227425107616659)
              ·
                refine ⟨38755532212841137661424989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25837021475227425107616659 38755532212841137661424989)
                ·
                  refine ⟨14533324579815426623034371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38755532212841137661424989 14533324579815426623034371)
                  ·
                    refine ⟨21799986869723139934551557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14533324579815426623034371 21799986869723139934551557)
                    ·
                      refine ⟨4087497538073088737728417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21799986869723139934551557 4087497538073088737728417)
                      ·
                        rfl

theorem cell23_7960373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_7960373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960373 prefixEnd_7960373 := by exact prefixLift 7960373
  have htrace : WordTrace (prefixWord ++ tailWord_7960373) baseStart_7960373 baseEnd_7960373 := by
    simpa [prefixWord, tailWord_7960373, baseEnd_7960373] using wordTrace_append hprefix tailTrace_7960373
  have hstable : (prefixWord ++ tailWord_7960373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960373).length < 2 ^ (prefixWord ++ tailWord_7960373).sum := by decide
  have hdescent : baseEnd_7960373 < baseStart_7960373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960377 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7960377 : Nat := 118140960795 + 7960377 * 2 ^ 59
def prefixEnd_7960377 : Nat := 4983230072969 + 3 ^ 40 * 7960377 * 2
def baseEnd_7960377 : Nat := 4087499591995706722078399

theorem tailTrace_7960377 : CollatzResearch.WordTrace tailWord_7960377 prefixEnd_7960377 4087499591995706722078399 := by
  unfold tailWord_7960377
  simp only [CollatzResearch.WordTrace]
  refine ⟨290338801481921127999463385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193559200987947418666308923 290338801481921127999463385)
  ·
    refine ⟨217754101111440845999597539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290338801481921127999463385 217754101111440845999597539)
    ·
      refine ⟨326631151667161268999396309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217754101111440845999597539 326631151667161268999396309)
      ·
        refine ⟨7655417617199092242173351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 326631151667161268999396309 7655417617199092242173351)
        ·
          refine ⟨11483126425798638363260027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655417617199092242173351 11483126425798638363260027)
          ·
            refine ⟨17224689638697957544890041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483126425798638363260027 17224689638697957544890041)
            ·
              refine ⟨12918517229023468158667531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17224689638697957544890041 12918517229023468158667531)
              ·
                refine ⟨19377775843535202238001297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918517229023468158667531 19377775843535202238001297)
                ·
                  refine ⟨14533331882651401678500973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19377775843535202238001297 14533331882651401678500973)
                  ·
                    refine ⟨5449999455994275629437865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14533331882651401678500973 5449999455994275629437865)
                    ·
                      refine ⟨4087499591995706722078399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449999455994275629437865 4087499591995706722078399)
                      ·
                        rfl

theorem cell23_7960377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7960377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960377 prefixEnd_7960377 := by exact prefixLift 7960377
  have htrace : WordTrace (prefixWord ++ tailWord_7960377) baseStart_7960377 baseEnd_7960377 := by
    simpa [prefixWord, tailWord_7960377, baseEnd_7960377] using wordTrace_append hprefix tailTrace_7960377
  have hstable : (prefixWord ++ tailWord_7960377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960377).length < 2 ^ (prefixWord ++ tailWord_7960377).sum := by decide
  have hdescent : baseEnd_7960377 < baseStart_7960377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960396 : List Nat := [2, 2, 1, 3, 5, 10]
def baseStart_7960396 : Nat := 118140960795 + 7960396 * 2 ^ 59
def prefixEnd_7960396 : Nat := 4983230072969 + 3 ^ 40 * 7960396 * 2
def baseEnd_7960396 : Nat := 16821026123984124064777

theorem tailTrace_7960396 : CollatzResearch.WordTrace tailWord_7960396 prefixEnd_7960396 16821026123984124064777 := by
  unfold tailWord_7960396
  simp only [CollatzResearch.WordTrace]
  refine ⟨145169747234426147122202521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193559662979234862829603361 145169747234426147122202521)
  ·
    refine ⟨108877310425819610341651891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145169747234426147122202521 108877310425819610341651891)
    ·
      refine ⟨163315965638729415512477837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108877310425819610341651891 163315965638729415512477837)
      ·
        refine ⟨61243487114523530817179189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163315965638729415512477837 61243487114523530817179189)
        ·
          refine ⟨5741576916986581014110549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61243487114523530817179189 5741576916986581014110549)
          ·
            refine ⟨16821026123984124064777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5741576916986581014110549 16821026123984124064777)
            ·
              rfl

theorem cell23_7960396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 10].length) (baseStart_7960396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960396 prefixEnd_7960396 := by exact prefixLift 7960396
  have htrace : WordTrace (prefixWord ++ tailWord_7960396) baseStart_7960396 baseEnd_7960396 := by
    simpa [prefixWord, tailWord_7960396, baseEnd_7960396] using wordTrace_append hprefix tailTrace_7960396
  have hstable : (prefixWord ++ tailWord_7960396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960396).length < 2 ^ (prefixWord ++ tailWord_7960396).sum := by decide
  have hdescent : baseEnd_7960396 < baseStart_7960396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960409 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_7960409 : Nat := 118140960795 + 7960409 * 2 ^ 59
def prefixEnd_7960409 : Nat := 4983230072969 + 3 ^ 40 * 7960409 * 2
def baseEnd_7960409 : Nat := 1362505341125550198959417

theorem tailTrace_7960409 : CollatzResearch.WordTrace tailWord_7960409 prefixEnd_7960409 1362505341125550198959417 := by
  unfold tailWord_7960409
  simp only [CollatzResearch.WordTrace]
  refine ⟨290339968617805197464628281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193559979078536798309752187 290339968617805197464628281)
  ·
    refine ⟨217754976463353898098471211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290339968617805197464628281 217754976463353898098471211)
    ·
      refine ⟨326632464695030847147706817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217754976463353898098471211 326632464695030847147706817)
      ·
        refine ⟨244974348521273135360780113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326632464695030847147706817 244974348521273135360780113)
        ·
          refine ⟨183730761390954851520585085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244974348521273135360780113 183730761390954851520585085)
          ·
            refine ⟨68899035521608069320219407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183730761390954851520585085 68899035521608069320219407)
            ·
              refine ⟨103348553282412103980329111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68899035521608069320219407 103348553282412103980329111)
              ·
                refine ⟨155022829923618155970493667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103348553282412103980329111 155022829923618155970493667)
                ·
                  refine ⟨232534244885427233955740501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155022829923618155970493667 232534244885427233955740501)
                  ·
                    refine ⟨1362505341125550198959417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232534244885427233955740501 1362505341125550198959417)
                    ·
                      rfl

theorem cell23_7960409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_7960409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960409 prefixEnd_7960409 := by exact prefixLift 7960409
  have htrace : WordTrace (prefixWord ++ tailWord_7960409) baseStart_7960409 baseEnd_7960409 := by
    simpa [prefixWord, tailWord_7960409, baseEnd_7960409] using wordTrace_append hprefix tailTrace_7960409
  have hstable : (prefixWord ++ tailWord_7960409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960409).length < 2 ^ (prefixWord ++ tailWord_7960409).sum := by decide
  have hdescent : baseEnd_7960409 < baseStart_7960409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960423 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_7960423 : Nat := 118140960795 + 7960423 * 2 ^ 59
def prefixEnd_7960423 : Nat := 4983230072969 + 3 ^ 40 * 7960423 * 2
def baseEnd_7960423 : Nat := 4087523212105813542103187

theorem tailTrace_7960423 : CollatzResearch.WordTrace tailWord_7960423 prefixEnd_7960423 4087523212105813542103187 := by
  unfold tailWord_7960423
  simp only [CollatzResearch.WordTrace]
  refine ⟨290340479239754477855637923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193560319493169651903758615 290340479239754477855637923)
  ·
    refine ⟨435510718859631716783456885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290340479239754477855637923 435510718859631716783456885)
    ·
      refine ⟨40829129893090473448449083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435510718859631716783456885 40829129893090473448449083)
      ·
        refine ⟨61243694839635710172673625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40829129893090473448449083 61243694839635710172673625)
        ·
          refine ⟨45932771129726782629505219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61243694839635710172673625 45932771129726782629505219)
          ·
            refine ⟨68899156694590173944257829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45932771129726782629505219 68899156694590173944257829)
            ·
              refine ⟨12918591880235657614548343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68899156694590173944257829 12918591880235657614548343)
              ·
                refine ⟨19377887820353486421822515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918591880235657614548343 19377887820353486421822515)
                ·
                  refine ⟨29066831730530229632733773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19377887820353486421822515 29066831730530229632733773)
                  ·
                    refine ⟨10900061898948836112275165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29066831730530229632733773 10900061898948836112275165)
                    ·
                      refine ⟨4087523212105813542103187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900061898948836112275165 4087523212105813542103187)
                      ·
                        rfl

theorem cell23_7960423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_7960423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960423 prefixEnd_7960423 := by exact prefixLift 7960423
  have htrace : WordTrace (prefixWord ++ tailWord_7960423) baseStart_7960423 baseEnd_7960423 := by
    simpa [prefixWord, tailWord_7960423, baseEnd_7960423] using wordTrace_append hprefix tailTrace_7960423
  have hstable : (prefixWord ++ tailWord_7960423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960423).length < 2 ^ (prefixWord ++ tailWord_7960423).sum := by decide
  have hdescent : baseEnd_7960423 < baseStart_7960423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960433 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_7960433 : Nat := 118140960795 + 7960433 * 2 ^ 59
def prefixEnd_7960433 : Nat := 4983230072969 + 3 ^ 40 * 7960433 * 2
def baseEnd_7960433 : Nat := 4087528346912358502978141

theorem tailTrace_7960433 : CollatzResearch.WordTrace tailWord_7960433 prefixEnd_7960433 4087528346912358502978141 := by
  unfold tailWord_7960433
  simp only [CollatzResearch.WordTrace]
  refine ⟨290340843969718249563501953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193560562646478833042334635 290340843969718249563501953)
  ·
    refine ⟨217755632977288687172626465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290340843969718249563501953 217755632977288687172626465)
    ·
      refine ⟨163316724732966515379469849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217755632977288687172626465 163316724732966515379469849)
      ·
        refine ⟨122487543549724886534602387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163316724732966515379469849 122487543549724886534602387)
        ·
          refine ⟨183731315324587329801903581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122487543549724886534602387 183731315324587329801903581)
          ·
            refine ⟨68899243246720248675713843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183731315324587329801903581 68899243246720248675713843)
            ·
              refine ⟨103348864870080373013570765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68899243246720248675713843 103348864870080373013570765)
              ·
                refine ⟨38755824326280139880089037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103348864870080373013570765 38755824326280139880089037)
                ·
                  refine ⟨14533434122355052455033389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38755824326280139880089037 14533434122355052455033389)
                  ·
                    refine ⟨5450037795883144670637521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14533434122355052455033389 5450037795883144670637521)
                    ·
                      refine ⟨4087528346912358502978141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450037795883144670637521 4087528346912358502978141)
                      ·
                        rfl

theorem cell23_7960433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_7960433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960433 prefixEnd_7960433 := by exact prefixLift 7960433
  have htrace : WordTrace (prefixWord ++ tailWord_7960433) baseStart_7960433 baseEnd_7960433 := by
    simpa [prefixWord, tailWord_7960433, baseEnd_7960433] using wordTrace_append hprefix tailTrace_7960433
  have hstable : (prefixWord ++ tailWord_7960433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960433).length < 2 ^ (prefixWord ++ tailWord_7960433).sum := by decide
  have hdescent : baseEnd_7960433 < baseStart_7960433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960523 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 5, 2]
def baseStart_7960523 : Nat := 118140960795 + 7960523 * 2 ^ 59
def prefixEnd_7960523 : Nat := 4983230072969 + 3 ^ 40 * 7960523 * 2
def baseEnd_7960523 : Nat := 4087574560171263150852727

theorem tailTrace_7960523 : CollatzResearch.WordTrace tailWord_7960523 prefixEnd_7960523 4087574560171263150852727 := by
  unfold tailWord_7960523
  simp only [CollatzResearch.WordTrace]
  refine ⟨290344126539392194934278223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193562751026261463289518815 290344126539392194934278223)
  ·
    refine ⟨435516189809088292401417335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290344126539392194934278223 435516189809088292401417335)
    ·
      refine ⟨653274284713632438602126003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435516189809088292401417335 653274284713632438602126003)
      ·
        refine ⟨979911427070448657903189005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653274284713632438602126003 979911427070448657903189005)
        ·
          refine ⟨367466785151418246713695877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979911427070448657903189005 367466785151418246713695877)
          ·
            refine ⟨68900022215890921258817977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367466785151418246713695877 68900022215890921258817977)
            ·
              refine ⟨51675016661918190944113483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68900022215890921258817977 51675016661918190944113483)
              ·
                refine ⟨77512524992877286416170225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51675016661918190944113483 77512524992877286416170225)
                ·
                  refine ⟨58134393744657964812127669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77512524992877286416170225 58134393744657964812127669)
                  ·
                    refine ⟨5450099413561684201136969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58134393744657964812127669 5450099413561684201136969)
                    ·
                      refine ⟨4087574560171263150852727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450099413561684201136969 4087574560171263150852727)
                      ·
                        rfl

theorem cell23_7960523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5, 2].length) (baseStart_7960523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960523 prefixEnd_7960523 := by exact prefixLift 7960523
  have htrace : WordTrace (prefixWord ++ tailWord_7960523) baseStart_7960523 baseEnd_7960523 := by
    simpa [prefixWord, tailWord_7960523, baseEnd_7960523] using wordTrace_append hprefix tailTrace_7960523
  have hstable : (prefixWord ++ tailWord_7960523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960523).length < 2 ^ (prefixWord ++ tailWord_7960523).sum := by decide
  have hdescent : baseEnd_7960523 < baseStart_7960523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960637 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7960637 : Nat := 118140960795 + 7960637 * 2 ^ 59
def prefixEnd_7960637 : Nat := 4983230072969 + 3 ^ 40 * 7960637 * 2
def baseEnd_7960637 : Nat := 4087633096965875704827203

theorem tailTrace_7960637 : CollatzResearch.WordTrace tailWord_7960637 prefixEnd_7960637 4087633096965875704827203 := by
  unfold tailWord_7960637
  simp only [CollatzResearch.WordTrace]
  refine ⟨290348284460979192403928165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193565522973986128269285443 290348284460979192403928165)
  ·
    refine ⟨54440303336433598575736531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290348284460979192403928165 54440303336433598575736531)
    ·
      refine ⟨81660455004650397863604797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54440303336433598575736531 81660455004650397863604797)
      ·
        refine ⟨30622670626743899198851799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81660455004650397863604797 30622670626743899198851799)
        ·
          refine ⟨45934005940115848798277699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30622670626743899198851799 45934005940115848798277699)
          ·
            refine ⟨68901008910173773197416549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45934005940115848798277699 68901008910173773197416549)
            ·
              refine ⟨12918939170657582474515603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68901008910173773197416549 12918939170657582474515603)
              ·
                refine ⟨19378408755986373711773405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918939170657582474515603 19378408755986373711773405)
                ·
                  refine ⟨7266903283494890141915027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19378408755986373711773405 7266903283494890141915027)
                  ·
                    refine ⟨10900354925242335212872541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7266903283494890141915027 10900354925242335212872541)
                    ·
                      refine ⟨4087633096965875704827203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900354925242335212872541 4087633096965875704827203)
                      ·
                        rfl

theorem cell23_7960637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7960637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960637 prefixEnd_7960637 := by exact prefixLift 7960637
  have htrace : WordTrace (prefixWord ++ tailWord_7960637) baseStart_7960637 baseEnd_7960637 := by
    simpa [prefixWord, tailWord_7960637, baseEnd_7960637] using wordTrace_append hprefix tailTrace_7960637
  have hstable : (prefixWord ++ tailWord_7960637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960637).length < 2 ^ (prefixWord ++ tailWord_7960637).sum := by decide
  have hdescent : baseEnd_7960637 < baseStart_7960637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960643 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4]
def baseStart_7960643 : Nat := 118140960795 + 7960643 * 2 ^ 59
def prefixEnd_7960643 : Nat := 4983230072969 + 3 ^ 40 * 7960643 * 2
def baseEnd_7960643 : Nat := 4087636177849802681352175

theorem tailTrace_7960643 : CollatzResearch.WordTrace tailWord_7960643 prefixEnd_7960643 4087636177849802681352175 := by
  unfold tailWord_7960643
  simp only [CollatzResearch.WordTrace]
  refine ⟨290348503298957455428646583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193565668865971636952431055 290348503298957455428646583)
  ·
    refine ⟨435522754948436183142969875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290348503298957455428646583 435522754948436183142969875)
    ·
      refine ⟨653284132422654274714454813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435522754948436183142969875 653284132422654274714454813)
      ·
        refine ⟨244981549658495353017920555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653284132422654274714454813 244981549658495353017920555)
        ·
          refine ⟨367472324487743029526880833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244981549658495353017920555 367472324487743029526880833)
          ·
            refine ⟨275604243365807272145160625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367472324487743029526880833 275604243365807272145160625)
            ·
              refine ⟨206703182524355454108870469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275604243365807272145160625 206703182524355454108870469)
              ·
                refine ⟨38756846723316647645413213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206703182524355454108870469 38756846723316647645413213)
                ·
                  refine ⟨14533817521243742867029955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38756846723316647645413213 14533817521243742867029955)
                  ·
                    refine ⟨21800726281865614300544933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14533817521243742867029955 21800726281865614300544933)
                    ·
                      refine ⟨4087636177849802681352175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21800726281865614300544933 4087636177849802681352175)
                      ·
                        rfl

theorem cell23_7960643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_7960643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960643 prefixEnd_7960643 := by exact prefixLift 7960643
  have htrace : WordTrace (prefixWord ++ tailWord_7960643) baseStart_7960643 baseEnd_7960643 := by
    simpa [prefixWord, tailWord_7960643, baseEnd_7960643] using wordTrace_append hprefix tailTrace_7960643
  have hstable : (prefixWord ++ tailWord_7960643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960643).length < 2 ^ (prefixWord ++ tailWord_7960643).sum := by decide
  have hdescent : baseEnd_7960643 < baseStart_7960643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960660 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_7960660 : Nat := 118140960795 + 7960660 * 2 ^ 59
def prefixEnd_7960660 : Nat := 4983230072969 + 3 ^ 40 * 7960660 * 2
def baseEnd_7960660 : Nat := 4087644907020929114839597

theorem tailTrace_7960660 : CollatzResearch.WordTrace tailWord_7960660 prefixEnd_7960660 4087644907020929114839597 := by
  unfold tailWord_7960660
  simp only [CollatzResearch.WordTrace]
  refine ⟨145174561669947933666007717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193566082226597244888010289 145174561669947933666007717)
  ·
    refine ⟨27220230313115237562376447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145174561669947933666007717 27220230313115237562376447)
    ·
      refine ⟨40830345469672856343564671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27220230313115237562376447 40830345469672856343564671)
      ·
        refine ⟨61245518204509284515347007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40830345469672856343564671 61245518204509284515347007)
        ·
          refine ⟨91868277306763926773020511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61245518204509284515347007 91868277306763926773020511)
          ·
            refine ⟨137802415960145890159530767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91868277306763926773020511 137802415960145890159530767)
            ·
              refine ⟨206703623940218835239296151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137802415960145890159530767 206703623940218835239296151)
              ·
                refine ⟨310055435910328252858944227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206703623940218835239296151 310055435910328252858944227)
                ·
                  refine ⟨465083153865492379288416341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310055435910328252858944227 465083153865492379288416341)
                  ·
                    refine ⟨5450193209361238819786129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 465083153865492379288416341 5450193209361238819786129)
                    ·
                      refine ⟨4087644907020929114839597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450193209361238819786129 4087644907020929114839597)
                      ·
                        rfl

theorem cell23_7960660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_7960660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960660 prefixEnd_7960660 := by exact prefixLift 7960660
  have htrace : WordTrace (prefixWord ++ tailWord_7960660) baseStart_7960660 baseEnd_7960660 := by
    simpa [prefixWord, tailWord_7960660, baseEnd_7960660] using wordTrace_append hprefix tailTrace_7960660
  have hstable : (prefixWord ++ tailWord_7960660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960660).length < 2 ^ (prefixWord ++ tailWord_7960660).sum := by decide
  have hdescent : baseEnd_7960660 < baseStart_7960660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960673 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7960673 : Nat := 118140960795 + 7960673 * 2 ^ 59
def prefixEnd_7960673 : Nat := 4983230072969 + 3 ^ 40 * 7960673 * 2
def baseEnd_7960673 : Nat := 4087651582269437563977037

theorem tailTrace_7960673 : CollatzResearch.WordTrace tailWord_7960673 prefixEnd_7960673 4087651582269437563977037 := by
  unfold tailWord_7960673
  simp only [CollatzResearch.WordTrace]
  refine ⟨290349597488848770552238673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193566398325899180368159115 290349597488848770552238673)
  ·
    refine ⟨217762198116636577914179005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290349597488848770552238673 217762198116636577914179005)
    ·
      refine ⟨81660824293738716717817127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217762198116636577914179005 81660824293738716717817127)
      ·
        refine ⟨122491236440608075076725691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81660824293738716717817127 122491236440608075076725691)
        ·
          refine ⟨183736854660912112615088537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122491236440608075076725691 183736854660912112615088537)
          ·
            refine ⟨137802640995684084461316403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183736854660912112615088537 137802640995684084461316403)
            ·
              refine ⟨206703961493526126691974605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137802640995684084461316403 206703961493526126691974605)
              ·
                refine ⟨77513985560072297509490477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206703961493526126691974605 77513985560072297509490477)
                ·
                  refine ⟨29067744585027111566058929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77513985560072297509490477 29067744585027111566058929)
                  ·
                    refine ⟨21800808438770333674544197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29067744585027111566058929 21800808438770333674544197)
                    ·
                      refine ⟨4087651582269437563977037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21800808438770333674544197 4087651582269437563977037)
                      ·
                        rfl

theorem cell23_7960673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7960673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960673 prefixEnd_7960673 := by exact prefixLift 7960673
  have htrace : WordTrace (prefixWord ++ tailWord_7960673) baseStart_7960673 baseEnd_7960673 := by
    simpa [prefixWord, tailWord_7960673, baseEnd_7960673] using wordTrace_append hprefix tailTrace_7960673
  have hstable : (prefixWord ++ tailWord_7960673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960673).length < 2 ^ (prefixWord ++ tailWord_7960673).sum := by decide
  have hdescent : baseEnd_7960673 < baseStart_7960673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960714 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7960714 : Nat := 118140960795 + 7960714 * 2 ^ 59
def prefixEnd_7960714 : Nat := 4983230072969 + 3 ^ 40 * 7960714 * 2
def baseEnd_7960714 : Nat := 4087672634976271903564349

theorem tailTrace_7960714 : CollatzResearch.WordTrace tailWord_7960714 prefixEnd_7960714 4087672634976271903564349 := by
  unfold tailWord_7960714
  simp only [CollatzResearch.WordTrace]
  refine ⟨72587773220425058638620299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193567395254466823036320797 72587773220425058638620299)
  ·
    refine ⟨108881659830637587957930449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72587773220425058638620299 108881659830637587957930449)
    ·
      refine ⟨81661244872978190968447837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108881659830637587957930449 81661244872978190968447837)
      ·
        refine ⟨30622966827366821613167939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81661244872978190968447837 30622966827366821613167939)
        ·
          refine ⟨45934450241050232419751909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30622966827366821613167939 45934450241050232419751909)
          ·
            refine ⟨8612709420196918578703483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45934450241050232419751909 8612709420196918578703483)
            ·
              refine ⟨12919064130295377868055225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612709420196918578703483 12919064130295377868055225)
              ·
                refine ⟨9689298097721533401041419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12919064130295377868055225 9689298097721533401041419)
                ·
                  refine ⟨14533947146582300101562129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9689298097721533401041419 14533947146582300101562129)
                  ·
                    refine ⟨10900460359936725076171597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14533947146582300101562129 10900460359936725076171597)
                    ·
                      refine ⟨4087672634976271903564349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900460359936725076171597 4087672634976271903564349)
                      ·
                        rfl

theorem cell23_7960714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7960714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960714 prefixEnd_7960714 := by exact prefixLift 7960714
  have htrace : WordTrace (prefixWord ++ tailWord_7960714) baseStart_7960714 baseEnd_7960714 := by
    simpa [prefixWord, tailWord_7960714, baseEnd_7960714] using wordTrace_append hprefix tailTrace_7960714
  have hstable : (prefixWord ++ tailWord_7960714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960714).length < 2 ^ (prefixWord ++ tailWord_7960714).sum := by decide
  have hdescent : baseEnd_7960714 < baseStart_7960714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960724 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7960724 : Nat := 118140960795 + 7960724 * 2 ^ 59
def prefixEnd_7960724 : Nat := 4983230072969 + 3 ^ 40 * 7960724 * 2
def baseEnd_7960724 : Nat := 4087677769782816864439303

theorem tailTrace_7960724 : CollatzResearch.WordTrace tailWord_7960724 prefixEnd_7960724 4087677769782816864439303 := by
  unfold tailWord_7960724
  simp only [CollatzResearch.WordTrace]
  refine ⟨145175728805832003131172613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193567638407776004174896817 145175728805832003131172613)
  ·
    refine ⟨27220449151093500587094865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145175728805832003131172613 27220449151093500587094865)
    ·
      refine ⟨20415336863320125440321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27220449151093500587094865 20415336863320125440321149)
      ·
        refine ⟨7655751323745047040120431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20415336863320125440321149 7655751323745047040120431)
        ·
          refine ⟨11483626985617570560180647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655751323745047040120431 11483626985617570560180647)
          ·
            refine ⟨17225440478426355840270971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483626985617570560180647 17225440478426355840270971)
            ·
              refine ⟨25838160717639533760406457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225440478426355840270971 25838160717639533760406457)
              ·
                refine ⟨19378620538229650320304843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25838160717639533760406457 19378620538229650320304843)
                ·
                  refine ⟨29067930807344475480457265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19378620538229650320304843 29067930807344475480457265)
                  ·
                    refine ⟨21800948105508356610342949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29067930807344475480457265 21800948105508356610342949)
                    ·
                      refine ⟨4087677769782816864439303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21800948105508356610342949 4087677769782816864439303)
                      ·
                        rfl

theorem cell23_7960724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7960724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960724 prefixEnd_7960724 := by exact prefixLift 7960724
  have htrace : WordTrace (prefixWord ++ tailWord_7960724) baseStart_7960724 baseEnd_7960724 := by
    simpa [prefixWord, tailWord_7960724, baseEnd_7960724] using wordTrace_append hprefix tailTrace_7960724
  have hstable : (prefixWord ++ tailWord_7960724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960724).length < 2 ^ (prefixWord ++ tailWord_7960724).sum := by decide
  have hdescent : baseEnd_7960724 < baseStart_7960724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960727 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7960727 : Nat := 118140960795 + 7960727 * 2 ^ 59
def prefixEnd_7960727 : Nat := 4983230072969 + 3 ^ 40 * 7960727 * 2
def baseEnd_7960727 : Nat := 4087679310224780352701789

theorem tailTrace_7960727 : CollatzResearch.WordTrace tailWord_7960727 prefixEnd_7960727 4087679310224780352701789 := by
  unfold tailWord_7960727
  simp only [CollatzResearch.WordTrace]
  refine ⟨290351567030653137774704435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193567711353768758516469623 290351567030653137774704435)
  ·
    refine ⟨435527350545979706662056653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290351567030653137774704435 435527350545979706662056653)
    ·
      refine ⟨163322756454742389998271245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435527350545979706662056653 163322756454742389998271245)
      ·
        refine ⟨61246033670528396249351717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163322756454742389998271245 61246033670528396249351717)
        ·
          refine ⟨11483631313224074296753447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61246033670528396249351717 11483631313224074296753447)
          ·
            refine ⟨17225446969836111445130171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11483631313224074296753447 17225446969836111445130171)
            ·
              refine ⟨25838170454754167167695257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17225446969836111445130171 25838170454754167167695257)
              ·
                refine ⟨19378627841065625375771443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25838170454754167167695257 19378627841065625375771443)
                ·
                  refine ⟨29067941761598438063657165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19378627841065625375771443 29067941761598438063657165)
                  ·
                    refine ⟨10900478160599414273871437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29067941761598438063657165 10900478160599414273871437)
                    ·
                      refine ⟨4087679310224780352701789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900478160599414273871437 4087679310224780352701789)
                      ·
                        rfl

theorem cell23_7960727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7960727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960727 prefixEnd_7960727 := by exact prefixLift 7960727
  have htrace : WordTrace (prefixWord ++ tailWord_7960727) baseStart_7960727 baseEnd_7960727 := by
    simpa [prefixWord, tailWord_7960727, baseEnd_7960727] using wordTrace_append hprefix tailTrace_7960727
  have hstable : (prefixWord ++ tailWord_7960727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960727).length < 2 ^ (prefixWord ++ tailWord_7960727).sum := by decide
  have hdescent : baseEnd_7960727 < baseStart_7960727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960767 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 6, 2, 2]
def baseStart_7960767 : Nat := 118140960795 + 7960767 * 2 ^ 59
def prefixEnd_7960767 : Nat := 4983230072969 + 3 ^ 40 * 7960767 * 2
def baseEnd_7960767 : Nat := 4087699849450960196201605

theorem tailTrace_7960767 : CollatzResearch.WordTrace tailWord_7960767 prefixEnd_7960767 4087699849450960196201605 := by
  unfold tailWord_7960767
  simp only [CollatzResearch.WordTrace]
  refine ⟨290353025950508224606160555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193568683967005483070773703 290353025950508224606160555)
  ·
    refine ⟨435529538925762336909240833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290353025950508224606160555 435529538925762336909240833)
    ·
      refine ⟨326647154194321752681930625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435529538925762336909240833 326647154194321752681930625)
      ·
        refine ⟨244985365645741314511447969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326647154194321752681930625 244985365645741314511447969)
        ·
          refine ⟨183739024234305985883585977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244985365645741314511447969 183739024234305985883585977)
          ·
            refine ⟨137804268175729489412689483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183739024234305985883585977 137804268175729489412689483)
            ·
              refine ⟨206706402263594234119034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137804268175729489412689483 206706402263594234119034225)
              ·
                refine ⟨155029801697695675589275669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206706402263594234119034225 155029801697695675589275669)
                ·
                  refine ⟨7267021954579484793247297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155029801697695675589275669 7267021954579484793247297)
                  ·
                    refine ⟨5450266465934613594935473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267021954579484793247297 5450266465934613594935473)
                    ·
                      refine ⟨4087699849450960196201605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450266465934613594935473 4087699849450960196201605)
                      ·
                        rfl

theorem cell23_7960767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_7960767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960767 prefixEnd_7960767 := by exact prefixLift 7960767
  have htrace : WordTrace (prefixWord ++ tailWord_7960767) baseStart_7960767 baseEnd_7960767 := by
    simpa [prefixWord, tailWord_7960767, baseEnd_7960767] using wordTrace_append hprefix tailTrace_7960767
  have hstable : (prefixWord ++ tailWord_7960767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960767).length < 2 ^ (prefixWord ++ tailWord_7960767).sum := by decide
  have hdescent : baseEnd_7960767 < baseStart_7960767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960773 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 9]
def baseStart_7960773 : Nat := 118140960795 + 7960773 * 2 ^ 59
def prefixEnd_7960773 : Nat := 4983230072969 + 3 ^ 40 * 7960773 * 2
def baseEnd_7960773 : Nat := 454189214481654130302953

theorem tailTrace_7960773 : CollatzResearch.WordTrace tailWord_7960773 prefixEnd_7960773 454189214481654130302953 := by
  unfold tailWord_7960773
  simp only [CollatzResearch.WordTrace]
  refine ⟨290353244788486487630878973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193568829858990991753919315 290353244788486487630878973)
  ·
    refine ⟨108882466795682432861579615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290353244788486487630878973 108882466795682432861579615)
    ·
      refine ⟨163323700193523649292369423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108882466795682432861579615 163323700193523649292369423)
      ·
        refine ⟨244985550290285473938554135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163323700193523649292369423 244985550290285473938554135)
        ·
          refine ⟨367478325435428210907831203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244985550290285473938554135 367478325435428210907831203)
          ·
            refine ⟨551217488153142316361746805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367478325435428210907831203 551217488153142316361746805)
            ·
              refine ⟨51676639514357092158913763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551217488153142316361746805 51676639514357092158913763)
              ·
                refine ⟨77514959271535638238370645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51676639514357092158913763 77514959271535638238370645)
                ·
                  refine ⟨454189214481654130302953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77514959271535638238370645 454189214481654130302953)
                  ·
                    rfl

theorem cell23_7960773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_7960773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960773 prefixEnd_7960773 := by exact prefixLift 7960773
  have htrace : WordTrace (prefixWord ++ tailWord_7960773) baseStart_7960773 baseEnd_7960773 := by
    simpa [prefixWord, tailWord_7960773, baseEnd_7960773] using wordTrace_append hprefix tailTrace_7960773
  have hstable : (prefixWord ++ tailWord_7960773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960773).length < 2 ^ (prefixWord ++ tailWord_7960773).sum := by decide
  have hdescent : baseEnd_7960773 < baseStart_7960773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960797 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7960797 : Nat := 118140960795 + 7960797 * 2 ^ 59
def prefixEnd_7960797 : Nat := 4983230072969 + 3 ^ 40 * 7960797 * 2
def baseEnd_7960797 : Nat := 4087715253870595078826467

theorem tailTrace_7960797 : CollatzResearch.WordTrace tailWord_7960797 prefixEnd_7960797 4087715253870595078826467 := by
  unfold tailWord_7960797
  simp only [CollatzResearch.WordTrace]
  refine ⟨290354120140399539729752645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193569413426933026486501763 290354120140399539729752645)
  ·
    refine ⟨54441397526324913699328621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290354120140399539729752645 54441397526324913699328621)
    ·
      refine ⟨20415524072371842637248233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54441397526324913699328621 20415524072371842637248233)
      ·
        refine ⟨15311643054278881977936175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20415524072371842637248233 15311643054278881977936175)
        ·
          refine ⟨22967464581418322966904263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311643054278881977936175 22967464581418322966904263)
          ·
            refine ⟨34451196872127484450356395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967464581418322966904263 34451196872127484450356395)
            ·
              refine ⟨51676795308191226675534593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34451196872127484450356395 51676795308191226675534593)
              ·
                refine ⟨38757596481143420006650945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51676795308191226675534593 38757596481143420006650945)
                ·
                  refine ⟨29068197360857565004988209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38757596481143420006650945 29068197360857565004988209)
                  ·
                    refine ⟨21801148020643173753741157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29068197360857565004988209 21801148020643173753741157)
                    ·
                      refine ⟨4087715253870595078826467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21801148020643173753741157 4087715253870595078826467)
                      ·
                        rfl

theorem cell23_7960797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7960797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960797 prefixEnd_7960797 := by exact prefixLift 7960797
  have htrace : WordTrace (prefixWord ++ tailWord_7960797) baseStart_7960797 baseEnd_7960797 := by
    simpa [prefixWord, tailWord_7960797, baseEnd_7960797] using wordTrace_append hprefix tailTrace_7960797
  have hstable : (prefixWord ++ tailWord_7960797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960797).length < 2 ^ (prefixWord ++ tailWord_7960797).sum := by decide
  have hdescent : baseEnd_7960797 < baseStart_7960797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960800 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_7960800 : Nat := 118140960795 + 7960800 * 2 ^ 59
def prefixEnd_7960800 : Nat := 4983230072969 + 3 ^ 40 * 7960800 * 2
def baseEnd_7960800 : Nat := 4087716794312558567088953

theorem tailTrace_7960800 : CollatzResearch.WordTrace tailWord_7960800 prefixEnd_7960800 4087716794312558567088953 := by
  unfold tailWord_7960800
  simp only [CollatzResearch.WordTrace]
  refine ⟨145177114779694335621055927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193569486372925780828074569 145177114779694335621055927)
  ·
    refine ⟨217765672169541503431583891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145177114779694335621055927 217765672169541503431583891)
    ·
      refine ⟨326648508254312255147375837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217765672169541503431583891 326648508254312255147375837)
      ·
        refine ⟨122493190595367095680265939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326648508254312255147375837 122493190595367095680265939)
        ·
          refine ⟨183739785893050643520398909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122493190595367095680265939 183739785893050643520398909)
          ·
            refine ⟨68902419709893991320149591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183739785893050643520398909 68902419709893991320149591)
            ·
              refine ⟨103353629564840986980224387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68902419709893991320149591 103353629564840986980224387)
              ·
                refine ⟨155030444347261480470336581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103353629564840986980224387 155030444347261480470336581)
                ·
                  refine ⟨29068208315111527588188109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155030444347261480470336581 29068208315111527588188109)
                  ·
                    refine ⟨10900578118166822845570541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29068208315111527588188109 10900578118166822845570541)
                    ·
                      refine ⟨4087716794312558567088953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900578118166822845570541 4087716794312558567088953)
                      ·
                        rfl

theorem cell23_7960800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_7960800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960800 prefixEnd_7960800 := by exact prefixLift 7960800
  have htrace : WordTrace (prefixWord ++ tailWord_7960800) baseStart_7960800 baseEnd_7960800 := by
    simpa [prefixWord, tailWord_7960800, baseEnd_7960800] using wordTrace_append hprefix tailTrace_7960800
  have hstable : (prefixWord ++ tailWord_7960800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960800).length < 2 ^ (prefixWord ++ tailWord_7960800).sum := by decide
  have hdescent : baseEnd_7960800 < baseStart_7960800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960807 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 7]
def baseStart_7960807 : Nat := 118140960795 + 7960807 * 2 ^ 59
def prefixEnd_7960807 : Nat := 4983230072969 + 3 ^ 40 * 7960807 * 2
def baseEnd_7960807 : Nat := 454191154297460004411269

theorem tailTrace_7960807 : CollatzResearch.WordTrace tailWord_7960807 prefixEnd_7960807 454191154297460004411269 := by
  unfold tailWord_7960807
  simp only [CollatzResearch.WordTrace]
  refine ⟨290354484870363311437616675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193569656580242207625077783 290354484870363311437616675)
  ·
    refine ⟨435531727305544967156425013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290354484870363311437616675 435531727305544967156425013)
    ·
      refine ⟨40831099434894840670914845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435531727305544967156425013 40831099434894840670914845)
      ·
        refine ⟨15311662288085565251593067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40831099434894840670914845 15311662288085565251593067)
        ·
          refine ⟨22967493432128347877389601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311662288085565251593067 22967493432128347877389601)
          ·
            refine ⟨17225620074096260908042201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22967493432128347877389601 17225620074096260908042201)
            ·
              refine ⟨12919215055572195681031651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17225620074096260908042201 12919215055572195681031651)
              ·
                refine ⟨19378822583358293521547477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919215055572195681031651 19378822583358293521547477)
                ·
                  refine ⟨454191154297460004411269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19378822583358293521547477 454191154297460004411269)
                  ·
                    rfl

theorem cell23_7960807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 7].length) (baseStart_7960807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960807 prefixEnd_7960807 := by exact prefixLift 7960807
  have htrace : WordTrace (prefixWord ++ tailWord_7960807) baseStart_7960807 baseEnd_7960807 := by
    simpa [prefixWord, tailWord_7960807, baseEnd_7960807] using wordTrace_append hprefix tailTrace_7960807
  have hstable : (prefixWord ++ tailWord_7960807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960807).length < 2 ^ (prefixWord ++ tailWord_7960807).sum := by decide
  have hdescent : baseEnd_7960807 < baseStart_7960807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960818 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_7960818 : Nat := 118140960795 + 7960818 * 2 ^ 59
def prefixEnd_7960818 : Nat := 4983230072969 + 3 ^ 40 * 7960818 * 2
def baseEnd_7960818 : Nat := 4087726036964339496663871

theorem tailTrace_7960818 : CollatzResearch.WordTrace tailWord_7960818 prefixEnd_7960818 4087726036964339496663871 := by
  unfold tailWord_7960818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72588721518330865079066777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193569924048882306877511405 72588721518330865079066777)
  ·
    refine ⟨54441541138748148809300083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72588721518330865079066777 54441541138748148809300083)
    ·
      refine ⟨81662311708122223213950125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54441541138748148809300083 81662311708122223213950125)
      ·
        refine ⟨30623366890545833705231297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81662311708122223213950125 30623366890545833705231297)
        ·
          refine ⟨22967525167909375278923473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30623366890545833705231297 22967525167909375278923473)
          ·
            refine ⟨17225643875932031459192605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22967525167909375278923473 17225643875932031459192605)
            ·
              refine ⟨6459616453474511797197227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17225643875932031459192605 6459616453474511797197227)
              ·
                refine ⟨9689424680211767695795841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459616453474511797197227 9689424680211767695795841)
                ·
                  refine ⟨7267068510158825771846881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689424680211767695795841 7267068510158825771846881)
                  ·
                    refine ⟨5450301382619119328885161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267068510158825771846881 5450301382619119328885161)
                    ·
                      refine ⟨4087726036964339496663871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450301382619119328885161 4087726036964339496663871)
                      ·
                        rfl

theorem cell23_7960818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_7960818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960818 prefixEnd_7960818 := by exact prefixLift 7960818
  have htrace : WordTrace (prefixWord ++ tailWord_7960818) baseStart_7960818 baseEnd_7960818 := by
    simpa [prefixWord, tailWord_7960818, baseEnd_7960818] using wordTrace_append hprefix tailTrace_7960818
  have hstable : (prefixWord ++ tailWord_7960818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960818).length < 2 ^ (prefixWord ++ tailWord_7960818).sum := by decide
  have hdescent : baseEnd_7960818 < baseStart_7960818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960894 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7960894 : Nat := 118140960795 + 7960894 * 2 ^ 59
def prefixEnd_7960894 : Nat := 4983230072969 + 3 ^ 40 * 7960894 * 2
def baseEnd_7960894 : Nat := 4087765061494081199313521

theorem tailTrace_7960894 : CollatzResearch.WordTrace tailWord_7960894 prefixEnd_7960894 4087765061494081199313521 := by
  unfold tailWord_7960894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294707252631015662004217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193571772014032083530689157 36294707252631015662004217)
  ·
    refine ⟨27221030439473261746503163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36294707252631015662004217 27221030439473261746503163)
    ·
      refine ⟨40831545659209892619754745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27221030439473261746503163 40831545659209892619754745)
      ·
        refine ⟨30623659244407419464816059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40831545659209892619754745 30623659244407419464816059)
        ·
          refine ⟨45935488866611129197224089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30623659244407419464816059 45935488866611129197224089)
          ·
            refine ⟨34451616649958346897918067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45935488866611129197224089 34451616649958346897918067)
            ·
              refine ⟨51677424974937520346877101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34451616649958346897918067 51677424974937520346877101)
              ·
                refine ⟨19379034365601570130078913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51677424974937520346877101 19379034365601570130078913)
                ·
                  refine ⟨14534275774201177597559185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19379034365601570130078913 14534275774201177597559185)
                  ·
                    refine ⟨10900706830650883198169389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14534275774201177597559185 10900706830650883198169389)
                    ·
                      refine ⟨4087765061494081199313521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900706830650883198169389 4087765061494081199313521)
                      ·
                        rfl

theorem cell23_7960894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7960894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960894 prefixEnd_7960894 := by exact prefixLift 7960894
  have htrace : WordTrace (prefixWord ++ tailWord_7960894) baseStart_7960894 baseEnd_7960894 := by
    simpa [prefixWord, tailWord_7960894, baseEnd_7960894] using wordTrace_append hprefix tailTrace_7960894
  have hstable : (prefixWord ++ tailWord_7960894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960894).length < 2 ^ (prefixWord ++ tailWord_7960894).sum := by decide
  have hdescent : baseEnd_7960894 < baseStart_7960894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960907 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 3]
def baseStart_7960907 : Nat := 118140960795 + 7960907 * 2 ^ 59
def prefixEnd_7960907 : Nat := 4983230072969 + 3 ^ 40 * 7960907 * 2
def baseEnd_7960907 : Nat := 4087771736742589648450961

theorem tailTrace_7960907 : CollatzResearch.WordTrace tailWord_7960907 prefixEnd_7960907 4087771736742589648450961 := by
  unfold tailWord_7960907
  simp only [CollatzResearch.WordTrace]
  refine ⟨290358132170001028516256975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193572088113334019010837983 290358132170001028516256975)
  ·
    refine ⟨435537198255001542774385463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290358132170001028516256975 435537198255001542774385463)
    ·
      refine ⟨653305797382502314161578195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435537198255001542774385463 653305797382502314161578195)
      ·
        refine ⟨979958696073753471242367293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653305797382502314161578195 979958696073753471242367293)
        ·
          refine ⟨367484511027657551715887735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979958696073753471242367293 367484511027657551715887735)
          ·
            refine ⟨551226766541486327573831603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367484511027657551715887735 551226766541486327573831603)
            ·
              refine ⟨826840149812229491360747405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551226766541486327573831603 826840149812229491360747405)
              ·
                refine ⟨310065056179586059260280277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826840149812229491360747405 310065056179586059260280277)
                ·
                  refine ⟨7267149754209048263912819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310065056179586059260280277 7267149754209048263912819)
                  ·
                    refine ⟨10900724631313572395869229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7267149754209048263912819 10900724631313572395869229)
                    ·
                      refine ⟨4087771736742589648450961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10900724631313572395869229 4087771736742589648450961)
                      ·
                        rfl

theorem cell23_7960907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 3].length) (baseStart_7960907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960907 prefixEnd_7960907 := by exact prefixLift 7960907
  have htrace : WordTrace (prefixWord ++ tailWord_7960907) baseStart_7960907 baseEnd_7960907 := by
    simpa [prefixWord, tailWord_7960907, baseEnd_7960907] using wordTrace_append hprefix tailTrace_7960907
  have hstable : (prefixWord ++ tailWord_7960907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960907).length < 2 ^ (prefixWord ++ tailWord_7960907).sum := by decide
  have hdescent : baseEnd_7960907 < baseStart_7960907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960947 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 6, 2]
def baseStart_7960947 : Nat := 118140960795 + 7960947 * 2 ^ 59
def prefixEnd_7960947 : Nat := 4983230072969 + 3 ^ 40 * 7960947 * 2
def baseEnd_7960947 : Nat := 4087792275968769491950777

theorem tailTrace_7960947 : CollatzResearch.WordTrace tailWord_7960947 prefixEnd_7960947 4087792275968769491950777 := by
  unfold tailWord_7960947
  simp only [CollatzResearch.WordTrace]
  refine ⟨290359591089856115347713095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193573060726570743565142063 290359591089856115347713095)
  ·
    refine ⟨435539386634784173021569643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290359591089856115347713095 435539386634784173021569643)
    ·
      refine ⟨653309079952176259532354465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435539386634784173021569643 653309079952176259532354465)
      ·
        refine ⟨489981809964132194649265849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653309079952176259532354465 489981809964132194649265849)
        ·
          refine ⟨367486357473099145986949387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489981809964132194649265849 367486357473099145986949387)
          ·
            refine ⟨551229536209648718980424081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367486357473099145986949387 551229536209648718980424081)
            ·
              refine ⟨413422152157236539235318061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551229536209648718980424081 413422152157236539235318061)
              ·
                refine ⟨155033307058963702213244273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413422152157236539235318061 155033307058963702213244273)
                ·
                  refine ⟨116274980294222776659933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155033307058963702213244273 116274980294222776659933205)
                  ·
                    refine ⟨5450389701291692655934369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116274980294222776659933205 5450389701291692655934369)
                    ·
                      refine ⟨4087792275968769491950777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450389701291692655934369 4087792275968769491950777)
                      ·
                        rfl

theorem cell23_7960947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6, 2].length) (baseStart_7960947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960947 prefixEnd_7960947 := by exact prefixLift 7960947
  have htrace : WordTrace (prefixWord ++ tailWord_7960947) baseStart_7960947 baseEnd_7960947 := by
    simpa [prefixWord, tailWord_7960947, baseEnd_7960947] using wordTrace_append hprefix tailTrace_7960947
  have hstable : (prefixWord ++ tailWord_7960947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960947).length < 2 ^ (prefixWord ++ tailWord_7960947).sum := by decide
  have hdescent : baseEnd_7960947 < baseStart_7960947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960957 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7960957 : Nat := 118140960795 + 7960957 * 2 ^ 59
def prefixEnd_7960957 : Nat := 4983230072969 + 3 ^ 40 * 7960957 * 2
def baseEnd_7960957 : Nat := 1362599136925104817608577

theorem tailTrace_7960957 : CollatzResearch.WordTrace tailWord_7960957 prefixEnd_7960957 1362599136925104817608577 := by
  unfold tailWord_7960957
  simp only [CollatzResearch.WordTrace]
  refine ⟨290359955819819887055577125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193573303879879924703718083 290359955819819887055577125)
  ·
    refine ⟨54442491716216228822920711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290359955819819887055577125 54442491716216228822920711)
    ·
      refine ⟨81663737574324343234381067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54442491716216228822920711 81663737574324343234381067)
      ·
        refine ⟨122495606361486514851571601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81663737574324343234381067 122495606361486514851571601)
        ·
          refine ⟨91871704771114886138678701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122495606361486514851571601 91871704771114886138678701)
          ·
            refine ⟨34451889289168082302004513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91871704771114886138678701 34451889289168082302004513)
            ·
              refine ⟨25838916966876061726503385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34451889289168082302004513 25838916966876061726503385)
              ·
                refine ⟨19379187725157046294877539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25838916966876061726503385 19379187725157046294877539)
                ·
                  refine ⟨29068781587735569442316309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19379187725157046294877539 29068781587735569442316309)
                  ·
                    refine ⟨1362599136925104817608577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29068781587735569442316309 1362599136925104817608577)
                    ·
                      rfl

theorem cell23_7960957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7960957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960957 prefixEnd_7960957 := by exact prefixLift 7960957
  have htrace : WordTrace (prefixWord ++ tailWord_7960957) baseStart_7960957 baseEnd_7960957 := by
    simpa [prefixWord, tailWord_7960957, baseEnd_7960957] using wordTrace_append hprefix tailTrace_7960957
  have hstable : (prefixWord ++ tailWord_7960957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960957).length < 2 ^ (prefixWord ++ tailWord_7960957).sum := by decide
  have hdescent : baseEnd_7960957 < baseStart_7960957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960960 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_7960960 : Nat := 118140960795 + 7960960 * 2 ^ 59
def prefixEnd_7960960 : Nat := 4983230072969 + 3 ^ 40 * 7960960 * 2
def baseEnd_7960960 : Nat := 4087798951217277941088217

theorem tailTrace_7960960 : CollatzResearch.WordTrace tailWord_7960960 prefixEnd_7960960 4087798951217277941088217 := by
  unfold tailWord_7960960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145180032619404509283968167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193573376825872679045290889 145180032619404509283968167)
  ·
    refine ⟨217770048929106763925952251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145180032619404509283968167 217770048929106763925952251)
    ·
      refine ⟨326655073393660145888928377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217770048929106763925952251 326655073393660145888928377)
      ·
        refine ⟨244991305045245109416696283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326655073393660145888928377 244991305045245109416696283)
        ·
          refine ⟨367486957567867664125044425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244991305045245109416696283 367486957567867664125044425)
          ·
            refine ⟨275615218175900748093783319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367486957567867664125044425 275615218175900748093783319)
            ·
              refine ⟨413422827263851122140674979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275615218175900748093783319 413422827263851122140674979)
              ·
                refine ⟨620134240895776683211012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413422827263851122140674979 620134240895776683211012469)
                ·
                  refine ⟨58137585083979064051032419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 620134240895776683211012469 58137585083979064051032419)
                  ·
                    refine ⟨87206377625968596076548629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58137585083979064051032419 87206377625968596076548629)
                    ·
                      refine ⟨4087798951217277941088217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87206377625968596076548629 4087798951217277941088217)
                      ·
                        rfl

theorem cell23_7960960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_7960960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960960 prefixEnd_7960960 := by exact prefixLift 7960960
  have htrace : WordTrace (prefixWord ++ tailWord_7960960) baseStart_7960960 baseEnd_7960960 := by
    simpa [prefixWord, tailWord_7960960, baseEnd_7960960] using wordTrace_append hprefix tailTrace_7960960
  have hstable : (prefixWord ++ tailWord_7960960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960960).length < 2 ^ (prefixWord ++ tailWord_7960960).sum := by decide
  have hdescent : baseEnd_7960960 < baseStart_7960960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960961 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7960961 : Nat := 118140960795 + 7960961 * 2 ^ 59
def prefixEnd_7960961 : Nat := 4983230072969 + 3 ^ 40 * 7960961 * 2
def baseEnd_7960961 : Nat := 1362599821565977479058571

theorem tailTrace_7960961 : CollatzResearch.WordTrace tailWord_7960961 prefixEnd_7960961 1362599821565977479058571 := by
  unfold tailWord_7960961
  simp only [CollatzResearch.WordTrace]
  refine ⟨290360101711805395738722737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193573401141203597159148491 290360101711805395738722737)
  ·
    refine ⟨217770076283854046804042053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290360101711805395738722737 217770076283854046804042053)
    ·
      refine ⟨40831889303222633775757885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217770076283854046804042053 40831889303222633775757885)
      ·
        refine ⟨15311958488708487665909207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40831889303222633775757885 15311958488708487665909207)
        ·
          refine ⟨22967937733062731498863811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311958488708487665909207 22967937733062731498863811)
          ·
            refine ⟨34451906599594097248295717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967937733062731498863811 34451906599594097248295717)
            ·
              refine ⟨6459732487423893234055447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34451906599594097248295717 6459732487423893234055447)
              ·
                refine ⟨9689598731135839851083171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459732487423893234055447 9689598731135839851083171)
                ·
                  refine ⟨14534398096703759776624757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9689598731135839851083171 14534398096703759776624757)
                  ·
                    refine ⟨1362599821565977479058571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14534398096703759776624757 1362599821565977479058571)
                    ·
                      rfl

theorem cell23_7960961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7960961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960961 prefixEnd_7960961 := by exact prefixLift 7960961
  have htrace : WordTrace (prefixWord ++ tailWord_7960961) baseStart_7960961 baseEnd_7960961 := by
    simpa [prefixWord, tailWord_7960961, baseEnd_7960961] using wordTrace_append hprefix tailTrace_7960961
  have hstable : (prefixWord ++ tailWord_7960961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960961).length < 2 ^ (prefixWord ++ tailWord_7960961).sum := by decide
  have hdescent : baseEnd_7960961 < baseStart_7960961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960964 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7960964 : Nat := 118140960795 + 7960964 * 2 ^ 59
def prefixEnd_7960964 : Nat := 4983230072969 + 3 ^ 40 * 7960964 * 2
def baseEnd_7960964 : Nat := 4087801005139895925438199

theorem tailTrace_7960964 : CollatzResearch.WordTrace tailWord_7960964 prefixEnd_7960964 4087801005139895925438199 := by
  unfold tailWord_7960964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145180105565397263625540973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193573474087196351500721297 145180105565397263625540973)
  ·
    refine ⟨54442539587023973859577865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145180105565397263625540973 54442539587023973859577865)
    ·
      refine ⟨40831904690267980394683399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54442539587023973859577865 40831904690267980394683399)
      ·
        refine ⟨61247857035401970592025099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40831904690267980394683399 61247857035401970592025099)
        ·
          refine ⟨91871785553102955888037649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61247857035401970592025099 91871785553102955888037649)
          ·
            refine ⟨68903839164827216916028237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91871785553102955888037649 68903839164827216916028237)
            ·
              refine ⟨25838939686810206343510589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68903839164827216916028237 25838939686810206343510589)
              ·
                refine ⟨9689602382553827378816471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25838939686810206343510589 9689602382553827378816471)
                ·
                  refine ⟨14534403573830741068224707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9689602382553827378816471 14534403573830741068224707)
                  ·
                    refine ⟨21801605360746111602337061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14534403573830741068224707 21801605360746111602337061)
                    ·
                      refine ⟨4087801005139895925438199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21801605360746111602337061 4087801005139895925438199)
                      ·
                        rfl

theorem cell23_7960964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7960964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960964 prefixEnd_7960964 := by exact prefixLift 7960964
  have htrace : WordTrace (prefixWord ++ tailWord_7960964) baseStart_7960964 baseEnd_7960964 := by
    simpa [prefixWord, tailWord_7960964, baseEnd_7960964] using wordTrace_append hprefix tailTrace_7960964
  have hstable : (prefixWord ++ tailWord_7960964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960964).length < 2 ^ (prefixWord ++ tailWord_7960964).sum := by decide
  have hdescent : baseEnd_7960964 < baseStart_7960964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960967 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7960967 : Nat := 118140960795 + 7960967 * 2 ^ 59
def prefixEnd_7960967 : Nat := 4983230072969 + 3 ^ 40 * 7960967 * 2
def baseEnd_7960967 : Nat := 4087802545581859413700685

theorem tailTrace_7960967 : CollatzResearch.WordTrace tailWord_7960967 prefixEnd_7960967 4087802545581859413700685 := by
  unfold tailWord_7960967
  simp only [CollatzResearch.WordTrace]
  refine ⟨290360320549783658763441155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193573547033189105842294103 290360320549783658763441155)
  ·
    refine ⟨435540480824675488145161733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290360320549783658763441155 435540480824675488145161733)
    ·
      refine ⟨81663840154626654027217825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435540480824675488145161733 81663840154626654027217825)
      ·
        refine ⟨61247880115969990520413369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81663840154626654027217825 61247880115969990520413369)
        ·
          refine ⟨45935910086977492890310027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61247880115969990520413369 45935910086977492890310027)
          ·
            refine ⟨68903865130466239335465041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45935910086977492890310027 68903865130466239335465041)
            ·
              refine ⟨51677898847849679501598781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68903865130466239335465041 51677898847849679501598781)
              ·
                refine ⟨19379212067943629813099543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51677898847849679501598781 19379212067943629813099543)
                ·
                  refine ⟨29068818101915444719649315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19379212067943629813099543 29068818101915444719649315)
                  ·
                    refine ⟨43603227152873167079473973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29068818101915444719649315 43603227152873167079473973)
                    ·
                      refine ⟨4087802545581859413700685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43603227152873167079473973 4087802545581859413700685)
                      ·
                        rfl

theorem cell23_7960967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7960967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960967 prefixEnd_7960967 := by exact prefixLift 7960967
  have htrace : WordTrace (prefixWord ++ tailWord_7960967) baseStart_7960967 baseEnd_7960967 := by
    simpa [prefixWord, tailWord_7960967, baseEnd_7960967] using wordTrace_append hprefix tailTrace_7960967
  have hstable : (prefixWord ++ tailWord_7960967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960967).length < 2 ^ (prefixWord ++ tailWord_7960967).sum := by decide
  have hdescent : baseEnd_7960967 < baseStart_7960967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960984 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7960984 : Nat := 118140960795 + 7960984 * 2 ^ 59
def prefixEnd_7960984 : Nat := 4983230072969 + 3 ^ 40 * 7960984 * 2
def baseEnd_7960984 : Nat := 4087811274752985847188107

theorem tailTrace_7960984 : CollatzResearch.WordTrace tailWord_7960984 prefixEnd_7960984 4087811274752985847188107 := by
  unfold tailWord_7960984
  simp only [CollatzResearch.WordTrace]
  refine ⟨145180470295361035333405003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193573960393814713777873337 145180470295361035333405003)
  ·
    refine ⟨217770705443041553000107505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145180470295361035333405003 217770705443041553000107505)
    ·
      refine ⟨163328029082281164750080629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217770705443041553000107505 163328029082281164750080629)
      ·
        refine ⟨15312002726463859195320059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163328029082281164750080629 15312002726463859195320059)
        ·
          refine ⟨22968004089695788792980089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15312002726463859195320059 22968004089695788792980089)
          ·
            refine ⟨17226003067271841594735067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22968004089695788792980089 17226003067271841594735067)
            ·
              refine ⟨25839004600907762392102601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17226003067271841594735067 25839004600907762392102601)
              ·
                refine ⟨19379253450680821794076951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25839004600907762392102601 19379253450680821794076951)
                ·
                  refine ⟨29068880176021232691115427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19379253450680821794076951 29068880176021232691115427)
                  ·
                    refine ⟨43603320264031849036673141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29068880176021232691115427 43603320264031849036673141)
                    ·
                      refine ⟨4087811274752985847188107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43603320264031849036673141 4087811274752985847188107)
                      ·
                        rfl

theorem cell23_7960984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7960984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960984 prefixEnd_7960984 := by exact prefixLift 7960984
  have htrace : WordTrace (prefixWord ++ tailWord_7960984) baseStart_7960984 baseEnd_7960984 := by
    simpa [prefixWord, tailWord_7960984, baseEnd_7960984] using wordTrace_append hprefix tailTrace_7960984
  have hstable : (prefixWord ++ tailWord_7960984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960984).length < 2 ^ (prefixWord ++ tailWord_7960984).sum := by decide
  have hdescent : baseEnd_7960984 < baseStart_7960984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7960991 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 2, 4]
def baseStart_7960991 : Nat := 118140960795 + 7960991 * 2 ^ 59
def prefixEnd_7960991 : Nat := 4983230072969 + 3 ^ 40 * 7960991 * 2
def baseEnd_7960991 : Nat := 1362604956372522439933525

theorem tailTrace_7960991 : CollatzResearch.WordTrace tailWord_7960991 prefixEnd_7960991 1362604956372522439933525 := by
  unfold tailWord_7960991
  simp only [CollatzResearch.WordTrace]
  refine ⟨290361195901696710862314827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193574130601131140574876551 290361195901696710862314827)
  ·
    refine ⟨435541793852545066293472241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290361195901696710862314827 435541793852545066293472241)
    ·
      refine ⟨326656345389408799720104181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435541793852545066293472241 326656345389408799720104181)
      ·
        refine ⟨30624032380257074973759767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326656345389408799720104181 30624032380257074973759767)
        ·
          refine ⟨45936048570385612460639651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30624032380257074973759767 45936048570385612460639651)
          ·
            refine ⟨68904072855578418690959477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45936048570385612460639651 68904072855578418690959477)
            ·
              refine ⟨6459756830210476752277451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68904072855578418690959477 6459756830210476752277451)
              ·
                refine ⟨9689635245315715128416177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459756830210476752277451 9689635245315715128416177)
                ·
                  refine ⟨7267226433986786346312133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689635245315715128416177 7267226433986786346312133)
                  ·
                    refine ⟨1362604956372522439933525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267226433986786346312133 1362604956372522439933525)
                    ·
                      rfl

theorem cell23_7960991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_7960991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7960991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7960991 prefixEnd_7960991 := by exact prefixLift 7960991
  have htrace : WordTrace (prefixWord ++ tailWord_7960991) baseStart_7960991 baseEnd_7960991 := by
    simpa [prefixWord, tailWord_7960991, baseEnd_7960991] using wordTrace_append hprefix tailTrace_7960991
  have hstable : (prefixWord ++ tailWord_7960991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7960991).length < 2 ^ (prefixWord ++ tailWord_7960991).sum := by decide
  have hdescent : baseEnd_7960991 < baseStart_7960991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7960991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961015 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_7961015 : Nat := 118140960795 + 7961015 * 2 ^ 59
def prefixEnd_7961015 : Nat := 4983230072969 + 3 ^ 40 * 7961015 * 2
def baseEnd_7961015 : Nat := 4087827192653275225900465

theorem tailTrace_7961015 : CollatzResearch.WordTrace tailWord_7961015 prefixEnd_7961015 4087827192653275225900465 := by
  unfold tailWord_7961015
  simp only [CollatzResearch.WordTrace]
  refine ⟨290362071253609762961188499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193574714169073175307458999 290362071253609762961188499)
  ·
    refine ⟨435543106880414644441782749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290362071253609762961188499 435543106880414644441782749)
    ·
      refine ⟨163328665080155491665668531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435543106880414644441782749 163328665080155491665668531)
      ·
        refine ⟨244992997620233237498502797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163328665080155491665668531 244992997620233237498502797)
        ·
          refine ⟨91872374107587464061938549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244992997620233237498502797 91872374107587464061938549)
          ·
            refine ⟨8613035072586324755806739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91872374107587464061938549 8613035072586324755806739)
            ·
              refine ⟨12919552608879487133710109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613035072586324755806739 12919552608879487133710109)
              ·
                refine ⟨4844832228329807675141291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12919552608879487133710109 4844832228329807675141291)
                ·
                  refine ⟨7267248342494711512711937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844832228329807675141291 7267248342494711512711937)
                  ·
                    refine ⟨5450436256871033634533953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267248342494711512711937 5450436256871033634533953)
                    ·
                      refine ⟨4087827192653275225900465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450436256871033634533953 4087827192653275225900465)
                      ·
                        rfl

theorem cell23_7961015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_7961015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961015 prefixEnd_7961015 := by exact prefixLift 7961015
  have htrace : WordTrace (prefixWord ++ tailWord_7961015) baseStart_7961015 baseEnd_7961015 := by
    simpa [prefixWord, tailWord_7961015, baseEnd_7961015] using wordTrace_append hprefix tailTrace_7961015
  have hstable : (prefixWord ++ tailWord_7961015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961015).length < 2 ^ (prefixWord ++ tailWord_7961015).sum := by decide
  have hdescent : baseEnd_7961015 < baseStart_7961015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961024 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2]
def baseStart_7961024 : Nat := 118140960795 + 7961024 * 2 ^ 59
def prefixEnd_7961024 : Nat := 4983230072969 + 3 ^ 40 * 7961024 * 2
def baseEnd_7961024 : Nat := 4087831813979165690687923

theorem tailTrace_7961024 : CollatzResearch.WordTrace tailWord_7961024 prefixEnd_7961024 4087831813979165690687923 := by
  unfold tailWord_7961024
  simp only [CollatzResearch.WordTrace]
  refine ⟨145181199755288578749133063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193574933007051438332177417 145181199755288578749133063)
  ·
    refine ⟨217771799632932868123699595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145181199755288578749133063 217771799632932868123699595)
    ·
      refine ⟨326657699449399302185549393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217771799632932868123699595 326657699449399302185549393)
      ·
        refine ⟨244993274587049476639162045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326657699449399302185549393 244993274587049476639162045)
        ·
          refine ⟨91872477970143553739685767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244993274587049476639162045 91872477970143553739685767)
          ·
            refine ⟨137808716955215330609528651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91872477970143553739685767 137808716955215330609528651)
            ·
              refine ⟨206713075432822995914292977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137808716955215330609528651 206713075432822995914292977)
              ·
                refine ⟨155034806574617246935719733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206713075432822995914292977 155034806574617246935719733)
                ·
                  refine ⟨14534513116370366900223725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155034806574617246935719733 14534513116370366900223725)
                  ·
                    refine ⟨5450442418638887587583897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14534513116370366900223725 5450442418638887587583897)
                    ·
                      refine ⟨4087831813979165690687923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450442418638887587583897 4087831813979165690687923)
                      ·
                        rfl

theorem cell23_7961024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_7961024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961024 prefixEnd_7961024 := by exact prefixLift 7961024
  have htrace : WordTrace (prefixWord ++ tailWord_7961024) baseStart_7961024 baseEnd_7961024 := by
    simpa [prefixWord, tailWord_7961024, baseEnd_7961024] using wordTrace_append hprefix tailTrace_7961024
  have hstable : (prefixWord ++ tailWord_7961024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961024).length < 2 ^ (prefixWord ++ tailWord_7961024).sum := by decide
  have hdescent : baseEnd_7961024 < baseStart_7961024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961042 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_7961042 : Nat := 118140960795 + 7961042 * 2 ^ 59
def prefixEnd_7961042 : Nat := 4983230072969 + 3 ^ 40 * 7961042 * 2
def baseEnd_7961042 : Nat := 1362613685543648873420947

theorem tailTrace_7961042 : CollatzResearch.WordTrace tailWord_7961042 prefixEnd_7961042 1362613685543648873420947 := by
  unfold tailWord_7961042
  simp only [CollatzResearch.WordTrace]
  refine ⟨72590764006127986643105345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193575370683007964381614253 72590764006127986643105345)
  ·
    refine ⟨54443073004595989982329009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72590764006127986643105345 54443073004595989982329009)
    ·
      refine ⟨40832304753446992486746757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54443073004595989982329009 40832304753446992486746757)
      ·
        refine ⟨7656057141271311091265017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40832304753446992486746757 7656057141271311091265017)
        ·
          refine ⟨5742042855953483318448763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656057141271311091265017 5742042855953483318448763)
          ·
            refine ⟨8613064283930224977673145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742042855953483318448763 8613064283930224977673145)
            ·
              refine ⟨6459798212947668733254859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613064283930224977673145 6459798212947668733254859)
              ·
                refine ⟨9689697319421503099882289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459798212947668733254859 9689697319421503099882289)
                ·
                  refine ⟨7267272989566127324911717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689697319421503099882289 7267272989566127324911717)
                  ·
                    refine ⟨1362613685543648873420947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267272989566127324911717 1362613685543648873420947)
                    ·
                      rfl

theorem cell23_7961042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_7961042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961042 prefixEnd_7961042 := by exact prefixLift 7961042
  have htrace : WordTrace (prefixWord ++ tailWord_7961042) baseStart_7961042 baseEnd_7961042 := by
    simpa [prefixWord, tailWord_7961042, baseEnd_7961042] using wordTrace_append hprefix tailTrace_7961042
  have hstable : (prefixWord ++ tailWord_7961042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961042).length < 2 ^ (prefixWord ++ tailWord_7961042).sum := by decide
  have hdescent : baseEnd_7961042 < baseStart_7961042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961057 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7961057 : Nat := 118140960795 + 7961057 * 2 ^ 59
def prefixEnd_7961057 : Nat := 4983230072969 + 3 ^ 40 * 7961057 * 2
def baseEnd_7961057 : Nat := 4087848758840764061575271

theorem tailTrace_7961057 : CollatzResearch.WordTrace tailWord_7961057 prefixEnd_7961057 4087848758840764061575271 := by
  unfold tailWord_7961057
  simp only [CollatzResearch.WordTrace]
  refine ⟨290363603119457604134217425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193575735412971736089478283 290363603119457604134217425)
  ·
    refine ⟨217772702339593203100663069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290363603119457604134217425 217772702339593203100663069)
    ·
      refine ⟨81664763377347451162748651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217772702339593203100663069 81664763377347451162748651)
      ·
        refine ⟨122497145066021176744122977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81664763377347451162748651 122497145066021176744122977)
        ·
          refine ⟨91872858799515882558092233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122497145066021176744122977 91872858799515882558092233)
          ·
            refine ⟨68904644099636911918569175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91872858799515882558092233 68904644099636911918569175)
            ·
              refine ⟨103356966149455367877853763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68904644099636911918569175 103356966149455367877853763)
              ·
                refine ⟨155035449224183051816780645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103356966149455367877853763 155035449224183051816780645)
                ·
                  refine ⟨29069146729534322215646371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155035449224183051816780645 29069146729534322215646371)
                  ·
                    refine ⟨43603720094301483323469557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29069146729534322215646371 43603720094301483323469557)
                    ·
                      refine ⟨4087848758840764061575271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43603720094301483323469557 4087848758840764061575271)
                      ·
                        rfl

theorem cell23_7961057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7961057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961057 prefixEnd_7961057 := by exact prefixLift 7961057
  have htrace : WordTrace (prefixWord ++ tailWord_7961057) baseStart_7961057 baseEnd_7961057 := by
    simpa [prefixWord, tailWord_7961057, baseEnd_7961057] using wordTrace_append hprefix tailTrace_7961057
  have hstable : (prefixWord ++ tailWord_7961057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961057).length < 2 ^ (prefixWord ++ tailWord_7961057).sum := by decide
  have hdescent : baseEnd_7961057 < baseStart_7961057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961107 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 7]
def baseStart_7961107 : Nat := 118140960795 + 7961107 * 2 ^ 59
def prefixEnd_7961107 : Nat := 4983230072969 + 3 ^ 40 * 7961107 * 2
def baseEnd_7961107 : Nat := 1362624810957829621983347

theorem tailTrace_7961107 : CollatzResearch.WordTrace tailWord_7961107 prefixEnd_7961107 1362624810957829621983347 := by
  unfold tailWord_7961107
  simp only [CollatzResearch.WordTrace]
  refine ⟨290365426769276462673537575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193576951179517641782358383 290365426769276462673537575)
  ·
    refine ⟨435548140153914694010306363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290365426769276462673537575 435548140153914694010306363)
    ·
      refine ⟨653322210230872041015459545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435548140153914694010306363 653322210230872041015459545)
      ·
        refine ⟨489991657673154030761594659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653322210230872041015459545 489991657673154030761594659)
        ·
          refine ⟨734987486509731046142391989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489991657673154030761594659 734987486509731046142391989)
          ·
            refine ⟨68905076860287285575849249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 734987486509731046142391989 68905076860287285575849249)
            ·
              refine ⟨51678807645215464181886937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68905076860287285575849249 51678807645215464181886937)
              ·
                refine ⟨38759105733911598136415203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51678807645215464181886937 38759105733911598136415203)
                ·
                  refine ⟨58138658600867397204622805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38759105733911598136415203 58138658600867397204622805)
                  ·
                    refine ⟨1362624810957829621983347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58138658600867397204622805 1362624810957829621983347)
                    ·
                      rfl

theorem cell23_7961107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_7961107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961107 prefixEnd_7961107 := by exact prefixLift 7961107
  have htrace : WordTrace (prefixWord ++ tailWord_7961107) baseStart_7961107 baseEnd_7961107 := by
    simpa [prefixWord, tailWord_7961107, baseEnd_7961107] using wordTrace_append hprefix tailTrace_7961107
  have hstable : (prefixWord ++ tailWord_7961107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961107).length < 2 ^ (prefixWord ++ tailWord_7961107).sum := by decide
  have hdescent : baseEnd_7961107 < baseStart_7961107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961111 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 7]
def baseStart_7961111 : Nat := 118140960795 + 7961111 * 2 ^ 59
def prefixEnd_7961111 : Nat := 4983230072969 + 3 ^ 40 * 7961111 * 2
def baseEnd_7961111 : Nat := 454208498532900761144447

theorem tailTrace_7961111 : CollatzResearch.WordTrace tailWord_7961111 prefixEnd_7961111 454208498532900761144447 := by
  unfold tailWord_7961111
  simp only [CollatzResearch.WordTrace]
  refine ⟨290365572661261971356683187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193577048440841314237788791 290365572661261971356683187)
  ·
    refine ⟨435548358991892957035024781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290365572661261971356683187 435548358991892957035024781)
    ·
      refine ⟨163330634621959858888134293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435548358991892957035024781 163330634621959858888134293)
      ·
        refine ⟨7656123497904368385381295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163330634621959858888134293 7656123497904368385381295)
        ·
          refine ⟨11484185246856552578071943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656123497904368385381295 11484185246856552578071943)
          ·
            refine ⟨17226277870284828867107915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11484185246856552578071943 17226277870284828867107915)
            ·
              refine ⟨25839416805427243300661873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17226277870284828867107915 25839416805427243300661873)
              ·
                refine ⟨19379562604070432475496405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25839416805427243300661873 19379562604070432475496405)
                ·
                  refine ⟨454208498532900761144447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19379562604070432475496405 454208498532900761144447)
                  ·
                    rfl

theorem cell23_7961111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 7].length) (baseStart_7961111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961111 prefixEnd_7961111 := by exact prefixLift 7961111
  have htrace : WordTrace (prefixWord ++ tailWord_7961111) baseStart_7961111 baseEnd_7961111 := by
    simpa [prefixWord, tailWord_7961111, baseEnd_7961111] using wordTrace_append hprefix tailTrace_7961111
  have hstable : (prefixWord ++ tailWord_7961111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961111).length < 2 ^ (prefixWord ++ tailWord_7961111).sum := by decide
  have hdescent : baseEnd_7961111 < baseStart_7961111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961128 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 5]
def baseStart_7961128 : Nat := 118140960795 + 7961128 * 2 ^ 59
def prefixEnd_7961128 : Nat := 4983230072969 + 3 ^ 40 * 7961128 * 2
def baseEnd_7961128 : Nat := 454209468440803698198605

theorem tailTrace_7961128 : CollatzResearch.WordTrace tailWord_7961128 prefixEnd_7961128 454209468440803698198605 := by
  unfold tailWord_7961128
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183096351100191630026019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193577461801466922173368025 145183096351100191630026019)
  ·
    refine ⟨217774644526650287445039029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145183096351100191630026019 217774644526650287445039029)
    ·
      refine ⟨20416372924373464447972409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217774644526650287445039029 20416372924373464447972409)
      ·
        refine ⟨15312279693280098335979307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20416372924373464447972409 15312279693280098335979307)
        ·
          refine ⟨22968419539920147503968961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15312279693280098335979307 22968419539920147503968961)
          ·
            refine ⟨17226314654940110627976721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22968419539920147503968961 17226314654940110627976721)
            ·
              refine ⟨12919735991205082970982541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17226314654940110627976721 12919735991205082970982541)
              ·
                refine ⟨4844900996701906114118453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12919735991205082970982541 4844900996701906114118453)
                ·
                  refine ⟨454209468440803698198605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4844900996701906114118453 454209468440803698198605)
                  ·
                    rfl

theorem cell23_7961128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 5].length) (baseStart_7961128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961128 prefixEnd_7961128 := by exact prefixLift 7961128
  have htrace : WordTrace (prefixWord ++ tailWord_7961128) baseStart_7961128 baseEnd_7961128 := by
    simpa [prefixWord, tailWord_7961128, baseEnd_7961128] using wordTrace_append hprefix tailTrace_7961128
  have hstable : (prefixWord ++ tailWord_7961128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961128).length < 2 ^ (prefixWord ++ tailWord_7961128).sum := by decide
  have hdescent : baseEnd_7961128 < baseStart_7961128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961144 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_7961144 : Nat := 118140960795 + 7961144 * 2 ^ 59
def prefixEnd_7961144 : Nat := 4983230072969 + 3 ^ 40 * 7961144 * 2
def baseEnd_7961144 : Nat := 4087893431657705221187371

theorem tailTrace_7961144 : CollatzResearch.WordTrace tailWord_7961144 prefixEnd_7961144 4087893431657705221187371 := by
  unfold tailWord_7961144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183388135071208996317243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193577850846761611995089657 145183388135071208996317243)
  ·
    refine ⟨217775082202606813494475865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145183388135071208996317243 217775082202606813494475865)
    ·
      refine ⟨163331311651955110120856899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217775082202606813494475865 163331311651955110120856899)
      ·
        refine ⟨244996967477932665181285349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163331311651955110120856899 244996967477932665181285349)
        ·
          refine ⟨45936931402112374721491003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244996967477932665181285349 45936931402112374721491003)
          ·
            refine ⟨68905397103168562082236505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45936931402112374721491003 68905397103168562082236505)
            ·
              refine ⟨51679047827376421561677379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68905397103168562082236505 51679047827376421561677379)
              ·
                refine ⟨77518571741064632342516069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51679047827376421561677379 77518571741064632342516069)
                ·
                  refine ⟨14534732201449618564221763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77518571741064632342516069 14534732201449618564221763)
                  ·
                    refine ⟨21802098302174427846332645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14534732201449618564221763 21802098302174427846332645)
                    ·
                      refine ⟨4087893431657705221187371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21802098302174427846332645 4087893431657705221187371)
                      ·
                        rfl

theorem cell23_7961144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_7961144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961144 prefixEnd_7961144 := by exact prefixLift 7961144
  have htrace : WordTrace (prefixWord ++ tailWord_7961144) baseStart_7961144 baseEnd_7961144 := by
    simpa [prefixWord, tailWord_7961144, baseEnd_7961144] using wordTrace_append hprefix tailTrace_7961144
  have hstable : (prefixWord ++ tailWord_7961144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961144).length < 2 ^ (prefixWord ++ tailWord_7961144).sum := by decide
  have hdescent : baseEnd_7961144 < baseStart_7961144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961156 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7961156 : Nat := 118140960795 + 7961156 * 2 ^ 59
def prefixEnd_7961156 : Nat := 4983230072969 + 3 ^ 40 * 7961156 * 2
def baseEnd_7961156 : Nat := 4087899593425559174237317

theorem tailTrace_7961156 : CollatzResearch.WordTrace tailWord_7961156 prefixEnd_7961156 4087899593425559174237317 := by
  unfold tailWord_7961156
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183606973049472021035661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193578142630732629361380881 145183606973049472021035661)
  ·
    refine ⟨54443852614893552007888373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145183606973049472021035661 54443852614893552007888373)
    ·
      refine ⟨5104111182646270500739535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54443852614893552007888373 5104111182646270500739535)
      ·
        refine ⟨7656166773969405751109303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104111182646270500739535 7656166773969405751109303)
        ·
          refine ⟨11484250160954108626663955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656166773969405751109303 11484250160954108626663955)
          ·
            refine ⟨17226375241431162939995933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11484250160954108626663955 17226375241431162939995933)
            ·
              refine ⟨6459890715536686102498475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17226375241431162939995933 6459890715536686102498475)
              ·
                refine ⟨9689836073305029153747713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459890715536686102498475 9689836073305029153747713)
                ·
                  refine ⟨7267377054978771865310785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689836073305029153747713 7267377054978771865310785)
                  ·
                    refine ⟨5450532791234078898983089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267377054978771865310785 5450532791234078898983089)
                    ·
                      refine ⟨4087899593425559174237317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450532791234078898983089 4087899593425559174237317)
                      ·
                        rfl

theorem cell23_7961156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7961156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961156 prefixEnd_7961156 := by exact prefixLift 7961156
  have htrace : WordTrace (prefixWord ++ tailWord_7961156) baseStart_7961156 baseEnd_7961156 := by
    simpa [prefixWord, tailWord_7961156, baseEnd_7961156] using wordTrace_append hprefix tailTrace_7961156
  have hstable : (prefixWord ++ tailWord_7961156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961156).length < 2 ^ (prefixWord ++ tailWord_7961156).sum := by decide
  have hdescent : baseEnd_7961156 < baseStart_7961156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961164 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7961164 : Nat := 118140960795 + 7961164 * 2 ^ 59
def prefixEnd_7961164 : Nat := 4983230072969 + 3 ^ 40 * 7961164 * 2
def baseEnd_7961164 : Nat := 4087903701270795142937279

theorem tailTrace_7961164 : CollatzResearch.WordTrace tailWord_7961164 prefixEnd_7961164 4087903701270795142937279 := by
  unfold tailWord_7961164
  simp only [CollatzResearch.WordTrace]
  refine ⟨145183752865034980704181273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193578337153379974272241697 145183752865034980704181273)
  ·
    refine ⟨108887814648776235528135955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145183752865034980704181273 108887814648776235528135955)
    ·
      refine ⟨163331721973164353292203933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108887814648776235528135955 163331721973164353292203933)
      ·
        refine ⟨61249395739936632484576475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163331721973164353292203933 61249395739936632484576475)
        ·
          refine ⟨91874093609904948726864713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61249395739936632484576475 91874093609904948726864713)
          ·
            refine ⟨68905570207428711545148535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91874093609904948726864713 68905570207428711545148535)
            ·
              refine ⟨103358355311143067317722803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68905570207428711545148535 103358355311143067317722803)
              ·
                refine ⟨155037532966714600976584205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103358355311143067317722803 155037532966714600976584205)
                ·
                  refine ⟨58139074862517975366219077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155037532966714600976584205 58139074862517975366219077)
                  ·
                    refine ⟨10901076536722120381166077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58139074862517975366219077 10901076536722120381166077)
                    ·
                      refine ⟨4087903701270795142937279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901076536722120381166077 4087903701270795142937279)
                      ·
                        rfl

theorem cell23_7961164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7961164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961164 prefixEnd_7961164 := by exact prefixLift 7961164
  have htrace : WordTrace (prefixWord ++ tailWord_7961164) baseStart_7961164 baseEnd_7961164 := by
    simpa [prefixWord, tailWord_7961164, baseEnd_7961164] using wordTrace_append hprefix tailTrace_7961164
  have hstable : (prefixWord ++ tailWord_7961164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961164).length < 2 ^ (prefixWord ++ tailWord_7961164).sum := by decide
  have hdescent : baseEnd_7961164 < baseStart_7961164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961177 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_7961177 : Nat := 118140960795 + 7961177 * 2 ^ 59
def prefixEnd_7961177 : Nat := 4983230072969 + 3 ^ 40 * 7961177 * 2
def baseEnd_7961177 : Nat := 4087910376519303592074719

theorem tailTrace_7961177 : CollatzResearch.WordTrace tailWord_7961177 prefixEnd_7961177 4087910376519303592074719 := by
  unfold tailWord_7961177
  simp only [CollatzResearch.WordTrace]
  refine ⟨290367979879022864628585785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193578653252681909752390523 290367979879022864628585785)
  ·
    refine ⟨217775984909267148471439339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290367979879022864628585785 217775984909267148471439339)
    ·
      refine ⟨326663977363900722707159009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217775984909267148471439339 326663977363900722707159009)
      ·
        refine ⟨244997983022925542030369257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326663977363900722707159009 244997983022925542030369257)
        ·
          refine ⟨183748487267194156522776943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244997983022925542030369257 183748487267194156522776943)
          ·
            refine ⟨275622730900791234784165415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183748487267194156522776943 275622730900791234784165415)
            ·
              refine ⟨413434096351186852176248123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275622730900791234784165415 413434096351186852176248123)
              ·
                refine ⟨620151144526780278264372185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413434096351186852176248123 620151144526780278264372185)
                ·
                  refine ⟨465113358395085208698279139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620151144526780278264372185 465113358395085208698279139)
                  ·
                    refine ⟨697670037592627813047418709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465113358395085208698279139 697670037592627813047418709)
                    ·
                      refine ⟨4087910376519303592074719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 697670037592627813047418709 4087910376519303592074719)
                      ·
                        rfl

theorem cell23_7961177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_7961177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961177 prefixEnd_7961177 := by exact prefixLift 7961177
  have htrace : WordTrace (prefixWord ++ tailWord_7961177) baseStart_7961177 baseEnd_7961177 := by
    simpa [prefixWord, tailWord_7961177, baseEnd_7961177] using wordTrace_append hprefix tailTrace_7961177
  have hstable : (prefixWord ++ tailWord_7961177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961177).length < 2 ^ (prefixWord ++ tailWord_7961177).sum := by decide
  have hdescent : baseEnd_7961177 < baseStart_7961177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961198 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7961198 : Nat := 118140960795 + 7961198 * 2 ^ 59
def prefixEnd_7961198 : Nat := 4983230072969 + 3 ^ 40 * 7961198 * 2
def baseEnd_7961198 : Nat := 4087921159613048009912123

theorem tailTrace_7961198 : CollatzResearch.WordTrace tailWord_7961198 prefixEnd_7961198 4087921159613048009912123 := by
  unfold tailWord_7961198
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296093226493348151887531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193579163874631190143400165 36296093226493348151887531)
  ·
    refine ⟨54444139839740022227831297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36296093226493348151887531 54444139839740022227831297)
    ·
      refine ⟨40833104879805016670873473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54444139839740022227831297 40833104879805016670873473)
      ·
        refine ⟨30624828659853762503155105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40833104879805016670873473 30624828659853762503155105)
        ·
          refine ⟨22968621494890321877366329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30624828659853762503155105 22968621494890321877366329)
          ·
            refine ⟨17226466121167741408024747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22968621494890321877366329 17226466121167741408024747)
            ·
              refine ⟨25839699181751612112037121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17226466121167741408024747 25839699181751612112037121)
              ·
                refine ⟨19379774386313709084027841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25839699181751612112037121 19379774386313709084027841)
                ·
                  refine ⟨14534830789735281813020881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19379774386313709084027841 14534830789735281813020881)
                  ·
                    refine ⟨10901123092301461359765661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14534830789735281813020881 10901123092301461359765661)
                    ·
                      refine ⟨4087921159613048009912123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901123092301461359765661 4087921159613048009912123)
                      ·
                        rfl

theorem cell23_7961198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7961198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961198 prefixEnd_7961198 := by exact prefixLift 7961198
  have htrace : WordTrace (prefixWord ++ tailWord_7961198) baseStart_7961198 baseEnd_7961198 := by
    simpa [prefixWord, tailWord_7961198, baseEnd_7961198] using wordTrace_append hprefix tailTrace_7961198
  have hstable : (prefixWord ++ tailWord_7961198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961198).length < 2 ^ (prefixWord ++ tailWord_7961198).sum := by decide
  have hdescent : baseEnd_7961198 < baseStart_7961198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961205 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7961205 : Nat := 118140960795 + 7961205 * 2 ^ 59
def prefixEnd_7961205 : Nat := 4983230072969 + 3 ^ 40 * 7961205 * 2
def baseEnd_7961205 : Nat := 1362641584659209827508197

theorem tailTrace_7961205 : CollatzResearch.WordTrace tailWord_7961205 prefixEnd_7961205 1362641584659209827508197 := by
  unfold tailWord_7961205
  simp only [CollatzResearch.WordTrace]
  refine ⟨290369001122921425410605069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193579334081947616940403379 290369001122921425410605069)
  ·
    refine ⟨108888375421095534528976901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290369001122921425410605069 108888375421095534528976901)
    ·
      refine ⟨20416570391455412724183169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108888375421095534528976901 20416570391455412724183169)
      ·
        refine ⟨15312427793591559543137377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20416570391455412724183169 15312427793591559543137377)
        ·
          refine ⟨11484320845193669657353033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15312427793591559543137377 11484320845193669657353033)
          ·
            refine ⟨8613240633895252243014775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484320845193669657353033 8613240633895252243014775)
            ·
              refine ⟨12919860950842878364522163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613240633895252243014775 12919860950842878364522163)
              ·
                refine ⟨19379791426264317546783245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12919860950842878364522163 19379791426264317546783245)
                ·
                  refine ⟨7267421784849119080043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19379791426264317546783245 7267421784849119080043717)
                  ·
                    refine ⟨1362641584659209827508197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267421784849119080043717 1362641584659209827508197)
                    ·
                      rfl

theorem cell23_7961205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7961205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961205 prefixEnd_7961205 := by exact prefixLift 7961205
  have htrace : WordTrace (prefixWord ++ tailWord_7961205) baseStart_7961205 baseEnd_7961205 := by
    simpa [prefixWord, tailWord_7961205, baseEnd_7961205] using wordTrace_append hprefix tailTrace_7961205
  have hstable : (prefixWord ++ tailWord_7961205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961205).length < 2 ^ (prefixWord ++ tailWord_7961205).sum := by decide
  have hdescent : baseEnd_7961205 < baseStart_7961205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961211 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 3]
def baseStart_7961211 : Nat := 118140960795 + 7961211 * 2 ^ 59
def prefixEnd_7961211 : Nat := 4983230072969 + 3 ^ 40 * 7961211 * 2
def baseEnd_7961211 : Nat := 4087927834861556459049563

theorem tailTrace_7961211 : CollatzResearch.WordTrace tailWord_7961211 prefixEnd_7961211 4087927834861556459049563 := by
  unfold tailWord_7961211
  simp only [CollatzResearch.WordTrace]
  refine ⟨290369219960899688435323487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193579479973933125623548991 290369219960899688435323487)
  ·
    refine ⟨435553829941349532652985231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290369219960899688435323487 435553829941349532652985231)
    ·
      refine ⟨653330744912024298979477847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435553829941349532652985231 653330744912024298979477847)
      ·
        refine ⟨979996117368036448469216771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653330744912024298979477847 979996117368036448469216771)
        ·
          refine ⟨1469994176052054672703825157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979996117368036448469216771 1469994176052054672703825157)
          ·
            refine ⟨275623908009760251131967217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1469994176052054672703825157 275623908009760251131967217)
            ·
              refine ⟨206717931007320188348975413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275623908009760251131967217 206717931007320188348975413)
              ·
                refine ⟨19379806031936267657716445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206717931007320188348975413 19379806031936267657716445)
                ·
                  refine ⟨7267427261976100371643667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19379806031936267657716445 7267427261976100371643667)
                  ·
                    refine ⟨10901140892964150557465501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7267427261976100371643667 10901140892964150557465501)
                    ·
                      refine ⟨4087927834861556459049563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901140892964150557465501 4087927834861556459049563)
                      ·
                        rfl

theorem cell23_7961211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 3].length) (baseStart_7961211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961211 prefixEnd_7961211 := by exact prefixLift 7961211
  have htrace : WordTrace (prefixWord ++ tailWord_7961211) baseStart_7961211 baseEnd_7961211 := by
    simpa [prefixWord, tailWord_7961211, baseEnd_7961211] using wordTrace_append hprefix tailTrace_7961211
  have hstable : (prefixWord ++ tailWord_7961211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961211).length < 2 ^ (prefixWord ++ tailWord_7961211).sum := by decide
  have hdescent : baseEnd_7961211 < baseStart_7961211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961264 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_7961264 : Nat := 118140960795 + 7961264 * 2 ^ 59
def prefixEnd_7961264 : Nat := 4983230072969 + 3 ^ 40 * 7961264 * 2
def baseEnd_7961264 : Nat := 4087955049336244751686819

theorem tailTrace_7961264 : CollatzResearch.WordTrace tailWord_7961264 prefixEnd_7961264 4087955049336244751686819 := by
  unfold tailWord_7961264
  simp only [CollatzResearch.WordTrace]
  refine ⟨145185576514853839243501423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193580768686471785658001897 145185576514853839243501423)
  ·
    refine ⟨217778364772280758865252135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145185576514853839243501423 217778364772280758865252135)
    ·
      refine ⟨326667547158421138297878203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217778364772280758865252135 326667547158421138297878203)
      ·
        refine ⟨490001320737631707446817305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326667547158421138297878203 490001320737631707446817305)
        ·
          refine ⟨367500990553223780585112979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490001320737631707446817305 367500990553223780585112979)
          ·
            refine ⟨551251485829835670877669469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367500990553223780585112979 551251485829835670877669469)
            ·
              refine ⟨206719307186188376579126051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551251485829835670877669469 206719307186188376579126051)
              ·
                refine ⟨310078960779282564868689077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206719307186188376579126051 310078960779282564868689077)
                ·
                  refine ⟨29069902573057740456439601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310078960779282564868689077 29069902573057740456439601)
                  ·
                    refine ⟨21802426929793305342329701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29069902573057740456439601 21802426929793305342329701)
                    ·
                      refine ⟨4087955049336244751686819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21802426929793305342329701 4087955049336244751686819)
                      ·
                        rfl

theorem cell23_7961264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_7961264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961264 prefixEnd_7961264 := by exact prefixLift 7961264
  have htrace : WordTrace (prefixWord ++ tailWord_7961264) baseStart_7961264 baseEnd_7961264 := by
    simpa [prefixWord, tailWord_7961264, baseEnd_7961264] using wordTrace_append hprefix tailTrace_7961264
  have hstable : (prefixWord ++ tailWord_7961264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961264).length < 2 ^ (prefixWord ++ tailWord_7961264).sum := by decide
  have hdescent : baseEnd_7961264 < baseStart_7961264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961278 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7961278 : Nat := 118140960795 + 7961278 * 2 ^ 59
def prefixEnd_7961278 : Nat := 4983230072969 + 3 ^ 40 * 7961278 * 2
def baseEnd_7961278 : Nat := 1362654079355135898970585

theorem tailTrace_7961278 : CollatzResearch.WordTrace tailWord_7961278 prefixEnd_7961278 1362654079355135898970585 := by
  unfold tailWord_7961278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296457956457119859751561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193581109101104639252008325 36296457956457119859751561)
  ·
    refine ⟨27222343467342839894813671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36296457956457119859751561 27222343467342839894813671)
    ·
      refine ⟨40833515201014259842220507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27222343467342839894813671 40833515201014259842220507)
      ·
        refine ⟨61250272801521389763330761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40833515201014259842220507 61250272801521389763330761)
        ·
          refine ⟨45937704601141042322498071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61250272801521389763330761 45937704601141042322498071)
          ·
            refine ⟨68906556901711563483747107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45937704601141042322498071 68906556901711563483747107)
            ·
              refine ⟨103359835352567345225620661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68906556901711563483747107 103359835352567345225620661)
              ·
                refine ⟨9689984564303188614901937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103359835352567345225620661 9689984564303188614901937)
                ·
                  refine ⟨7267488423227391461176453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9689984564303188614901937 7267488423227391461176453)
                  ·
                    refine ⟨1362654079355135898970585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267488423227391461176453 1362654079355135898970585)
                    ·
                      rfl

theorem cell23_7961278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7961278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961278 prefixEnd_7961278 := by exact prefixLift 7961278
  have htrace : WordTrace (prefixWord ++ tailWord_7961278) baseStart_7961278 baseEnd_7961278 := by
    simpa [prefixWord, tailWord_7961278, baseEnd_7961278] using wordTrace_append hprefix tailTrace_7961278
  have hstable : (prefixWord ++ tailWord_7961278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961278).length < 2 ^ (prefixWord ++ tailWord_7961278).sum := by decide
  have hdescent : baseEnd_7961278 < baseStart_7961278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961358 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7961358 : Nat := 118140960795 + 7961358 * 2 ^ 59
def prefixEnd_7961358 : Nat := 4983230072969 + 3 ^ 40 * 7961358 * 2
def baseEnd_7961358 : Nat := 4088003316517767383911387

theorem tailTrace_7961358 : CollatzResearch.WordTrace tailWord_7961358 prefixEnd_7961358 4088003316517767383911387 := by
  unfold tailWord_7961358
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296822686420891567615591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193583054327578088360616485 36296822686420891567615591)
  ·
    refine ⟨54445234029631337351423387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36296822686420891567615591 54445234029631337351423387)
    ·
      refine ⟨81667851044447006027135081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54445234029631337351423387 81667851044447006027135081)
      ·
        refine ⟨61250888283335254520351311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81667851044447006027135081 61250888283335254520351311)
        ·
          refine ⟨91876332425002881780526967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61250888283335254520351311 91876332425002881780526967)
          ·
            refine ⟨137814498637504322670790451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91876332425002881780526967 137814498637504322670790451)
            ·
              refine ⟨206721747956256484006185677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137814498637504322670790451 206721747956256484006185677)
              ·
                refine ⟨77520655483596181502319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206721747956256484006185677 77520655483596181502319629)
                ·
                  refine ⟨29070245806348568063369861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77520655483596181502319629 29070245806348568063369861)
                  ·
                    refine ⟨5450671088690356511881849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29070245806348568063369861 5450671088690356511881849)
                    ·
                      refine ⟨4088003316517767383911387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450671088690356511881849 4088003316517767383911387)
                      ·
                        rfl

theorem cell23_7961358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7961358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961358 prefixEnd_7961358 := by exact prefixLift 7961358
  have htrace : WordTrace (prefixWord ++ tailWord_7961358) baseStart_7961358 baseEnd_7961358 := by
    simpa [prefixWord, tailWord_7961358, baseEnd_7961358] using wordTrace_append hprefix tailTrace_7961358
  have hstable : (prefixWord ++ tailWord_7961358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961358).length < 2 ^ (prefixWord ++ tailWord_7961358).sum := by decide
  have hdescent : baseEnd_7961358 < baseStart_7961358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961375 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 4, 2, 2]
def baseStart_7961375 : Nat := 118140960795 + 7961375 * 2 ^ 59
def prefixEnd_7961375 : Nat := 4983230072969 + 3 ^ 40 * 7961375 * 2
def baseEnd_7961375 : Nat := 4088012045688893817398809

theorem tailTrace_7961375 : CollatzResearch.WordTrace tailWord_7961375 prefixEnd_7961375 4088012045688893817398809 := by
  unfold tailWord_7961375
  simp only [CollatzResearch.WordTrace]
  refine ⟨290375201532305544444293579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193583467688203696296195719 290375201532305544444293579)
  ·
    refine ⟨435562802298458316666440369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290375201532305544444293579 435562802298458316666440369)
    ·
      refine ⟨326672101723843737499830277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435562802298458316666440369 326672101723843737499830277)
      ·
        refine ⟨61251019073220700781218177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326672101723843737499830277 61251019073220700781218177)
        ·
          refine ⟨45938264304915525585913633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61251019073220700781218177 45938264304915525585913633)
          ·
            refine ⟨34453698228686644189435225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45938264304915525585913633 34453698228686644189435225)
            ·
              refine ⟨25840273671514983142076419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34453698228686644189435225 25840273671514983142076419)
              ·
                refine ⟨38760410507272474713114629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25840273671514983142076419 38760410507272474713114629)
                ·
                  refine ⟨7267576970113589008708993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38760410507272474713114629 7267576970113589008708993)
                  ·
                    refine ⟨5450682727585191756531745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7267576970113589008708993 5450682727585191756531745)
                    ·
                      refine ⟨4088012045688893817398809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450682727585191756531745 4088012045688893817398809)
                      ·
                        rfl

theorem cell23_7961375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_7961375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961375 prefixEnd_7961375 := by exact prefixLift 7961375
  have htrace : WordTrace (prefixWord ++ tailWord_7961375) baseStart_7961375 baseEnd_7961375 := by
    simpa [prefixWord, tailWord_7961375, baseEnd_7961375] using wordTrace_append hprefix tailTrace_7961375
  have hstable : (prefixWord ++ tailWord_7961375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961375).length < 2 ^ (prefixWord ++ tailWord_7961375).sum := by decide
  have hdescent : baseEnd_7961375 < baseStart_7961375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961386 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7961386 : Nat := 118140960795 + 7961386 * 2 ^ 59
def prefixEnd_7961386 : Nat := 4983230072969 + 3 ^ 40 * 7961386 * 2
def baseEnd_7961386 : Nat := 4088017693976093274361259

theorem tailTrace_7961386 : CollatzResearch.WordTrace tailWord_7961386 prefixEnd_7961386 4088017693976093274361259 := by
  unfold tailWord_7961386
  simp only [CollatzResearch.WordTrace]
  refine ⟨72593900683816423330736003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193583735156843795548629341 72593900683816423330736003)
  ·
    refine ⟨108890851025724634996104005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72593900683816423330736003 108890851025724634996104005)
    ·
      refine ⟨20417034567323369061769501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108890851025724634996104005 20417034567323369061769501)
      ·
        refine ⟨7656387962746263398163563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20417034567323369061769501 7656387962746263398163563)
        ·
          refine ⟨11484581944119395097245345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656387962746263398163563 11484581944119395097245345)
          ·
            refine ⟨8613436458089546322934009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484581944119395097245345 8613436458089546322934009)
            ·
              refine ⟨6460077343567159742200507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613436458089546322934009 6460077343567159742200507)
              ·
                refine ⟨9690116015350739613300761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460077343567159742200507 9690116015350739613300761)
                ·
                  refine ⟨7267587011513054709975571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9690116015350739613300761 7267587011513054709975571)
                  ·
                    refine ⟨10901380517269582064963357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7267587011513054709975571 10901380517269582064963357)
                    ·
                      refine ⟨4088017693976093274361259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901380517269582064963357 4088017693976093274361259)
                      ·
                        rfl

theorem cell23_7961386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7961386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961386 prefixEnd_7961386 := by exact prefixLift 7961386
  have htrace : WordTrace (prefixWord ++ tailWord_7961386) baseStart_7961386 baseEnd_7961386 := by
    simpa [prefixWord, tailWord_7961386, baseEnd_7961386] using wordTrace_append hprefix tailTrace_7961386
  have hstable : (prefixWord ++ tailWord_7961386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961386).length < 2 ^ (prefixWord ++ tailWord_7961386).sum := by decide
  have hdescent : baseEnd_7961386 < baseStart_7961386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961396 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_7961396 : Nat := 118140960795 + 7961396 * 2 ^ 59
def prefixEnd_7961396 : Nat := 4983230072969 + 3 ^ 40 * 7961396 * 2
def baseEnd_7961396 : Nat := 4088022828782638235236213

theorem tailTrace_7961396 : CollatzResearch.WordTrace tailWord_7961396 prefixEnd_7961396 4088022828782638235236213 := by
  unfold tailWord_7961396
  simp only [CollatzResearch.WordTrace]
  refine ⟨145187983732614732515404021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193583978310152976687205361 145187983732614732515404021)
  ·
    refine ⟨13611373474932631173319127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145187983732614732515404021 13611373474932631173319127)
    ·
      refine ⟨20417060212398946759978691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13611373474932631173319127 20417060212398946759978691)
      ·
        refine ⟨30625590318598420139968037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20417060212398946759978691 30625590318598420139968037)
        ·
          refine ⟨5742298184737203776244007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30625590318598420139968037 5742298184737203776244007)
          ·
            refine ⟨8613447277105805664366011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742298184737203776244007 8613447277105805664366011)
            ·
              refine ⟨12920170915658708496549017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613447277105805664366011 12920170915658708496549017)
              ·
                refine ⟨9690128186744031372411763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12920170915658708496549017 9690128186744031372411763)
                ·
                  refine ⟨14535192280116047058617645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690128186744031372411763 14535192280116047058617645)
                  ·
                    refine ⟨5450697105043517646981617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14535192280116047058617645 5450697105043517646981617)
                    ·
                      refine ⟨4088022828782638235236213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450697105043517646981617 4088022828782638235236213)
                      ·
                        rfl

theorem cell23_7961396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_7961396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961396 prefixEnd_7961396 := by exact prefixLift 7961396
  have htrace : WordTrace (prefixWord ++ tailWord_7961396) baseStart_7961396 baseEnd_7961396 := by
    simpa [prefixWord, tailWord_7961396, baseEnd_7961396] using wordTrace_append hprefix tailTrace_7961396
  have hstable : (prefixWord ++ tailWord_7961396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961396).length < 2 ^ (prefixWord ++ tailWord_7961396).sum := by decide
  have hdescent : baseEnd_7961396 < baseStart_7961396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961458 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_7961458 : Nat := 118140960795 + 7961458 * 2 ^ 59
def prefixEnd_7961458 : Nat := 4983230072969 + 3 ^ 40 * 7961458 * 2
def baseEnd_7961458 : Nat := 1362684888194405664220309

theorem tailTrace_7961458 : CollatzResearch.WordTrace tailWord_7961458 prefixEnd_7961458 1362684888194405664220309 := by
  unfold tailWord_7961458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72594557197751212404891257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193585485860669899746376685 72594557197751212404891257)
  ·
    refine ⟨54445917898313409303668443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72594557197751212404891257 54445917898313409303668443)
    ·
      refine ⟨81668876847470113955502665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54445917898313409303668443 81668876847470113955502665)
      ·
        refine ⟨61251657635602585466626999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81668876847470113955502665 61251657635602585466626999)
        ·
          refine ⟨91877486453403878199940499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61251657635602585466626999 91877486453403878199940499)
          ·
            refine ⟨137816229680105817299910749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91877486453403878199940499 137816229680105817299910749)
            ·
              refine ⟨51681086130039681487466531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137816229680105817299910749 51681086130039681487466531)
              ·
                refine ⟨77521629195059522231199797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51681086130039681487466531 77521629195059522231199797)
                ·
                  refine ⟨7267652737036830209174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77521629195059522231199797 7267652737036830209174981)
                  ·
                    refine ⟨1362684888194405664220309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267652737036830209174981 1362684888194405664220309)
                    ·
                      rfl

theorem cell23_7961458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_7961458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961458 prefixEnd_7961458 := by exact prefixLift 7961458
  have htrace : WordTrace (prefixWord ++ tailWord_7961458) baseStart_7961458 baseEnd_7961458 := by
    simpa [prefixWord, tailWord_7961458, baseEnd_7961458] using wordTrace_append hprefix tailTrace_7961458
  have hstable : (prefixWord ++ tailWord_7961458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961458).length < 2 ^ (prefixWord ++ tailWord_7961458).sum := by decide
  have hdescent : baseEnd_7961458 < baseStart_7961458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961462 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7961462 : Nat := 118140960795 + 7961462 * 2 ^ 59
def prefixEnd_7961462 : Nat := 4983230072969 + 3 ^ 40 * 7961462 * 2
def baseEnd_7961462 : Nat := 1362685572835278325670303

theorem tailTrace_7961462 : CollatzResearch.WordTrace tailWord_7961462 prefixEnd_7961462 1362685572835278325670303 := by
  unfold tailWord_7961462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18148648417686897393919415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193585583121993572201807093 18148648417686897393919415)
  ·
    refine ⟨27222972626530346090879123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18148648417686897393919415 27222972626530346090879123)
    ·
      refine ⟨40834458939795519136318685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27222972626530346090879123 40834458939795519136318685)
      ·
        refine ⟨15312922102423319676119507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40834458939795519136318685 15312922102423319676119507)
        ·
          refine ⟨22969383153634979514179261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15312922102423319676119507 22969383153634979514179261)
          ·
            refine ⟨8613518682613117317817223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22969383153634979514179261 8613518682613117317817223)
            ·
              refine ⟨12920278023919675976725835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613518682613117317817223 12920278023919675976725835)
              ·
                refine ⟨19380417035879513965088753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920278023919675976725835 19380417035879513965088753)
                ·
                  refine ⟨14535312776909635473816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19380417035879513965088753 14535312776909635473816565)
                  ·
                    refine ⟨1362685572835278325670303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14535312776909635473816565 1362685572835278325670303)
                    ·
                      rfl

theorem cell23_7961462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7961462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961462 prefixEnd_7961462 := by exact prefixLift 7961462
  have htrace : WordTrace (prefixWord ++ tailWord_7961462) baseStart_7961462 baseEnd_7961462 := by
    simpa [prefixWord, tailWord_7961462, baseEnd_7961462] using wordTrace_append hprefix tailTrace_7961462
  have hstable : (prefixWord ++ tailWord_7961462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961462).length < 2 ^ (prefixWord ++ tailWord_7961462).sum := by decide
  have hdescent : baseEnd_7961462 < baseStart_7961462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961465 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7961465 : Nat := 118140960795 + 7961465 * 2 ^ 59
def prefixEnd_7961465 : Nat := 4983230072969 + 3 ^ 40 * 7961465 * 2
def baseEnd_7961465 : Nat := 4088058258947798465273395

theorem tailTrace_7961465 : CollatzResearch.WordTrace tailWord_7961465 prefixEnd_7961465 4088058258947798465273395 := by
  unfold tailWord_7961465
  simp only [CollatzResearch.WordTrace]
  refine ⟨290378484101979489815069849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193585656067986326543379899 290378484101979489815069849)
  ·
    refine ⟨217783863076484617361302387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290378484101979489815069849 217783863076484617361302387)
    ·
      refine ⟨326675794614726926041953581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217783863076484617361302387 326675794614726926041953581)
      ·
        refine ⟨122503422980522597265732593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326675794614726926041953581 122503422980522597265732593)
        ·
          refine ⟨91877567235391947949299445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122503422980522597265732593 91877567235391947949299445)
          ·
            refine ⟨8613521928317995120246823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91877567235391947949299445 8613521928317995120246823)
            ·
              refine ⟨12920282892476992680370235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613521928317995120246823 12920282892476992680370235)
              ·
                refine ⟨19380424338715489020555353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920282892476992680370235 19380424338715489020555353)
                ·
                  refine ⟨14535318254036616765416515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19380424338715489020555353 14535318254036616765416515)
                  ·
                    refine ⟨21802977381054925148124773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14535318254036616765416515 21802977381054925148124773)
                    ·
                      refine ⟨4088058258947798465273395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21802977381054925148124773 4088058258947798465273395)
                      ·
                        rfl

theorem cell23_7961465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7961465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961465 prefixEnd_7961465 := by exact prefixLift 7961465
  have htrace : WordTrace (prefixWord ++ tailWord_7961465) baseStart_7961465 baseEnd_7961465 := by
    simpa [prefixWord, tailWord_7961465, baseEnd_7961465] using wordTrace_append hprefix tailTrace_7961465
  have hstable : (prefixWord ++ tailWord_7961465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961465).length < 2 ^ (prefixWord ++ tailWord_7961465).sum := by decide
  have hdescent : baseEnd_7961465 < baseStart_7961465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961492 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7961492 : Nat := 118140960795 + 7961492 * 2 ^ 59
def prefixEnd_7961492 : Nat := 4983230072969 + 3 ^ 40 * 7961492 * 2
def baseEnd_7961492 : Nat := 1362690707641823286545257

theorem tailTrace_7961492 : CollatzResearch.WordTrace tailWord_7961492 prefixEnd_7961492 1362690707641823286545257 := by
  unfold tailWord_7961492
  simp only [CollatzResearch.WordTrace]
  refine ⟨145189734436440836713151365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193586312581921115617535153 145189734436440836713151365)
  ·
    refine ⟨27223075206832656883715881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145189734436440836713151365 27223075206832656883715881)
    ·
      refine ⟨20417306405124492662786911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27223075206832656883715881 20417306405124492662786911)
      ·
        refine ⟨30625959607686738994180367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20417306405124492662786911 30625959607686738994180367)
        ·
          refine ⟨45938939411530108491270551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30625959607686738994180367 45938939411530108491270551)
          ·
            refine ⟨68908409117295162736905827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45938939411530108491270551 68908409117295162736905827)
            ·
              refine ⟨103362613675942744105358741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68908409117295162736905827 103362613675942744105358741)
              ·
                refine ⟨4845122516059816129938691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103362613675942744105358741 4845122516059816129938691)
                ·
                  refine ⟨7267683774089724194908037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845122516059816129938691 7267683774089724194908037)
                  ·
                    refine ⟨1362690707641823286545257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7267683774089724194908037 1362690707641823286545257)
                    ·
                      rfl

theorem cell23_7961492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7961492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961492 prefixEnd_7961492 := by exact prefixLift 7961492
  have htrace : WordTrace (prefixWord ++ tailWord_7961492) baseStart_7961492 baseEnd_7961492 := by
    simpa [prefixWord, tailWord_7961492, baseEnd_7961492] using wordTrace_append hprefix tailTrace_7961492
  have hstable : (prefixWord ++ tailWord_7961492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961492).length < 2 ^ (prefixWord ++ tailWord_7961492).sum := by decide
  have hdescent : baseEnd_7961492 < baseStart_7961492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961525 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7961525 : Nat := 118140960795 + 7961525 * 2 ^ 59
def prefixEnd_7961525 : Nat := 4983230072969 + 3 ^ 40 * 7961525 * 2
def baseEnd_7961525 : Nat := 4088089067787068230523119

theorem tailTrace_7961525 : CollatzResearch.WordTrace tailWord_7961525 prefixEnd_7961525 4088089067787068230523119 := by
  unfold tailWord_7961525
  simp only [CollatzResearch.WordTrace]
  refine ⟨290380672481762120062254029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193587114987841413374836019 290380672481762120062254029)
  ·
    refine ⟨108892752180660795023345261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290380672481762120062254029 108892752180660795023345261)
    ·
      refine ⟨40834782067747798133754473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108892752180660795023345261 40834782067747798133754473)
      ·
        refine ⟨30626086550810848600315855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40834782067747798133754473 30626086550810848600315855)
        ·
          refine ⟨45939129826216272900473783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30626086550810848600315855 45939129826216272900473783)
          ·
            refine ⟨68908694739324409350710675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45939129826216272900473783 68908694739324409350710675)
            ·
              refine ⟨103363042108986614026066013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68908694739324409350710675 103363042108986614026066013)
              ·
                refine ⟨38761140790869980259774755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103363042108986614026066013 38761140790869980259774755)
                ·
                  refine ⟨58141711186304970389662133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38761140790869980259774755 58141711186304970389662133)
                  ·
                    refine ⟨5450785423716090974030825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58141711186304970389662133 5450785423716090974030825)
                    ·
                      refine ⟨4088089067787068230523119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5450785423716090974030825 4088089067787068230523119)
                      ·
                        rfl

theorem cell23_7961525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7961525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961525 prefixEnd_7961525 := by exact prefixLift 7961525
  have htrace : WordTrace (prefixWord ++ tailWord_7961525) baseStart_7961525 baseEnd_7961525 := by
    simpa [prefixWord, tailWord_7961525, baseEnd_7961525] using wordTrace_append hprefix tailTrace_7961525
  have hstable : (prefixWord ++ tailWord_7961525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961525).length < 2 ^ (prefixWord ++ tailWord_7961525).sum := by decide
  have hdescent : baseEnd_7961525 < baseStart_7961525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961578 : List Nat := [3, 1, 3, 1, 2, 2, 2, 9]
def baseStart_7961578 : Nat := 118140960795 + 7961578 * 2 ^ 59
def prefixEnd_7961578 : Nat := 4983230072969 + 3 ^ 40 * 7961578 * 2
def baseEnd_7961578 : Nat := 151411714157842834191125

theorem tailTrace_7961578 : CollatzResearch.WordTrace tailWord_7961578 prefixEnd_7961578 151411714157842834191125 := by
  unfold tailWord_7961578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72595651387642527528483347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193588403700380073409288925 72595651387642527528483347)
  ·
    refine ⟨108893477081463791292725021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72595651387642527528483347 108893477081463791292725021)
    ·
      refine ⟨40835053905548921734771883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108893477081463791292725021 40835053905548921734771883)
      ·
        refine ⟨61252580858323382602157825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40835053905548921734771883 61252580858323382602157825)
        ·
          refine ⟨45939435643742536951618369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61252580858323382602157825 45939435643742536951618369)
          ·
            refine ⟨34454576732806902713713777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45939435643742536951618369 34454576732806902713713777)
            ·
              refine ⟨25840932549605177035285333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34454576732806902713713777 25840932549605177035285333)
              ·
                refine ⟨151411714157842834191125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25840932549605177035285333 151411714157842834191125)
                ·
                  rfl

theorem cell23_7961578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_7961578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961578 prefixEnd_7961578 := by exact prefixLift 7961578
  have htrace : WordTrace (prefixWord ++ tailWord_7961578) baseStart_7961578 baseEnd_7961578 := by
    simpa [prefixWord, tailWord_7961578, baseEnd_7961578] using wordTrace_append hprefix tailTrace_7961578
  have hstable : (prefixWord ++ tailWord_7961578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961578).length < 2 ^ (prefixWord ++ tailWord_7961578).sum := by decide
  have hdescent : baseEnd_7961578 < baseStart_7961578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961585 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_7961585 : Nat := 118140960795 + 7961585 * 2 ^ 59
def prefixEnd_7961585 : Nat := 4983230072969 + 3 ^ 40 * 7961585 * 2
def baseEnd_7961585 : Nat := 4088119876626337995772843

theorem tailTrace_7961585 : CollatzResearch.WordTrace tailWord_7961585 prefixEnd_7961585 4088119876626337995772843 := by
  unfold tailWord_7961585
  simp only [CollatzResearch.WordTrace]
  refine ⟨290382860861544750309438209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193588573907696500206292139 290382860861544750309438209)
  ·
    refine ⟨217787145646158562732078657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290382860861544750309438209 217787145646158562732078657)
    ·
      refine ⟨163340359234618922049058993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217787145646158562732078657 163340359234618922049058993)
      ·
        refine ⟨122505269425964191536794245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163340359234618922049058993 122505269425964191536794245)
        ·
          refine ⟨22969738017368285913148921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122505269425964191536794245 22969738017368285913148921)
          ·
            refine ⟨17227303513026214434861691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22969738017368285913148921 17227303513026214434861691)
            ·
              refine ⟨25840955269539321652292537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17227303513026214434861691 25840955269539321652292537)
              ·
                refine ⟨19380716452154491239219403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25840955269539321652292537 19380716452154491239219403)
                ·
                  refine ⟨29071074678231736858829105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19380716452154491239219403 29071074678231736858829105)
                  ·
                    refine ⟨21803306008673802644121829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29071074678231736858829105 21803306008673802644121829)
                    ·
                      refine ⟨4088119876626337995772843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21803306008673802644121829 4088119876626337995772843)
                      ·
                        rfl

theorem cell23_7961585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_7961585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961585 prefixEnd_7961585 := by exact prefixLift 7961585
  have htrace : WordTrace (prefixWord ++ tailWord_7961585) baseStart_7961585 baseEnd_7961585 := by
    simpa [prefixWord, tailWord_7961585, baseEnd_7961585] using wordTrace_append hprefix tailTrace_7961585
  have hstable : (prefixWord ++ tailWord_7961585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961585).length < 2 ^ (prefixWord ++ tailWord_7961585).sum := by decide
  have hdescent : baseEnd_7961585 < baseStart_7961585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961608 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_7961608 : Nat := 118140960795 + 7961608 * 2 ^ 59
def prefixEnd_7961608 : Nat := 4983230072969 + 3 ^ 40 * 7961608 * 2
def baseEnd_7961608 : Nat := 1362710562227130468595079

theorem tailTrace_7961608 : CollatzResearch.WordTrace tailWord_7961608 prefixEnd_7961608 1362710562227130468595079 := by
  unfold tailWord_7961608
  simp only [CollatzResearch.WordTrace]
  refine ⟨145191849870230712618762739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193589133160307616825016985 145191849870230712618762739)
  ·
    refine ⟨217787774805346068928144109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145191849870230712618762739 217787774805346068928144109)
    ·
      refine ⟨81670415552004775848054041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217787774805346068928144109 81670415552004775848054041)
      ·
        refine ⟨61252811664003581886040531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81670415552004775848054041 61252811664003581886040531)
        ·
          refine ⟨91879217496005372829060797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61252811664003581886040531 91879217496005372829060797)
          ·
            refine ⟨34454706561002014810897799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91879217496005372829060797 34454706561002014810897799)
            ·
              refine ⟨51682059841503022216346699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34454706561002014810897799 51682059841503022216346699)
              ·
                refine ⟨77523089762254533324520049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51682059841503022216346699 77523089762254533324520049)
                ·
                  refine ⟨58142317321690899993390037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77523089762254533324520049 58142317321690899993390037)
                  ·
                    refine ⟨1362710562227130468595079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58142317321690899993390037 1362710562227130468595079)
                    ·
                      rfl

theorem cell23_7961608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_7961608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961608 prefixEnd_7961608 := by exact prefixLift 7961608
  have htrace : WordTrace (prefixWord ++ tailWord_7961608) baseStart_7961608 baseEnd_7961608 := by
    simpa [prefixWord, tailWord_7961608, baseEnd_7961608] using wordTrace_append hprefix tailTrace_7961608
  have hstable : (prefixWord ++ tailWord_7961608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961608).length < 2 ^ (prefixWord ++ tailWord_7961608).sum := by decide
  have hdescent : baseEnd_7961608 < baseStart_7961608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961648 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_7961648 : Nat := 118140960795 + 7961648 * 2 ^ 59
def prefixEnd_7961648 : Nat := 4983230072969 + 3 ^ 40 * 7961648 * 2
def baseEnd_7961648 : Nat := 4088152225907571249285053

theorem tailTrace_7961648 : CollatzResearch.WordTrace tailWord_7961648 prefixEnd_7961648 4088152225907571249285053 := by
  unfold tailWord_7961648
  simp only [CollatzResearch.WordTrace]
  refine ⟨145192579330158256034490799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193590105773544341379321065 145192579330158256034490799)
  ·
    refine ⟨217788868995237384051736199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145192579330158256034490799 217788868995237384051736199)
    ·
      refine ⟨326683303492856076077604299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217788868995237384051736199 326683303492856076077604299)
      ·
        refine ⟨490024955239284114116406449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326683303492856076077604299 490024955239284114116406449)
        ·
          refine ⟨367518716429463085587304837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490024955239284114116406449 367518716429463085587304837)
          ·
            refine ⟨68909759330524328547619657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367518716429463085587304837 68909759330524328547619657)
            ·
              refine ⟨51682319497893246410714743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68909759330524328547619657 51682319497893246410714743)
              ·
                refine ⟨77523479246839869616072115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51682319497893246410714743 77523479246839869616072115)
                ·
                  refine ⟨116285218870259804424108173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77523479246839869616072115 116285218870259804424108173)
                  ·
                    refine ⟨43606957076347426659040565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116285218870259804424108173 43606957076347426659040565)
                    ·
                      refine ⟨4088152225907571249285053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43606957076347426659040565 4088152225907571249285053)
                      ·
                        rfl

theorem cell23_7961648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_7961648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961648 prefixEnd_7961648 := by exact prefixLift 7961648
  have htrace : WordTrace (prefixWord ++ tailWord_7961648) baseStart_7961648 baseEnd_7961648 := by
    simpa [prefixWord, tailWord_7961648, baseEnd_7961648] using wordTrace_append hprefix tailTrace_7961648
  have hstable : (prefixWord ++ tailWord_7961648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961648).length < 2 ^ (prefixWord ++ tailWord_7961648).sum := by decide
  have hdescent : baseEnd_7961648 < baseStart_7961648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961725 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7961725 : Nat := 118140960795 + 7961725 * 2 ^ 59
def prefixEnd_7961725 : Nat := 4983230072969 + 3 ^ 40 * 7961725 * 2
def baseEnd_7961725 : Nat := 4088191763917967448022199

theorem tailTrace_7961725 : CollatzResearch.WordTrace tailWord_7961725 prefixEnd_7961725 4088191763917967448022199 := by
  unfold tailWord_7961725
  simp only [CollatzResearch.WordTrace]
  refine ⟨290387967081037554219534629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193591978054025036146356419 290387967081037554219534629)
  ·
    refine ⟨54447743827694541416162743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290387967081037554219534629 54447743827694541416162743)
    ·
      refine ⟨81671615741541812124244115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54447743827694541416162743 81671615741541812124244115)
      ·
        refine ⟨122507423612312718186366173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81671615741541812124244115 122507423612312718186366173)
        ·
          refine ⟨45940283854617269319887315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122507423612312718186366173 45940283854617269319887315)
          ·
            refine ⟨68910425781925903979830973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45940283854617269319887315 68910425781925903979830973)
            ·
              refine ⟨25841409668222213992436615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68910425781925903979830973 25841409668222213992436615)
              ·
                refine ⟨38762114502333320988654923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25841409668222213992436615 38762114502333320988654923)
                ·
                  refine ⟨58143171753499981482982385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38762114502333320988654923 58143171753499981482982385)
                  ·
                    refine ⟨43607378815124986112236789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58143171753499981482982385 43607378815124986112236789)
                    ·
                      refine ⟨4088191763917967448022199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43607378815124986112236789 4088191763917967448022199)
                      ·
                        rfl

theorem cell23_7961725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7961725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961725 prefixEnd_7961725 := by exact prefixLift 7961725
  have htrace : WordTrace (prefixWord ++ tailWord_7961725) baseStart_7961725 baseEnd_7961725 := by
    simpa [prefixWord, tailWord_7961725, baseEnd_7961725] using wordTrace_append hprefix tailTrace_7961725
  have hstable : (prefixWord ++ tailWord_7961725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961725).length < 2 ^ (prefixWord ++ tailWord_7961725).sum := by decide
  have hdescent : baseEnd_7961725 < baseStart_7961725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961735 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7961735 : Nat := 118140960795 + 7961735 * 2 ^ 59
def prefixEnd_7961735 : Nat := 4983230072969 + 3 ^ 40 * 7961735 * 2
def baseEnd_7961735 : Nat := 4088196898724512408897153

theorem tailTrace_7961735 : CollatzResearch.WordTrace tailWord_7961735 prefixEnd_7961735 4088196898724512408897153 := by
  unfold tailWord_7961735
  simp only [CollatzResearch.WordTrace]
  refine ⟨290388331811001325927398659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193592221207334217284932439 290388331811001325927398659)
  ·
    refine ⟨435582497716501988891097989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290388331811001325927398659 435582497716501988891097989)
    ·
      refine ⟨81671718321844122917080873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435582497716501988891097989 81671718321844122917080873)
      ·
        refine ⟨61253788741383092187810655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81671718321844122917080873 61253788741383092187810655)
        ·
          refine ⟨91880683112074638281715983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61253788741383092187810655 91880683112074638281715983)
          ·
            refine ⟨137821024668111957422573975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91880683112074638281715983 137821024668111957422573975)
            ·
              refine ⟨206731537002167936133860963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137821024668111957422573975 206731537002167936133860963)
              ·
                refine ⟨310097305503251904200791445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206731537002167936133860963 310097305503251904200791445)
                ·
                  refine ⟨14535811195464933009412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310097305503251904200791445 14535811195464933009412099)
                  ·
                    refine ⟨21803716793197399514118149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14535811195464933009412099 21803716793197399514118149)
                    ·
                      refine ⟨4088196898724512408897153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21803716793197399514118149 4088196898724512408897153)
                      ·
                        rfl

theorem cell23_7961735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7961735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961735 prefixEnd_7961735 := by exact prefixLift 7961735
  have htrace : WordTrace (prefixWord ++ tailWord_7961735) baseStart_7961735 baseEnd_7961735 := by
    simpa [prefixWord, tailWord_7961735, baseEnd_7961735] using wordTrace_append hprefix tailTrace_7961735
  have hstable : (prefixWord ++ tailWord_7961735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961735).length < 2 ^ (prefixWord ++ tailWord_7961735).sum := by decide
  have hdescent : baseEnd_7961735 < baseStart_7961735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961752 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7961752 : Nat := 118140960795 + 7961752 * 2 ^ 59
def prefixEnd_7961752 : Nat := 4983230072969 + 3 ^ 40 * 7961752 * 2
def baseEnd_7961752 : Nat := 4088205627895638842384575

theorem tailTrace_7961752 : CollatzResearch.WordTrace tailWord_7961752 prefixEnd_7961752 4088205627895638842384575 := by
  unfold tailWord_7961752
  simp only [CollatzResearch.WordTrace]
  refine ⟨145194475925969868915383755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193592634567959825220511673 145194475925969868915383755)
  ·
    refine ⟨217791713888954803373075633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145194475925969868915383755 217791713888954803373075633)
    ·
      refine ⟨163343785416716102529806725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217791713888954803373075633 163343785416716102529806725)
      ·
        refine ⟨30626959765634269224338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163343785416716102529806725 30626959765634269224338761)
        ·
          refine ⟨22970219824225701918254071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30626959765634269224338761 22970219824225701918254071)
          ·
            refine ⟨34455329736338552877381107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22970219824225701918254071 34455329736338552877381107)
            ·
              refine ⟨51682994604507829316071661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34455329736338552877381107 51682994604507829316071661)
              ·
                refine ⟨19381122976690435993526873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51682994604507829316071661 19381122976690435993526873)
                ·
                  refine ⟨14535842232517826995145155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19381122976690435993526873 14535842232517826995145155)
                  ·
                    refine ⟨21803763348776740492717733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14535842232517826995145155 21803763348776740492717733)
                    ·
                      refine ⟨4088205627895638842384575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21803763348776740492717733 4088205627895638842384575)
                      ·
                        rfl

theorem cell23_7961752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7961752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961752 prefixEnd_7961752 := by exact prefixLift 7961752
  have htrace : WordTrace (prefixWord ++ tailWord_7961752) baseStart_7961752 baseEnd_7961752 := by
    simpa [prefixWord, tailWord_7961752, baseEnd_7961752] using wordTrace_append hprefix tailTrace_7961752
  have hstable : (prefixWord ++ tailWord_7961752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961752).length < 2 ^ (prefixWord ++ tailWord_7961752).sum := by decide
  have hdescent : baseEnd_7961752 < baseStart_7961752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961775 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 6]
def baseStart_7961775 : Nat := 118140960795 + 7961775 * 2 ^ 59
def prefixEnd_7961775 : Nat := 4983230072969 + 3 ^ 40 * 7961775 * 2
def baseEnd_7961775 : Nat := 454246381994521361377441

theorem tailTrace_7961775 : CollatzResearch.WordTrace tailWord_7961775 prefixEnd_7961775 454246381994521361377441 := by
  unfold tailWord_7961775
  simp only [CollatzResearch.WordTrace]
  refine ⟨290389790730856412758854779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193593193820570941839236519 290389790730856412758854779)
  ·
    refine ⟨435584686096284619138282169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290389790730856412758854779 435584686096284619138282169)
    ·
      refine ⟨326688514572213464353711627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435584686096284619138282169 326688514572213464353711627)
      ·
        refine ⟨490032771858320196530567441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326688514572213464353711627 490032771858320196530567441)
        ·
          refine ⟨367524578893740147397925581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490032771858320196530567441 367524578893740147397925581)
          ·
            refine ⟨137821717085152555274222093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367524578893740147397925581 137821717085152555274222093)
            ·
              refine ⟨51683143906932208227833285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137821717085152555274222093 51683143906932208227833285)
              ·
                refine ⟨9690589482549789042718741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51683143906932208227833285 9690589482549789042718741)
                ·
                  refine ⟨454246381994521361377441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9690589482549789042718741 454246381994521361377441)
                  ·
                    rfl

theorem cell23_7961775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 6].length) (baseStart_7961775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961775 prefixEnd_7961775 := by exact prefixLift 7961775
  have htrace : WordTrace (prefixWord ++ tailWord_7961775) baseStart_7961775 baseEnd_7961775 := by
    simpa [prefixWord, tailWord_7961775, baseEnd_7961775] using wordTrace_append hprefix tailTrace_7961775
  have hstable : (prefixWord ++ tailWord_7961775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961775).length < 2 ^ (prefixWord ++ tailWord_7961775).sum := by decide
  have hdescent : baseEnd_7961775 < baseStart_7961775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961806 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_7961806 : Nat := 118140960795 + 7961806 * 2 ^ 59
def prefixEnd_7961806 : Nat := 4983230072969 + 3 ^ 40 * 7961806 * 2
def baseEnd_7961806 : Nat := 4088233355850981631109327

theorem tailTrace_7961806 : CollatzResearch.WordTrace tailWord_7961806 prefixEnd_7961806 4088233355850981631109327 := by
  unfold tailWord_7961806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298865174218013131654159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193593947595829403368822181 36298865174218013131654159)
  ·
    refine ⟨54448297761327019697481239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36298865174218013131654159 54448297761327019697481239)
    ·
      refine ⟨81672446641990529546221859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54448297761327019697481239 81672446641990529546221859)
      ·
        refine ⟨122508669962985794319332789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81672446641990529546221859 122508669962985794319332789)
        ·
          refine ⟨11485187809029918217437449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122508669962985794319332789 11485187809029918217437449)
          ·
            refine ⟨8613890856772438663078087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485187809029918217437449 8613890856772438663078087)
            ·
              refine ⟨12920836285158657994617131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613890856772438663078087 12920836285158657994617131)
              ·
                refine ⟨19381254427737986991925697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920836285158657994617131 19381254427737986991925697)
                ·
                  refine ⟨14535940820803490243944273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19381254427737986991925697 14535940820803490243944273)
                  ·
                    refine ⟨10901955615602617682958205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14535940820803490243944273 10901955615602617682958205)
                    ·
                      refine ⟨4088233355850981631109327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901955615602617682958205 4088233355850981631109327)
                      ·
                        rfl

theorem cell23_7961806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_7961806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961806 prefixEnd_7961806 := by exact prefixLift 7961806
  have htrace : WordTrace (prefixWord ++ tailWord_7961806) baseStart_7961806 baseEnd_7961806 := by
    simpa [prefixWord, tailWord_7961806, baseEnd_7961806] using wordTrace_append hprefix tailTrace_7961806
  have hstable : (prefixWord ++ tailWord_7961806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961806).length < 2 ^ (prefixWord ++ tailWord_7961806).sum := by decide
  have hdescent : baseEnd_7961806 < baseStart_7961806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961836 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_7961836 : Nat := 118140960795 + 7961836 * 2 ^ 59
def prefixEnd_7961836 : Nat := 4983230072969 + 3 ^ 40 * 7961836 * 2
def baseEnd_7961836 : Nat := 4088248760270616513734189

theorem tailTrace_7961836 : CollatzResearch.WordTrace tailWord_7961836 prefixEnd_7961836 4088248760270616513734189 := by
  unfold tailWord_7961836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145196007791817710088412681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193594677055756946784550241 145196007791817710088412681)
  ·
    refine ⟨108897005843863282566309511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145196007791817710088412681 108897005843863282566309511)
    ·
      refine ⟨163345508765794923849464267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108897005843863282566309511 163345508765794923849464267)
      ·
        refine ⟨245018263148692385774196401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163345508765794923849464267 245018263148692385774196401)
        ·
          refine ⟨183763697361519289330647301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245018263148692385774196401 183763697361519289330647301)
          ·
            refine ⟨34455693255284866749496369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183763697361519289330647301 34455693255284866749496369)
            ·
              refine ⟨25841769941463650062122277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34455693255284866749496369 25841769941463650062122277)
              ·
                refine ⟨4845331864024434386647927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25841769941463650062122277 4845331864024434386647927)
                ·
                  refine ⟨7267997796036651579971891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845331864024434386647927 7267997796036651579971891)
                  ·
                    refine ⟨10901996694054977369957837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7267997796036651579971891 10901996694054977369957837)
                    ·
                      refine ⟨4088248760270616513734189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10901996694054977369957837 4088248760270616513734189)
                      ·
                        rfl

theorem cell23_7961836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_7961836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961836 prefixEnd_7961836 := by exact prefixLift 7961836
  have htrace : WordTrace (prefixWord ++ tailWord_7961836) baseStart_7961836 baseEnd_7961836 := by
    simpa [prefixWord, tailWord_7961836, baseEnd_7961836] using wordTrace_append hprefix tailTrace_7961836
  have hstable : (prefixWord ++ tailWord_7961836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961836).length < 2 ^ (prefixWord ++ tailWord_7961836).sum := by decide
  have hdescent : baseEnd_7961836 < baseStart_7961836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961859 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 4]
def baseStart_7961859 : Nat := 118140960795 + 7961859 * 2 ^ 59
def prefixEnd_7961859 : Nat := 4983230072969 + 3 ^ 40 * 7961859 * 2
def baseEnd_7961859 : Nat := 4088260570325669923746583

theorem tailTrace_7961859 : CollatzResearch.WordTrace tailWord_7961859 prefixEnd_7961859 4088260570325669923746583 := by
  unfold tailWord_7961859
  simp only [CollatzResearch.WordTrace]
  refine ⟨290392854462552095104912631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193595236308368063403275087 290392854462552095104912631)
  ·
    refine ⟨435589281693828142657368947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290392854462552095104912631 435589281693828142657368947)
    ·
      refine ⟨653383922540742213986053421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435589281693828142657368947 653383922540742213986053421)
      ·
        refine ⟨245018970952778330244770033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653383922540742213986053421 245018970952778330244770033)
        ·
          refine ⟨183764228214583747683577525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245018970952778330244770033 183764228214583747683577525)
          ·
            refine ⟨17227896395117226345335393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183764228214583747683577525 17227896395117226345335393)
            ·
              refine ⟨12920922296337919759001545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17227896395117226345335393 12920922296337919759001545)
              ·
                refine ⟨9690691722253439819251159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12920922296337919759001545 9690691722253439819251159)
                ·
                  refine ⟨14536037583380159728876739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690691722253439819251159 14536037583380159728876739)
                  ·
                    refine ⟨21804056375070239593315109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536037583380159728876739 21804056375070239593315109)
                    ·
                      refine ⟨4088260570325669923746583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804056375070239593315109 4088260570325669923746583)
                      ·
                        rfl

theorem cell23_7961859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_7961859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961859 prefixEnd_7961859 := by exact prefixLift 7961859
  have htrace : WordTrace (prefixWord ++ tailWord_7961859) baseStart_7961859 baseEnd_7961859 := by
    simpa [prefixWord, tailWord_7961859, baseEnd_7961859] using wordTrace_append hprefix tailTrace_7961859
  have hstable : (prefixWord ++ tailWord_7961859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961859).length < 2 ^ (prefixWord ++ tailWord_7961859).sum := by decide
  have hdescent : baseEnd_7961859 < baseStart_7961859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961865 : List Nat := [1, 2, 1, 1, 3, 3, 3, 9]
def baseStart_7961865 : Nat := 118140960795 + 7961865 * 2 ^ 59
def prefixEnd_7961865 : Nat := 4983230072969 + 3 ^ 40 * 7961865 * 2
def baseEnd_7961865 : Nat := 151417172267022107417465

theorem tailTrace_7961865 : CollatzResearch.WordTrace tailWord_7961865 prefixEnd_7961865 151417172267022107417465 := by
  unfold tailWord_7961865
  simp only [CollatzResearch.WordTrace]
  refine ⟨290393073300530358129631049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193595382200353572086420699 290393073300530358129631049)
  ·
    refine ⟨217794804975397768597223287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290393073300530358129631049 217794804975397768597223287)
    ·
      refine ⟨326692207463096652895834931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217794804975397768597223287 326692207463096652895834931)
      ·
        refine ⟨490038311194644979343752397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326692207463096652895834931 490038311194644979343752397)
        ·
          refine ⟨183764366697991867253907149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490038311194644979343752397 183764366697991867253907149)
          ·
            refine ⟨68911637511746950220215181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183764366697991867253907149 68911637511746950220215181)
            ·
              refine ⟨25841864066905106332580693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68911637511746950220215181 25841864066905106332580693)
              ·
                refine ⟨151417172267022107417465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25841864066905106332580693 151417172267022107417465)
                ·
                  rfl

theorem cell23_7961865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 9].length) (baseStart_7961865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961865 prefixEnd_7961865 := by exact prefixLift 7961865
  have htrace : WordTrace (prefixWord ++ tailWord_7961865) baseStart_7961865 baseEnd_7961865 := by
    simpa [prefixWord, tailWord_7961865, baseEnd_7961865] using wordTrace_append hprefix tailTrace_7961865
  have hstable : (prefixWord ++ tailWord_7961865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961865).length < 2 ^ (prefixWord ++ tailWord_7961865).sum := by decide
  have hdescent : baseEnd_7961865 < baseStart_7961865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961879 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7961879 : Nat := 118140960795 + 7961879 * 2 ^ 59
def prefixEnd_7961879 : Nat := 4983230072969 + 3 ^ 40 * 7961879 * 2
def baseEnd_7961879 : Nat := 4088270839938759845496491

theorem tailTrace_7961879 : CollatzResearch.WordTrace tailWord_7961879 prefixEnd_7961879 4088270839938759845496491 := by
  unfold tailWord_7961879
  simp only [CollatzResearch.WordTrace]
  refine ⟨290393583922479638520640691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193595722614986425680427127 290393583922479638520640691)
  ·
    refine ⟨435590375883719457780961037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290393583922479638520640691 435590375883719457780961037)
    ·
      refine ⟨163346390956394796667860389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435590375883719457780961037 163346390956394796667860389)
      ·
        refine ⟨30627448304324024375223823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163346390956394796667860389 30627448304324024375223823)
        ·
          refine ⟨45941172456486036562835735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30627448304324024375223823 45941172456486036562835735)
          ·
            refine ⟨68911758684729054844253603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45941172456486036562835735 68911758684729054844253603)
            ·
              refine ⟨103367638027093582266380405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68911758684729054844253603 103367638027093582266380405)
              ·
                refine ⟨9690716065040023337473163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103367638027093582266380405 9690716065040023337473163)
                ·
                  refine ⟨14536074097560035006209745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690716065040023337473163 14536074097560035006209745)
                  ·
                    refine ⟨10902055573170026254657309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14536074097560035006209745 10902055573170026254657309)
                    ·
                      refine ⟨4088270839938759845496491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902055573170026254657309 4088270839938759845496491)
                      ·
                        rfl

theorem cell23_7961879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7961879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961879 prefixEnd_7961879 := by exact prefixLift 7961879
  have htrace : WordTrace (prefixWord ++ tailWord_7961879) baseStart_7961879 baseEnd_7961879 := by
    simpa [prefixWord, tailWord_7961879, baseEnd_7961879] using wordTrace_append hprefix tailTrace_7961879
  have hstable : (prefixWord ++ tailWord_7961879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961879).length < 2 ^ (prefixWord ++ tailWord_7961879).sum := by decide
  have hdescent : baseEnd_7961879 < baseStart_7961879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961882 : List Nat := [3, 1, 1, 3, 3, 3, 9]
def baseStart_7961882 : Nat := 118140960795 + 7961882 * 2 ^ 59
def prefixEnd_7961882 : Nat := 4983230072969 + 3 ^ 40 * 7961882 * 2
def baseEnd_7961882 : Nat := 50472498523218806589617

theorem tailTrace_7961882 : CollatzResearch.WordTrace tailWord_7961882 prefixEnd_7961882 50472498523218806589617 := by
  unfold tailWord_7961882
  simp only [CollatzResearch.WordTrace]
  refine ⟨72598423335367192508249975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193595795560979180021999933 72598423335367192508249975)
  ·
    refine ⟨108897635003050788762374963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72598423335367192508249975 108897635003050788762374963)
    ·
      refine ⟨163346452504576183143562445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108897635003050788762374963 163346452504576183143562445)
      ·
        refine ⟨61254919689216068678835917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163346452504576183143562445 61254919689216068678835917)
        ·
          refine ⟨22970594883456025754563469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61254919689216068678835917 22970594883456025754563469)
          ·
            refine ⟨8613973081296009657961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22970594883456025754563469 8613973081296009657961301)
            ·
              refine ⟨50472498523218806589617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8613973081296009657961301 50472498523218806589617)
              ·
                rfl

theorem cell23_7961882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 9].length) (baseStart_7961882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961882 prefixEnd_7961882 := by exact prefixLift 7961882
  have htrace : WordTrace (prefixWord ++ tailWord_7961882) baseStart_7961882 baseEnd_7961882 := by
    simpa [prefixWord, tailWord_7961882, baseEnd_7961882] using wordTrace_append hprefix tailTrace_7961882
  have hstable : (prefixWord ++ tailWord_7961882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961882).length < 2 ^ (prefixWord ++ tailWord_7961882).sum := by decide
  have hdescent : baseEnd_7961882 < baseStart_7961882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961893 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_7961893 : Nat := 118140960795 + 7961893 * 2 ^ 59
def prefixEnd_7961893 : Nat := 4983230072969 + 3 ^ 40 * 7961893 * 2
def baseEnd_7961893 : Nat := 4088278028667922790721427

theorem tailTrace_7961893 : CollatzResearch.WordTrace tailWord_7961893 prefixEnd_7961893 4088278028667922790721427 := by
  unfold tailWord_7961893
  simp only [CollatzResearch.WordTrace]
  refine ⟨290394094544428918911650333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193596063029619279274433555 290394094544428918911650333)
  ·
    refine ⟨108897785454160844591868875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290394094544428918911650333 108897785454160844591868875)
    ·
      refine ⟨163346678181241266887803313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108897785454160844591868875 163346678181241266887803313)
      ·
        refine ⟨122510008635930950165852485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163346678181241266887803313 122510008635930950165852485)
        ·
          refine ⟨22970626619237053156097341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122510008635930950165852485 22970626619237053156097341)
          ·
            refine ⟨8613984982213894933536503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22970626619237053156097341 8613984982213894933536503)
            ·
              refine ⟨12920977473320842400304755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613984982213894933536503 12920977473320842400304755)
              ·
                refine ⟨19381466209981263600457133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12920977473320842400304755 19381466209981263600457133)
                ·
                  refine ⟨7268049828742973850171425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19381466209981263600457133 7268049828742973850171425)
                  ·
                    refine ⟨5451037371557230387628569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7268049828742973850171425 5451037371557230387628569)
                    ·
                      refine ⟨4088278028667922790721427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451037371557230387628569 4088278028667922790721427)
                      ·
                        rfl

theorem cell23_7961893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_7961893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961893 prefixEnd_7961893 := by exact prefixLift 7961893
  have htrace : WordTrace (prefixWord ++ tailWord_7961893) baseStart_7961893 baseEnd_7961893 := by
    simpa [prefixWord, tailWord_7961893, baseEnd_7961893] using wordTrace_append hprefix tailTrace_7961893
  have hstable : (prefixWord ++ tailWord_7961893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961893).length < 2 ^ (prefixWord ++ tailWord_7961893).sum := by decide
  have hdescent : baseEnd_7961893 < baseStart_7961893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961910 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7961910 : Nat := 118140960795 + 7961910 * 2 ^ 59
def prefixEnd_7961910 : Nat := 4983230072969 + 3 ^ 40 * 7961910 * 2
def baseEnd_7961910 : Nat := 4088286757839049224208849

theorem tailTrace_7961910 : CollatzResearch.WordTrace tailWord_7961910 prefixEnd_7961910 4088286757839049224208849 := by
  unfold tailWord_7961910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18149669661585458175938699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193596476390244887210012789 18149669661585458175938699)
  ·
    refine ⟨27224504492378187263908049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18149669661585458175938699 27224504492378187263908049)
    ·
      refine ⟨20418378369283640447931037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27224504492378187263908049 20418378369283640447931037)
      ·
        refine ⟨7656891888481365167974139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20418378369283640447931037 7656891888481365167974139)
        ·
          refine ⟨11485337832722047751961209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656891888481365167974139 11485337832722047751961209)
          ·
            refine ⟨8614003374541535813970907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485337832722047751961209 8614003374541535813970907)
            ·
              refine ⟨12921005061812303720956361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614003374541535813970907 12921005061812303720956361)
              ·
                refine ⟨9690753796359227790717271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12921005061812303720956361 9690753796359227790717271)
                ·
                  refine ⟨14536130694538841686075907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690753796359227790717271 14536130694538841686075907)
                  ·
                    refine ⟨21804196041808262529113861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536130694538841686075907 21804196041808262529113861)
                    ·
                      refine ⟨4088286757839049224208849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804196041808262529113861 4088286757839049224208849)
                      ·
                        rfl

theorem cell23_7961910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7961910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961910 prefixEnd_7961910 := by exact prefixLift 7961910
  have htrace : WordTrace (prefixWord ++ tailWord_7961910) baseStart_7961910 baseEnd_7961910 := by
    simpa [prefixWord, tailWord_7961910, baseEnd_7961910] using wordTrace_append hprefix tailTrace_7961910
  have hstable : (prefixWord ++ tailWord_7961910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961910).length < 2 ^ (prefixWord ++ tailWord_7961910).sum := by decide
  have hdescent : baseEnd_7961910 < baseStart_7961910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961913 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7961913 : Nat := 118140960795 + 7961913 * 2 ^ 59
def prefixEnd_7961913 : Nat := 4983230072969 + 3 ^ 40 * 7961913 * 2
def baseEnd_7961913 : Nat := 4088288298281012712471335

theorem tailTrace_7961913 : CollatzResearch.WordTrace tailWord_7961913 prefixEnd_7961913 4088288298281012712471335 := by
  unfold tailWord_7961913
  simp only [CollatzResearch.WordTrace]
  refine ⟨290394824004356462327378393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193596549336237641551585595 290394824004356462327378393)
  ·
    refine ⟨217796118003267346745533795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290394824004356462327378393 217796118003267346745533795)
    ·
      refine ⟨326694177004901020118300693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217796118003267346745533795 326694177004901020118300693)
      ·
        refine ⟨15313789547104735318045345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326694177004901020118300693 15313789547104735318045345)
        ·
          refine ⟨11485342160328551488534009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15313789547104735318045345 11485342160328551488534009)
          ·
            refine ⟨8614006620246413616400507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485342160328551488534009 8614006620246413616400507)
            ·
              refine ⟨12921009930369620424600761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614006620246413616400507 12921009930369620424600761)
              ·
                refine ⟨9690757447777215318450571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12921009930369620424600761 9690757447777215318450571)
                ·
                  refine ⟨14536136171665822977675857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9690757447777215318450571 14536136171665822977675857)
                  ·
                    refine ⟨10902102128749367233256893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14536136171665822977675857 10902102128749367233256893)
                    ·
                      refine ⟨4088288298281012712471335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902102128749367233256893 4088288298281012712471335)
                      ·
                        rfl

theorem cell23_7961913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7961913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961913 prefixEnd_7961913 := by exact prefixLift 7961913
  have htrace : WordTrace (prefixWord ++ tailWord_7961913) baseStart_7961913 baseEnd_7961913 := by
    simpa [prefixWord, tailWord_7961913, baseEnd_7961913] using wordTrace_append hprefix tailTrace_7961913
  have hstable : (prefixWord ++ tailWord_7961913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961913).length < 2 ^ (prefixWord ++ tailWord_7961913).sum := by decide
  have hdescent : baseEnd_7961913 < baseStart_7961913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961959 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 6]
def baseStart_7961959 : Nat := 118140960795 + 7961959 * 2 ^ 59
def prefixEnd_7961959 : Nat := 4983230072969 + 3 ^ 40 * 7961959 * 2
def baseEnd_7961959 : Nat := 1362770639463706510832041

theorem tailTrace_7961959 : CollatzResearch.WordTrace tailWord_7961959 prefixEnd_7961959 1362770639463706510832041 := by
  unfold tailWord_7961959
  simp only [CollatzResearch.WordTrace]
  refine ⟨290396501762189812183552931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193597667841459874789035287 290396501762189812183552931)
  ·
    refine ⟨435594752643284718275329397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290396501762189812183552931 435594752643284718275329397)
    ·
      refine ⟨40837008060307942338312131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435594752643284718275329397 40837008060307942338312131)
      ·
        refine ⟨61255512090461913507468197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40837008060307942338312131 61255512090461913507468197)
        ·
          refine ⟨11485408516961608782650287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61255512090461913507468197 11485408516961608782650287)
          ·
            refine ⟨17228112775442413173975431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485408516961608782650287 17228112775442413173975431)
            ·
              refine ⟨25842169163163619760963147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228112775442413173975431 25842169163163619760963147)
              ·
                refine ⟨38763253744745429641444721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25842169163163619760963147 38763253744745429641444721)
                ·
                  refine ⟨29072440308559072231083541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38763253744745429641444721 29072440308559072231083541)
                  ·
                    refine ⟨1362770639463706510832041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29072440308559072231083541 1362770639463706510832041)
                    ·
                      rfl

theorem cell23_7961959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_7961959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961959 prefixEnd_7961959 := by exact prefixLift 7961959
  have htrace : WordTrace (prefixWord ++ tailWord_7961959) baseStart_7961959 baseEnd_7961959 := by
    simpa [prefixWord, tailWord_7961959, baseEnd_7961959] using wordTrace_append hprefix tailTrace_7961959
  have hstable : (prefixWord ++ tailWord_7961959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961959).length < 2 ^ (prefixWord ++ tailWord_7961959).sum := by decide
  have hdescent : baseEnd_7961959 < baseStart_7961959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961989 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 5]
def baseStart_7961989 : Nat := 118140960795 + 7961989 * 2 ^ 59
def prefixEnd_7961989 : Nat := 4983230072969 + 3 ^ 40 * 7961989 * 2
def baseEnd_7961989 : Nat := 454258591423417157235665

theorem tailTrace_7961989 : CollatzResearch.WordTrace tailWord_7961989 prefixEnd_7961989 454258591423417157235665 := by
  unfold tailWord_7961989
  simp only [CollatzResearch.WordTrace]
  refine ⟨290397595952081127307145021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193598397301387418204763347 290397595952081127307145021)
  ·
    refine ⟨108899098482030422740179383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290397595952081127307145021 108899098482030422740179383)
    ·
      refine ⟨163348647723045634110269075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108899098482030422740179383 163348647723045634110269075)
      ·
        refine ⟨245022971584568451165403613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163348647723045634110269075 245022971584568451165403613)
        ·
          refine ⟨91883614344213169187026355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245022971584568451165403613 91883614344213169187026355)
          ·
            refine ⟨137825421516319753780539533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91883614344213169187026355 137825421516319753780539533)
            ·
              refine ⟨51684533068619907667702325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137825421516319753780539533 51684533068619907667702325)
              ·
                refine ⟨4845424975183116343847093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51684533068619907667702325 4845424975183116343847093)
                ·
                  refine ⟨454258591423417157235665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4845424975183116343847093 454258591423417157235665)
                  ·
                    rfl

theorem cell23_7961989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_7961989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7961989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7961989 prefixEnd_7961989 := by exact prefixLift 7961989
  have htrace : WordTrace (prefixWord ++ tailWord_7961989) baseStart_7961989 baseEnd_7961989 := by
    simpa [prefixWord, tailWord_7961989, baseEnd_7961989] using wordTrace_append hprefix tailTrace_7961989
  have hstable : (prefixWord ++ tailWord_7961989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961989).length < 2 ^ (prefixWord ++ tailWord_7961989).sum := by decide
  have hdescent : baseEnd_7961989 < baseStart_7961989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962039 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_7962039 : Nat := 118140960795 + 7962039 * 2 ^ 59
def prefixEnd_7962039 : Nat := 4983230072969 + 3 ^ 40 * 7962039 * 2
def baseEnd_7962039 : Nat := 4088352996843479219495755

theorem tailTrace_7962039 : CollatzResearch.WordTrace tailWord_7962039 prefixEnd_7962039 4088352996843479219495755 := by
  unfold tailWord_7962039
  simp only [CollatzResearch.WordTrace]
  refine ⟨290399419601899985846465171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193599613067933323897643447 290399419601899985846465171)
  ·
    refine ⟨435599129402849978769697757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290399419601899985846465171 435599129402849978769697757)
    ·
      refine ⟨163349673526068742038636659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435599129402849978769697757 163349673526068742038636659)
      ·
        refine ⟨245024510289103113057954989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163349673526068742038636659 245024510289103113057954989)
        ·
          refine ⟨91884191358413667396733121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245024510289103113057954989 91884191358413667396733121)
          ·
            refine ⟨68913143518810250547549841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91884191358413667396733121 68913143518810250547549841)
            ·
              refine ⟨51684857639107687910662381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68913143518810250547549841 51684857639107687910662381)
              ·
                refine ⟨19381821614665382966498393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51684857639107687910662381 19381821614665382966498393)
                ·
                  refine ⟨14536366210999037224873795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19381821614665382966498393 14536366210999037224873795)
                  ·
                    refine ⟨21804549316498555837310693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536366210999037224873795 21804549316498555837310693)
                    ·
                      refine ⟨4088352996843479219495755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804549316498555837310693 4088352996843479219495755)
                      ·
                        rfl

theorem cell23_7962039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_7962039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962039 prefixEnd_7962039 := by exact prefixLift 7962039
  have htrace : WordTrace (prefixWord ++ tailWord_7962039) baseStart_7962039 baseEnd_7962039 := by
    simpa [prefixWord, tailWord_7962039, baseEnd_7962039] using wordTrace_append hprefix tailTrace_7962039
  have hstable : (prefixWord ++ tailWord_7962039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962039).length < 2 ^ (prefixWord ++ tailWord_7962039).sum := by decide
  have hdescent : baseEnd_7962039 < baseStart_7962039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962042 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_7962042 : Nat := 118140960795 + 7962042 * 2 ^ 59
def prefixEnd_7962042 : Nat := 4983230072969 + 3 ^ 40 * 7962042 * 2
def baseEnd_7962042 : Nat := 4088354537285442707758241

theorem tailTrace_7962042 : CollatzResearch.WordTrace tailWord_7962042 prefixEnd_7962042 4088354537285442707758241 := by
  unfold tailWord_7962042
  simp only [CollatzResearch.WordTrace]
  refine ⟨72599882255222279339706095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193599686013926078239216253 72599882255222279339706095)
  ·
    refine ⟨108899823382833419009559143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72599882255222279339706095 108899823382833419009559143)
    ·
      refine ⟨163349735074250128514338715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108899823382833419009559143 163349735074250128514338715)
      ·
        refine ⟨245024602611375192771508073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163349735074250128514338715 245024602611375192771508073)
        ·
          refine ⟨183768451958531394578631055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245024602611375192771508073 183768451958531394578631055)
          ·
            refine ⟨275652677937797091867946583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183768451958531394578631055 275652677937797091867946583)
            ·
              refine ⟨413479016906695637801919875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275652677937797091867946583 413479016906695637801919875)
              ·
                refine ⟨620218525360043456702879813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413479016906695637801919875 620218525360043456702879813)
                ·
                  refine ⟨116290973505008148131789965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620218525360043456702879813 116290973505008148131789965)
                  ·
                    refine ⟨43609115064378055549421237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116290973505008148131789965 43609115064378055549421237)
                    ·
                      refine ⟨4088354537285442707758241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43609115064378055549421237 4088354537285442707758241)
                      ·
                        rfl

theorem cell23_7962042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_7962042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962042 prefixEnd_7962042 := by exact prefixLift 7962042
  have htrace : WordTrace (prefixWord ++ tailWord_7962042) baseStart_7962042 baseEnd_7962042 := by
    simpa [prefixWord, tailWord_7962042, baseEnd_7962042] using wordTrace_append hprefix tailTrace_7962042
  have hstable : (prefixWord ++ tailWord_7962042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962042).length < 2 ^ (prefixWord ++ tailWord_7962042).sum := by decide
  have hdescent : baseEnd_7962042 < baseStart_7962042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962059 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3]
def baseStart_7962059 : Nat := 118140960795 + 7962059 * 2 ^ 59
def prefixEnd_7962059 : Nat := 4983230072969 + 3 ^ 40 * 7962059 * 2
def baseEnd_7962059 : Nat := 4088363266456569141245663

theorem tailTrace_7962059 : CollatzResearch.WordTrace tailWord_7962059 prefixEnd_7962059 4088363266456569141245663 := by
  unfold tailWord_7962059
  simp only [CollatzResearch.WordTrace]
  refine ⟨290400149061827529262193231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193600099374551686174795487 290400149061827529262193231)
  ·
    refine ⟨435600223592741293893289847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290400149061827529262193231 435600223592741293893289847)
    ·
      refine ⟨653400335389111940839934771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435600223592741293893289847 653400335389111940839934771)
      ·
        refine ⟨980100503083667911259902157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653400335389111940839934771 980100503083667911259902157)
        ·
          refine ⟨367537688656375466722463309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980100503083667911259902157 367537688656375466722463309)
          ·
            refine ⟨137826633246140800020923741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367537688656375466722463309 137826633246140800020923741)
            ·
              refine ⟨51684987467302800007846403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137826633246140800020923741 51684987467302800007846403)
              ·
                refine ⟨77527481200954200011769605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51684987467302800007846403 77527481200954200011769605)
                ·
                  refine ⟨14536402725178912502206801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77527481200954200011769605 14536402725178912502206801)
                  ·
                    refine ⟨10902302043884184376655101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14536402725178912502206801 10902302043884184376655101)
                    ·
                      refine ⟨4088363266456569141245663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902302043884184376655101 4088363266456569141245663)
                      ·
                        rfl

theorem cell23_7962059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].length) (baseStart_7962059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962059 prefixEnd_7962059 := by exact prefixLift 7962059
  have htrace : WordTrace (prefixWord ++ tailWord_7962059) baseStart_7962059 baseEnd_7962059 := by
    simpa [prefixWord, tailWord_7962059, baseEnd_7962059] using wordTrace_append hprefix tailTrace_7962059
  have hstable : (prefixWord ++ tailWord_7962059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962059).length < 2 ^ (prefixWord ++ tailWord_7962059).sum := by decide
  have hdescent : baseEnd_7962059 < baseStart_7962059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962079 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 6]
def baseStart_7962079 : Nat := 118140960795 + 7962079 * 2 ^ 59
def prefixEnd_7962079 : Nat := 4983230072969 + 3 ^ 40 * 7962079 * 2
def baseEnd_7962079 : Nat := 454263726229962118110619

theorem tailTrace_7962079 : CollatzResearch.WordTrace tailWord_7962079 prefixEnd_7962079 454263726229962118110619 := by
  unfold tailWord_7962079
  simp only [CollatzResearch.WordTrace]
  refine ⟨290400878521755072677921291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193600585681170048451947527 290400878521755072677921291)
  ·
    refine ⟨435601317782632609016881937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290400878521755072677921291 435601317782632609016881937)
    ·
      refine ⟨326700988336974456762661453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435601317782632609016881937 326700988336974456762661453)
      ·
        refine ⟨122512870626365421285998045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326700988336974456762661453 122512870626365421285998045)
        ·
          refine ⟨45942326484887032982249267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122512870626365421285998045 45942326484887032982249267)
          ·
            refine ⟨68913489727330549473373901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45942326484887032982249267 68913489727330549473373901)
            ·
              refine ⟨25842558647748956052515213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68913489727330549473373901 25842558647748956052515213)
              ·
                refine ⟨9690959492905858519693205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25842558647748956052515213 9690959492905858519693205)
                ·
                  refine ⟨454263726229962118110619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9690959492905858519693205 454263726229962118110619)
                  ·
                    rfl

theorem cell23_7962079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 6].length) (baseStart_7962079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962079 prefixEnd_7962079 := by exact prefixLift 7962079
  have htrace : WordTrace (prefixWord ++ tailWord_7962079) baseStart_7962079 baseEnd_7962079 := by
    simpa [prefixWord, tailWord_7962079, baseEnd_7962079] using wordTrace_append hprefix tailTrace_7962079
  have hstable : (prefixWord ++ tailWord_7962079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962079).length < 2 ^ (prefixWord ++ tailWord_7962079).sum := by decide
  have hdescent : baseEnd_7962079 < baseStart_7962079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962129 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_7962129 : Nat := 118140960795 + 7962129 * 2 ^ 59
def prefixEnd_7962129 : Nat := 4983230072969 + 3 ^ 40 * 7962129 * 2
def baseEnd_7962129 : Nat := 4088399210102383867370341

theorem tailTrace_7962129 : CollatzResearch.WordTrace tailWord_7962129 prefixEnd_7962129 4088399210102383867370341 := by
  unfold tailWord_7962129
  simp only [CollatzResearch.WordTrace]
  refine ⟨290402702171573931217241441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193601801447715954144827627 290402702171573931217241441)
  ·
    refine ⟨217802026628680448412931081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290402702171573931217241441 217802026628680448412931081)
    ·
      refine ⟨163351519971510336309698311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217802026628680448412931081 163351519971510336309698311)
      ·
        refine ⟨245027279957265504464547467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163351519971510336309698311 245027279957265504464547467)
        ·
          refine ⟨367540919935898256696821201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245027279957265504464547467 367540919935898256696821201)
          ·
            refine ⟨275655689951923692522615901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367540919935898256696821201 275655689951923692522615901)
            ·
              refine ⟨103370883731971384695980963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275655689951923692522615901 103370883731971384695980963)
              ·
                refine ⟨155056325597957077043971445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103370883731971384695980963 155056325597957077043971445)
                ·
                  refine ⟨14536530524808475972872323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155056325597957077043971445 14536530524808475972872323)
                  ·
                    refine ⟨21804795787212713959308485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536530524808475972872323 21804795787212713959308485)
                    ·
                      refine ⟨4088399210102383867370341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804795787212713959308485 4088399210102383867370341)
                      ·
                        rfl

theorem cell23_7962129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_7962129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962129 prefixEnd_7962129 := by exact prefixLift 7962129
  have htrace : WordTrace (prefixWord ++ tailWord_7962129) baseStart_7962129 baseEnd_7962129 := by
    simpa [prefixWord, tailWord_7962129, baseEnd_7962129] using wordTrace_append hprefix tailTrace_7962129
  have hstable : (prefixWord ++ tailWord_7962129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962129).length < 2 ^ (prefixWord ++ tailWord_7962129).sum := by decide
  have hdescent : baseEnd_7962129 < baseStart_7962129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962146 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7962146 : Nat := 118140960795 + 7962146 * 2 ^ 59
def prefixEnd_7962146 : Nat := 4983230072969 + 3 ^ 40 * 7962146 * 2
def baseEnd_7962146 : Nat := 4088407939273510300857763

theorem tailTrace_7962146 : CollatzResearch.WordTrace tailWord_7962146 prefixEnd_7962146 4088407939273510300857763 := by
  unfold tailWord_7962146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72600830553128085780152573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193602214808341562080406861 72600830553128085780152573)
  ·
    refine ⟨27225311457423032167557215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72600830553128085780152573 27225311457423032167557215)
    ·
      refine ⟨40837967186134548251335823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27225311457423032167557215 40837967186134548251335823)
      ·
        refine ⟨61256950779201822377003735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40837967186134548251335823 61256950779201822377003735)
        ·
          refine ⟨91885426168802733565505603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61256950779201822377003735 91885426168802733565505603)
          ·
            refine ⟨137828139253204100348258405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91885426168802733565505603 137828139253204100348258405)
            ·
              refine ⟨25842776109975768815298451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137828139253204100348258405 25842776109975768815298451)
              ·
                refine ⟨38764164164963653222947677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25842776109975768815298451 38764164164963653222947677)
                ·
                  refine ⟨14536561561861369958605379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38764164164963653222947677 14536561561861369958605379)
                  ·
                    refine ⟨21804842342792054937908069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536561561861369958605379 21804842342792054937908069)
                    ·
                      refine ⟨4088407939273510300857763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804842342792054937908069 4088407939273510300857763)
                      ·
                        rfl

theorem cell23_7962146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7962146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962146 prefixEnd_7962146 := by exact prefixLift 7962146
  have htrace : WordTrace (prefixWord ++ tailWord_7962146) baseStart_7962146 baseEnd_7962146 := by
    simpa [prefixWord, tailWord_7962146, baseEnd_7962146] using wordTrace_append hprefix tailTrace_7962146
  have hstable : (prefixWord ++ tailWord_7962146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962146).length < 2 ^ (prefixWord ++ tailWord_7962146).sum := by decide
  have hdescent : baseEnd_7962146 < baseStart_7962146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962163 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 1, 1, 4]
def baseStart_7962163 : Nat := 118140960795 + 7962163 * 2 ^ 59
def prefixEnd_7962163 : Nat := 4983230072969 + 3 ^ 40 * 7962163 * 2
def baseEnd_7962163 : Nat := 4088416668444636734345185

theorem tailTrace_7962163 : CollatzResearch.WordTrace tailWord_7962163 prefixEnd_7962163 4088416668444636734345185 := by
  unfold tailWord_7962163
  simp only [CollatzResearch.WordTrace]
  refine ⟨290403942253450755023979143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193602628168967170015986095 290403942253450755023979143)
  ·
    refine ⟨435605913380176132535968715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290403942253450755023979143 435605913380176132535968715)
    ·
      refine ⟨653408870070264198803953073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435605913380176132535968715 653408870070264198803953073)
      ·
        refine ⟨490056652552698149102964805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653408870070264198803953073 490056652552698149102964805)
        ·
          refine ⟨91885622353630902956805901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490056652552698149102964805 91885622353630902956805901)
          ·
            refine ⟨34457108382611588608802213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91885622353630902956805901 34457108382611588608802213)
            ·
              refine ⟨6460707821739672864150415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34457108382611588608802213 6460707821739672864150415)
              ·
                refine ⟨9691061732609509296225623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460707821739672864150415 9691061732609509296225623)
                ·
                  refine ⟨14536592598914263944338435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9691061732609509296225623 14536592598914263944338435)
                  ·
                    refine ⟨21804888898371395916507653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14536592598914263944338435 21804888898371395916507653)
                    ·
                      refine ⟨4088416668444636734345185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21804888898371395916507653 4088416668444636734345185)
                      ·
                        rfl

theorem cell23_7962163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 1, 4].length) (baseStart_7962163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962163 prefixEnd_7962163 := by exact prefixLift 7962163
  have htrace : WordTrace (prefixWord ++ tailWord_7962163) baseStart_7962163 baseEnd_7962163 := by
    simpa [prefixWord, tailWord_7962163, baseEnd_7962163] using wordTrace_append hprefix tailTrace_7962163
  have hstable : (prefixWord ++ tailWord_7962163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962163).length < 2 ^ (prefixWord ++ tailWord_7962163).sum := by decide
  have hdescent : baseEnd_7962163 < baseStart_7962163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962169 : List Nat := [1, 2, 1, 5, 1, 3, 10]
def baseStart_7962169 : Nat := 118140960795 + 7962169 * 2 ^ 59
def prefixEnd_7962169 : Nat := 4983230072969 + 3 ^ 40 * 7962169 * 2
def baseEnd_7962169 : Nat := 50474317892945230998397

theorem tailTrace_7962169 : CollatzResearch.WordTrace tailWord_7962169 prefixEnd_7962169 50474317892945230998397 := by
  unfold tailWord_7962169
  simp only [CollatzResearch.WordTrace]
  refine ⟨290404161091429018048697561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193602774060952678699131707 290404161091429018048697561)
  ·
    refine ⟨217803120818571763536523171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290404161091429018048697561 217803120818571763536523171)
    ·
      refine ⟨326704681227857645304784757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217803120818571763536523171 326704681227857645304784757)
      ·
        refine ⟨30628563865111654247323571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326704681227857645304784757 30628563865111654247323571)
        ·
          refine ⟨45942845797667481370985357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30628563865111654247323571 45942845797667481370985357)
          ·
            refine ⟨17228567174125305514119509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45942845797667481370985357 17228567174125305514119509)
            ·
              refine ⟨50474317892945230998397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17228567174125305514119509 50474317892945230998397)
              ·
                rfl

theorem cell23_7962169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 10].length) (baseStart_7962169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962169 prefixEnd_7962169 := by exact prefixLift 7962169
  have htrace : WordTrace (prefixWord ++ tailWord_7962169) baseStart_7962169 baseEnd_7962169 := by
    simpa [prefixWord, tailWord_7962169, baseEnd_7962169] using wordTrace_append hprefix tailTrace_7962169
  have hstable : (prefixWord ++ tailWord_7962169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962169).length < 2 ^ (prefixWord ++ tailWord_7962169).sum := by decide
  have hdescent : baseEnd_7962169 < baseStart_7962169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962173 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_7962173 : Nat := 118140960795 + 7962173 * 2 ^ 59
def prefixEnd_7962173 : Nat := 4983230072969 + 3 ^ 40 * 7962173 * 2
def baseEnd_7962173 : Nat := 1362807267750393898406713

theorem tailTrace_7962173 : CollatzResearch.WordTrace tailWord_7962173 prefixEnd_7962173 1362807267750393898406713 := by
  unfold tailWord_7962173
  simp only [CollatzResearch.WordTrace]
  refine ⟨290404306983414526731843173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193602871322276351154562115 290404306983414526731843173)
  ·
    refine ⟨54450807559390223762220595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290404306983414526731843173 54450807559390223762220595)
    ·
      refine ⟨81676211339085335643330893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54450807559390223762220595 81676211339085335643330893)
      ·
        refine ⟨30628579252157000866249085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81676211339085335643330893 30628579252157000866249085)
        ·
          refine ⟨11485717219558875324843407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30628579252157000866249085 11485717219558875324843407)
          ·
            refine ⟨17228575829338312987265111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485717219558875324843407 17228575829338312987265111)
            ·
              refine ⟨25842863744007469480897667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17228575829338312987265111 25842863744007469480897667)
              ·
                refine ⟨38764295616011204221346501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25842863744007469480897667 38764295616011204221346501)
                ·
                  refine ⟨7268305428002100791502469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38764295616011204221346501 7268305428002100791502469)
                  ·
                    refine ⟨1362807267750393898406713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268305428002100791502469 1362807267750393898406713)
                    ·
                      rfl

theorem cell23_7962173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_7962173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962173 prefixEnd_7962173 := by exact prefixLift 7962173
  have htrace : WordTrace (prefixWord ++ tailWord_7962173) baseStart_7962173 baseEnd_7962173 := by
    simpa [prefixWord, tailWord_7962173, baseEnd_7962173] using wordTrace_append hprefix tailTrace_7962173
  have hstable : (prefixWord ++ tailWord_7962173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962173).length < 2 ^ (prefixWord ++ tailWord_7962173).sum := by decide
  have hdescent : baseEnd_7962173 < baseStart_7962173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962179 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3]
def baseStart_7962179 : Nat := 118140960795 + 7962179 * 2 ^ 59
def prefixEnd_7962179 : Nat := 4983230072969 + 3 ^ 40 * 7962179 * 2
def baseEnd_7962179 : Nat := 4088424884135108671745111

theorem tailTrace_7962179 : CollatzResearch.WordTrace tailWord_7962179 prefixEnd_7962179 4088424884135108671745111 := by
  unfold tailWord_7962179
  simp only [CollatzResearch.WordTrace]
  refine ⟨290404525821392789756561591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193603017214261859837707727 290404525821392789756561591)
  ·
    refine ⟨435606788732089184634842387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290404525821392789756561591 435606788732089184634842387)
    ·
      refine ⟨653410183098133776952263581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435606788732089184634842387 653410183098133776952263581)
      ·
        refine ⟨245028818661800166357098843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653410183098133776952263581 245028818661800166357098843)
        ·
          refine ⟨367543227992700249535648265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245028818661800166357098843 367543227992700249535648265)
          ·
            refine ⟨275657420994525187151736199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367543227992700249535648265 275657420994525187151736199)
            ·
              refine ⟨413486131491787780727604299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275657420994525187151736199 413486131491787780727604299)
              ·
                refine ⟨620229197237681671091406449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413486131491787780727604299 620229197237681671091406449)
                ·
                  refine ⟨465171897928261253318554837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620229197237681671091406449 465171897928261253318554837)
                  ·
                    refine ⟨10902466357693623124653629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 465171897928261253318554837 10902466357693623124653629)
                    ·
                      refine ⟨4088424884135108671745111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902466357693623124653629 4088424884135108671745111)
                      ·
                        rfl

theorem cell23_7962179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_7962179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962179 prefixEnd_7962179 := by exact prefixLift 7962179
  have htrace : WordTrace (prefixWord ++ tailWord_7962179) baseStart_7962179 baseEnd_7962179 := by
    simpa [prefixWord, tailWord_7962179, baseEnd_7962179] using wordTrace_append hprefix tailTrace_7962179
  have hstable : (prefixWord ++ tailWord_7962179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962179).length < 2 ^ (prefixWord ++ tailWord_7962179).sum := by decide
  have hdescent : baseEnd_7962179 < baseStart_7962179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962209 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7962209 : Nat := 118140960795 + 7962209 * 2 ^ 59
def prefixEnd_7962209 : Nat := 4983230072969 + 3 ^ 40 * 7962209 * 2
def baseEnd_7962209 : Nat := 4088440288554743554369973

theorem tailTrace_7962209 : CollatzResearch.WordTrace tailWord_7962209 prefixEnd_7962209 4088440288554743554369973 := by
  unfold tailWord_7962209
  simp only [CollatzResearch.WordTrace]
  refine ⟨290405620011284104880153681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193603746674189403253435787 290405620011284104880153681)
  ·
    refine ⟨217804215008463078660115261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290405620011284104880153681 217804215008463078660115261)
    ·
      refine ⟨81676580628173654497543223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217804215008463078660115261 81676580628173654497543223)
      ·
        refine ⟨122514870942260481746314835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81676580628173654497543223 122514870942260481746314835)
        ·
          refine ⟨183772306413390722619472253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122514870942260481746314835 183772306413390722619472253)
          ·
            refine ⟨68914614905021520982302095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183772306413390722619472253 68914614905021520982302095)
            ·
              refine ⟨103371922357532281473453143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68914614905021520982302095 103371922357532281473453143)
              ·
                refine ⟨155057883536298422210179715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103371922357532281473453143 155057883536298422210179715)
                ·
                  refine ⟨232586825304447633315269573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155057883536298422210179715 232586825304447633315269573)
                  ·
                    refine ⟨43610029744583931246613045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232586825304447633315269573 43610029744583931246613045)
                    ·
                      refine ⟨4088440288554743554369973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43610029744583931246613045 4088440288554743554369973)
                      ·
                        rfl

theorem cell23_7962209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7962209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962209 prefixEnd_7962209 := by exact prefixLift 7962209
  have htrace : WordTrace (prefixWord ++ tailWord_7962209) baseStart_7962209 baseEnd_7962209 := by
    simpa [prefixWord, tailWord_7962209, baseEnd_7962209] using wordTrace_append hprefix tailTrace_7962209
  have hstable : (prefixWord ++ tailWord_7962209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962209).length < 2 ^ (prefixWord ++ tailWord_7962209).sum := by decide
  have hdescent : baseEnd_7962209 < baseStart_7962209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962213 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_7962213 : Nat := 118140960795 + 7962213 * 2 ^ 59
def prefixEnd_7962213 : Nat := 4983230072969 + 3 ^ 40 * 7962213 * 2
def baseEnd_7962213 : Nat := 4088442342477361538719955

theorem tailTrace_7962213 : CollatzResearch.WordTrace tailWord_7962213 prefixEnd_7962213 4088442342477361538719955 := by
  unfold tailWord_7962213
  simp only [CollatzResearch.WordTrace]
  refine ⟨290405765903269613563299293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193603843935513075708866195 290405765903269613563299293)
  ·
    refine ⟨108902162213726105086237235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290405765903269613563299293 108902162213726105086237235)
    ·
      refine ⟨163353243320589157629355853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108902162213726105086237235 163353243320589157629355853)
      ·
        refine ⟨61257466245220934111008445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163353243320589157629355853 61257466245220934111008445)
        ·
          refine ⟨22971549841957850291628167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61257466245220934111008445 22971549841957850291628167)
          ·
            refine ⟨34457324762936775437442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971549841957850291628167 34457324762936775437442251)
            ·
              refine ⟨51685987144405163156163377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34457324762936775437442251 51685987144405163156163377)
              ·
                refine ⟨38764490358303872367122533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51685987144405163156163377 38764490358303872367122533)
                ·
                  refine ⟨7268341942181976068835475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38764490358303872367122533 7268341942181976068835475)
                  ·
                    refine ⟨10902512913272964103253213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7268341942181976068835475 10902512913272964103253213)
                    ·
                      refine ⟨4088442342477361538719955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902512913272964103253213 4088442342477361538719955)
                      ·
                        rfl

theorem cell23_7962213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_7962213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962213 prefixEnd_7962213 := by exact prefixLift 7962213
  have htrace : WordTrace (prefixWord ++ tailWord_7962213) baseStart_7962213 baseEnd_7962213 := by
    simpa [prefixWord, tailWord_7962213, baseEnd_7962213] using wordTrace_append hprefix tailTrace_7962213
  have hstable : (prefixWord ++ tailWord_7962213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962213).length < 2 ^ (prefixWord ++ tailWord_7962213).sum := by decide
  have hdescent : baseEnd_7962213 < baseStart_7962213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962230 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7962230 : Nat := 118140960795 + 7962230 * 2 ^ 59
def prefixEnd_7962230 : Nat := 4983230072969 + 3 ^ 40 * 7962230 * 2
def baseEnd_7962230 : Nat := 4088451071648487972207377

theorem tailTrace_7962230 : CollatzResearch.WordTrace tailWord_7962230 prefixEnd_7962230 4088451071648487972207377 := by
  unfold tailWord_7962230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150399121513001591666759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193604257296138683644445429 18150399121513001591666759)
  ·
    refine ⟨27225598682269502387500139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18150399121513001591666759 27225598682269502387500139)
    ·
      refine ⟨40838398023404253581250209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27225598682269502387500139 40838398023404253581250209)
      ·
        refine ⟨30628798517553190185937657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40838398023404253581250209 30628798517553190185937657)
        ·
          refine ⟨22971598888164892639453243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30628798517553190185937657 22971598888164892639453243)
          ·
            refine ⟨34457398332247338959179865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971598888164892639453243 34457398332247338959179865)
            ·
              refine ⟨25843048749185504219384899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34457398332247338959179865 25843048749185504219384899)
              ·
                refine ⟨38764573123778256329077349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25843048749185504219384899 38764573123778256329077349)
                ·
                  refine ⟨7268357460708423061702003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38764573123778256329077349 7268357460708423061702003)
                  ·
                    refine ⟨10902536191062634592553005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7268357460708423061702003 10902536191062634592553005)
                    ·
                      refine ⟨4088451071648487972207377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902536191062634592553005 4088451071648487972207377)
                      ·
                        rfl

theorem cell23_7962230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7962230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962230 prefixEnd_7962230 := by exact prefixLift 7962230
  have htrace : WordTrace (prefixWord ++ tailWord_7962230) baseStart_7962230 baseEnd_7962230 := by
    simpa [prefixWord, tailWord_7962230, baseEnd_7962230] using wordTrace_append hprefix tailTrace_7962230
  have hstable : (prefixWord ++ tailWord_7962230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962230).length < 2 ^ (prefixWord ++ tailWord_7962230).sum := by decide
  have hdescent : baseEnd_7962230 < baseStart_7962230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962247 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_7962247 : Nat := 118140960795 + 7962247 * 2 ^ 59
def prefixEnd_7962247 : Nat := 4983230072969 + 3 ^ 40 * 7962247 * 2
def baseEnd_7962247 : Nat := 4088459800819614405694799

theorem tailTrace_7962247 : CollatzResearch.WordTrace tailWord_7962247 prefixEnd_7962247 4088459800819614405694799 := by
  unfold tailWord_7962247
  simp only [CollatzResearch.WordTrace]
  refine ⟨290407005985146437370036995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193604670656764291580024663 290407005985146437370036995)
  ·
    refine ⟨435610508977719656055055493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290407005985146437370036995 435610508977719656055055493)
    ·
      refine ⟨81676970433322435510322905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435610508977719656055055493 81676970433322435510322905)
      ·
        refine ⟨61257727824991826632742179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81676970433322435510322905 61257727824991826632742179)
        ·
          refine ⟨91886591737487739949113269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61257727824991826632742179 91886591737487739949113269)
          ·
            refine ⟨8614367975389475620229369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91886591737487739949113269 8614367975389475620229369)
            ·
              refine ⟨6460775981542106715172027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614367975389475620229369 6460775981542106715172027)
              ·
                refine ⟨9691163972313160072758041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6460775981542106715172027 9691163972313160072758041)
                ·
                  refine ⟨7268372979234870054568531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9691163972313160072758041 7268372979234870054568531)
                  ·
                    refine ⟨10902559468852305081852797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7268372979234870054568531 10902559468852305081852797)
                    ·
                      refine ⟨4088459800819614405694799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902559468852305081852797 4088459800819614405694799)
                      ·
                        rfl

theorem cell23_7962247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_7962247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962247 prefixEnd_7962247 := by exact prefixLift 7962247
  have htrace : WordTrace (prefixWord ++ tailWord_7962247) baseStart_7962247 baseEnd_7962247 := by
    simpa [prefixWord, tailWord_7962247, baseEnd_7962247] using wordTrace_append hprefix tailTrace_7962247
  have hstable : (prefixWord ++ tailWord_7962247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962247).length < 2 ^ (prefixWord ++ tailWord_7962247).sum := by decide
  have hdescent : baseEnd_7962247 < baseStart_7962247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962270 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7962270 : Nat := 118140960795 + 7962270 * 2 ^ 59
def prefixEnd_7962270 : Nat := 4983230072969 + 3 ^ 40 * 7962270 * 2
def baseEnd_7962270 : Nat := 4088471610874667815707193

theorem tailTrace_7962270 : CollatzResearch.WordTrace tailWord_7962270 prefixEnd_7962270 4088471610874667815707193 := by
  unfold tailWord_7962270
  simp only [CollatzResearch.WordTrace]
  refine ⟨36300980608007889037265533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193605229909375408198749509 36300980608007889037265533)
  ·
    refine ⟨13612867728002958388974575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36300980608007889037265533 13612867728002958388974575)
    ·
      refine ⟨20419301592004437583461863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612867728002958388974575 20419301592004437583461863)
      ·
        refine ⟨30628952388006656375192795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419301592004437583461863 30628952388006656375192795)
        ·
          refine ⟨45943428582009984562789193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30628952388006656375192795 45943428582009984562789193)
          ·
            refine ⟨34457571436507488422091895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45943428582009984562789193 34457571436507488422091895)
            ·
              refine ⟨51686357154761232633137843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34457571436507488422091895 51686357154761232633137843)
              ·
                refine ⟨77529535732141848949706765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51686357154761232633137843 77529535732141848949706765)
                ·
                  refine ⟨29073575899553193356140037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77529535732141848949706765 29073575899553193356140037)
                  ·
                    refine ⟨5451295481166223754276257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29073575899553193356140037 5451295481166223754276257)
                    ·
                      refine ⟨4088471610874667815707193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451295481166223754276257 4088471610874667815707193)
                      ·
                        rfl

theorem cell23_7962270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7962270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962270 prefixEnd_7962270 := by exact prefixLift 7962270
  have htrace : WordTrace (prefixWord ++ tailWord_7962270) baseStart_7962270 baseEnd_7962270 := by
    simpa [prefixWord, tailWord_7962270, baseEnd_7962270] using wordTrace_append hprefix tailTrace_7962270
  have hstable : (prefixWord ++ tailWord_7962270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962270).length < 2 ^ (prefixWord ++ tailWord_7962270).sum := by decide
  have hdescent : baseEnd_7962270 < baseStart_7962270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962310 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7962310 : Nat := 118140960795 + 7962310 * 2 ^ 59
def prefixEnd_7962310 : Nat := 4983230072969 + 3 ^ 40 * 7962310 * 2
def baseEnd_7962310 : Nat := 454276905566760851023001

theorem tailTrace_7962310 : CollatzResearch.WordTrace tailWord_7962310 prefixEnd_7962310 454276905566760851023001 := by
  unfold tailWord_7962310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075290743247443722799387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193606202522612132753053589 9075290743247443722799387)
  ·
    refine ⟨13612936114871165584199081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075290743247443722799387 13612936114871165584199081)
    ·
      refine ⟨10209702086153374188149311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13612936114871165584199081 10209702086153374188149311)
      ·
        refine ⟨15314553129230061282223967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209702086153374188149311 15314553129230061282223967)
        ·
          refine ⟨22971829693845091923335951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15314553129230061282223967 22971829693845091923335951)
          ·
            refine ⟨34457744540767637885003927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22971829693845091923335951 34457744540767637885003927)
            ·
              refine ⟨51686616811151456827505891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34457744540767637885003927 51686616811151456827505891)
              ·
                refine ⟨77529925216727185241258837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51686616811151456827505891 77529925216727185241258837)
                ·
                  refine ⟨454276905566760851023001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77529925216727185241258837 454276905566760851023001)
                  ·
                    rfl

theorem cell23_7962310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7962310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962310 prefixEnd_7962310 := by exact prefixLift 7962310
  have htrace : WordTrace (prefixWord ++ tailWord_7962310) baseStart_7962310 baseEnd_7962310 := by
    simpa [prefixWord, tailWord_7962310, baseEnd_7962310] using wordTrace_append hprefix tailTrace_7962310
  have hstable : (prefixWord ++ tailWord_7962310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962310).length < 2 ^ (prefixWord ++ tailWord_7962310).sum := by decide
  have hdescent : baseEnd_7962310 < baseStart_7962310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962346 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7962346 : Nat := 118140960795 + 7962346 * 2 ^ 59
def prefixEnd_7962346 : Nat := 4983230072969 + 3 ^ 40 * 7962346 * 2
def baseEnd_7962346 : Nat := 4088510635404409518356843

theorem tailTrace_7962346 : CollatzResearch.WordTrace tailWord_7962346 prefixEnd_7962346 4088510635404409518356843 := by
  unfold tailWord_7962346
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602654202946944319472723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193607077874525184851927261 72602654202946944319472723)
  ·
    refine ⟨108903981304420416479209085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72602654202946944319472723 108903981304420416479209085)
    ·
      refine ⟨40838992989157656179703407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108903981304420416479209085 40838992989157656179703407)
      ·
        refine ⟨61258489483736484269555111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40838992989157656179703407 61258489483736484269555111)
        ·
          refine ⟨91887734225604726404332667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61258489483736484269555111 91887734225604726404332667)
          ·
            refine ⟨137831601338407089606499001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91887734225604726404332667 137831601338407089606499001)
            ·
              refine ⟨103373701003805317204874251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137831601338407089606499001 103373701003805317204874251)
              ·
                refine ⟨155060551505707975807311377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103373701003805317204874251 155060551505707975807311377)
                ·
                  refine ⟨116295413629280981855483533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155060551505707975807311377 116295413629280981855483533)
                  ·
                    refine ⟨43610780110980368195806325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116295413629280981855483533 43610780110980368195806325)
                    ·
                      refine ⟨4088510635404409518356843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43610780110980368195806325 4088510635404409518356843)
                      ·
                        rfl

theorem cell23_7962346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7962346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962346 prefixEnd_7962346 := by exact prefixLift 7962346
  have htrace : WordTrace (prefixWord ++ tailWord_7962346) baseStart_7962346 baseEnd_7962346 := by
    simpa [prefixWord, tailWord_7962346, baseEnd_7962346] using wordTrace_append hprefix tailTrace_7962346
  have hstable : (prefixWord ++ tailWord_7962346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962346).length < 2 ^ (prefixWord ++ tailWord_7962346).sum := by decide
  have hdescent : baseEnd_7962346 < baseStart_7962346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962353 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_7962353 : Nat := 118140960795 + 7962353 * 2 ^ 59
def prefixEnd_7962353 : Nat := 4983230072969 + 3 ^ 40 * 7962353 * 2
def baseEnd_7962353 : Nat := 1362838076589663663656437

theorem tailTrace_7962353 : CollatzResearch.WordTrace tailWord_7962353 prefixEnd_7962353 1362838076589663663656437 := by
  unfold tailWord_7962353
  simp only [CollatzResearch.WordTrace]
  refine ⟨290410872122762417473395713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193607248081841611648930475 290410872122762417473395713)
  ·
    refine ⟨217808154092071813105046785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290410872122762417473395713 217808154092071813105046785)
    ·
      refine ⟨163356115569053859828785089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217808154092071813105046785 163356115569053859828785089)
      ·
        refine ⟨122517086676790394871588817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163356115569053859828785089 122517086676790394871588817)
        ·
          refine ⟨91887815007592796153691613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122517086676790394871588817 91887815007592796153691613)
          ·
            refine ⟨34457930627847298557634355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91887815007592796153691613 34457930627847298557634355)
            ·
              refine ⟨51686895941770947836451533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34457930627847298557634355 51686895941770947836451533)
              ·
                refine ⟨19382585978164105438669325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51686895941770947836451533 19382585978164105438669325)
                ·
                  refine ⟨7268469741811539539500997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19382585978164105438669325 7268469741811539539500997)
                  ·
                    refine ⟨1362838076589663663656437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268469741811539539500997 1362838076589663663656437)
                    ·
                      rfl

theorem cell23_7962353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_7962353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962353 prefixEnd_7962353 := by exact prefixLift 7962353
  have htrace : WordTrace (prefixWord ++ tailWord_7962353) baseStart_7962353 baseEnd_7962353 := by
    simpa [prefixWord, tailWord_7962353, baseEnd_7962353] using wordTrace_append hprefix tailTrace_7962353
  have hstable : (prefixWord ++ tailWord_7962353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962353).length < 2 ^ (prefixWord ++ tailWord_7962353).sum := by decide
  have hdescent : baseEnd_7962353 < baseStart_7962353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962370 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7962370 : Nat := 118140960795 + 7962370 * 2 ^ 59
def prefixEnd_7962370 : Nat := 4983230072969 + 3 ^ 40 * 7962370 * 2
def baseEnd_7962370 : Nat := 1362840986313372474818911

theorem tailTrace_7962370 : CollatzResearch.WordTrace tailWord_7962370 prefixEnd_7962370 1362840986313372474818911 := by
  unfold tailWord_7962370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602873040925207344191141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193607661442467219584509709 72602873040925207344191141)
  ·
    refine ⟨13613038695173476377035839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72602873040925207344191141 13613038695173476377035839)
    ·
      refine ⟨20419558042760214565553759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13613038695173476377035839 20419558042760214565553759)
      ·
        refine ⟨30629337064140321848330639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419558042760214565553759 30629337064140321848330639)
        ·
          refine ⟨45944005596210482772495959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30629337064140321848330639 45944005596210482772495959)
          ·
            refine ⟨68916008394315724158743939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45944005596210482772495959 68916008394315724158743939)
            ·
              refine ⟨103374012591473586238115909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68916008394315724158743939 103374012591473586238115909)
              ·
                refine ⟨19382627360901297419646733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103374012591473586238115909 19382627360901297419646733)
                ·
                  refine ⟨7268485260337986532367525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19382627360901297419646733 7268485260337986532367525)
                  ·
                    refine ⟨1362840986313372474818911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268485260337986532367525 1362840986313372474818911)
                    ·
                      rfl

theorem cell23_7962370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7962370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962370 prefixEnd_7962370 := by exact prefixLift 7962370
  have htrace : WordTrace (prefixWord ++ tailWord_7962370) baseStart_7962370 baseEnd_7962370 := by
    simpa [prefixWord, tailWord_7962370, baseEnd_7962370] using wordTrace_append hprefix tailTrace_7962370
  have hstable : (prefixWord ++ tailWord_7962370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962370).length < 2 ^ (prefixWord ++ tailWord_7962370).sum := by decide
  have hdescent : baseEnd_7962370 < baseStart_7962370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962404 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_7962404 : Nat := 118140960795 + 7962404 * 2 ^ 59
def prefixEnd_7962404 : Nat := 4983230072969 + 3 ^ 40 * 7962404 * 2
def baseEnd_7962404 : Nat := 1362846805760790097143859

theorem tailTrace_7962404 : CollatzResearch.WordTrace tailWord_7962404 prefixEnd_7962404 1362846805760790097143859 := by
  unfold tailWord_7962404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145206366122788826591751133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193608488163718435455668177 145206366122788826591751133)
  ·
    refine ⟨54452387296045809971906675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145206366122788826591751133 54452387296045809971906675)
    ·
      refine ⟨81678580944068714957860013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54452387296045809971906675 81678580944068714957860013)
      ·
        refine ⟨30629467854025768109197505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81678580944068714957860013 30629467854025768109197505)
        ·
          refine ⟨22972100890519326081898129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30629467854025768109197505 22972100890519326081898129)
          ·
            refine ⟨17229075667889494561423597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22972100890519326081898129 17229075667889494561423597)
            ·
              refine ⟨6460903375458560460533849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17229075667889494561423597 6460903375458560460533849)
              ·
                refine ⟨4845677531593920345400387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6460903375458560460533849 4845677531593920345400387)
                ·
                  refine ⟨7268516297390880518100581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845677531593920345400387 7268516297390880518100581)
                  ·
                    refine ⟨1362846805760790097143859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268516297390880518100581 1362846805760790097143859)
                    ·
                      rfl

theorem cell23_7962404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_7962404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962404 prefixEnd_7962404 := by exact prefixLift 7962404
  have htrace : WordTrace (prefixWord ++ tailWord_7962404) baseStart_7962404 baseEnd_7962404 := by
    simpa [prefixWord, tailWord_7962404, baseEnd_7962404] using wordTrace_append hprefix tailTrace_7962404
  have hstable : (prefixWord ++ tailWord_7962404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962404).length < 2 ^ (prefixWord ++ tailWord_7962404).sum := by decide
  have hdescent : baseEnd_7962404 < baseStart_7962404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962416 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_7962416 : Nat := 118140960795 + 7962416 * 2 ^ 59
def prefixEnd_7962416 : Nat := 4983230072969 + 3 ^ 40 * 7962416 * 2
def baseEnd_7962416 : Nat := 4088546579050224244481521

theorem tailTrace_7962416 : CollatzResearch.WordTrace tailWord_7962416 prefixEnd_7962416 4088546579050224244481521 := by
  unfold tailWord_7962416
  simp only [CollatzResearch.WordTrace]
  refine ⟨145206584960767089616469551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193608779947689452821959401 145206584960767089616469551)
  ·
    refine ⟨217809877441150634424704327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145206584960767089616469551 217809877441150634424704327)
    ·
      refine ⟨326714816161725951637056491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217809877441150634424704327 326714816161725951637056491)
      ·
        refine ⟨490072224242588927455584737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326714816161725951637056491 490072224242588927455584737)
        ·
          refine ⟨367554168181941695591688553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490072224242588927455584737 367554168181941695591688553)
          ·
            refine ⟨275665626136456271693766415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367554168181941695591688553 275665626136456271693766415)
            ·
              refine ⟨413498439204684407540649623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275665626136456271693766415 413498439204684407540649623)
              ·
                refine ⟨620247658807026611310974435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413498439204684407540649623 620247658807026611310974435)
                ·
                  refine ⟨930371488210539916966461653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620247658807026611310974435 930371488210539916966461653)
                  ·
                    refine ⟨21805581754934529303901445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 930371488210539916966461653 21805581754934529303901445)
                    ·
                      refine ⟨4088546579050224244481521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21805581754934529303901445 4088546579050224244481521)
                      ·
                        rfl

theorem cell23_7962416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_7962416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962416 prefixEnd_7962416 := by exact prefixLift 7962416
  have htrace : WordTrace (prefixWord ++ tailWord_7962416) baseStart_7962416 baseEnd_7962416 := by
    simpa [prefixWord, tailWord_7962416, baseEnd_7962416] using wordTrace_append hprefix tailTrace_7962416
  have hstable : (prefixWord ++ tailWord_7962416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962416).length < 2 ^ (prefixWord ++ tailWord_7962416).sum := by decide
  have hdescent : baseEnd_7962416 < baseStart_7962416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962430 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7962430 : Nat := 118140960795 + 7962430 * 2 ^ 59
def prefixEnd_7962430 : Nat := 4983230072969 + 3 ^ 40 * 7962430 * 2
def baseEnd_7962430 : Nat := 1362851255926462396568819

theorem tailTrace_7962430 : CollatzResearch.WordTrace tailWord_7962430 prefixEnd_7962430 1362851255926462396568819 := by
  unfold tailWord_7962430
  simp only [CollatzResearch.WordTrace]
  refine ⟨36301710067935432452993593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193609120362322306415965829 36301710067935432452993593)
  ·
    refine ⟨27226282550951574339745195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36301710067935432452993593 27226282550951574339745195)
    ·
      refine ⟨40839423826427361509617793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27226282550951574339745195 40839423826427361509617793)
      ·
        refine ⟨30629567869820521132213345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40839423826427361509617793 30629567869820521132213345)
        ·
          refine ⟨22972175902365390849160009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30629567869820521132213345 22972175902365390849160009)
          ·
            refine ⟨17229131926774043136870007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22972175902365390849160009 17229131926774043136870007)
            ·
              refine ⟨25843697890161064705305011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17229131926774043136870007 25843697890161064705305011)
              ·
                refine ⟨38765546835241597057957517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25843697890161064705305011 38765546835241597057957517)
                ·
                  refine ⟨14537080063215598896734069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38765546835241597057957517 14537080063215598896734069)
                  ·
                    refine ⟨1362851255926462396568819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14537080063215598896734069 1362851255926462396568819)
                    ·
                      rfl

theorem cell23_7962430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7962430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962430 prefixEnd_7962430 := by exact prefixLift 7962430
  have htrace : WordTrace (prefixWord ++ tailWord_7962430) baseStart_7962430 baseEnd_7962430 := by
    simpa [prefixWord, tailWord_7962430, baseEnd_7962430] using wordTrace_append hprefix tailTrace_7962430
  have hstable : (prefixWord ++ tailWord_7962430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962430).length < 2 ^ (prefixWord ++ tailWord_7962430).sum := by decide
  have hdescent : baseEnd_7962430 < baseStart_7962430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962500 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7962500 : Nat := 118140960795 + 7962500 * 2 ^ 59
def prefixEnd_7962500 : Nat := 4983230072969 + 3 ^ 40 * 7962500 * 2
def baseEnd_7962500 : Nat := 4088589711425201915831135

theorem tailTrace_7962500 : CollatzResearch.WordTrace tailWord_7962500 prefixEnd_7962500 4088589711425201915831135 := by
  unfold tailWord_7962500
  simp only [CollatzResearch.WordTrace]
  refine ⟨145208116826614930789498477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193610822435486574385997969 145208116826614930789498477)
  ·
    refine ⟨54453043809980599046061929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145208116826614930789498477 54453043809980599046061929)
    ·
      refine ⟨40839782857485449284546447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54453043809980599046061929 40839782857485449284546447)
      ·
        refine ⟨61259674286228173926819671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40839782857485449284546447 61259674286228173926819671)
        ·
          refine ⟨91889511429342260890229507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61259674286228173926819671 91889511429342260890229507)
          ·
            refine ⟨137834267144013391335344261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91889511429342260890229507 137834267144013391335344261)
            ·
              refine ⟨25843925089502510875377049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137834267144013391335344261 25843925089502510875377049)
              ·
                refine ⟨19382943817126883156532787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25843925089502510875377049 19382943817126883156532787)
                ·
                  refine ⟨29074415725690324734799181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19382943817126883156532787 29074415725690324734799181)
                  ·
                    refine ⟨10902905897133871775549693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29074415725690324734799181 10902905897133871775549693)
                    ·
                      refine ⟨4088589711425201915831135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10902905897133871775549693 4088589711425201915831135)
                      ·
                        rfl

theorem cell23_7962500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7962500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962500 prefixEnd_7962500 := by exact prefixLift 7962500
  have htrace : WordTrace (prefixWord ++ tailWord_7962500) baseStart_7962500 baseEnd_7962500 := by
    simpa [prefixWord, tailWord_7962500, baseEnd_7962500] using wordTrace_append hprefix tailTrace_7962500
  have hstable : (prefixWord ++ tailWord_7962500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962500).length < 2 ^ (prefixWord ++ tailWord_7962500).sum := by decide
  have hdescent : baseEnd_7962500 < baseStart_7962500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962543 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_7962543 : Nat := 118140960795 + 7962543 * 2 ^ 59
def prefixEnd_7962543 : Nat := 4983230072969 + 3 ^ 40 * 7962543 * 2
def baseEnd_7962543 : Nat := 4088611791093345247593437

theorem tailTrace_7962543 : CollatzResearch.WordTrace tailWord_7962543 prefixEnd_7962543 4088611791093345247593437 := by
  unfold tailWord_7962543
  simp only [CollatzResearch.WordTrace]
  refine ⟨290417801992074079922812283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193611867994716053281874855 290417801992074079922812283)
  ·
    refine ⟨435626702988111119884218425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290417801992074079922812283 435626702988111119884218425)
    ·
      refine ⟨326720027241083339913163819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435626702988111119884218425 326720027241083339913163819)
      ·
        refine ⟨490080040861625009869745729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326720027241083339913163819 490080040861625009869745729)
        ·
          refine ⟨367560030646218757402309297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490080040861625009869745729 367560030646218757402309297)
          ·
            refine ⟨275670022984664068051731973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367560030646218757402309297 275670022984664068051731973)
            ·
              refine ⟨51688129309624512759699745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275670022984664068051731973 51688129309624512759699745)
              ·
                refine ⟨38766096982218384569774809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51688129309624512759699745 38766096982218384569774809)
                ·
                  refine ⟨29074572736663788427331107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38766096982218384569774809 29074572736663788427331107)
                  ·
                    refine ⟨43611859104995682640996661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29074572736663788427331107 43611859104995682640996661)
                    ·
                      refine ⟨4088611791093345247593437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43611859104995682640996661 4088611791093345247593437)
                      ·
                        rfl

theorem cell23_7962543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_7962543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962543 prefixEnd_7962543 := by exact prefixLift 7962543
  have htrace : WordTrace (prefixWord ++ tailWord_7962543) baseStart_7962543 baseEnd_7962543 := by
    simpa [prefixWord, tailWord_7962543, baseEnd_7962543] using wordTrace_append hprefix tailTrace_7962543
  have hstable : (prefixWord ++ tailWord_7962543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962543).length < 2 ^ (prefixWord ++ tailWord_7962543).sum := by decide
  have hdescent : baseEnd_7962543 < baseStart_7962543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962574 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_7962574 : Nat := 118140960795 + 7962574 * 2 ^ 59
def prefixEnd_7962574 : Nat := 4983230072969 + 3 ^ 40 * 7962574 * 2
def baseEnd_7962574 : Nat := 4088627708993634626305795

theorem tailTrace_7962574 : CollatzResearch.WordTrace tailWord_7962574 prefixEnd_7962574 4088627708993634626305795 := by
  unfold tailWord_7962574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302366581870221527148847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193612621769974514811460517 36302366581870221527148847)
  ·
    refine ⟨54453549872805332290723271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36302366581870221527148847 54453549872805332290723271)
    ·
      refine ⟨81680324809207998436084907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54453549872805332290723271 81680324809207998436084907)
      ·
        refine ⟨122520487213811997654127361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81680324809207998436084907 122520487213811997654127361)
        ·
          refine ⟨91890365410358998240595521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122520487213811997654127361 91890365410358998240595521)
          ·
            refine ⟨68917774057769248680446641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91890365410358998240595521 68917774057769248680446641)
            ·
              refine ⟨51688330543326936510334981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68917774057769248680446641 51688330543326936510334981)
              ·
                refine ⟨9691561976873800595687809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51688330543326936510334981 9691561976873800595687809)
                ·
                  refine ⟨7268671482655350446765857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9691561976873800595687809 7268671482655350446765857)
                  ·
                    refine ⟨5451503611991512835074393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7268671482655350446765857 5451503611991512835074393)
                    ·
                      refine ⟨4088627708993634626305795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451503611991512835074393 4088627708993634626305795)
                      ·
                        rfl

theorem cell23_7962574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_7962574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962574 prefixEnd_7962574 := by exact prefixLift 7962574
  have htrace : WordTrace (prefixWord ++ tailWord_7962574) baseStart_7962574 baseEnd_7962574 := by
    simpa [prefixWord, tailWord_7962574, baseEnd_7962574] using wordTrace_append hprefix tailTrace_7962574
  have hstable : (prefixWord ++ tailWord_7962574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962574).length < 2 ^ (prefixWord ++ tailWord_7962574).sum := by decide
  have hdescent : baseEnd_7962574 < baseStart_7962574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962591 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 2, 2, 2]
def baseStart_7962591 : Nat := 118140960795 + 7962591 * 2 ^ 59
def prefixEnd_7962591 : Nat := 4983230072969 + 3 ^ 40 * 7962591 * 2
def baseEnd_7962591 : Nat := 4088636438164761059793217

theorem tailTrace_7962591 : CollatzResearch.WordTrace tailWord_7962591 prefixEnd_7962591 4088636438164761059793217 := by
  unfold tailWord_7962591
  simp only [CollatzResearch.WordTrace]
  refine ⟨290419552695900184120559627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193613035130600122747039751 290419552695900184120559627)
  ·
    refine ⟨435629329043850276180839441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290419552695900184120559627 435629329043850276180839441)
    ·
      refine ⟨326721996782887707135629581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435629329043850276180839441 326721996782887707135629581)
      ·
        refine ⟨122520748793582890175861093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326721996782887707135629581 122520748793582890175861093)
        ·
          refine ⟨22972640398796791907973955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122520748793582890175861093 22972640398796791907973955)
          ·
            refine ⟨34458960598195187861960933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22972640398796791907973955 34458960598195187861960933)
            ·
              refine ⟨6461055112161597724117675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34458960598195187861960933 6461055112161597724117675)
              ·
                refine ⟨9691582668242396586176513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461055112161597724117675 9691582668242396586176513)
                ·
                  refine ⟨7268687001181797439632385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9691582668242396586176513 7268687001181797439632385)
                  ·
                    refine ⟨5451515250886348079724289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7268687001181797439632385 5451515250886348079724289)
                    ·
                      refine ⟨4088636438164761059793217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451515250886348079724289 4088636438164761059793217)
                      ·
                        rfl

theorem cell23_7962591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_7962591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962591 prefixEnd_7962591 := by exact prefixLift 7962591
  have htrace : WordTrace (prefixWord ++ tailWord_7962591) baseStart_7962591 baseEnd_7962591 := by
    simpa [prefixWord, tailWord_7962591, baseEnd_7962591] using wordTrace_append hprefix tailTrace_7962591
  have hstable : (prefixWord ++ tailWord_7962591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962591).length < 2 ^ (prefixWord ++ tailWord_7962591).sum := by decide
  have hdescent : baseEnd_7962591 < baseStart_7962591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962593 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_7962593 : Nat := 118140960795 + 7962593 * 2 ^ 59
def prefixEnd_7962593 : Nat := 4983230072969 + 3 ^ 40 * 7962593 * 2
def baseEnd_7962593 : Nat := 1362879155042023350656069

theorem tailTrace_7962593 : CollatzResearch.WordTrace tailWord_7962593 prefixEnd_7962593 1362879155042023350656069 := by
  unfold tailWord_7962593
  simp only [CollatzResearch.WordTrace]
  refine ⟨290419625641892938462132433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193613083761261958974754955 290419625641892938462132433)
  ·
    refine ⟨217814719231419703846599325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290419625641892938462132433 217814719231419703846599325)
    ·
      refine ⟨81680519711782388942474747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217814719231419703846599325 81680519711782388942474747)
      ·
        refine ⟨122520779567673583413712121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81680519711782388942474747 122520779567673583413712121)
        ·
          refine ⟨91890584675755187560284091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122520779567673583413712121 91890584675755187560284091)
          ·
            refine ⟨137835877013632781340426137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91890584675755187560284091 137835877013632781340426137)
            ·
              refine ⟨103376907760224586005319603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137835877013632781340426137 103376907760224586005319603)
              ·
                refine ⟨155065361640336879007979405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103376907760224586005319603 155065361640336879007979405)
                ·
                  refine ⟨58149510615126329627992277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155065361640336879007979405 58149510615126329627992277)
                  ·
                    refine ⟨1362879155042023350656069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58149510615126329627992277 1362879155042023350656069)
                    ·
                      rfl

theorem cell23_7962593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_7962593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962593 prefixEnd_7962593 := by exact prefixLift 7962593
  have htrace : WordTrace (prefixWord ++ tailWord_7962593) baseStart_7962593 baseEnd_7962593 := by
    simpa [prefixWord, tailWord_7962593, baseEnd_7962593] using wordTrace_append hprefix tailTrace_7962593
  have hstable : (prefixWord ++ tailWord_7962593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962593).length < 2 ^ (prefixWord ++ tailWord_7962593).sum := by decide
  have hdescent : baseEnd_7962593 < baseStart_7962593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962664 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7962664 : Nat := 118140960795 + 7962664 * 2 ^ 59
def prefixEnd_7962664 : Nat := 4983230072969 + 3 ^ 40 * 7962664 * 2
def baseEnd_7962664 : Nat := 4088673922252539274180381

theorem tailTrace_7962664 : CollatzResearch.WordTrace tailWord_7962664 prefixEnd_7962664 4088673922252539274180381 := by
  unfold tailWord_7962664
  simp only [CollatzResearch.WordTrace]
  refine ⟨145211107612317858793983523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193614810149757145058644697 145211107612317858793983523)
  ·
    refine ⟨217816661418476788190975285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145211107612317858793983523 217816661418476788190975285)
    ·
      refine ⟨20420312007982198892903933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217816661418476788190975285 20420312007982198892903933)
      ·
        refine ⟨7657617002993324584838975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20420312007982198892903933 7657617002993324584838975)
        ·
          refine ⟨11486425504489986877258463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7657617002993324584838975 11486425504489986877258463)
          ·
            refine ⟨17229638256734980315887695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486425504489986877258463 17229638256734980315887695)
            ·
              refine ⟨25844457385102470473831543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17229638256734980315887695 25844457385102470473831543)
              ·
                refine ⟨38766686077653705710747315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25844457385102470473831543 38766686077653705710747315)
                ·
                  refine ⟨58150029116480558566120973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38766686077653705710747315 58150029116480558566120973)
                  ·
                    refine ⟨21806260918680209462295365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58150029116480558566120973 21806260918680209462295365)
                    ·
                      refine ⟨4088673922252539274180381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21806260918680209462295365 4088673922252539274180381)
                      ·
                        rfl

theorem cell23_7962664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7962664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962664 prefixEnd_7962664 := by exact prefixLift 7962664
  have htrace : WordTrace (prefixWord ++ tailWord_7962664) baseStart_7962664 baseEnd_7962664 := by
    simpa [prefixWord, tailWord_7962664, baseEnd_7962664] using wordTrace_append hprefix tailTrace_7962664
  have hstable : (prefixWord ++ tailWord_7962664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962664).length < 2 ^ (prefixWord ++ tailWord_7962664).sum := by decide
  have hdescent : baseEnd_7962664 < baseStart_7962664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962674 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_7962674 : Nat := 118140960795 + 7962674 * 2 ^ 59
def prefixEnd_7962674 : Nat := 4983230072969 + 3 ^ 40 * 7962674 * 2
def baseEnd_7962674 : Nat := 1362893019019694745018445

theorem tailTrace_7962674 : CollatzResearch.WordTrace tailWord_7962674 prefixEnd_7962674 1362893019019694745018445 := by
  unfold tailWord_7962674
  simp only [CollatzResearch.WordTrace]
  refine ⟨72605644988649872323957769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193615053303066326197220717 72605644988649872323957769)
  ·
    refine ⟨54454233741487404242968327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72605644988649872323957769 54454233741487404242968327)
    ·
      refine ⟨81681350612231106364452491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54454233741487404242968327 81681350612231106364452491)
      ·
        refine ⟨122522025918346659546678737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81681350612231106364452491 122522025918346659546678737)
        ·
          refine ⟨91891519438759994660009053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122522025918346659546678737 91891519438759994660009053)
          ·
            refine ⟨34459319789534997997503395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91891519438759994660009053 34459319789534997997503395)
            ·
              refine ⟨51688979684302496996255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34459319789534997997503395 51688979684302496996255093)
              ·
                refine ⟨4845841845403359093398915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51688979684302496996255093 4845841845403359093398915)
                ·
                  refine ⟨7268762768105038640098373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845841845403359093398915 7268762768105038640098373)
                  ·
                    refine ⟨1362893019019694745018445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7268762768105038640098373 1362893019019694745018445)
                    ·
                      rfl

theorem cell23_7962674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_7962674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962674 prefixEnd_7962674 := by exact prefixLift 7962674
  have htrace : WordTrace (prefixWord ++ tailWord_7962674) baseStart_7962674 baseEnd_7962674 := by
    simpa [prefixWord, tailWord_7962674, baseEnd_7962674] using wordTrace_append hprefix tailTrace_7962674
  have hstable : (prefixWord ++ tailWord_7962674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962674).length < 2 ^ (prefixWord ++ tailWord_7962674).sum := by decide
  have hdescent : baseEnd_7962674 < baseStart_7962674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962700 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_7962700 : Nat := 118140960795 + 7962700 * 2 ^ 59
def prefixEnd_7962700 : Nat := 4983230072969 + 3 ^ 40 * 7962700 * 2
def baseEnd_7962700 : Nat := 1362897469185367044443405

theorem tailTrace_7962700 : CollatzResearch.WordTrace tailWord_7962700 prefixEnd_7962700 1362897469185367044443405 := by
  unfold tailWord_7962700
  simp only [CollatzResearch.WordTrace]
  refine ⟨145211764126252647868138777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193615685501670197157518369 145211764126252647868138777)
  ·
    refine ⟨108908823094689485901104083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145211764126252647868138777 108908823094689485901104083)
    ·
      refine ⟨163363234642034228851656125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108908823094689485901104083 163363234642034228851656125)
      ·
        refine ⟨61261212990762835819371047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163363234642034228851656125 61261212990762835819371047)
        ·
          refine ⟨91891819486144253729056571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61261212990762835819371047 91891819486144253729056571)
          ·
            refine ⟨137837729229216380593584857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91891819486144253729056571 137837729229216380593584857)
            ·
              refine ⟨103378296921912285445188643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137837729229216380593584857 103378296921912285445188643)
              ·
                refine ⟨155067445382868428167782965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103378296921912285445188643 155067445382868428167782965)
                ·
                  refine ⟨14537573004643915140729653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155067445382868428167782965 14537573004643915140729653)
                  ·
                    refine ⟨1362897469185367044443405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14537573004643915140729653 1362897469185367044443405)
                    ·
                      rfl

theorem cell23_7962700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_7962700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962700 prefixEnd_7962700 := by exact prefixLift 7962700
  have htrace : WordTrace (prefixWord ++ tailWord_7962700) baseStart_7962700 baseEnd_7962700 := by
    simpa [prefixWord, tailWord_7962700, baseEnd_7962700] using wordTrace_append hprefix tailTrace_7962700
  have hstable : (prefixWord ++ tailWord_7962700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962700).length < 2 ^ (prefixWord ++ tailWord_7962700).sum := by decide
  have hdescent : baseEnd_7962700 < baseStart_7962700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962737 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_7962737 : Nat := 118140960795 + 7962737 * 2 ^ 59
def prefixEnd_7962737 : Nat := 4983230072969 + 3 ^ 40 * 7962737 * 2
def baseEnd_7962737 : Nat := 4088711406340317488567545

theorem tailTrace_7962737 : CollatzResearch.WordTrace tailWord_7962737 prefixEnd_7962737 4088711406340317488567545 := by
  unfold tailWord_7962737
  simp only [CollatzResearch.WordTrace]
  refine ⟨290424877753371251055374465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193616585168914167370249643 290424877753371251055374465)
  ·
    refine ⟨217818658315028438291530849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290424877753371251055374465 217818658315028438291530849)
    ·
      refine ⟨163363993736271328718648137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217818658315028438291530849 163363993736271328718648137)
      ·
        refine ⟨122522995302203496538986103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163363993736271328718648137 122522995302203496538986103)
        ·
          refine ⟨183784492953305244808479155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122522995302203496538986103 183784492953305244808479155)
          ·
            refine ⟨275676739429957867212718733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183784492953305244808479155 275676739429957867212718733)
            ·
              refine ⟨103378777286234200204769525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275676739429957867212718733 103378777286234200204769525)
              ·
                refine ⟨9691760370584456269197143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103378777286234200204769525 9691760370584456269197143)
                ·
                  refine ⟨14537640555876684403795715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9691760370584456269197143 14537640555876684403795715)
                  ·
                    refine ⟨21806460833815026605693573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14537640555876684403795715 21806460833815026605693573)
                    ·
                      refine ⟨4088711406340317488567545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21806460833815026605693573 4088711406340317488567545)
                      ·
                        rfl

theorem cell23_7962737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_7962737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962737 prefixEnd_7962737 := by exact prefixLift 7962737
  have htrace : WordTrace (prefixWord ++ tailWord_7962737) baseStart_7962737 baseEnd_7962737 := by
    simpa [prefixWord, tailWord_7962737, baseEnd_7962737] using wordTrace_append hprefix tailTrace_7962737
  have hstable : (prefixWord ++ tailWord_7962737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962737).length < 2 ^ (prefixWord ++ tailWord_7962737).sum := by decide
  have hdescent : baseEnd_7962737 < baseStart_7962737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962748 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_7962748 : Nat := 118140960795 + 7962748 * 2 ^ 59
def prefixEnd_7962748 : Nat := 4983230072969 + 3 ^ 40 * 7962748 * 2
def baseEnd_7962748 : Nat := 4088717054627516945529995

theorem tailTrace_7962748 : CollatzResearch.WordTrace tailWord_7962748 prefixEnd_7962748 4088717054627516945529995 := by
  unfold tailWord_7962748
  simp only [CollatzResearch.WordTrace]
  refine ⟨145212639478165699967012449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193616852637554266622683265 145212639478165699967012449)
  ·
    refine ⟨108909479608624274975259337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145212639478165699967012449 108909479608624274975259337)
    ·
      refine ⟨81682109706468206231444503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108909479608624274975259337 81682109706468206231444503)
      ·
        refine ⟨122523164559702309347166755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81682109706468206231444503 122523164559702309347166755)
        ·
          refine ⟨183784746839553464020750133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122523164559702309347166755 183784746839553464020750133)
          ·
            refine ⟨17229820016208137251945325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183784746839553464020750133 17229820016208137251945325)
            ·
              refine ⟨6461182506078051469479497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17229820016208137251945325 6461182506078051469479497)
              ·
                refine ⟨4845886879558538602109623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461182506078051469479497 4845886879558538602109623)
                ·
                  refine ⟨7268830319337807903164435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845886879558538602109623 7268830319337807903164435)
                  ·
                    refine ⟨10903245479006711854746653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7268830319337807903164435 10903245479006711854746653)
                    ·
                      refine ⟨4088717054627516945529995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10903245479006711854746653 4088717054627516945529995)
                      ·
                        rfl

theorem cell23_7962748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_7962748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962748 prefixEnd_7962748 := by exact prefixLift 7962748
  have htrace : WordTrace (prefixWord ++ tailWord_7962748) baseStart_7962748 baseEnd_7962748 := by
    simpa [prefixWord, tailWord_7962748, baseEnd_7962748] using wordTrace_append hprefix tailTrace_7962748
  have hstable : (prefixWord ++ tailWord_7962748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962748).length < 2 ^ (prefixWord ++ tailWord_7962748).sum := by decide
  have hdescent : baseEnd_7962748 < baseStart_7962748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962757 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_7962757 : Nat := 118140960795 + 7962757 * 2 ^ 59
def prefixEnd_7962757 : Nat := 4983230072969 + 3 ^ 40 * 7962757 * 2
def baseEnd_7962757 : Nat := 4088721675953407410317453

theorem tailTrace_7962757 : CollatzResearch.WordTrace tailWord_7962757 prefixEnd_7962757 4088721675953407410317453 := by
  unfold tailWord_7962757
  simp only [CollatzResearch.WordTrace]
  refine ⟨290425607213298794471102525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193617071475532529647401683 290425607213298794471102525)
  ·
    refine ⟨108909602704987047926663447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290425607213298794471102525 108909602704987047926663447)
    ·
      refine ⟨163364404057480571889995171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108909602704987047926663447 163364404057480571889995171)
      ·
        refine ⟨245046606086220857834992757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163364404057480571889995171 245046606086220857834992757)
        ·
          refine ⟨22973119320583205422030571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245046606086220857834992757 22973119320583205422030571)
          ·
            refine ⟨34459678980874808133045857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22973119320583205422030571 34459678980874808133045857)
            ·
              refine ⟨25844759235656106099784393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34459678980874808133045857 25844759235656106099784393)
              ·
                refine ⟨19383569426742079574838295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25844759235656106099784393 19383569426742079574838295)
                ·
                  refine ⟨29075354140113119362257443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19383569426742079574838295 29075354140113119362257443)
                  ·
                    refine ⟨43613031210169679043386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29075354140113119362257443 43613031210169679043386165)
                    ·
                      refine ⟨4088721675953407410317453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43613031210169679043386165 4088721675953407410317453)
                      ·
                        rfl

theorem cell23_7962757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_7962757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962757 prefixEnd_7962757 := by exact prefixLift 7962757
  have htrace : WordTrace (prefixWord ++ tailWord_7962757) baseStart_7962757 baseEnd_7962757 := by
    simpa [prefixWord, tailWord_7962757, baseEnd_7962757] using wordTrace_append hprefix tailTrace_7962757
  have hstable : (prefixWord ++ tailWord_7962757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962757).length < 2 ^ (prefixWord ++ tailWord_7962757).sum := by decide
  have hdescent : baseEnd_7962757 < baseStart_7962757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962791 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7962791 : Nat := 118140960795 + 7962791 * 2 ^ 59
def prefixEnd_7962791 : Nat := 4983230072969 + 3 ^ 40 * 7962791 * 2
def baseEnd_7962791 : Nat := 4088739134295660277292297

theorem tailTrace_7962791 : CollatzResearch.WordTrace tailWord_7962791 prefixEnd_7962791 4088739134295660277292297 := by
  unfold tailWord_7962791
  simp only [CollatzResearch.WordTrace]
  refine ⟨290426847295175618277840227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193617898196783745518560151 290426847295175618277840227)
  ·
    refine ⟨435640270942763427416760341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290426847295175618277840227 435640270942763427416760341)
    ·
      refine ⟨20420637700442035660160641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435640270942763427416760341 20420637700442035660160641)
      ·
        refine ⟨15315478275331526745120481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20420637700442035660160641 15315478275331526745120481)
        ·
          refine ⟨11486608706498645058840361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15315478275331526745120481 11486608706498645058840361)
          ·
            refine ⟨8614956529873983794130271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11486608706498645058840361 8614956529873983794130271)
            ·
              refine ⟨12922434794810975691195407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8614956529873983794130271 12922434794810975691195407)
              ·
                refine ⟨19383652192216463536793111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922434794810975691195407 19383652192216463536793111)
                ·
                  refine ⟨29075478288324695305189667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19383652192216463536793111 29075478288324695305189667)
                  ·
                    refine ⟨43613217432487042957784501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29075478288324695305189667 43613217432487042957784501)
                    ·
                      refine ⟨4088739134295660277292297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43613217432487042957784501 4088739134295660277292297)
                      ·
                        rfl

theorem cell23_7962791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7962791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962791 prefixEnd_7962791 := by exact prefixLift 7962791
  have htrace : WordTrace (prefixWord ++ tailWord_7962791) baseStart_7962791 baseEnd_7962791 := by
    simpa [prefixWord, tailWord_7962791, baseEnd_7962791] using wordTrace_append hprefix tailTrace_7962791
  have hstable : (prefixWord ++ tailWord_7962791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962791).length < 2 ^ (prefixWord ++ tailWord_7962791).sum := by decide
  have hdescent : baseEnd_7962791 < baseStart_7962791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962794 : List Nat := [3, 1, 5, 1, 3, 10]
def baseStart_7962794 : Nat := 118140960795 + 7962794 * 2 ^ 59
def prefixEnd_7962794 : Nat := 4983230072969 + 3 ^ 40 * 7962794 * 2
def baseEnd_7962794 : Nat := 16826093311677464055781

theorem tailTrace_7962794 : CollatzResearch.WordTrace tailWord_7962794 prefixEnd_7962794 16826093311677464055781 := by
  unfold tailWord_7962794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72606739178541187447549859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193617971142776499860132957 72606739178541187447549859)
  ·
    refine ⟨108910108767811781171324789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72606739178541187447549859 108910108767811781171324789)
    ·
      refine ⟨10210322696982354484811699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108910108767811781171324789 10210322696982354484811699)
      ·
        refine ⟨15315484045473531727217549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210322696982354484811699 15315484045473531727217549)
        ·
          refine ⟨5743306517052574397706581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15315484045473531727217549 5743306517052574397706581)
          ·
            refine ⟨16826093311677464055781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5743306517052574397706581 16826093311677464055781)
            ·
              rfl

theorem cell23_7962794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 10].length) (baseStart_7962794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962794 prefixEnd_7962794 := by exact prefixLift 7962794
  have htrace : WordTrace (prefixWord ++ tailWord_7962794) baseStart_7962794 baseEnd_7962794 := by
    simpa [prefixWord, tailWord_7962794, baseEnd_7962794] using wordTrace_append hprefix tailTrace_7962794
  have hstable : (prefixWord ++ tailWord_7962794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962794).length < 2 ^ (prefixWord ++ tailWord_7962794).sum := by decide
  have hdescent : baseEnd_7962794 < baseStart_7962794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962818 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7962818 : Nat := 118140960795 + 7962818 * 2 ^ 59
def prefixEnd_7962818 : Nat := 4983230072969 + 3 ^ 40 * 7962818 * 2
def baseEnd_7962818 : Nat := 4088752998273331671654673

theorem tailTrace_7962818 : CollatzResearch.WordTrace tailWord_7962818 prefixEnd_7962818 4088752998273331671654673 := by
  unfold tailWord_7962818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72606958016519450472268277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193618554710718534592715405 72606958016519450472268277)
  ·
    refine ⟨6806902314048698481775151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72606958016519450472268277 6806902314048698481775151)
    ·
      refine ⟨10210353471073047722662727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806902314048698481775151 10210353471073047722662727)
      ·
        refine ⟨15315530206609571583994091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210353471073047722662727 15315530206609571583994091)
        ·
          refine ⟨22973295309914357375991137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15315530206609571583994091 22973295309914357375991137)
          ·
            refine ⟨17229971482435768031993353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22973295309914357375991137 17229971482435768031993353)
            ·
              refine ⟨12922478611826826023995015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17229971482435768031993353 12922478611826826023995015)
              ·
                refine ⟨19383717917740239035992523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922478611826826023995015 19383717917740239035992523)
                ·
                  refine ⟨29075576876610358553988785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19383717917740239035992523 29075576876610358553988785)
                  ·
                    refine ⟨21806682657457768915491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29075576876610358553988785 21806682657457768915491589)
                    ·
                      refine ⟨4088752998273331671654673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21806682657457768915491589 4088752998273331671654673)
                      ·
                        rfl

theorem cell23_7962818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7962818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962818 prefixEnd_7962818 := by exact prefixLift 7962818
  have htrace : WordTrace (prefixWord ++ tailWord_7962818) baseStart_7962818 baseEnd_7962818 := by
    simpa [prefixWord, tailWord_7962818, baseEnd_7962818] using wordTrace_append hprefix tailTrace_7962818
  have hstable : (prefixWord ++ tailWord_7962818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962818).length < 2 ^ (prefixWord ++ tailWord_7962818).sum := by decide
  have hdescent : baseEnd_7962818 < baseStart_7962818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962867 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 7]
def baseStart_7962867 : Nat := 118140960795 + 7962867 * 2 ^ 59
def prefixEnd_7962867 : Nat := 4983230072969 + 3 ^ 40 * 7962867 * 2
def baseEnd_7962867 : Nat := 454308684313933553326883

theorem tailTrace_7962867 : CollatzResearch.WordTrace tailWord_7962867 prefixEnd_7962867 454308684313933553326883 := by
  unfold tailWord_7962867
  simp only [CollatzResearch.WordTrace]
  refine ⟨290429619242900283257606855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193619746161933522171737903 290429619242900283257606855)
  ·
    refine ⟨435644428864350424886410283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290429619242900283257606855 435644428864350424886410283)
    ·
      refine ⟨653466643296525637329615425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435644428864350424886410283 653466643296525637329615425)
      ·
        refine ⟨490099982472394227997211569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653466643296525637329615425 490099982472394227997211569)
        ·
          refine ⟨367574986854295670997908677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490099982472394227997211569 367574986854295670997908677)
          ·
            refine ⟨68920310035180438312107877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367574986854295670997908677 68920310035180438312107877)
            ·
              refine ⟨12922558131596332183520227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68920310035180438312107877 12922558131596332183520227)
              ·
                refine ⟨19383837197394498275280341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922558131596332183520227 19383837197394498275280341)
                ·
                  refine ⟨454308684313933553326883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19383837197394498275280341 454308684313933553326883)
                  ·
                    rfl

theorem cell23_7962867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 7].length) (baseStart_7962867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962867 prefixEnd_7962867 := by exact prefixLift 7962867
  have htrace : WordTrace (prefixWord ++ tailWord_7962867) baseStart_7962867 baseEnd_7962867 := by
    simpa [prefixWord, tailWord_7962867, baseEnd_7962867] using wordTrace_append hprefix tailTrace_7962867
  have hstable : (prefixWord ++ tailWord_7962867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962867).length < 2 ^ (prefixWord ++ tailWord_7962867).sum := by decide
  have hdescent : baseEnd_7962867 < baseStart_7962867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962897 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_7962897 : Nat := 118140960795 + 7962897 * 2 ^ 59
def prefixEnd_7962897 : Nat := 4983230072969 + 3 ^ 40 * 7962897 * 2
def baseEnd_7962897 : Nat := 1362931187748345620855603

theorem tailTrace_7962897 : CollatzResearch.WordTrace tailWord_7962897 prefixEnd_7962897 1362931187748345620855603 := by
  unfold tailWord_7962897
  simp only [CollatzResearch.WordTrace]
  refine ⟨290430713432791598381198945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193620475621861065587465963 290430713432791598381198945)
  ·
    refine ⟨217823035074593698785899209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290430713432791598381198945 217823035074593698785899209)
    ·
      refine ⟨163367276305945274089424407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217823035074593698785899209 163367276305945274089424407)
      ·
        refine ⟨245050914458917911134136611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163367276305945274089424407 245050914458917911134136611)
        ·
          refine ⟨367576371688376866701204917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245050914458917911134136611 367576371688376866701204917)
          ·
            refine ⟨34460284845785331253237961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367576371688376866701204917 34460284845785331253237961)
            ·
              refine ⟨25845213634338998439928471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34460284845785331253237961 25845213634338998439928471)
              ·
                refine ⟨38767820451508497659892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25845213634338998439928471 38767820451508497659892707)
                ·
                  refine ⟨58151730677262746489839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38767820451508497659892707 58151730677262746489839061)
                  ·
                    refine ⟨1362931187748345620855603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58151730677262746489839061 1362931187748345620855603)
                    ·
                      rfl

theorem cell23_7962897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_7962897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962897 prefixEnd_7962897 := by exact prefixLift 7962897
  have htrace : WordTrace (prefixWord ++ tailWord_7962897) baseStart_7962897 baseEnd_7962897 := by
    simpa [prefixWord, tailWord_7962897, baseEnd_7962897] using wordTrace_append hprefix tailTrace_7962897
  have hstable : (prefixWord ++ tailWord_7962897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962897).length < 2 ^ (prefixWord ++ tailWord_7962897).sum := by decide
  have hdescent : baseEnd_7962897 < baseStart_7962897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962914 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7962914 : Nat := 118140960795 + 7962914 * 2 ^ 59
def prefixEnd_7962914 : Nat := 4983230072969 + 3 ^ 40 * 7962914 * 2
def baseEnd_7962914 : Nat := 1362934097472054432018077

theorem tailTrace_7962914 : CollatzResearch.WordTrace tailWord_7962914 prefixEnd_7962914 1362934097472054432018077 := by
  unfold tailWord_7962914
  simp only [CollatzResearch.WordTrace]
  refine ⟨72607833368432502571141949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193620888982486673523045197 72607833368432502571141949)
  ·
    refine ⟨27227937513162188464178231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72607833368432502571141949 27227937513162188464178231)
    ·
      refine ⟨40841906269743282696267347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27227937513162188464178231 40841906269743282696267347)
      ·
        refine ⟨61262859404614924044401021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40841906269743282696267347 61262859404614924044401021)
        ·
          refine ⟨22973572276730596516650383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61262859404614924044401021 22973572276730596516650383)
          ·
            refine ⟨34460358415095894774975575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22973572276730596516650383 34460358415095894774975575)
            ·
              refine ⟨51690537622643842162463363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34460358415095894774975575 51690537622643842162463363)
              ·
                refine ⟨77535806433965763243695045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51690537622643842162463363 77535806433965763243695045)
                ·
                  refine ⟨14537963706368580608192821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77535806433965763243695045 14537963706368580608192821)
                  ·
                    refine ⟨1362934097472054432018077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14537963706368580608192821 1362934097472054432018077)
                    ·
                      rfl

theorem cell23_7962914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7962914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962914 prefixEnd_7962914 := by exact prefixLift 7962914
  have htrace : WordTrace (prefixWord ++ tailWord_7962914) baseStart_7962914 baseEnd_7962914 := by
    simpa [prefixWord, tailWord_7962914, baseEnd_7962914] using wordTrace_append hprefix tailTrace_7962914
  have hstable : (prefixWord ++ tailWord_7962914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962914).length < 2 ^ (prefixWord ++ tailWord_7962914).sum := by decide
  have hdescent : baseEnd_7962914 < baseStart_7962914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962947 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_7962947 : Nat := 118140960795 + 7962947 * 2 ^ 59
def prefixEnd_7962947 : Nat := 4983230072969 + 3 ^ 40 * 7962947 * 2
def baseEnd_7962947 : Nat := 4088819237277761666941579

theorem tailTrace_7962947 : CollatzResearch.WordTrace tailWord_7962947 prefixEnd_7962947 4088819237277761666941579 := by
  unfold tailWord_7962947
  simp only [CollatzResearch.WordTrace]
  refine ⟨290432537082610456920519095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193621691388406971280346063 290432537082610456920519095)
  ·
    refine ⟨435648805623915685380778643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290432537082610456920519095 435648805623915685380778643)
    ·
      refine ⟨653473208435873528071167965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435648805623915685380778643 653473208435873528071167965)
      ·
        refine ⟨245052453163452573026687987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653473208435873528071167965 245052453163452573026687987)
        ·
          refine ⟨367578679745178859540031981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245052453163452573026687987 367578679745178859540031981)
          ·
            refine ⟨137842004904442072327511993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367578679745178859540031981 137842004904442072327511993)
            ·
              refine ⟨103381503678331554245633995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137842004904442072327511993 103381503678331554245633995)
              ·
                refine ⟨155072255517497331368450993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103381503678331554245633995 155072255517497331368450993)
                ·
                  refine ⟨116304191638122998526338245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155072255517497331368450993 116304191638122998526338245)
                  ·
                    refine ⟨21807035932148062223688421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116304191638122998526338245 21807035932148062223688421)
                    ·
                      refine ⟨4088819237277761666941579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21807035932148062223688421 4088819237277761666941579)
                      ·
                        rfl

theorem cell23_7962947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_7962947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962947 prefixEnd_7962947 := by exact prefixLift 7962947
  have htrace : WordTrace (prefixWord ++ tailWord_7962947) baseStart_7962947 baseEnd_7962947 := by
    simpa [prefixWord, tailWord_7962947, baseEnd_7962947] using wordTrace_append hprefix tailTrace_7962947
  have hstable : (prefixWord ++ tailWord_7962947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962947).length < 2 ^ (prefixWord ++ tailWord_7962947).sum := by decide
  have hdescent : baseEnd_7962947 < baseStart_7962947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7962948 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7962948 : Nat := 118140960795 + 7962948 * 2 ^ 59
def prefixEnd_7962948 : Nat := 4983230072969 + 3 ^ 40 * 7962948 * 2
def baseEnd_7962948 : Nat := 1362939916919472054343025

theorem tailTrace_7962948 : CollatzResearch.WordTrace tailWord_7962948 prefixEnd_7962948 1362939916919472054343025 := by
  unfold tailWord_7962948
  simp only [CollatzResearch.WordTrace]
  refine ⟨145216286777803417045652749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193621715703737889394203665 145216286777803417045652749)
  ·
    refine ⟨54456107541676281392119781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145216286777803417045652749 54456107541676281392119781)
    ·
      refine ⟨10210520164064302761022459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54456107541676281392119781 10210520164064302761022459)
      ·
        refine ⟨15315780246096454141533689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210520164064302761022459 15315780246096454141533689)
        ·
          refine ⟨11486835184572340606150267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15315780246096454141533689 11486835184572340606150267)
          ·
            refine ⟨17230252776858510909225401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486835184572340606150267 17230252776858510909225401)
            ·
              refine ⟨12922689582643883181919051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17230252776858510909225401 12922689582643883181919051)
              ·
                refine ⟨19384034373965824772878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922689582643883181919051 19384034373965824772878577)
                ·
                  refine ⟨14538025780474368579658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19384034373965824772878577 14538025780474368579658933)
                  ·
                    refine ⟨1362939916919472054343025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14538025780474368579658933 1362939916919472054343025)
                    ·
                      rfl

theorem cell23_7962948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7962948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7962948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7962948 prefixEnd_7962948 := by exact prefixLift 7962948
  have htrace : WordTrace (prefixWord ++ tailWord_7962948) baseStart_7962948 baseEnd_7962948 := by
    simpa [prefixWord, tailWord_7962948, baseEnd_7962948] using wordTrace_append hprefix tailTrace_7962948
  have hstable : (prefixWord ++ tailWord_7962948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7962948).length < 2 ^ (prefixWord ++ tailWord_7962948).sum := by decide
  have hdescent : baseEnd_7962948 < baseStart_7962948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7962948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963044 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7963044 : Nat := 118140960795 + 7963044 * 2 ^ 59
def prefixEnd_7963044 : Nat := 4983230072969 + 3 ^ 40 * 7963044 * 2
def baseEnd_7963044 : Nat := 4088869044901247787428633

theorem tailTrace_7963044 : CollatzResearch.WordTrace tailWord_7963044 prefixEnd_7963044 4088869044901247787428633 := by
  unfold tailWord_7963044
  simp only [CollatzResearch.WordTrace]
  refine ⟨145218037481629521243400093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193624049975506028324533457 145218037481629521243400093)
  ·
    refine ⟨54456764055611070466275035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145218037481629521243400093 54456764055611070466275035)
    ·
      refine ⟨81685146083416605699412553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54456764055611070466275035 81685146083416605699412553)
      ·
        refine ⟨61263859562562454274559415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81685146083416605699412553 61263859562562454274559415)
        ·
          refine ⟨91895789343843681411839123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61263859562562454274559415 91895789343843681411839123)
          ·
            refine ⟨137843684015765522117758685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91895789343843681411839123 137843684015765522117758685)
            ·
              refine ⟨51691381505912070794159507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137843684015765522117758685 51691381505912070794159507)
              ·
                refine ⟨77537072258868106191239261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51691381505912070794159507 77537072258868106191239261)
                ·
                  refine ⟨29076402097075539821714723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77537072258868106191239261 29076402097075539821714723)
                  ·
                    refine ⟨43614603145613309732572085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29076402097075539821714723 43614603145613309732572085)
                    ·
                      refine ⟨4088869044901247787428633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43614603145613309732572085 4088869044901247787428633)
                      ·
                        rfl

theorem cell23_7963044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7963044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963044 prefixEnd_7963044 := by exact prefixLift 7963044
  have htrace : WordTrace (prefixWord ++ tailWord_7963044) baseStart_7963044 baseEnd_7963044 := by
    simpa [prefixWord, tailWord_7963044, baseEnd_7963044] using wordTrace_append hprefix tailTrace_7963044
  have hstable : (prefixWord ++ tailWord_7963044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963044).length < 2 ^ (prefixWord ++ tailWord_7963044).sum := by decide
  have hdescent : baseEnd_7963044 < baseStart_7963044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963058 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_7963058 : Nat := 118140960795 + 7963058 * 2 ^ 59
def prefixEnd_7963058 : Nat := 4983230072969 + 3 ^ 40 * 7963058 * 2
def baseEnd_7963058 : Nat := 4088876233630410732653569

theorem tailTrace_7963058 : CollatzResearch.WordTrace tailWord_7963058 prefixEnd_7963058 4088876233630410732653569 := by
  unfold tailWord_7963058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72609146396302080719452457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193624390390138881918539885 72609146396302080719452457)
  ·
    refine ⟨54456859797226560539589343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72609146396302080719452457 54456859797226560539589343)
    ·
      refine ⟨81685289695839840809384015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54456859797226560539589343 81685289695839840809384015)
      ·
        refine ⟨122527934543759761214076023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81685289695839840809384015 122527934543759761214076023)
        ·
          refine ⟨183791901815639641821114035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122527934543759761214076023 183791901815639641821114035)
          ·
            refine ⟨275687852723459462731671053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183791901815639641821114035 275687852723459462731671053)
            ·
              refine ⟨103382944771297298524376645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275687852723459462731671053 103382944771297298524376645)
              ·
                refine ⟨19384302144618243473320621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103382944771297298524376645 19384302144618243473320621)
                ·
                  refine ⟨7269113304231841302495233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19384302144618243473320621 7269113304231841302495233)
                  ·
                    refine ⟨5451834978173880976871425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269113304231841302495233 5451834978173880976871425)
                    ·
                      refine ⟨4088876233630410732653569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451834978173880976871425 4088876233630410732653569)
                      ·
                        rfl

theorem cell23_7963058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_7963058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963058 prefixEnd_7963058 := by exact prefixLift 7963058
  have htrace : WordTrace (prefixWord ++ tailWord_7963058) baseStart_7963058 baseEnd_7963058 := by
    simpa [prefixWord, tailWord_7963058, baseEnd_7963058] using wordTrace_append hprefix tailTrace_7963058
  have hstable : (prefixWord ++ tailWord_7963058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963058).length < 2 ^ (prefixWord ++ tailWord_7963058).sum := by decide
  have hdescent : baseEnd_7963058 < baseStart_7963058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963092 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7963092 : Nat := 118140960795 + 7963092 * 2 ^ 59
def prefixEnd_7963092 : Nat := 4983230072969 + 3 ^ 40 * 7963092 * 2
def baseEnd_7963092 : Nat := 4088893691972663599628413

theorem tailTrace_7963092 : CollatzResearch.WordTrace tailWord_7963092 prefixEnd_7963092 4088893691972663599628413 := by
  unfold tailWord_7963092
  simp only [CollatzResearch.WordTrace]
  refine ⟨145218912833542573342273765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193625217111390097789698353 145218912833542573342273765)
  ·
    refine ⟨27228546156289232501676331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145218912833542573342273765 27228546156289232501676331)
    ·
      refine ⟨40842819234433848752514497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27228546156289232501676331 40842819234433848752514497)
      ·
        refine ⟨30632114425825386564385873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40842819234433848752514497 30632114425825386564385873)
        ·
          refine ⟨22974085819369039923289405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30632114425825386564385873 22974085819369039923289405)
          ·
            refine ⟨8615282182263389971233527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22974085819369039923289405 8615282182263389971233527)
            ·
              refine ⟨12922923273395084956850291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615282182263389971233527 12922923273395084956850291)
              ·
                refine ⟨19384384910092627435275437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12922923273395084956850291 19384384910092627435275437)
                ·
                  refine ⟨7269144341284735288228289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19384384910092627435275437 7269144341284735288228289)
                  ·
                    refine ⟨5451858255963551466171217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269144341284735288228289 5451858255963551466171217)
                    ·
                      refine ⟨4088893691972663599628413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451858255963551466171217 4088893691972663599628413)
                      ·
                        rfl

theorem cell23_7963092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7963092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963092 prefixEnd_7963092 := by exact prefixLift 7963092
  have htrace : WordTrace (prefixWord ++ tailWord_7963092) baseStart_7963092 baseEnd_7963092 := by
    simpa [prefixWord, tailWord_7963092, baseEnd_7963092] using wordTrace_append hprefix tailTrace_7963092
  have hstable : (prefixWord ++ tailWord_7963092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963092).length < 2 ^ (prefixWord ++ tailWord_7963092).sum := by decide
  have hdescent : baseEnd_7963092 < baseStart_7963092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963125 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7963125 : Nat := 118140960795 + 7963125 * 2 ^ 59
def prefixEnd_7963125 : Nat := 4983230072969 + 3 ^ 40 * 7963125 * 2
def baseEnd_7963125 : Nat := 4088910636834261970515761

theorem tailTrace_7963125 : CollatzResearch.WordTrace tailWord_7963125 prefixEnd_7963125 4088910636834261970515761 := by
  unfold tailWord_7963125
  simp only [CollatzResearch.WordTrace]
  refine ⟨290439029275965593320498829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193626019517310395546999219 290439029275965593320498829)
  ·
    refine ⟨108914635978487097495187061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290439029275965593320498829 108914635978487097495187061)
    ·
      refine ⟨10210747122983165390173787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108914635978487097495187061 10210747122983165390173787)
      ·
        refine ⟨15316120684474748085260681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210747122983165390173787 15316120684474748085260681)
        ·
          refine ⟨11487090513356061063945511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15316120684474748085260681 11487090513356061063945511)
          ·
            refine ⟨17230635770034091595918267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487090513356061063945511 17230635770034091595918267)
            ·
              refine ⟨25845953655051137393877401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17230635770034091595918267 25845953655051137393877401)
              ·
                refine ⟨19384465241288353045408051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25845953655051137393877401 19384465241288353045408051)
                ·
                  refine ⟨29076697861932529568112077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19384465241288353045408051 29076697861932529568112077)
                  ·
                    refine ⟨10903761698224698588042029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29076697861932529568112077 10903761698224698588042029)
                    ·
                      refine ⟨4088910636834261970515761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10903761698224698588042029 4088910636834261970515761)
                      ·
                        rfl

theorem cell23_7963125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7963125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963125 prefixEnd_7963125 := by exact prefixLift 7963125
  have htrace : WordTrace (prefixWord ++ tailWord_7963125) baseStart_7963125 baseEnd_7963125 := by
    simpa [prefixWord, tailWord_7963125, baseEnd_7963125] using wordTrace_append hprefix tailTrace_7963125
  have hstable : (prefixWord ++ tailWord_7963125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963125).length < 2 ^ (prefixWord ++ tailWord_7963125).sum := by decide
  have hdescent : baseEnd_7963125 < baseStart_7963125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963135 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 1, 3, 2]
def baseStart_7963135 : Nat := 118140960795 + 7963135 * 2 ^ 59
def prefixEnd_7963135 : Nat := 4983230072969 + 3 ^ 40 * 7963135 * 2
def baseEnd_7963135 : Nat := 4088915771640806931390715

theorem tailTrace_7963135 : CollatzResearch.WordTrace tailWord_7963135 prefixEnd_7963135 4088915771640806931390715 := by
  unfold tailWord_7963135
  simp only [CollatzResearch.WordTrace]
  refine ⟨290439394005929365028362859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193626262670619576685575239 290439394005929365028362859)
  ·
    refine ⟨435659091008894047542544289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290439394005929365028362859 435659091008894047542544289)
    ·
      refine ⟨326744318256670535656908217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435659091008894047542544289 326744318256670535656908217)
      ·
        refine ⟨245058238692502901742681163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326744318256670535656908217 245058238692502901742681163)
        ·
          refine ⟨367587358038754352614021745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245058238692502901742681163 367587358038754352614021745)
          ·
            refine ⟨275690518529065764460516309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367587358038754352614021745 275690518529065764460516309)
            ·
              refine ⟨6461496528024978854543351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 275690518529065764460516309 6461496528024978854543351)
              ·
                refine ⟨9692244792037468281815027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461496528024978854543351 9692244792037468281815027)
                ·
                  refine ⟨14538367188056202422722541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9692244792037468281815027 14538367188056202422722541)
                  ·
                    refine ⟨5451887695521075908520953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14538367188056202422722541 5451887695521075908520953)
                    ·
                      refine ⟨4088915771640806931390715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451887695521075908520953 4088915771640806931390715)
                      ·
                        rfl

theorem cell23_7963135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_7963135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963135 prefixEnd_7963135 := by exact prefixLift 7963135
  have htrace : WordTrace (prefixWord ++ tailWord_7963135) baseStart_7963135 baseEnd_7963135 := by
    simpa [prefixWord, tailWord_7963135, baseEnd_7963135] using wordTrace_append hprefix tailTrace_7963135
  have hstable : (prefixWord ++ tailWord_7963135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963135).length < 2 ^ (prefixWord ++ tailWord_7963135).sum := by decide
  have hdescent : baseEnd_7963135 < baseStart_7963135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963144 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_7963144 : Nat := 118140960795 + 7963144 * 2 ^ 59
def prefixEnd_7963144 : Nat := 4983230072969 + 3 ^ 40 * 7963144 * 2
def baseEnd_7963144 : Nat := 4088920392966697396178173

theorem tailTrace_7963144 : CollatzResearch.WordTrace tailWord_7963144 prefixEnd_7963144 4088920392966697396178173 := by
  unfold tailWord_7963144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145219861131448379782720243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193626481508597839710293657 145219861131448379782720243)
  ·
    refine ⟨217829791697172569674080365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145219861131448379782720243 217829791697172569674080365)
    ·
      refine ⟨81686171886439713627780137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217829791697172569674080365 81686171886439713627780137)
      ·
        refine ⟨61264628914829785220835103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81686171886439713627780137 61264628914829785220835103)
        ·
          refine ⟨91896943372244677831252655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61264628914829785220835103 91896943372244677831252655)
          ·
            refine ⟨137845415058367016746878983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91896943372244677831252655 137845415058367016746878983)
            ·
              refine ⟨206768122587550525120318475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137845415058367016746878983 206768122587550525120318475)
              ·
                refine ⟨310152183881325787680477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206768122587550525120318475 310152183881325787680477713)
                ·
                  refine ⟨232614137910994340760358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310152183881325787680477713 232614137910994340760358285)
                  ·
                    refine ⟨87230301716622877785134357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232614137910994340760358285 87230301716622877785134357)
                    ·
                      refine ⟨4088920392966697396178173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87230301716622877785134357 4088920392966697396178173)
                      ·
                        rfl

theorem cell23_7963144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_7963144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963144 prefixEnd_7963144 := by exact prefixLift 7963144
  have htrace : WordTrace (prefixWord ++ tailWord_7963144) baseStart_7963144 baseEnd_7963144 := by
    simpa [prefixWord, tailWord_7963144, baseEnd_7963144] using wordTrace_append hprefix tailTrace_7963144
  have hstable : (prefixWord ++ tailWord_7963144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963144).length < 2 ^ (prefixWord ++ tailWord_7963144).sum := by decide
  have hdescent : baseEnd_7963144 < baseStart_7963144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963165 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7963165 : Nat := 118140960795 + 7963165 * 2 ^ 59
def prefixEnd_7963165 : Nat := 4983230072969 + 3 ^ 40 * 7963165 * 2
def baseEnd_7963165 : Nat := 4088931176060441814015577

theorem tailTrace_7963165 : CollatzResearch.WordTrace tailWord_7963165 prefixEnd_7963165 4088931176060441814015577 := by
  unfold tailWord_7963165
  simp only [CollatzResearch.WordTrace]
  refine ⟨290440488195820680151954949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193626992130547120101303299 290440488195820680151954949)
  ·
    refine ⟨54457591536716377528491553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290440488195820680151954949 54457591536716377528491553)
    ·
      refine ⟨40843193652537283146368665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54457591536716377528491553 40843193652537283146368665)
      ·
        refine ⟨30632395239402962359776499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40843193652537283146368665 30632395239402962359776499)
        ·
          refine ⟨45948592859104443539664749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30632395239402962359776499 45948592859104443539664749)
          ·
            refine ⟨17230722322164166327374281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45948592859104443539664749 17230722322164166327374281)
            ·
              refine ⟨12923041741623124745530711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17230722322164166327374281 12923041741623124745530711)
              ·
                refine ⟨19384562612434687118296067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12923041741623124745530711 19384562612434687118296067)
                ·
                  refine ⟨29076843918652030677444101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19384562612434687118296067 29076843918652030677444101)
                  ·
                    refine ⟨5451908234747255752020769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29076843918652030677444101 5451908234747255752020769)
                    ·
                      refine ⟨4088931176060441814015577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5451908234747255752020769 4088931176060441814015577)
                      ·
                        rfl

theorem cell23_7963165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7963165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963165 prefixEnd_7963165 := by exact prefixLift 7963165
  have htrace : WordTrace (prefixWord ++ tailWord_7963165) baseStart_7963165 baseEnd_7963165 := by
    simpa [prefixWord, tailWord_7963165, baseEnd_7963165] using wordTrace_append hprefix tailTrace_7963165
  have hstable : (prefixWord ++ tailWord_7963165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963165).length < 2 ^ (prefixWord ++ tailWord_7963165).sum := by decide
  have hdescent : baseEnd_7963165 < baseStart_7963165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963171 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 7]
def baseStart_7963171 : Nat := 118140960795 + 7963171 * 2 ^ 59
def prefixEnd_7963171 : Nat := 4983230072969 + 3 ^ 40 * 7963171 * 2
def baseEnd_7963171 : Nat := 454326028549374310060061

theorem tailTrace_7963171 : CollatzResearch.WordTrace tailWord_7963171 prefixEnd_7963171 454326028549374310060061 := by
  unfold tailWord_7963171
  simp only [CollatzResearch.WordTrace]
  refine ⟨290440707033798943176673367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193627138022532628784448911 290440707033798943176673367)
  ·
    refine ⟨435661060550698414765010051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290440707033798943176673367 435661060550698414765010051)
    ·
      refine ⟨653491590826047622147515077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435661060550698414765010051 653491590826047622147515077)
      ·
        refine ⟨122529673279883929152659077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 653491590826047622147515077 122529673279883929152659077)
        ·
          refine ⟨22974313739978236716123577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122529673279883929152659077 22974313739978236716123577)
          ·
            refine ⟨17230735304983677537092683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22974313739978236716123577 17230735304983677537092683)
            ·
              refine ⟨25846102957475516305639025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17230735304983677537092683 25846102957475516305639025)
              ·
                refine ⟨19384577218106637229229269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25846102957475516305639025 19384577218106637229229269)
                ·
                  refine ⟨454326028549374310060061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19384577218106637229229269 454326028549374310060061)
                  ·
                    rfl

theorem cell23_7963171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 7].length) (baseStart_7963171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963171 prefixEnd_7963171 := by exact prefixLift 7963171
  have htrace : WordTrace (prefixWord ++ tailWord_7963171) baseStart_7963171 baseEnd_7963171 := by
    simpa [prefixWord, tailWord_7963171, baseEnd_7963171] using wordTrace_append hprefix tailTrace_7963171
  have hstable : (prefixWord ++ tailWord_7963171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963171).length < 2 ^ (prefixWord ++ tailWord_7963171).sum := by decide
  have hdescent : baseEnd_7963171 < baseStart_7963171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963221 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7963221 : Nat := 118140960795 + 7963221 * 2 ^ 59
def prefixEnd_7963221 : Nat := 4983230072969 + 3 ^ 40 * 7963221 * 2
def baseEnd_7963221 : Nat := 4088959930977093594915319

theorem tailTrace_7963221 : CollatzResearch.WordTrace tailWord_7963221 prefixEnd_7963221 4088959930977093594915319 := by
  unfold tailWord_7963221
  simp only [CollatzResearch.WordTrace]
  refine ⟨290442530683617801715993517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193628353789078534477329011 290442530683617801715993517)
  ·
    refine ⟨108915949006356675643497569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290442530683617801715993517 108915949006356675643497569)
    ·
      refine ⟨81686961754767506732623177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108915949006356675643497569 81686961754767506732623177)
      ·
        refine ⟨61265221316075630049467383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81686961754767506732623177 61265221316075630049467383)
        ·
          refine ⟨91897831974113445074201075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61265221316075630049467383 91897831974113445074201075)
          ·
            refine ⟨137846747961170167611301613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91897831974113445074201075 137846747961170167611301613)
            ·
              refine ⟨51692530485438812854238105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137846747961170167611301613 51692530485438812854238105)
              ·
                refine ⟨38769397864079109640678579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51692530485438812854238105 38769397864079109640678579)
                ·
                  refine ⟨58154096796118664461017869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38769397864079109640678579 58154096796118664461017869)
                  ·
                    refine ⟨21807786298544499172881701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58154096796118664461017869 21807786298544499172881701)
                    ·
                      refine ⟨4088959930977093594915319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21807786298544499172881701 4088959930977093594915319)
                      ·
                        rfl

theorem cell23_7963221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7963221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963221 prefixEnd_7963221 := by exact prefixLift 7963221
  have htrace : WordTrace (prefixWord ++ tailWord_7963221) baseStart_7963221 baseEnd_7963221 := by
    simpa [prefixWord, tailWord_7963221, baseEnd_7963221] using wordTrace_append hprefix tailTrace_7963221
  have hstable : (prefixWord ++ tailWord_7963221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963221).length < 2 ^ (prefixWord ++ tailWord_7963221).sum := by decide
  have hdescent : baseEnd_7963221 < baseStart_7963221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963278 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_7963278 : Nat := 118140960795 + 7963278 * 2 ^ 59
def prefixEnd_7963278 : Nat := 4983230072969 + 3 ^ 40 * 7963278 * 2
def baseEnd_7963278 : Nat := 454332133263822207989173

theorem tailTrace_7963278 : CollatzResearch.WordTrace tailWord_7963278 prefixEnd_7963278 454332133263822207989173 := by
  unfold tailWord_7963278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36305576205551412556352311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193629739762940866967212325 36305576205551412556352311)
  ·
    refine ⟨54458364308327118834528467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36305576205551412556352311 54458364308327118834528467)
    ·
      refine ⟨81687546462490678251792701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54458364308327118834528467 81687546462490678251792701)
      ·
        refine ⟨30632829923434004344422263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81687546462490678251792701 30632829923434004344422263)
        ·
          refine ⟨45949244885151006516633395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30632829923434004344422263 45949244885151006516633395)
          ·
            refine ⟨68923867327726509774950093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45949244885151006516633395 68923867327726509774950093)
            ·
              refine ⟨25846450247897441165606285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68923867327726509774950093 25846450247897441165606285)
              ·
                refine ⟨9692418842961540437102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25846450247897441165606285 9692418842961540437102357)
                ·
                  refine ⟨454332133263822207989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9692418842961540437102357 454332133263822207989173)
                  ·
                    rfl

theorem cell23_7963278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_7963278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963278 prefixEnd_7963278 := by exact prefixLift 7963278
  have htrace : WordTrace (prefixWord ++ tailWord_7963278) baseStart_7963278 baseEnd_7963278 := by
    simpa [prefixWord, tailWord_7963278, baseEnd_7963278] using wordTrace_append hprefix tailTrace_7963278
  have hstable : (prefixWord ++ tailWord_7963278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963278).length < 2 ^ (prefixWord ++ tailWord_7963278).sum := by decide
  have hdescent : baseEnd_7963278 < baseStart_7963278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963315 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 2, 3, 2]
def baseStart_7963315 : Nat := 118140960795 + 7963315 * 2 ^ 59
def prefixEnd_7963315 : Nat := 4983230072969 + 3 ^ 40 * 7963315 * 2
def baseEnd_7963315 : Nat := 4089008198158616227139887

theorem tailTrace_7963315 : CollatzResearch.WordTrace tailWord_7963315 prefixEnd_7963315 4089008198158616227139887 := by
  unfold tailWord_7963315
  simp only [CollatzResearch.WordTrace]
  refine ⟨290445959145277255769915399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193630639430184837179943599 290445959145277255769915399)
  ·
    refine ⟨435668938717915883654873099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290445959145277255769915399 435668938717915883654873099)
    ·
      refine ⟨653503408076873825482309649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435668938717915883654873099 653503408076873825482309649)
      ·
        refine ⟨490127556057655369111732237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653503408076873825482309649 490127556057655369111732237)
        ·
          refine ⟨183797833521620763416899589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490127556057655369111732237 183797833521620763416899589)
          ·
            refine ⟨34462093785303893140668673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183797833521620763416899589 34462093785303893140668673)
            ·
              refine ⟨25846570338977919855501505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34462093785303893140668673 25846570338977919855501505)
              ·
                refine ⟨19384927754233439891626129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25846570338977919855501505 19384927754233439891626129)
                ·
                  refine ⟨14538695815675079918719597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19384927754233439891626129 14538695815675079918719597)
                  ·
                    refine ⟨5452010930878154969519849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14538695815675079918719597 5452010930878154969519849)
                    ·
                      refine ⟨4089008198158616227139887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452010930878154969519849 4089008198158616227139887)
                      ·
                        rfl

theorem cell23_7963315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3, 2].length) (baseStart_7963315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963315 prefixEnd_7963315 := by exact prefixLift 7963315
  have htrace : WordTrace (prefixWord ++ tailWord_7963315) baseStart_7963315 baseEnd_7963315 := by
    simpa [prefixWord, tailWord_7963315, baseEnd_7963315] using wordTrace_append hprefix tailTrace_7963315
  have hstable : (prefixWord ++ tailWord_7963315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963315).length < 2 ^ (prefixWord ++ tailWord_7963315).sum := by decide
  have hdescent : baseEnd_7963315 < baseStart_7963315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963321 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_7963321 : Nat := 118140960795 + 7963321 * 2 ^ 59
def prefixEnd_7963321 : Nat := 4983230072969 + 3 ^ 40 * 7963321 * 2
def baseEnd_7963321 : Nat := 1363003759680847734554953

theorem tailTrace_7963321 : CollatzResearch.WordTrace tailWord_7963321 prefixEnd_7963321 1363003759680847734554953 := by
  unfold tailWord_7963321
  simp only [CollatzResearch.WordTrace]
  refine ⟨290446177983255518794633817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193630785322170345863089211 290446177983255518794633817)
  ·
    refine ⟨217834633487441639095975363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290446177983255518794633817 217834633487441639095975363)
    ·
      refine ⟨326751950231162458643963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217834633487441639095975363 326751950231162458643963045)
      ·
        refine ⟨61265990668342960995743071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326751950231162458643963045 61265990668342960995743071)
        ·
          refine ⟨91898986002514441493614607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61265990668342960995743071 91898986002514441493614607)
          ·
            refine ⟨137848479003771662240421911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91898986002514441493614607 137848479003771662240421911)
            ·
              refine ⟨206772718505657493360632867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137848479003771662240421911 206772718505657493360632867)
              ·
                refine ⟨310159077758486240040949301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206772718505657493360632867 310159077758486240040949301)
                ·
                  refine ⟨29077413539858085003838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310159077758486240040949301 29077413539858085003838997)
                  ·
                    refine ⟨1363003759680847734554953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29077413539858085003838997 1363003759680847734554953)
                    ·
                      rfl

theorem cell23_7963321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_7963321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963321 prefixEnd_7963321 := by exact prefixLift 7963321
  have htrace : WordTrace (prefixWord ++ tailWord_7963321) baseStart_7963321 baseEnd_7963321 := by
    simpa [prefixWord, tailWord_7963321, baseEnd_7963321] using wordTrace_append hprefix tailTrace_7963321
  have hstable : (prefixWord ++ tailWord_7963321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963321).length < 2 ^ (prefixWord ++ tailWord_7963321).sum := by decide
  have hdescent : baseEnd_7963321 < baseStart_7963321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963322 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_7963322 : Nat := 118140960795 + 7963322 * 2 ^ 59
def prefixEnd_7963322 : Nat := 4983230072969 + 3 ^ 40 * 7963322 * 2
def baseEnd_7963322 : Nat := 4089011792523197699752355

theorem tailTrace_7963322 : CollatzResearch.WordTrace tailWord_7963322 prefixEnd_7963322 4089011792523197699752355 := by
  unfold tailWord_7963322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72611553614062973991355055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193630809637501263976946813 72611553614062973991355055)
  ·
    refine ⟨108917330421094460987032583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72611553614062973991355055 108917330421094460987032583)
    ·
      refine ⟨163375995631641691480548875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108917330421094460987032583 163375995631641691480548875)
      ·
        refine ⟨245063993447462537220823313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163375995631641691480548875 245063993447462537220823313)
        ·
          refine ⟨183797995085596902915617485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245063993447462537220823313 183797995085596902915617485)
          ·
            refine ⟨68924248157098838593356557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183797995085596902915617485 68924248157098838593356557)
            ·
              refine ⟨25846593058912064472508709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68924248157098838593356557 25846593058912064472508709)
              ·
                refine ⟨4846236198546012088595383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25846593058912064472508709 4846236198546012088595383)
                ·
                  refine ⟨7269354297819018132893075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846236198546012088595383 7269354297819018132893075)
                  ·
                    refine ⟨10904031446728527199339613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269354297819018132893075 10904031446728527199339613)
                    ·
                      refine ⟨4089011792523197699752355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904031446728527199339613 4089011792523197699752355)
                      ·
                        rfl

theorem cell23_7963322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_7963322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963322 prefixEnd_7963322 := by exact prefixLift 7963322
  have htrace : WordTrace (prefixWord ++ tailWord_7963322) baseStart_7963322 baseEnd_7963322 := by
    simpa [prefixWord, tailWord_7963322, baseEnd_7963322] using wordTrace_append hprefix tailTrace_7963322
  have hstable : (prefixWord ++ tailWord_7963322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963322).length < 2 ^ (prefixWord ++ tailWord_7963322).sum := by decide
  have hdescent : baseEnd_7963322 < baseStart_7963322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963328 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_7963328 : Nat := 118140960795 + 7963328 * 2 ^ 59
def prefixEnd_7963328 : Nat := 4983230072969 + 3 ^ 40 * 7963328 * 2
def baseEnd_7963328 : Nat := 4089014873407124676277327

theorem tailTrace_7963328 : CollatzResearch.WordTrace tailWord_7963328 prefixEnd_7963328 4089014873407124676277327 := by
  unfold tailWord_7963328
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223216647115079495069319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193630955529486772660092425 145223216647115079495069319)
  ·
    refine ⟨217834824970672619242603979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145223216647115079495069319 217834824970672619242603979)
    ·
      refine ⟨326752237456008928863905969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217834824970672619242603979 326752237456008928863905969)
      ·
        refine ⟨245064178092006696647929477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326752237456008928863905969 245064178092006696647929477)
        ·
          refine ⟨45949533392251255621486777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245064178092006696647929477 45949533392251255621486777)
          ·
            refine ⟨34462150044188441716115083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45949533392251255621486777 34462150044188441716115083)
            ·
              refine ⟨51693225066282662574172625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34462150044188441716115083 51693225066282662574172625)
              ·
                refine ⟨38769918799711996930629469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51693225066282662574172625 38769918799711996930629469)
                ·
                  refine ⟨14538719549891998848986051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38769918799711996930629469 14538719549891998848986051)
                  ·
                    refine ⟨21808079324837998273479077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14538719549891998848986051 21808079324837998273479077)
                    ·
                      refine ⟨4089014873407124676277327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21808079324837998273479077 4089014873407124676277327)
                      ·
                        rfl

theorem cell23_7963328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_7963328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963328 prefixEnd_7963328 := by exact prefixLift 7963328
  have htrace : WordTrace (prefixWord ++ tailWord_7963328) baseStart_7963328 baseEnd_7963328 := by
    simpa [prefixWord, tailWord_7963328, baseEnd_7963328] using wordTrace_append hprefix tailTrace_7963328
  have hstable : (prefixWord ++ tailWord_7963328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963328).length < 2 ^ (prefixWord ++ tailWord_7963328).sum := by decide
  have hdescent : baseEnd_7963328 < baseStart_7963328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963338 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_7963338 : Nat := 118140960795 + 7963338 * 2 ^ 59
def prefixEnd_7963338 : Nat := 4983230072969 + 3 ^ 40 * 7963338 * 2
def baseEnd_7963338 : Nat := 1363006669404556545717427

theorem tailTrace_7963338 : CollatzResearch.WordTrace tailWord_7963338 prefixEnd_7963338 1363006669404556545717427 := by
  unfold tailWord_7963338
  simp only [CollatzResearch.WordTrace]
  refine ⟨72611699506048482674500667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193631198682795953798668445 72611699506048482674500667)
  ·
    refine ⟨108917549259072724011751001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72611699506048482674500667 108917549259072724011751001)
    ·
      refine ⟨81688161944304543008813251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108917549259072724011751001 81688161944304543008813251)
      ·
        refine ⟨122532242916456814513219877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81688161944304543008813251 122532242916456814513219877)
        ·
          refine ⟨22974795546835652721228727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122532242916456814513219877 22974795546835652721228727)
          ·
            refine ⟨34462193320253479081843091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22974795546835652721228727 34462193320253479081843091)
            ·
              refine ⟨51693289980380218622764637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34462193320253479081843091 51693289980380218622764637)
              ·
                refine ⟨19384983742642581983536739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51693289980380218622764637 19384983742642581983536739)
                ·
                  refine ⟨29077475613963872975305109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19384983742642581983536739 29077475613963872975305109)
                  ·
                    refine ⟨1363006669404556545717427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29077475613963872975305109 1363006669404556545717427)
                    ·
                      rfl

theorem cell23_7963338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_7963338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963338 prefixEnd_7963338 := by exact prefixLift 7963338
  have htrace : WordTrace (prefixWord ++ tailWord_7963338) baseStart_7963338 baseEnd_7963338 := by
    simpa [prefixWord, tailWord_7963338, baseEnd_7963338] using wordTrace_append hprefix tailTrace_7963338
  have hstable : (prefixWord ++ tailWord_7963338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963338).length < 2 ^ (prefixWord ++ tailWord_7963338).sum := by decide
  have hdescent : baseEnd_7963338 < baseStart_7963338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963356 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7963356 : Nat := 118140960795 + 7963356 * 2 ^ 59
def prefixEnd_7963356 : Nat := 4983230072969 + 3 ^ 40 * 7963356 * 2
def baseEnd_7963356 : Nat := 4089029250865450566727199

theorem tailTrace_7963356 : CollatzResearch.WordTrace tailWord_7963356 prefixEnd_7963356 4089029250865450566727199 := by
  unfold tailWord_7963356
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223727269064359886078961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193631636358752479848105281 145223727269064359886078961)
  ·
    refine ⟨108917795451798269914559221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145223727269064359886078961 108917795451798269914559221)
    ·
      refine ⟨10211043323606087804489927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108917795451798269914559221 10211043323606087804489927)
      ·
        refine ⟨15316564985409131706734891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10211043323606087804489927 15316564985409131706734891)
        ·
          refine ⟨22974847478113697560102337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316564985409131706734891 22974847478113697560102337)
          ·
            refine ⟨17231135608585273170076753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22974847478113697560102337 17231135608585273170076753)
            ·
              refine ⟨12923351706438954877557565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17231135608585273170076753 12923351706438954877557565)
              ·
                refine ⟨4846256889914608079084087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12923351706438954877557565 4846256889914608079084087)
                ·
                  refine ⟨7269385334871912118626131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846256889914608079084087 7269385334871912118626131)
                  ·
                    refine ⟨10904078002307868177939197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269385334871912118626131 10904078002307868177939197)
                    ·
                      refine ⟨4089029250865450566727199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904078002307868177939197 4089029250865450566727199)
                      ·
                        rfl

theorem cell23_7963356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7963356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963356 prefixEnd_7963356 := by exact prefixLift 7963356
  have htrace : WordTrace (prefixWord ++ tailWord_7963356) baseStart_7963356 baseEnd_7963356 := by
    simpa [prefixWord, tailWord_7963356, baseEnd_7963356] using wordTrace_append hprefix tailTrace_7963356
  have hstable : (prefixWord ++ tailWord_7963356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963356).length < 2 ^ (prefixWord ++ tailWord_7963356).sum := by decide
  have hdescent : baseEnd_7963356 < baseStart_7963356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963368 : List Nat := [2, 1, 4, 1, 4, 1, 10]
def baseStart_7963368 : Nat := 118140960795 + 7963368 * 2 ^ 59
def prefixEnd_7963368 : Nat := 4983230072969 + 3 ^ 40 * 7963368 * 2
def baseEnd_7963368 : Nat := 50481918674485240984903

theorem tailTrace_7963368 : CollatzResearch.WordTrace tailWord_7963368 prefixEnd_7963368 50481918674485240984903 := by
  unfold tailWord_7963368
  simp only [CollatzResearch.WordTrace]
  refine ⟨145223946107042622910797379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193631928142723497214396505 145223946107042622910797379)
  ·
    refine ⟨217835919160563934366196069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145223946107042622910797379 217835919160563934366196069)
    ·
      refine ⟨40844234842605737693661763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217835919160563934366196069 40844234842605737693661763)
      ·
        refine ⟨61266352263908606540492645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40844234842605737693661763 61266352263908606540492645)
        ·
          refine ⟨11487441049482863726342371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61266352263908606540492645 11487441049482863726342371)
          ·
            refine ⟨17231161574224295589513557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487441049482863726342371 17231161574224295589513557)
            ·
              refine ⟨50481918674485240984903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17231161574224295589513557 50481918674485240984903)
              ·
                rfl

theorem cell23_7963368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 10].length) (baseStart_7963368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963368 prefixEnd_7963368 := by exact prefixLift 7963368
  have htrace : WordTrace (prefixWord ++ tailWord_7963368) baseStart_7963368 baseEnd_7963368 := by
    simpa [prefixWord, tailWord_7963368, baseEnd_7963368] using wordTrace_append hprefix tailTrace_7963368
  have hstable : (prefixWord ++ tailWord_7963368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963368).length < 2 ^ (prefixWord ++ tailWord_7963368).sum := by decide
  have hdescent : baseEnd_7963368 < baseStart_7963368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963371 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_7963371 : Nat := 118140960795 + 7963371 * 2 ^ 59
def prefixEnd_7963371 : Nat := 4983230072969 + 3 ^ 40 * 7963371 * 2
def baseEnd_7963371 : Nat := 4089036953075268008039629

theorem tailTrace_7963371 : CollatzResearch.WordTrace tailWord_7963371 prefixEnd_7963371 4089036953075268008039629 := by
  unfold tailWord_7963371
  simp only [CollatzResearch.WordTrace]
  refine ⟨290448001633074377333953967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193632001088716251555969311 290448001633074377333953967)
  ·
    refine ⟨435672002449611566000930951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290448001633074377333953967 435672002449611566000930951)
    ·
      refine ⟨653508003674417349001396427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435672002449611566000930951 653508003674417349001396427)
      ·
        refine ⟨980262005511626023502094641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653508003674417349001396427 980262005511626023502094641)
        ·
          refine ⟨735196504133719517626570981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980262005511626023502094641 735196504133719517626570981)
          ·
            refine ⟨137849344525072409554982059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 735196504133719517626570981 137849344525072409554982059)
            ·
              refine ⟨206774016787608614332473089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137849344525072409554982059 206774016787608614332473089)
              ·
                refine ⟨155080512590706460749354817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206774016787608614332473089 155080512590706460749354817)
                ·
                  refine ⟨116310384443029845562016113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155080512590706460749354817 116310384443029845562016113)
                  ·
                    refine ⟨87232788332272384171512085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116310384443029845562016113 87232788332272384171512085)
                    ·
                      refine ⟨4089036953075268008039629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87232788332272384171512085 4089036953075268008039629)
                      ·
                        rfl

theorem cell23_7963371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_7963371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963371 prefixEnd_7963371 := by exact prefixLift 7963371
  have htrace : WordTrace (prefixWord ++ tailWord_7963371) baseStart_7963371 baseEnd_7963371 := by
    simpa [prefixWord, tailWord_7963371, baseEnd_7963371] using wordTrace_append hprefix tailTrace_7963371
  have hstable : (prefixWord ++ tailWord_7963371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963371).length < 2 ^ (prefixWord ++ tailWord_7963371).sum := by decide
  have hdescent : baseEnd_7963371 < baseStart_7963371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963446 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7963446 : Nat := 118140960795 + 7963446 * 2 ^ 59
def prefixEnd_7963446 : Nat := 4983230072969 + 3 ^ 40 * 7963446 * 2
def baseEnd_7963446 : Nat := 4089075464124355214601785

theorem tailTrace_7963446 : CollatzResearch.WordTrace tailWord_7963446 prefixEnd_7963446 4089075464124355214601785 := by
  unfold tailWord_7963446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153171069237666571433387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193633824738535110095289461 18153171069237666571433387)
  ·
    refine ⟨27229756603856499857150081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18153171069237666571433387 27229756603856499857150081)
    ·
      refine ⟨20422317452892374892862561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27229756603856499857150081 20422317452892374892862561)
      ·
        refine ⟨15316738089669281169646921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422317452892374892862561 15316738089669281169646921)
        ·
          refine ⟨11487553567251960877235191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15316738089669281169646921 11487553567251960877235191)
          ·
            refine ⟨17231330350877941315852787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487553567251960877235191 17231330350877941315852787)
            ·
              refine ⟨25846995526316911973779181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231330350877941315852787 25846995526316911973779181)
              ·
                refine ⟨9692623322368841990167193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25846995526316911973779181 9692623322368841990167193)
                ·
                  refine ⟨7269467491776631492625395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692623322368841990167193 7269467491776631492625395)
                  ·
                    refine ⟨10904201237664947238938093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269467491776631492625395 10904201237664947238938093)
                    ·
                      refine ⟨4089075464124355214601785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904201237664947238938093 4089075464124355214601785)
                      ·
                        rfl

theorem cell23_7963446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7963446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963446 prefixEnd_7963446 := by exact prefixLift 7963446
  have htrace : WordTrace (prefixWord ++ tailWord_7963446) baseStart_7963446 baseEnd_7963446 := by
    simpa [prefixWord, tailWord_7963446, baseEnd_7963446] using wordTrace_append hprefix tailTrace_7963446
  have hstable : (prefixWord ++ tailWord_7963446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963446).length < 2 ^ (prefixWord ++ tailWord_7963446).sum := by decide
  have hdescent : baseEnd_7963446 < baseStart_7963446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963448 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_7963448 : Nat := 118140960795 + 7963448 * 2 ^ 59
def prefixEnd_7963448 : Nat := 4983230072969 + 3 ^ 40 * 7963448 * 2
def baseEnd_7963448 : Nat := 4089076491085664206776775

theorem tailTrace_7963448 : CollatzResearch.WordTrace tailWord_7963448 prefixEnd_7963448 4089076491085664206776775 := by
  unfold tailWord_7963448
  simp only [CollatzResearch.WordTrace]
  refine ⟨145225405026897709742253499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193633873369196946323004665 145225405026897709742253499)
  ·
    refine ⟨217838107540346564613380249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145225405026897709742253499 217838107540346564613380249)
    ·
      refine ⟨163378580655259923460035187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217838107540346564613380249 163378580655259923460035187)
      ·
        refine ⟨245067870982889885190052781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163378580655259923460035187 245067870982889885190052781)
        ·
          refine ⟨91900451618583706946269793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245067870982889885190052781 91900451618583706946269793)
          ·
            refine ⟨68925338713937780209702345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91900451618583706946269793 68925338713937780209702345)
            ·
              refine ⟨51694004035453335157276759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68925338713937780209702345 51694004035453335157276759)
              ·
                refine ⟨77541006053180002735915139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51694004035453335157276759 77541006053180002735915139)
                ·
                  refine ⟨116311509079770004103872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77541006053180002735915139 116311509079770004103872709)
                  ·
                    refine ⟨21808407952456875769476133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116311509079770004103872709 21808407952456875769476133)
                    ·
                      refine ⟨4089076491085664206776775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21808407952456875769476133 4089076491085664206776775)
                      ·
                        rfl

theorem cell23_7963448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_7963448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963448 prefixEnd_7963448 := by exact prefixLift 7963448
  have htrace : WordTrace (prefixWord ++ tailWord_7963448) baseStart_7963448 baseEnd_7963448 := by
    simpa [prefixWord, tailWord_7963448, baseEnd_7963448] using wordTrace_append hprefix tailTrace_7963448
  have hstable : (prefixWord ++ tailWord_7963448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963448).length < 2 ^ (prefixWord ++ tailWord_7963448).sum := by decide
  have hdescent : baseEnd_7963448 < baseStart_7963448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963492 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 5]
def baseStart_7963492 : Nat := 118140960795 + 7963492 * 2 ^ 59
def prefixEnd_7963492 : Nat := 4983230072969 + 3 ^ 40 * 7963492 * 2
def baseEnd_7963492 : Nat := 454344342692718003847397

theorem tailTrace_7963492 : CollatzResearch.WordTrace tailWord_7963492 prefixEnd_7963492 454344342692718003847397 := by
  unfold tailWord_7963492
  simp only [CollatzResearch.WordTrace]
  refine ⟨145226207432818007499554365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193634943243757343332739153 145226207432818007499554365)
  ·
    refine ⟨54459827787306752812332887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145226207432818007499554365 54459827787306752812332887)
    ·
      refine ⟨81689741680960129218499331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54459827787306752812332887 81689741680960129218499331)
      ·
        refine ⟨122534612521440193827748997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81689741680960129218499331 122534612521440193827748997)
        ·
          refine ⟨22975239847770036342702937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122534612521440193827748997 22975239847770036342702937)
          ·
            refine ⟨17231429885827527257027203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22975239847770036342702937 17231429885827527257027203)
            ·
              refine ⟨25847144828741290885540805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231429885827527257027203 25847144828741290885540805)
              ·
                refine ⟨4846339655388992041038901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25847144828741290885540805 4846339655388992041038901)
                ·
                  refine ⟨454344342692718003847397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846339655388992041038901 454344342692718003847397)
                  ·
                    rfl

theorem cell23_7963492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_7963492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963492 prefixEnd_7963492 := by exact prefixLift 7963492
  have htrace : WordTrace (prefixWord ++ tailWord_7963492) baseStart_7963492 baseEnd_7963492 := by
    simpa [prefixWord, tailWord_7963492, baseEnd_7963492] using wordTrace_append hprefix tailTrace_7963492
  have hstable : (prefixWord ++ tailWord_7963492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963492).length < 2 ^ (prefixWord ++ tailWord_7963492).sum := by decide
  have hdescent : baseEnd_7963492 < baseStart_7963492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963525 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_7963525 : Nat := 118140960795 + 7963525 * 2 ^ 59
def prefixEnd_7963525 : Nat := 4983230072969 + 3 ^ 40 * 7963525 * 2
def baseEnd_7963525 : Nat := 4089116029096060405513921

theorem tailTrace_7963525 : CollatzResearch.WordTrace tailWord_7963525 prefixEnd_7963525 4089116029096060405513921 := by
  unfold tailWord_7963525
  simp only [CollatzResearch.WordTrace]
  refine ⟨290453618474516461635060029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193635745649677641090040019 290453618474516461635060029)
  ·
    refine ⟨108920106927943673113147511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290453618474516461635060029 108920106927943673113147511)
    ·
      refine ⟨163380160391915509669721267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108920106927943673113147511 163380160391915509669721267)
      ·
        refine ⟨245070240587873264504581901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163380160391915509669721267 245070240587873264504581901)
        ·
          refine ⟨91901340220452474189218213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245070240587873264504581901 91901340220452474189218213)
          ·
            refine ⟨17231501291334838910478415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91901340220452474189218213 17231501291334838910478415)
            ·
              refine ⟨25847251937002258365717623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17231501291334838910478415 25847251937002258365717623)
              ·
                refine ⟨38770877905503387548576435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25847251937002258365717623 38770877905503387548576435)
                ·
                  refine ⟨58156316858255081322864653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38770877905503387548576435 58156316858255081322864653)
                  ·
                    refine ⟨21808618821845655496074245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58156316858255081322864653 21808618821845655496074245)
                    ·
                      refine ⟨4089116029096060405513921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21808618821845655496074245 4089116029096060405513921)
                      ·
                        rfl

theorem cell23_7963525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_7963525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963525 prefixEnd_7963525 := by exact prefixLift 7963525
  have htrace : WordTrace (prefixWord ++ tailWord_7963525) baseStart_7963525 baseEnd_7963525 := by
    simpa [prefixWord, tailWord_7963525, baseEnd_7963525] using wordTrace_append hprefix tailTrace_7963525
  have hstable : (prefixWord ++ tailWord_7963525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963525).length < 2 ^ (prefixWord ++ tailWord_7963525).sum := by decide
  have hdescent : baseEnd_7963525 < baseStart_7963525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963545 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_7963545 : Nat := 118140960795 + 7963545 * 2 ^ 59
def prefixEnd_7963545 : Nat := 4983230072969 + 3 ^ 40 * 7963545 * 2
def baseEnd_7963545 : Nat := 4089126298709150327263829

theorem tailTrace_7963545 : CollatzResearch.WordTrace tailWord_7963545 prefixEnd_7963545 4089126298709150327263829 := by
  unfold tailWord_7963545
  simp only [CollatzResearch.WordTrace]
  refine ⟨290454347934444005050788089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193636231956296003367192059 290454347934444005050788089)
  ·
    refine ⟨217840760950833003788091067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290454347934444005050788089 217840760950833003788091067)
    ·
      refine ⟨326761141426249505682136601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217840760950833003788091067 326761141426249505682136601)
      ·
        refine ⟨245070856069687129261602451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326761141426249505682136601 245070856069687129261602451)
        ·
          refine ⟨367606284104530693892403677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245070856069687129261602451 367606284104530693892403677)
          ·
            refine ⟨137852356539199010209651379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367606284104530693892403677 137852356539199010209651379)
            ·
              refine ⟨206778534808798515314477069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137852356539199010209651379 206778534808798515314477069)
              ·
                refine ⟨77541950553299443242928901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206778534808798515314477069 77541950553299443242928901)
                ·
                  refine ⟨14539115728743645608049169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77541950553299443242928901 14539115728743645608049169)
                  ·
                    refine ⟨10904336796557734206036877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14539115728743645608049169 10904336796557734206036877)
                    ·
                      refine ⟨4089126298709150327263829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904336796557734206036877 4089126298709150327263829)
                      ·
                        rfl

theorem cell23_7963545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_7963545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963545 prefixEnd_7963545 := by exact prefixLift 7963545
  have htrace : WordTrace (prefixWord ++ tailWord_7963545) baseStart_7963545 baseEnd_7963545 := by
    simpa [prefixWord, tailWord_7963545, baseEnd_7963545] using wordTrace_append hprefix tailTrace_7963545
  have hstable : (prefixWord ++ tailWord_7963545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963545).length < 2 ^ (prefixWord ++ tailWord_7963545).sum := by decide
  have hdescent : baseEnd_7963545 < baseStart_7963545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963609 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_7963609 : Nat := 118140960795 + 7963609 * 2 ^ 59
def prefixEnd_7963609 : Nat := 4983230072969 + 3 ^ 40 * 7963609 * 2
def baseEnd_7963609 : Nat := 4089159161471038076863535

theorem tailTrace_7963609 : CollatzResearch.WordTrace tailWord_7963609 prefixEnd_7963609 4089159161471038076863535 := by
  unfold tailWord_7963609
  simp only [CollatzResearch.WordTrace]
  refine ⟨290456682206212143981117881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193637788137474762654078587 290456682206212143981117881)
  ·
    refine ⟨217842511654659107985838411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290456682206212143981117881 217842511654659107985838411)
    ·
      refine ⟨326763767481988661978757617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217842511654659107985838411 326763767481988661978757617)
      ·
        refine ⟨245072825611491496484068213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326763767481988661978757617 245072825611491496484068213)
        ·
          refine ⟨22975577401077327795381395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245072825611491496484068213 22975577401077327795381395)
          ·
            refine ⟨34463366101615991693072093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22975577401077327795381395 34463366101615991693072093)
            ·
              refine ⟨12923762288105996884902035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34463366101615991693072093 12923762288105996884902035)
              ·
                refine ⟨19385643432158995327353053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12923762288105996884902035 19385643432158995327353053)
                ·
                  refine ⟨7269616287059623247757395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19385643432158995327353053 7269616287059623247757395)
                  ·
                    refine ⟨10904424430589434871636093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269616287059623247757395 10904424430589434871636093)
                    ·
                      refine ⟨4089159161471038076863535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904424430589434871636093 4089159161471038076863535)
                      ·
                        rfl

theorem cell23_7963609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_7963609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963609 prefixEnd_7963609 := by exact prefixLift 7963609
  have htrace : WordTrace (prefixWord ++ tailWord_7963609) baseStart_7963609 baseEnd_7963609 := by
    simpa [prefixWord, tailWord_7963609, baseEnd_7963609] using wordTrace_append hprefix tailTrace_7963609
  have hstable : (prefixWord ++ tailWord_7963609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963609).length < 2 ^ (prefixWord ++ tailWord_7963609).sum := by decide
  have hdescent : baseEnd_7963609 < baseStart_7963609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963659 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 2, 4]
def baseStart_7963659 : Nat := 118140960795 + 7963659 * 2 ^ 59
def prefixEnd_7963659 : Nat := 4983230072969 + 3 ^ 40 * 7963659 * 2
def baseEnd_7963659 : Nat := 1363061611834587627079435

theorem tailTrace_7963659 : CollatzResearch.WordTrace tailWord_7963659 prefixEnd_7963659 1363061611834587627079435 := by
  unfold tailWord_7963659
  simp only [CollatzResearch.WordTrace]
  refine ⟨290458505856031002520438031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193639003904020668346958687 290458505856031002520438031)
  ·
    refine ⟨435687758784046503780657047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290458505856031002520438031 435687758784046503780657047)
    ·
      refine ⟨653531638176069755670985571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435687758784046503780657047 653531638176069755670985571)
      ·
        refine ⟨980297457264104633506478357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653531638176069755670985571 980297457264104633506478357)
        ·
          refine ⟨45951443309254904695616173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 980297457264104633506478357 45951443309254904695616173)
          ·
            refine ⟨17231791240970589260856065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45951443309254904695616173 17231791240970589260856065)
            ·
              refine ⟨12923843430727941945642049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17231791240970589260856065 12923843430727941945642049)
              ·
                refine ⟨9692882573045956459231537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12923843430727941945642049 9692882573045956459231537)
                ·
                  refine ⟨7269661929784467344423653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692882573045956459231537 7269661929784467344423653)
                  ·
                    refine ⟨1363061611834587627079435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7269661929784467344423653 1363061611834587627079435)
                    ·
                      rfl

theorem cell23_7963659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 4].length) (baseStart_7963659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963659 prefixEnd_7963659 := by exact prefixLift 7963659
  have htrace : WordTrace (prefixWord ++ tailWord_7963659) baseStart_7963659 baseEnd_7963659 := by
    simpa [prefixWord, tailWord_7963659, baseEnd_7963659] using wordTrace_append hprefix tailTrace_7963659
  have hstable : (prefixWord ++ tailWord_7963659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963659).length < 2 ^ (prefixWord ++ tailWord_7963659).sum := by decide
  have hdescent : baseEnd_7963659 < baseStart_7963659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963672 : List Nat := [2, 1, 2, 3, 2, 4, 1, 8]
def baseStart_7963672 : Nat := 118140960795 + 7963672 * 2 ^ 59
def prefixEnd_7963672 : Nat := 4983230072969 + 3 ^ 40 * 7963672 * 2
def baseEnd_7963672 : Nat := 151451537435269308532435

theorem tailTrace_7963672 : CollatzResearch.WordTrace tailWord_7963672 prefixEnd_7963672 151451537435269308532435 := by
  unfold tailWord_7963672
  simp only [CollatzResearch.WordTrace]
  refine ⟨145229490002491952870330635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193639320003322603827107513 145229490002491952870330635)
  ·
    refine ⟨217844235003737929305495953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145229490002491952870330635 217844235003737929305495953)
    ·
      refine ⟨163383176252803446979121965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217844235003737929305495953 163383176252803446979121965)
      ·
        refine ⟨61268691094801292617170737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163383176252803446979121965 61268691094801292617170737)
        ·
          refine ⟨45951518321100969462878053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61268691094801292617170737 45951518321100969462878053)
          ·
            refine ⟨8615909685206431774289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45951518321100969462878053 8615909685206431774289635)
            ·
              refine ⟨12923864527809647661434453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8615909685206431774289635 12923864527809647661434453)
              ·
                refine ⟨151451537435269308532435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12923864527809647661434453 151451537435269308532435)
                ·
                  rfl

theorem cell23_7963672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 8].length) (baseStart_7963672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963672 prefixEnd_7963672 := by exact prefixLift 7963672
  have htrace : WordTrace (prefixWord ++ tailWord_7963672) baseStart_7963672 baseEnd_7963672 := by
    simpa [prefixWord, tailWord_7963672, baseEnd_7963672] using wordTrace_append hprefix tailTrace_7963672
  have hstable : (prefixWord ++ tailWord_7963672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963672).length < 2 ^ (prefixWord ++ tailWord_7963672).sum := by decide
  have hdescent : baseEnd_7963672 < baseStart_7963672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963685 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_7963685 : Nat := 118140960795 + 7963685 * 2 ^ 59
def prefixEnd_7963685 : Nat := 4983230072969 + 3 ^ 40 * 7963685 * 2
def baseEnd_7963685 : Nat := 1363066062000259926504395

theorem tailTrace_7963685 : CollatzResearch.WordTrace tailWord_7963685 prefixEnd_7963685 1363066062000259926504395 := by
  unfold tailWord_7963685
  simp only [CollatzResearch.WordTrace]
  refine ⟨290459454153936808960884509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193639636102624539307256339 290459454153936808960884509)
  ·
    refine ⟨108922295307726303360331691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290459454153936808960884509 108922295307726303360331691)
    ·
      refine ⟨163383442961589455040497537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108922295307726303360331691 163383442961589455040497537)
      ·
        refine ⟨122537582221192091280373153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163383442961589455040497537 122537582221192091280373153)
        ·
          refine ⟨91903186665894068460279865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122537582221192091280373153 91903186665894068460279865)
          ·
            refine ⟨68927389999420551345209899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91903186665894068460279865 68927389999420551345209899)
            ·
              refine ⟨103391084999130827017814849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68927389999420551345209899 103391084999130827017814849)
              ·
                refine ⟨77543313749348120263361137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103391084999130827017814849 77543313749348120263361137)
                ·
                  refine ⟨58157485312011090197520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77543313749348120263361137 58157485312011090197520853)
                  ·
                    refine ⟨1363066062000259926504395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58157485312011090197520853 1363066062000259926504395)
                    ·
                      rfl

theorem cell23_7963685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_7963685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963685 prefixEnd_7963685 := by exact prefixLift 7963685
  have htrace : WordTrace (prefixWord ++ tailWord_7963685) baseStart_7963685 baseEnd_7963685 := by
    simpa [prefixWord, tailWord_7963685, baseEnd_7963685] using wordTrace_append hprefix tailTrace_7963685
  have hstable : (prefixWord ++ tailWord_7963685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963685).length < 2 ^ (prefixWord ++ tailWord_7963685).sum := by decide
  have hdescent : baseEnd_7963685 < baseStart_7963685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963700 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7963700 : Nat := 118140960795 + 7963700 * 2 ^ 59
def prefixEnd_7963700 : Nat := 4983230072969 + 3 ^ 40 * 7963700 * 2
def baseEnd_7963700 : Nat := 4089205888210597220825617

theorem tailTrace_7963700 : CollatzResearch.WordTrace tailWord_7963700 prefixEnd_7963700 4089205888210597220825617 := by
  unfold tailWord_7963700
  simp only [CollatzResearch.WordTrace]
  refine ⟨145230000624441233261340277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193640000832588311015120369 145230000624441233261340277)
  ·
    refine ⟨13615312558541365618250651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145230000624441233261340277 13615312558541365618250651)
    ·
      refine ⟨20422968837812048427375977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615312558541365618250651 20422968837812048427375977)
      ·
        refine ⟨15317226628359036320531983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422968837812048427375977 15317226628359036320531983)
        ·
          refine ⟨22975839942538554480797975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317226628359036320531983 22975839942538554480797975)
          ·
            refine ⟨34463759913807831721196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22975839942538554480797975 34463759913807831721196963)
            ·
              refine ⟨51695639870711747581795445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34463759913807831721196963 51695639870711747581795445)
              ·
                refine ⟨4846466237879226335793323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51695639870711747581795445 4846466237879226335793323)
                ·
                  refine ⟨7269699356818839503689985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846466237879226335793323 7269699356818839503689985)
                  ·
                    refine ⟨5452274517614129627767489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269699356818839503689985 5452274517614129627767489)
                    ·
                      refine ⟨4089205888210597220825617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452274517614129627767489 4089205888210597220825617)
                      ·
                        rfl

theorem cell23_7963700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7963700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963700 prefixEnd_7963700 := by exact prefixLift 7963700
  have htrace : WordTrace (prefixWord ++ tailWord_7963700) baseStart_7963700 baseEnd_7963700 := by
    simpa [prefixWord, tailWord_7963700, baseEnd_7963700] using wordTrace_append hprefix tailTrace_7963700
  have hstable : (prefixWord ++ tailWord_7963700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963700).length < 2 ^ (prefixWord ++ tailWord_7963700).sum := by decide
  have hdescent : baseEnd_7963700 < baseStart_7963700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963715 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 6]
def baseStart_7963715 : Nat := 118140960795 + 7963715 * 2 ^ 59
def prefixEnd_7963715 : Nat := 4983230072969 + 3 ^ 40 * 7963715 * 2
def baseEnd_7963715 : Nat := 1363071196806804887379349

theorem tailTrace_7963715 : CollatzResearch.WordTrace tailWord_7963715 prefixEnd_7963715 1363071196806804887379349 := by
  unfold tailWord_7963715
  simp only [CollatzResearch.WordTrace]
  refine ⟨290460548343828124084476599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193640365562552082722984399 290460548343828124084476599)
  ·
    refine ⟨435690822515742186126714899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290460548343828124084476599 435690822515742186126714899)
    ·
      refine ⟨653536233773613279190072349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435690822515742186126714899 653536233773613279190072349)
      ·
        refine ⟨245076087665104979696277131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653536233773613279190072349 245076087665104979696277131)
        ·
          refine ⟨367614131497657469544415697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245076087665104979696277131 367614131497657469544415697)
          ·
            refine ⟨275710598623243102158311773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367614131497657469544415697 275710598623243102158311773)
            ·
              refine ⟨103391474483716163309366915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275710598623243102158311773 103391474483716163309366915)
              ·
                refine ⟨155087211725574244964050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103391474483716163309366915 155087211725574244964050373)
                ·
                  refine ⟨29078852198545170930759445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155087211725574244964050373 29078852198545170930759445)
                  ·
                    refine ⟨1363071196806804887379349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29078852198545170930759445 1363071196806804887379349)
                    ·
                      rfl

theorem cell23_7963715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_7963715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963715 prefixEnd_7963715 := by exact prefixLift 7963715
  have htrace : WordTrace (prefixWord ++ tailWord_7963715) baseStart_7963715 baseEnd_7963715 := by
    simpa [prefixWord, tailWord_7963715, baseEnd_7963715] using wordTrace_append hprefix tailTrace_7963715
  have hstable : (prefixWord ++ tailWord_7963715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963715).length < 2 ^ (prefixWord ++ tailWord_7963715).sum := by decide
  have hdescent : baseEnd_7963715 < baseStart_7963715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963732 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_7963732 : Nat := 118140960795 + 7963732 * 2 ^ 59
def prefixEnd_7963732 : Nat := 4983230072969 + 3 ^ 40 * 7963732 * 2
def baseEnd_7963732 : Nat := 1363074106530513698541823

theorem tailTrace_7963732 : CollatzResearch.WordTrace tailWord_7963732 prefixEnd_7963732 1363074106530513698541823 := by
  unfold tailWord_7963732
  simp only [CollatzResearch.WordTrace]
  refine ⟨145230584192383267993922725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193640778923177690658563633 145230584192383267993922725)
  ·
    refine ⟨27230734536071862748860511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145230584192383267993922725 27230734536071862748860511)
    ·
      refine ⟨40846101804107794123290767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27230734536071862748860511 40846101804107794123290767)
      ·
        refine ⟨61269152706161691184936151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40846101804107794123290767 61269152706161691184936151)
        ·
          refine ⟨91903729059242536777404227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61269152706161691184936151 91903729059242536777404227)
          ·
            refine ⟨137855593588863805166106341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91903729059242536777404227 137855593588863805166106341)
            ·
              refine ⟨25847923797911963468644939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137855593588863805166106341 25847923797911963468644939)
              ·
                refine ⟨38771885696867945202967409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25847923797911963468644939 38771885696867945202967409)
                ·
                  refine ⟨29078914272650958902225557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38771885696867945202967409 29078914272650958902225557)
                  ·
                    refine ⟨1363074106530513698541823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29078914272650958902225557 1363074106530513698541823)
                    ·
                      rfl

theorem cell23_7963732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_7963732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963732 prefixEnd_7963732 := by exact prefixLift 7963732
  have htrace : WordTrace (prefixWord ++ tailWord_7963732) baseStart_7963732 baseEnd_7963732 := by
    simpa [prefixWord, tailWord_7963732, baseEnd_7963732] using wordTrace_append hprefix tailTrace_7963732
  have hstable : (prefixWord ++ tailWord_7963732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963732).length < 2 ^ (prefixWord ++ tailWord_7963732).sum := by decide
  have hdescent : baseEnd_7963732 < baseStart_7963732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963775 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 11]
def baseStart_7963775 : Nat := 118140960795 + 7963775 * 2 ^ 59
def prefixEnd_7963775 : Nat := 4983230072969 + 3 ^ 40 * 7963775 * 2
def baseEnd_7963775 : Nat := 1363081466419894809129257

theorem tailTrace_7963775 : CollatzResearch.WordTrace tailWord_7963775 prefixEnd_7963775 1363081466419894809129257 := by
  unfold tailWord_7963775
  simp only [CollatzResearch.WordTrace]
  refine ⟨290462736723610754331660779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193641824482407169554440519 290462736723610754331660779)
  ·
    refine ⟨435694105085416131497491169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290462736723610754331660779 435694105085416131497491169)
    ·
      refine ⟨326770578814062098623118377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435694105085416131497491169 326770578814062098623118377)
      ·
        refine ⟨245077934110546573967338783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326770578814062098623118377 245077934110546573967338783)
        ·
          refine ⟨367616901165819860951008175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245077934110546573967338783 367616901165819860951008175)
          ·
            refine ⟨551425351748729791426512263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367616901165819860951008175 551425351748729791426512263)
            ·
              refine ⟨827138027623094687139768395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551425351748729791426512263 827138027623094687139768395)
              ·
                refine ⟨1240707041434642030709652593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827138027623094687139768395 1240707041434642030709652593)
                ·
                  refine ⟨930530281075981523032239445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1240707041434642030709652593 930530281075981523032239445)
                  ·
                    refine ⟨1363081466419894809129257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 930530281075981523032239445 1363081466419894809129257)
                    ·
                      rfl

theorem cell23_7963775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_7963775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963775 prefixEnd_7963775 := by exact prefixLift 7963775
  have htrace : WordTrace (prefixWord ++ tailWord_7963775) baseStart_7963775 baseEnd_7963775 := by
    simpa [prefixWord, tailWord_7963775, baseEnd_7963775] using wordTrace_append hprefix tailTrace_7963775
  have hstable : (prefixWord ++ tailWord_7963775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963775).length < 2 ^ (prefixWord ++ tailWord_7963775).sum := by decide
  have hdescent : baseEnd_7963775 < baseStart_7963775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963790 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7963790 : Nat := 118140960795 + 7963790 * 2 ^ 59
def prefixEnd_7963790 : Nat := 4983230072969 + 3 ^ 40 * 7963790 * 2
def baseEnd_7963790 : Nat := 4089252101469501868700203

theorem tailTrace_7963790 : CollatzResearch.WordTrace tailWord_7963790 prefixEnd_7963790 4089252101469501868700203 := by
  unfold tailWord_7963790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36307910477319551486682103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193642189212370941262304549 36307910477319551486682103)
  ·
    refine ⟨54461865715979327230023155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36307910477319551486682103 54461865715979327230023155)
    ·
      refine ⟨81692798573968990845034733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54461865715979327230023155 81692798573968990845034733)
      ·
        refine ⟨30634799465238371566888025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81692798573968990845034733 30634799465238371566888025)
        ·
          refine ⟨22976099598928778675166019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30634799465238371566888025 22976099598928778675166019)
          ·
            refine ⟨34464149398393168012749029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22976099598928778675166019 34464149398393168012749029)
            ·
              refine ⟨6462028012198719002390443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34464149398393168012749029 6462028012198719002390443)
              ·
                refine ⟨9693042018298078503585665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462028012198719002390443 9693042018298078503585665)
                ·
                  refine ⟨7269781513723558877689249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9693042018298078503585665 7269781513723558877689249)
                  ·
                    refine ⟨5452336135292669158266937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269781513723558877689249 5452336135292669158266937)
                    ·
                      refine ⟨4089252101469501868700203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452336135292669158266937 4089252101469501868700203)
                      ·
                        rfl

theorem cell23_7963790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7963790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963790 prefixEnd_7963790 := by exact prefixLift 7963790
  have htrace : WordTrace (prefixWord ++ tailWord_7963790) baseStart_7963790 baseEnd_7963790 := by
    simpa [prefixWord, tailWord_7963790, baseEnd_7963790] using wordTrace_append hprefix tailTrace_7963790
  have hstable : (prefixWord ++ tailWord_7963790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963790).length < 2 ^ (prefixWord ++ tailWord_7963790).sum := by decide
  have hdescent : baseEnd_7963790 < baseStart_7963790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963809 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7963809 : Nat := 118140960795 + 7963809 * 2 ^ 59
def prefixEnd_7963809 : Nat := 4983230072969 + 3 ^ 40 * 7963809 * 2
def baseEnd_7963809 : Nat := 1363087285867312431454205

theorem tailTrace_7963809 : CollatzResearch.WordTrace tailWord_7963809 prefixEnd_7963809 1363087285867312431454205 := by
  unfold tailWord_7963809
  simp only [CollatzResearch.WordTrace]
  refine ⟨290463976805487578138398481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193642651203658385425598987 290463976805487578138398481)
  ·
    refine ⟨217847982604115683603798861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290463976805487578138398481 217847982604115683603798861)
    ·
      refine ⟨81692993476543381351424573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217847982604115683603798861 81692993476543381351424573)
      ·
        refine ⟨30634872553703768006784215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81692993476543381351424573 30634872553703768006784215)
        ·
          refine ⟨45952308830555652010176323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30634872553703768006784215 45952308830555652010176323)
          ·
            refine ⟨68928463245833478015264485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45952308830555652010176323 68928463245833478015264485)
            ·
              refine ⟨12924086858593777127862091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68928463245833478015264485 12924086858593777127862091)
              ·
                refine ⟨19386130287890665691793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924086858593777127862091 19386130287890665691793137)
                ·
                  refine ⟨14539597715917999268844853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386130287890665691793137 14539597715917999268844853)
                  ·
                    refine ⟨1363087285867312431454205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14539597715917999268844853 1363087285867312431454205)
                    ·
                      rfl

theorem cell23_7963809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7963809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963809 prefixEnd_7963809 := by exact prefixLift 7963809
  have htrace : WordTrace (prefixWord ++ tailWord_7963809) baseStart_7963809 baseEnd_7963809 := by
    simpa [prefixWord, tailWord_7963809, baseEnd_7963809] using wordTrace_append hprefix tailTrace_7963809
  have hstable : (prefixWord ++ tailWord_7963809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963809).length < 2 ^ (prefixWord ++ tailWord_7963809).sum := by decide
  have hdescent : baseEnd_7963809 < baseStart_7963809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963830 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_7963830 : Nat := 118140960795 + 7963830 * 2 ^ 59
def prefixEnd_7963830 : Nat := 4983230072969 + 3 ^ 40 * 7963830 * 2
def baseEnd_7963830 : Nat := 454363626743964634688891

theorem tailTrace_7963830 : CollatzResearch.WordTrace tailWord_7963830 prefixEnd_7963830 454363626743964634688891 := by
  unfold tailWord_7963830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154046421150718670307059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193643161825607665816608629 18154046421150718670307059)
  ·
    refine ⟨27231069631726078005460589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18154046421150718670307059 27231069631726078005460589)
    ·
      refine ⟨10211651111897279252047721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27231069631726078005460589 10211651111897279252047721)
      ·
        refine ⟨7658738333922959439035791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10211651111897279252047721 7658738333922959439035791)
        ·
          refine ⟨11488107500884439158553687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658738333922959439035791 11488107500884439158553687)
          ·
            refine ⟨17232161251326658737830531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488107500884439158553687 17232161251326658737830531)
            ·
              refine ⟨25848241876989988106745797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17232161251326658737830531 25848241876989988106745797)
              ·
                refine ⟨4846545351935622770014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25848241876989988106745797 4846545351935622770014837)
                ·
                  refine ⟨454363626743964634688891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846545351935622770014837 454363626743964634688891)
                  ·
                    rfl

theorem cell23_7963830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_7963830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963830 prefixEnd_7963830 := by exact prefixLift 7963830
  have htrace : WordTrace (prefixWord ++ tailWord_7963830) baseStart_7963830 baseEnd_7963830 := by
    simpa [prefixWord, tailWord_7963830, baseEnd_7963830] using wordTrace_append hprefix tailTrace_7963830
  have hstable : (prefixWord ++ tailWord_7963830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963830).length < 2 ^ (prefixWord ++ tailWord_7963830).sum := by decide
  have hdescent : baseEnd_7963830 < baseStart_7963830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963860 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_7963860 : Nat := 118140960795 + 7963860 * 2 ^ 59
def prefixEnd_7963860 : Nat := 4983230072969 + 3 ^ 40 * 7963860 * 2
def baseEnd_7963860 : Nat := 1363096015038438864941627

theorem tailTrace_7963860 : CollatzResearch.WordTrace tailWord_7963860 prefixEnd_7963860 1363096015038438864941627 := by
  unfold tailWord_7963860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145232918464151406924252517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193643891285535209232336689 145232918464151406924252517)
  ·
    refine ⟨27231172212028388798297347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145232918464151406924252517 27231172212028388798297347)
    ·
      refine ⟨40846758318042583197446021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231172212028388798297347 40846758318042583197446021)
      ·
        refine ⟨7658767184632984349521129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40846758318042583197446021 7658767184632984349521129)
        ·
          refine ⟨5744075388474738262140847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7658767184632984349521129 5744075388474738262140847)
          ·
            refine ⟨8616113082712107393211271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744075388474738262140847 8616113082712107393211271)
            ·
              refine ⟨12924169624068161089816907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616113082712107393211271 12924169624068161089816907)
              ·
                refine ⟨19386254436102241634725361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924169624068161089816907 19386254436102241634725361)
                ·
                  refine ⟨14539690827076681226044021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386254436102241634725361 14539690827076681226044021)
                  ·
                    refine ⟨1363096015038438864941627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14539690827076681226044021 1363096015038438864941627)
                    ·
                      rfl

theorem cell23_7963860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_7963860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963860 prefixEnd_7963860 := by exact prefixLift 7963860
  have htrace : WordTrace (prefixWord ++ tailWord_7963860) baseStart_7963860 baseEnd_7963860 := by
    simpa [prefixWord, tailWord_7963860, baseEnd_7963860] using wordTrace_append hprefix tailTrace_7963860
  have hstable : (prefixWord ++ tailWord_7963860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963860).length < 2 ^ (prefixWord ++ tailWord_7963860).sum := by decide
  have hdescent : baseEnd_7963860 < baseStart_7963860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963873 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 1, 4]
def baseStart_7963873 : Nat := 118140960795 + 7963873 * 2 ^ 59
def prefixEnd_7963873 : Nat := 4983230072969 + 3 ^ 40 * 7963873 * 2
def baseEnd_7963873 : Nat := 1363098240121275014654107

theorem tailTrace_7963873 : CollatzResearch.WordTrace tailWord_7963873 prefixEnd_7963873 1363098240121275014654107 := by
  unfold tailWord_7963873
  simp only [CollatzResearch.WordTrace]
  refine ⟨290466311077255717068728273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193644207384837144712485515 290466311077255717068728273)
  ·
    refine ⟨217849733307941787801546205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290466311077255717068728273 217849733307941787801546205)
    ·
      refine ⟨81693649990478170425579827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217849733307941787801546205 81693649990478170425579827)
      ·
        refine ⟨122540474985717255638369741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81693649990478170425579827 122540474985717255638369741)
        ·
          refine ⟨45952678119643970864388653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122540474985717255638369741 45952678119643970864388653)
          ·
            refine ⟨17232254294866489074145745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45952678119643970864388653 17232254294866489074145745)
            ·
              refine ⟨12924190721149866805609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232254294866489074145745 12924190721149866805609309)
              ·
                refine ⟨4846571520431200052103491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12924190721149866805609309 4846571520431200052103491)
                ·
                  refine ⟨7269857280646800078155237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846571520431200052103491 7269857280646800078155237)
                  ·
                    refine ⟨1363098240121275014654107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7269857280646800078155237 1363098240121275014654107)
                    ·
                      rfl

theorem cell23_7963873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_7963873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963873 prefixEnd_7963873 := by exact prefixLift 7963873
  have htrace : WordTrace (prefixWord ++ tailWord_7963873) baseStart_7963873 baseEnd_7963873 := by
    simpa [prefixWord, tailWord_7963873, baseEnd_7963873] using wordTrace_append hprefix tailTrace_7963873
  have hstable : (prefixWord ++ tailWord_7963873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963873).length < 2 ^ (prefixWord ++ tailWord_7963873).sum := by decide
  have hdescent : baseEnd_7963873 < baseStart_7963873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963916 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_7963916 : Nat := 118140960795 + 7963916 * 2 ^ 59
def prefixEnd_7963916 : Nat := 4983230072969 + 3 ^ 40 * 7963916 * 2
def baseEnd_7963916 : Nat := 1363105600010656125241541

theorem tailTrace_7963916 : CollatzResearch.WordTrace tailWord_7963916 prefixEnd_7963916 1363105600010656125241541 := by
  unfold tailWord_7963916
  simp only [CollatzResearch.WordTrace]
  refine ⟨145233939708049967706271801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193645252944066623608362401 145233939708049967706271801)
  ·
    refine ⟨108925454781037475779703851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145233939708049967706271801 108925454781037475779703851)
    ·
      refine ⟨163388182171556213669555777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108925454781037475779703851 163388182171556213669555777)
      ·
        refine ⟨122541136628667160252166833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163388182171556213669555777 122541136628667160252166833)
        ·
          refine ⟨91905852471500370189125125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122541136628667160252166833 91905852471500370189125125)
          ·
            refine ⟨17232347338406319410460961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91905852471500370189125125 17232347338406319410460961)
            ·
              refine ⟨12924260503804739557845721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232347338406319410460961 12924260503804739557845721)
              ·
                refine ⟨9693195377853554668384291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12924260503804739557845721 9693195377853554668384291)
                ·
                  refine ⟨14539793066780332002576437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693195377853554668384291 14539793066780332002576437)
                  ·
                    refine ⟨1363105600010656125241541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14539793066780332002576437 1363105600010656125241541)
                    ·
                      rfl

theorem cell23_7963916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_7963916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963916 prefixEnd_7963916 := by exact prefixLift 7963916
  have htrace : WordTrace (prefixWord ++ tailWord_7963916) baseStart_7963916 baseEnd_7963916 := by
    simpa [prefixWord, tailWord_7963916, baseEnd_7963916] using wordTrace_append hprefix tailTrace_7963916
  have hstable : (prefixWord ++ tailWord_7963916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963916).length < 2 ^ (prefixWord ++ tailWord_7963916).sum := by decide
  have hdescent : baseEnd_7963916 < baseStart_7963916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963930 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_7963930 : Nat := 118140960795 + 7963930 * 2 ^ 59
def prefixEnd_7963930 : Nat := 4983230072969 + 3 ^ 40 * 7963930 * 2
def baseEnd_7963930 : Nat := 4089323988761131320949559

theorem tailTrace_7963930 : CollatzResearch.WordTrace tailWord_7963930 prefixEnd_7963930 4089323988761131320949559 := by
  unfold tailWord_7963930
  simp only [CollatzResearch.WordTrace]
  refine ⟨72617097509512303950888311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193645593358699477202368829 72617097509512303950888311)
  ·
    refine ⟨108925646264268455926332467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72617097509512303950888311 108925646264268455926332467)
    ·
      refine ⟨163388469396402683889498701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108925646264268455926332467 163388469396402683889498701)
      ·
        refine ⟨61270676023651006458562013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163388469396402683889498701 61270676023651006458562013)
        ·
          refine ⟨22976503508869127421960755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61270676023651006458562013 22976503508869127421960755)
          ·
            refine ⟨34464755263303691132941133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22976503508869127421960755 34464755263303691132941133)
            ·
              refine ⟨12924283223738884174852925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34464755263303691132941133 12924283223738884174852925)
              ·
                refine ⟨4846606208902081565569847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12924283223738884174852925 4846606208902081565569847)
                ·
                  refine ⟨7269909313353122348354771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846606208902081565569847 7269909313353122348354771)
                  ·
                    refine ⟨10904863970029683522532157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269909313353122348354771 10904863970029683522532157)
                    ·
                      refine ⟨4089323988761131320949559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904863970029683522532157 4089323988761131320949559)
                      ·
                        rfl

theorem cell23_7963930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_7963930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963930 prefixEnd_7963930 := by exact prefixLift 7963930
  have htrace : WordTrace (prefixWord ++ tailWord_7963930) baseStart_7963930 baseEnd_7963930 := by
    simpa [prefixWord, tailWord_7963930, baseEnd_7963930] using wordTrace_append hprefix tailTrace_7963930
  have hstable : (prefixWord ++ tailWord_7963930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963930).length < 2 ^ (prefixWord ++ tailWord_7963930).sum := by decide
  have hdescent : baseEnd_7963930 < baseStart_7963930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963939 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7963939 : Nat := 118140960795 + 7963939 * 2 ^ 59
def prefixEnd_7963939 : Nat := 4983230072969 + 3 ^ 40 * 7963939 * 2
def baseEnd_7963939 : Nat := 4089328610087021785737017

theorem tailTrace_7963939 : CollatzResearch.WordTrace tailWord_7963939 prefixEnd_7963939 4089328610087021785737017 := by
  unfold tailWord_7963939
  simp only [CollatzResearch.WordTrace]
  refine ⟨290468718295016610340630871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193645812196677740227087247 290468718295016610340630871)
  ·
    refine ⟨435703077442524915510946307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290468718295016610340630871 435703077442524915510946307)
    ·
      refine ⟨653554616163787373266419461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435703077442524915510946307 653554616163787373266419461)
      ·
        refine ⟨122541490530710132487453649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 653554616163787373266419461 122541490530710132487453649)
        ·
          refine ⟨91906117898032599365590237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122541490530710132487453649 91906117898032599365590237)
          ·
            refine ⟨34464794211762224762096339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91906117898032599365590237 34464794211762224762096339)
            ·
              refine ⟨51697191317643337143144509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34464794211762224762096339 51697191317643337143144509)
              ·
                refine ⟨19386446744116251428679191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51697191317643337143144509 19386446744116251428679191)
                ·
                  refine ⟨29079670116174377143018787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19386446744116251428679191 29079670116174377143018787)
                  ·
                    refine ⟨43619505174261565714528181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29079670116174377143018787 43619505174261565714528181)
                    ·
                      refine ⟨4089328610087021785737017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43619505174261565714528181 4089328610087021785737017)
                      ·
                        rfl

theorem cell23_7963939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7963939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963939 prefixEnd_7963939 := by exact prefixLift 7963939
  have htrace : WordTrace (prefixWord ++ tailWord_7963939) baseStart_7963939 baseEnd_7963939 := by
    simpa [prefixWord, tailWord_7963939, baseEnd_7963939] using wordTrace_append hprefix tailTrace_7963939
  have hstable : (prefixWord ++ tailWord_7963939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963939).length < 2 ^ (prefixWord ++ tailWord_7963939).sum := by decide
  have hdescent : baseEnd_7963939 < baseStart_7963939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963956 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7963956 : Nat := 118140960795 + 7963956 * 2 ^ 59
def prefixEnd_7963956 : Nat := 4983230072969 + 3 ^ 40 * 7963956 * 2
def baseEnd_7963956 : Nat := 4089337339258148219224439

theorem tailTrace_7963956 : CollatzResearch.WordTrace tailWord_7963956 prefixEnd_7963956 4089337339258148219224439 := by
  unfold tailWord_7963956
  simp only [CollatzResearch.WordTrace]
  refine ⟨145234669167977511121999861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193646225557303348162666481 145234669167977511121999861)
  ·
    refine ⟨13615750234497891667687487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145234669167977511121999861 13615750234497891667687487)
    ·
      refine ⟨20423625351746837501531231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615750234497891667687487 20423625351746837501531231)
      ·
        refine ⟨30635438027620256252296847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20423625351746837501531231 30635438027620256252296847)
        ·
          refine ⟨45953157041430384378445271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30635438027620256252296847 45953157041430384378445271)
          ·
            refine ⟨68929735562145576567667907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45953157041430384378445271 68929735562145576567667907)
            ·
              refine ⟨103394603343218364851501861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68929735562145576567667907 103394603343218364851501861)
              ·
                refine ⟨19386488126853443409656599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103394603343218364851501861 19386488126853443409656599)
                ·
                  refine ⟨29079732190280165114484899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19386488126853443409656599 29079732190280165114484899)
                  ·
                    refine ⟨43619598285420247671727349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29079732190280165114484899 43619598285420247671727349)
                    ·
                      refine ⟨4089337339258148219224439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43619598285420247671727349 4089337339258148219224439)
                      ·
                        rfl

theorem cell23_7963956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7963956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963956 prefixEnd_7963956 := by exact prefixLift 7963956
  have htrace : WordTrace (prefixWord ++ tailWord_7963956) baseStart_7963956 baseEnd_7963956 := by
    simpa [prefixWord, tailWord_7963956, baseEnd_7963956] using wordTrace_append hprefix tailTrace_7963956
  have hstable : (prefixWord ++ tailWord_7963956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963956).length < 2 ^ (prefixWord ++ tailWord_7963956).sum := by decide
  have hdescent : baseEnd_7963956 < baseStart_7963956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963966 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7963966 : Nat := 118140960795 + 7963966 * 2 ^ 59
def prefixEnd_7963966 : Nat := 4983230072969 + 3 ^ 40 * 7963966 * 2
def baseEnd_7963966 : Nat := 4089342474064693180099393

theorem tailTrace_7963966 : CollatzResearch.WordTrace tailWord_7963966 prefixEnd_7963966 4089342474064693180099393 := by
  unfold tailWord_7963966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36308712883239849243982969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193646468710612529301242501 36308712883239849243982969)
  ·
    refine ⟨27231534662429886932987227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36308712883239849243982969 27231534662429886932987227)
    ·
      refine ⟨40847301993644830399480841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231534662429886932987227 40847301993644830399480841)
      ·
        refine ⟨30635476495233622799610631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40847301993644830399480841 30635476495233622799610631)
        ·
          refine ⟨45953214742850434199415947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30635476495233622799610631 45953214742850434199415947)
          ·
            refine ⟨68929822114275651299123921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45953214742850434199415947 68929822114275651299123921)
            ·
              refine ⟨51697366585706738474342941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68929822114275651299123921 51697366585706738474342941)
              ·
                refine ⟨19386512469640026927878603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51697366585706738474342941 19386512469640026927878603)
                ·
                  refine ⟨29079768704460040391817905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19386512469640026927878603 29079768704460040391817905)
                  ·
                    refine ⟨21809826528345030293863429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29079768704460040391817905 21809826528345030293863429)
                    ·
                      refine ⟨4089342474064693180099393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21809826528345030293863429 4089342474064693180099393)
                      ·
                        rfl

theorem cell23_7963966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7963966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963966 prefixEnd_7963966 := by exact prefixLift 7963966
  have htrace : WordTrace (prefixWord ++ tailWord_7963966) baseStart_7963966 baseEnd_7963966 := by
    simpa [prefixWord, tailWord_7963966, baseEnd_7963966] using wordTrace_append hprefix tailTrace_7963966
  have hstable : (prefixWord ++ tailWord_7963966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963966).length < 2 ^ (prefixWord ++ tailWord_7963966).sum := by decide
  have hdescent : baseEnd_7963966 < baseStart_7963966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7963974 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7963974 : Nat := 118140960795 + 7963974 * 2 ^ 59
def prefixEnd_7963974 : Nat := 4983230072969 + 3 ^ 40 * 7963974 * 2
def baseEnd_7963974 : Nat := 4089346581909929148799357

theorem tailTrace_7963974 : CollatzResearch.WordTrace tailWord_7963974 prefixEnd_7963974 4089346581909929148799357 := by
  unfold tailWord_7963974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077187339059056603692343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193646663233259874212103317 9077187339059056603692343)
  ·
    refine ⟨13615781008588584905538515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077187339059056603692343 13615781008588584905538515)
    ·
      refine ⟨20423671512882877358307773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615781008588584905538515 20423671512882877358307773)
      ·
        refine ⟨7658876817331079009365415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20423671512882877358307773 7658876817331079009365415)
        ·
          refine ⟨11488315225996618514048123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658876817331079009365415 11488315225996618514048123)
          ·
            refine ⟨17232472838994927771072185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488315225996618514048123 17232472838994927771072185)
            ·
              refine ⟨12924354629246195828304139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232472838994927771072185 12924354629246195828304139)
              ·
                refine ⟨19386531943869293742456209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924354629246195828304139 19386531943869293742456209)
                ·
                  refine ⟨14539898957901970306842157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386531943869293742456209 14539898957901970306842157)
                  ·
                    refine ⟨5452462109213238865065809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14539898957901970306842157 5452462109213238865065809)
                    ·
                      refine ⟨4089346581909929148799357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452462109213238865065809 4089346581909929148799357)
                      ·
                        rfl

theorem cell23_7963974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7963974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7963974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7963974 prefixEnd_7963974 := by exact prefixLift 7963974
  have htrace : WordTrace (prefixWord ++ tailWord_7963974) baseStart_7963974 baseEnd_7963974 := by
    simpa [prefixWord, tailWord_7963974, baseEnd_7963974] using wordTrace_append hprefix tailTrace_7963974
  have hstable : (prefixWord ++ tailWord_7963974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7963974).length < 2 ^ (prefixWord ++ tailWord_7963974).sum := by decide
  have hdescent : baseEnd_7963974 < baseStart_7963974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7963974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964003 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7964003 : Nat := 118140960795 + 7964003 * 2 ^ 59
def prefixEnd_7964003 : Nat := 4983230072969 + 3 ^ 40 * 7964003 * 2
def baseEnd_7964003 : Nat := 4089361472848909535336723

theorem tailTrace_7964003 : CollatzResearch.WordTrace tailWord_7964003 prefixEnd_7964003 4089361472848909535336723 := by
  unfold tailWord_7964003
  simp only [CollatzResearch.WordTrace]
  refine ⟨290471052566784749270960663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193647368377856499513973775 290471052566784749270960663)
  ·
    refine ⟨435706578850177123906440995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290471052566784749270960663 435706578850177123906440995)
    ·
      refine ⟨653559868275265685859661493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435706578850177123906440995 653559868275265685859661493)
      ·
        refine ⟨61271237650806158049343265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 653559868275265685859661493 61271237650806158049343265)
        ·
          refine ⟨45953428238104618537007449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61271237650806158049343265 45953428238104618537007449)
          ·
            refine ⟨34465071178578463902755587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45953428238104618537007449 34465071178578463902755587)
            ·
              refine ⟨51697606767867695854133381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34465071178578463902755587 51697606767867695854133381)
              ·
                refine ⟨9693301268975192972650009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51697606767867695854133381 9693301268975192972650009)
                ·
                  refine ⟨7269975951731394729487507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9693301268975192972650009 7269975951731394729487507)
                  ·
                    refine ⟨10904963927597092094231261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7269975951731394729487507 10904963927597092094231261)
                    ·
                      refine ⟨4089361472848909535336723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10904963927597092094231261 4089361472848909535336723)
                      ·
                        rfl

theorem cell23_7964003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7964003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964003 prefixEnd_7964003 := by exact prefixLift 7964003
  have htrace : WordTrace (prefixWord ++ tailWord_7964003) baseStart_7964003 baseEnd_7964003 := by
    simpa [prefixWord, tailWord_7964003, baseEnd_7964003] using wordTrace_append hprefix tailTrace_7964003
  have hstable : (prefixWord ++ tailWord_7964003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964003).length < 2 ^ (prefixWord ++ tailWord_7964003).sum := by decide
  have hdescent : baseEnd_7964003 < baseStart_7964003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964004 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_7964004 : Nat := 118140960795 + 7964004 * 2 ^ 59
def prefixEnd_7964004 : Nat := 4983230072969 + 3 ^ 40 * 7964004 * 2
def baseEnd_7964004 : Nat := 4089361986329564031424219

theorem tailTrace_7964004 : CollatzResearch.WordTrace tailWord_7964004 prefixEnd_7964004 4089361986329564031424219 := by
  unfold tailWord_7964004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145235544519890563220873533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193647392693187417627831377 145235544519890563220873533)
  ·
    refine ⟨54463329194958961207827575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145235544519890563220873533 54463329194958961207827575)
    ·
      refine ⟨81694993792438441811741363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54463329194958961207827575 81694993792438441811741363)
      ·
        refine ⟨122542490688657662717612045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81694993792438441811741363 122542490688657662717612045)
        ·
          refine ⟨45953434008246623519104517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122542490688657662717612045 45953434008246623519104517)
          ·
            refine ⟨8616268876546241909832097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45953434008246623519104517 8616268876546241909832097)
            ·
              refine ⟨6462201657409681432374073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616268876546241909832097 6462201657409681432374073)
              ·
                refine ⟨4846651243057261074280555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6462201657409681432374073 4846651243057261074280555)
                ·
                  refine ⟨7269976864585891611420833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846651243057261074280555 7269976864585891611420833)
                  ·
                    refine ⟨5452482648439418708565625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7269976864585891611420833 5452482648439418708565625)
                    ·
                      refine ⟨4089361986329564031424219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452482648439418708565625 4089361986329564031424219)
                      ·
                        rfl

theorem cell23_7964004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_7964004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964004 prefixEnd_7964004 := by exact prefixLift 7964004
  have htrace : WordTrace (prefixWord ++ tailWord_7964004) baseStart_7964004 baseEnd_7964004 := by
    simpa [prefixWord, tailWord_7964004, baseEnd_7964004] using wordTrace_append hprefix tailTrace_7964004
  have hstable : (prefixWord ++ tailWord_7964004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964004).length < 2 ^ (prefixWord ++ tailWord_7964004).sum := by decide
  have hdescent : baseEnd_7964004 < baseStart_7964004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964013 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7964013 : Nat := 118140960795 + 7964013 * 2 ^ 59
def prefixEnd_7964013 : Nat := 4983230072969 + 3 ^ 40 * 7964013 * 2
def baseEnd_7964013 : Nat := 4089366607655454496211677

theorem tailTrace_7964013 : CollatzResearch.WordTrace tailWord_7964013 prefixEnd_7964013 4089366607655454496211677 := by
  unfold tailWord_7964013
  simp only [CollatzResearch.WordTrace]
  refine ⟨290471417296748520978824693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193647611531165680652549795 290471417296748520978824693)
  ·
    refine ⟨27231695371570173841764815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290471417296748520978824693 27231695371570173841764815)
    ·
      refine ⟨40847543057355260762647223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231695371570173841764815 40847543057355260762647223)
      ·
        refine ⟨61271314586032891143970835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40847543057355260762647223 61271314586032891143970835)
        ·
          refine ⟨91906971879049336715956253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61271314586032891143970835 91906971879049336715956253)
          ·
            refine ⟨34465114454643501268483595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91906971879049336715956253 34465114454643501268483595)
            ·
              refine ⟨51697671681965251902725393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34465114454643501268483595 51697671681965251902725393)
              ·
                refine ⟨38773253761473938927044045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51697671681965251902725393 38773253761473938927044045)
                ·
                  refine ⟨14539970160552727097641517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38773253761473938927044045 14539970160552727097641517)
                  ·
                    refine ⟨5452488810207272661615569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14539970160552727097641517 5452488810207272661615569)
                    ·
                      refine ⟨4089366607655454496211677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452488810207272661615569 4089366607655454496211677)
                      ·
                        rfl

theorem cell23_7964013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7964013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964013 prefixEnd_7964013 := by exact prefixLift 7964013
  have htrace : WordTrace (prefixWord ++ tailWord_7964013) baseStart_7964013 baseEnd_7964013 := by
    simpa [prefixWord, tailWord_7964013, baseEnd_7964013] using wordTrace_append hprefix tailTrace_7964013
  have hstable : (prefixWord ++ tailWord_7964013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964013).length < 2 ^ (prefixWord ++ tailWord_7964013).sum := by decide
  have hdescent : baseEnd_7964013 < baseStart_7964013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_7964026 : Nat := 118140960795 + 7964026 * 2 ^ 59
def prefixEnd_7964026 : Nat := 4983230072969 + 3 ^ 40 * 7964026 * 2
def baseEnd_7964026 : Nat := 4089373282903962945349117

theorem tailTrace_7964026 : CollatzResearch.WordTrace tailWord_7964026 prefixEnd_7964026 4089373282903962945349117 := by
  unfold tailWord_7964026
  simp only [CollatzResearch.WordTrace]
  refine ⟨72617972861425356049761983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193647927630467616132698621 72617972861425356049761983)
  ·
    refine ⟨108926959292138034074642975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72617972861425356049761983 108926959292138034074642975)
    ·
      refine ⟨163390438938207051111964463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108926959292138034074642975 163390438938207051111964463)
      ·
        refine ⟨245085658407310576667946695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163390438938207051111964463 245085658407310576667946695)
        ·
          refine ⟨367628487610965865001920043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245085658407310576667946695 367628487610965865001920043)
          ·
            refine ⟨551442731416448797502880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367628487610965865001920043 551442731416448797502880065)
            ·
              refine ⟨413582048562336598127160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551442731416448797502880065 413582048562336598127160049)
              ·
                refine ⟨310186536421752448595370037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413582048562336598127160049 310186536421752448595370037)
                ·
                  refine ⟨29079987789539292055815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310186536421752448595370037 29079987789539292055815941)
                  ·
                    refine ⟨5452497710538617260465489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29079987789539292055815941 5452497710538617260465489)
                    ·
                      refine ⟨4089373282903962945349117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452497710538617260465489 4089373282903962945349117)
                      ·
                        rfl

theorem cell23_7964026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_7964026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964026 prefixEnd_7964026 := by exact prefixLift 7964026
  have htrace : WordTrace (prefixWord ++ tailWord_7964026) baseStart_7964026 baseEnd_7964026 := by
    simpa [prefixWord, tailWord_7964026, baseEnd_7964026] using wordTrace_append hprefix tailTrace_7964026
  have hstable : (prefixWord ++ tailWord_7964026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964026).length < 2 ^ (prefixWord ++ tailWord_7964026).sum := by decide
  have hdescent : baseEnd_7964026 < baseStart_7964026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964043 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 4, 2, 2]
def baseStart_7964043 : Nat := 118140960795 + 7964043 * 2 ^ 59
def prefixEnd_7964043 : Nat := 4983230072969 + 3 ^ 40 * 7964043 * 2
def baseEnd_7964043 : Nat := 4089382012075089378836539

theorem tailTrace_7964043 : CollatzResearch.WordTrace tailWord_7964043 prefixEnd_7964043 4089382012075089378836539 := by
  unfold tailWord_7964043
  simp only [CollatzResearch.WordTrace]
  refine ⟨290472511486639836102416783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193648340991093224068277855 290472511486639836102416783)
  ·
    refine ⟨435708767229959754153625175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290472511486639836102416783 435708767229959754153625175)
    ·
      refine ⟨653563150844939631230437763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435708767229959754153625175 653563150844939631230437763)
      ·
        refine ⟨980344726267409446845656645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653563150844939631230437763 980344726267409446845656645)
        ·
          refine ⟨183814636175139271283560621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 980344726267409446845656645 183814636175139271283560621)
          ·
            refine ⟨68930488565677226731335233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183814636175139271283560621 68930488565677226731335233)
            ·
              refine ⟨51697866424257920048501425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68930488565677226731335233 51697866424257920048501425)
              ·
                refine ⟨38773399818193440036376069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51697866424257920048501425 38773399818193440036376069)
                ·
                  refine ⟨7270012465911270006820513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38773399818193440036376069 7270012465911270006820513)
                  ·
                    refine ⟨5452509349433452505115385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270012465911270006820513 5452509349433452505115385)
                    ·
                      refine ⟨4089382012075089378836539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452509349433452505115385 4089382012075089378836539)
                      ·
                        rfl

theorem cell23_7964043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 2, 2].length) (baseStart_7964043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964043 prefixEnd_7964043 := by exact prefixLift 7964043
  have htrace : WordTrace (prefixWord ++ tailWord_7964043) baseStart_7964043 baseEnd_7964043 := by
    simpa [prefixWord, tailWord_7964043, baseEnd_7964043] using wordTrace_append hprefix tailTrace_7964043
  have hstable : (prefixWord ++ tailWord_7964043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964043).length < 2 ^ (prefixWord ++ tailWord_7964043).sum := by decide
  have hdescent : baseEnd_7964043 < baseStart_7964043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964066 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_7964066 : Nat := 118140960795 + 7964066 * 2 ^ 59
def prefixEnd_7964066 : Nat := 4983230072969 + 3 ^ 40 * 7964066 * 2
def baseEnd_7964066 : Nat := 454377091347793643205437

theorem tailTrace_7964066 : CollatzResearch.WordTrace tailWord_7964066 prefixEnd_7964066 454377091347793643205437 := by
  unfold tailWord_7964066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72618337591389127757626013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193648900243704340687002701 72618337591389127757626013)
  ·
    refine ⟨27231876596770922909109755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72618337591389127757626013 27231876596770922909109755)
    ·
      refine ⟨40847814895156384363664633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27231876596770922909109755 40847814895156384363664633)
      ·
        refine ⟨30635861171367288272748475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40847814895156384363664633 30635861171367288272748475)
        ·
          refine ⟨45953791757050932409122713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30635861171367288272748475 45953791757050932409122713)
          ·
            refine ⟨34465343817788199306842035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45953791757050932409122713 34465343817788199306842035)
            ·
              refine ⟨51698015726682298960263053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34465343817788199306842035 51698015726682298960263053)
              ·
                refine ⟨19386755897505862110098645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51698015726682298960263053 19386755897505862110098645)
                ·
                  refine ⟨454377091347793643205437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19386755897505862110098645 454377091347793643205437)
                  ·
                    rfl

theorem cell23_7964066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_7964066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964066 prefixEnd_7964066 := by exact prefixLift 7964066
  have htrace : WordTrace (prefixWord ++ tailWord_7964066) baseStart_7964066 baseEnd_7964066 := by
    simpa [prefixWord, tailWord_7964066, baseEnd_7964066] using wordTrace_append hprefix tailTrace_7964066
  have hstable : (prefixWord ++ tailWord_7964066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964066).length < 2 ^ (prefixWord ++ tailWord_7964066).sum := by decide
  have hdescent : baseEnd_7964066 < baseStart_7964066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964076 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_7964076 : Nat := 118140960795 + 7964076 * 2 ^ 59
def prefixEnd_7964076 : Nat := 4983230072969 + 3 ^ 40 * 7964076 * 2
def baseEnd_7964076 : Nat := 4089398956936687749723887

theorem tailTrace_7964076 : CollatzResearch.WordTrace tailWord_7964076 prefixEnd_7964076 4089398956936687749723887 := by
  unfold tailWord_7964076
  simp only [CollatzResearch.WordTrace]
  refine ⟨145236857547760141369184041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193649143397013521825578721 145236857547760141369184041)
  ·
    refine ⟨108927643160820106026888031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145236857547760141369184041 108927643160820106026888031)
    ·
      refine ⟨163391464741230159040332047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108927643160820106026888031 163391464741230159040332047)
      ·
        refine ⟨245087197111845238560498071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163391464741230159040332047 245087197111845238560498071)
        ·
          refine ⟨367630795667767857840747107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245087197111845238560498071 367630795667767857840747107)
          ·
            refine ⟨551446193501651786761120661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367630795667767857840747107 551446193501651786761120661)
            ·
              refine ⟨25849040320389927504427531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 551446193501651786761120661 25849040320389927504427531)
              ·
                refine ⟨38773560480584891256641297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25849040320389927504427531 38773560480584891256641297)
                ·
                  refine ⟨29080170360438668442480973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38773560480584891256641297 29080170360438668442480973)
                  ·
                    refine ⟨10905063885164500665930365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29080170360438668442480973 10905063885164500665930365)
                    ·
                      refine ⟨4089398956936687749723887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905063885164500665930365 4089398956936687749723887)
                      ·
                        rfl

theorem cell23_7964076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_7964076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964076 prefixEnd_7964076 := by exact prefixLift 7964076
  have htrace : WordTrace (prefixWord ++ tailWord_7964076) baseStart_7964076 baseEnd_7964076 := by
    simpa [prefixWord, tailWord_7964076, baseEnd_7964076] using wordTrace_append hprefix tailTrace_7964076
  have hstable : (prefixWord ++ tailWord_7964076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964076).length < 2 ^ (prefixWord ++ tailWord_7964076).sum := by decide
  have hdescent : baseEnd_7964076 < baseStart_7964076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964077 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7964077 : Nat := 118140960795 + 7964077 * 2 ^ 59
def prefixEnd_7964077 : Nat := 4983230072969 + 3 ^ 40 * 7964077 * 2
def baseEnd_7964077 : Nat := 4089399470417342245811383

theorem tailTrace_7964077 : CollatzResearch.WordTrace tailWord_7964077 prefixEnd_7964077 4089399470417342245811383 := by
  unfold tailWord_7964077
  simp only [CollatzResearch.WordTrace]
  refine ⟨290473751568516659909154485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193649167712344439939436323 290473751568516659909154485)
  ·
    refine ⟨27231914209548436866483233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290473751568516659909154485 27231914209548436866483233)
    ·
      refine ⟨20423935657161327649862425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27231914209548436866483233 20423935657161327649862425)
      ·
        refine ⟨15317951742870995737396819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20423935657161327649862425 15317951742870995737396819)
        ·
          refine ⟨22976927614306493606095229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317951742870995737396819 22976927614306493606095229)
          ·
            refine ⟨8616347855364935102285711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22976927614306493606095229 8616347855364935102285711)
            ·
              refine ⟨12924521783047402653428567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8616347855364935102285711 12924521783047402653428567)
              ·
                refine ⟨19386782674571103980142851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924521783047402653428567 19386782674571103980142851)
                ·
                  refine ⟨29080174011856655970214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19386782674571103980142851 29080174011856655970214277)
                  ·
                    refine ⟨5452532627223122994415177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29080174011856655970214277 5452532627223122994415177)
                    ·
                      refine ⟨4089399470417342245811383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452532627223122994415177 4089399470417342245811383)
                      ·
                        rfl

theorem cell23_7964077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7964077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964077 prefixEnd_7964077 := by exact prefixLift 7964077
  have htrace : WordTrace (prefixWord ++ tailWord_7964077) baseStart_7964077 baseEnd_7964077 := by
    simpa [prefixWord, tailWord_7964077, baseEnd_7964077] using wordTrace_append hprefix tailTrace_7964077
  have hstable : (prefixWord ++ tailWord_7964077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964077).length < 2 ^ (prefixWord ++ tailWord_7964077).sum := by decide
  have hdescent : baseEnd_7964077 < baseStart_7964077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964100 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 5]
def baseStart_7964100 : Nat := 118140960795 + 7964100 * 2 ^ 59
def prefixEnd_7964100 : Nat := 4983230072969 + 3 ^ 40 * 7964100 * 2
def baseEnd_7964100 : Nat := 454379031163599517313753

theorem tailTrace_7964100 : CollatzResearch.WordTrace tailWord_7964100 prefixEnd_7964100 454379031163599517313753 := by
  unfold tailWord_7964100
  simp only [CollatzResearch.WordTrace]
  refine ⟨145237295223716667418620877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193649726964955556558161169 145237295223716667418620877)
  ·
    refine ⟨54463985708893750281982829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145237295223716667418620877 54463985708893750281982829)
    ·
      refine ⟨20423994640835156355743561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54463985708893750281982829 20423994640835156355743561)
      ·
        refine ⟨15317995980626367266807671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20423994640835156355743561 15317995980626367266807671)
        ·
          refine ⟨22976993970939550900211507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15317995980626367266807671 22976993970939550900211507)
          ·
            refine ⟨34465490956409326350317261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22976993970939550900211507 34465490956409326350317261)
            ·
              refine ⟨12924559108653497381368973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34465490956409326350317261 12924559108653497381368973)
              ·
                refine ⟨4846709665745061518013365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12924559108653497381368973 4846709665745061518013365)
                ·
                  refine ⟨454379031163599517313753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846709665745061518013365 454379031163599517313753)
                  ·
                    rfl

theorem cell23_7964100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_7964100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964100 prefixEnd_7964100 := by exact prefixLift 7964100
  have htrace : WordTrace (prefixWord ++ tailWord_7964100) baseStart_7964100 baseEnd_7964100 := by
    simpa [prefixWord, tailWord_7964100, baseEnd_7964100] using wordTrace_append hprefix tailTrace_7964100
  have hstable : (prefixWord ++ tailWord_7964100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964100).length < 2 ^ (prefixWord ++ tailWord_7964100).sum := by decide
  have hdescent : baseEnd_7964100 < baseStart_7964100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964139 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 10]
def baseStart_7964139 : Nat := 118140960795 + 7964139 * 2 ^ 59
def prefixEnd_7964139 : Nat := 4983230072969 + 3 ^ 40 * 7964139 * 2
def baseEnd_7964139 : Nat := 454381256246435667026233

theorem tailTrace_7964139 : CollatzResearch.WordTrace tailWord_7964139 prefixEnd_7964139 454381256246435667026233 := by
  unfold tailWord_7964139
  simp only [CollatzResearch.WordTrace]
  refine ⟨290476012894292044497911471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193650675262861362998607647 290476012894292044497911471)
  ·
    refine ⟨435714019341438066746867207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290476012894292044497911471 435714019341438066746867207)
    ·
      refine ⟨653571029012157100120300811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435714019341438066746867207 653571029012157100120300811)
      ·
        refine ⟨980356543518235650180451217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653571029012157100120300811 980356543518235650180451217)
        ·
          refine ⟨735267407638676737635338413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980356543518235650180451217 735267407638676737635338413)
          ·
            refine ⟨275725277864503776613251905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735267407638676737635338413 275725277864503776613251905)
            ·
              refine ⟨206793958398377832459938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275725277864503776613251905 206793958398377832459938929)
              ·
                refine ⟨155095468798783374344954197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206793958398377832459938929 155095468798783374344954197)
                ·
                  refine ⟨454381256246435667026233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155095468798783374344954197 454381256246435667026233)
                  ·
                    rfl

theorem cell23_7964139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_7964139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964139 prefixEnd_7964139 := by exact prefixLift 7964139
  have htrace : WordTrace (prefixWord ++ tailWord_7964139) baseStart_7964139 baseEnd_7964139 := by
    simpa [prefixWord, tailWord_7964139, baseEnd_7964139] using wordTrace_append hprefix tailTrace_7964139
  have hstable : (prefixWord ++ tailWord_7964139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964139).length < 2 ^ (prefixWord ++ tailWord_7964139).sum := by decide
  have hdescent : baseEnd_7964139 < baseStart_7964139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964150 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7964150 : Nat := 118140960795 + 7964150 * 2 ^ 59
def prefixEnd_7964150 : Nat := 4983230072969 + 3 ^ 40 * 7964150 * 2
def baseEnd_7964150 : Nat := 4089436954505120460198547

theorem tailTrace_7964150 : CollatzResearch.WordTrace tailWord_7964150 prefixEnd_7964150 4089436954505120460198547 := by
  unfold tailWord_7964150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18154775881078262086035119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193650942731501462251041269 18154775881078262086035119)
  ·
    refine ⟨27232163821617393129052679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18154775881078262086035119 27232163821617393129052679)
    ·
      refine ⟨40848245732426089693579019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27232163821617393129052679 40848245732426089693579019)
      ·
        refine ⟨61272368598639134540368529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848245732426089693579019 61272368598639134540368529)
        ·
          refine ⟨45954276448979350905276397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61272368598639134540368529 45954276448979350905276397)
          ·
            refine ⟨17232853668367256589478649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45954276448979350905276397 17232853668367256589478649)
            ·
              refine ⟨12924640251275442442108987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232853668367256589478649 12924640251275442442108987)
              ·
                refine ⟨19386960376913163663163481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924640251275442442108987 19386960376913163663163481)
                ·
                  refine ⟨14540220282684872747372611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19386960376913163663163481 14540220282684872747372611)
                  ·
                    refine ⟨21810330424027309121058917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14540220282684872747372611 21810330424027309121058917)
                    ·
                      refine ⟨4089436954505120460198547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21810330424027309121058917 4089436954505120460198547)
                      ·
                        rfl

theorem cell23_7964150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7964150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964150 prefixEnd_7964150 := by exact prefixLift 7964150
  have htrace : WordTrace (prefixWord ++ tailWord_7964150) baseStart_7964150 baseEnd_7964150 := by
    simpa [prefixWord, tailWord_7964150, baseEnd_7964150] using wordTrace_append hprefix tailTrace_7964150
  have hstable : (prefixWord ++ tailWord_7964150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964150).length < 2 ^ (prefixWord ++ tailWord_7964150).sum := by decide
  have hdescent : baseEnd_7964150 < baseStart_7964150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964217 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7964217 : Nat := 118140960795 + 7964217 * 2 ^ 59
def prefixEnd_7964217 : Nat := 4983230072969 + 3 ^ 40 * 7964217 * 2
def baseEnd_7964217 : Nat := 4089471357708971698060739

theorem tailTrace_7964217 : CollatzResearch.WordTrace tailWord_7964217 prefixEnd_7964217 4089471357708971698060739 := by
  unfold tailWord_7964217
  simp only [CollatzResearch.WordTrace]
  refine ⟨290478857788009463819250905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193652571858672975879500603 290478857788009463819250905)
  ·
    refine ⟨217859143341007097864438179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290478857788009463819250905 217859143341007097864438179)
    ·
      refine ⟨326788715011510646796657269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217859143341007097864438179 326788715011510646796657269)
      ·
        refine ⟨30636442032329123137186619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326788715011510646796657269 30636442032329123137186619)
        ·
          refine ⟨45954663048493684705779929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30636442032329123137186619 45954663048493684705779929)
          ·
            refine ⟨34465997286370263529334947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45954663048493684705779929 34465997286370263529334947)
            ·
              refine ⟨51698995929555395294002421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34465997286370263529334947 51698995929555395294002421)
              ·
                refine ⟨4846780868395818308812727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51698995929555395294002421 4846780868395818308812727)
                ·
                  refine ⟨7270171302593727463219091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846780868395818308812727 7270171302593727463219091)
                  ·
                    refine ⟨10905256953890591194828637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270171302593727463219091 10905256953890591194828637)
                    ·
                      refine ⟨4089471357708971698060739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905256953890591194828637 4089471357708971698060739)
                      ·
                        rfl

theorem cell23_7964217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7964217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964217 prefixEnd_7964217 := by exact prefixLift 7964217
  have htrace : WordTrace (prefixWord ++ tailWord_7964217) baseStart_7964217 baseEnd_7964217 := by
    simpa [prefixWord, tailWord_7964217, baseEnd_7964217] using wordTrace_append hprefix tailTrace_7964217
  have hstable : (prefixWord ++ tailWord_7964217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964217).length < 2 ^ (prefixWord ++ tailWord_7964217).sum := by decide
  have hdescent : baseEnd_7964217 < baseStart_7964217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964220 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_7964220 : Nat := 118140960795 + 7964220 * 2 ^ 59
def prefixEnd_7964220 : Nat := 4983230072969 + 3 ^ 40 * 7964220 * 2
def baseEnd_7964220 : Nat := 1363157632716978395441075

theorem tailTrace_7964220 : CollatzResearch.WordTrace tailWord_7964220 prefixEnd_7964220 1363157632716978395441075 := by
  unfold tailWord_7964220
  simp only [CollatzResearch.WordTrace]
  refine ⟨145239483603499297665805057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193652644804665730221073409 145239483603499297665805057)
  ·
    refine ⟨108929612702624473249353793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145239483603499297665805057 108929612702624473249353793)
    ·
      refine ⟨81697209526968354937015345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108929612702624473249353793 81697209526968354937015345)
      ·
        refine ⟨61272907145226266202761509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81697209526968354937015345 61272907145226266202761509)
        ·
          refine ⟨11488670089729924913017783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61272907145226266202761509 11488670089729924913017783)
          ·
            refine ⟨17233005134594887369526675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488670089729924913017783 17233005134594887369526675)
            ·
              refine ⟨25849507701892331054290013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233005134594887369526675 25849507701892331054290013)
              ·
                refine ⟨9693565388209624145358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25849507701892331054290013 9693565388209624145358755)
                ·
                  refine ⟨14540348082314436218038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693565388209624145358755 14540348082314436218038133)
                  ·
                    refine ⟨1363157632716978395441075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14540348082314436218038133 1363157632716978395441075)
                    ·
                      rfl

theorem cell23_7964220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_7964220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964220 prefixEnd_7964220 := by exact prefixLift 7964220
  have htrace : WordTrace (prefixWord ++ tailWord_7964220) baseStart_7964220 baseEnd_7964220 := by
    simpa [prefixWord, tailWord_7964220, baseEnd_7964220] using wordTrace_append hprefix tailTrace_7964220
  have hstable : (prefixWord ++ tailWord_7964220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964220).length < 2 ^ (prefixWord ++ tailWord_7964220).sum := by decide
  have hdescent : baseEnd_7964220 < baseStart_7964220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964260 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_7964260 : Nat := 118140960795 + 7964260 * 2 ^ 59
def prefixEnd_7964260 : Nat := 4983230072969 + 3 ^ 40 * 7964260 * 2
def baseEnd_7964260 : Nat := 4089493437377115029823041

theorem tailTrace_7964260 : CollatzResearch.WordTrace tailWord_7964260 prefixEnd_7964260 4089493437377115029823041 := by
  unfold tailWord_7964260
  simp only [CollatzResearch.WordTrace]
  refine ⟨145240213063426841081533117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193653617417902454775377489 145240213063426841081533117)
  ·
    refine ⟨54465079898785065405574919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145240213063426841081533117 54465079898785065405574919)
    ·
      refine ⟨81697619848177598108362379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54465079898785065405574919 81697619848177598108362379)
      ·
        refine ⟨122546429772266397162543569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81697619848177598108362379 122546429772266397162543569)
        ·
          refine ⟨91909822329199797871907677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122546429772266397162543569 91909822329199797871907677)
          ·
            refine ⟨34466183373449924201965379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91909822329199797871907677 34466183373449924201965379)
            ·
              refine ⟨51699275060174886302948069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34466183373449924201965379 51699275060174886302948069)
              ·
                refine ⟨9693614073782791181802763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51699275060174886302948069 9693614073782791181802763)
                ·
                  refine ⟨14540421110674186772704145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693614073782791181802763 14540421110674186772704145)
                  ·
                    refine ⟨10905315833005640079528109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14540421110674186772704145 10905315833005640079528109)
                    ·
                      refine ⟨4089493437377115029823041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905315833005640079528109 4089493437377115029823041)
                      ·
                        rfl

theorem cell23_7964260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_7964260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964260 prefixEnd_7964260 := by exact prefixLift 7964260
  have htrace : WordTrace (prefixWord ++ tailWord_7964260) baseStart_7964260 baseEnd_7964260 := by
    simpa [prefixWord, tailWord_7964260, baseEnd_7964260] using wordTrace_append hprefix tailTrace_7964260
  have hstable : (prefixWord ++ tailWord_7964260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964260).length < 2 ^ (prefixWord ++ tailWord_7964260).sum := by decide
  have hdescent : baseEnd_7964260 < baseStart_7964260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964263 : List Nat := [1, 1, 5, 1, 1, 1, 6, 7]
def baseStart_7964263 : Nat := 118140960795 + 7964263 * 2 ^ 59
def prefixEnd_7964263 : Nat := 4983230072969 + 3 ^ 40 * 7964263 * 2
def baseEnd_7964263 : Nat := 151462776956262167336501

theorem tailTrace_7964263 : CollatzResearch.WordTrace tailWord_7964263 prefixEnd_7964263 151462776956262167336501 := by
  unfold tailWord_7964263
  simp only [CollatzResearch.WordTrace]
  refine ⟨290480535545842813675425443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193653690363895209116950295 290480535545842813675425443)
  ·
    refine ⟨435720803318764220513138165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290480535545842813675425443 435720803318764220513138165)
    ·
      refine ⟨40848825311134145673106703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435720803318764220513138165 40848825311134145673106703)
      ·
        refine ⟨61273237966701218509660055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848825311134145673106703 61273237966701218509660055)
        ·
          refine ⟨91909856950051827764490083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273237966701218509660055 91909856950051827764490083)
          ·
            refine ⟨137864785425077741646735125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91909856950051827764490083 137864785425077741646735125)
            ·
              refine ⟨6462411816800519139690709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137864785425077741646735125 6462411816800519139690709)
              ·
                refine ⟨151462776956262167336501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6462411816800519139690709 151462776956262167336501)
                ·
                  rfl

theorem cell23_7964263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 7].length) (baseStart_7964263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964263 prefixEnd_7964263 := by exact prefixLift 7964263
  have htrace : WordTrace (prefixWord ++ tailWord_7964263) baseStart_7964263 baseEnd_7964263 := by
    simpa [prefixWord, tailWord_7964263, baseEnd_7964263] using wordTrace_append hprefix tailTrace_7964263
  have hstable : (prefixWord ++ tailWord_7964263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964263).length < 2 ^ (prefixWord ++ tailWord_7964263).sum := by decide
  have hdescent : baseEnd_7964263 < baseStart_7964263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964273 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_7964273 : Nat := 118140960795 + 7964273 * 2 ^ 59
def prefixEnd_7964273 : Nat := 4983230072969 + 3 ^ 40 * 7964273 * 2
def baseEnd_7964273 : Nat := 4089500112625623478960481

theorem tailTrace_7964273 : CollatzResearch.WordTrace tailWord_7964273 prefixEnd_7964273 4089500112625623478960481 := by
  unfold tailWord_7964273
  simp only [CollatzResearch.WordTrace]
  refine ⟨290480900275806585383289473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193653933517204390255526315 290480900275806585383289473)
  ·
    refine ⟨217860675206854939037467105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290480900275806585383289473 217860675206854939037467105)
    ·
      refine ⟨163395506405141204278100329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217860675206854939037467105 163395506405141204278100329)
      ·
        refine ⟨122546629803855903208575247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163395506405141204278100329 122546629803855903208575247)
        ·
          refine ⟨183819944705783854812862871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122546629803855903208575247 183819944705783854812862871)
          ·
            refine ⟨275729917058675782219294307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183819944705783854812862871 275729917058675782219294307)
            ·
              refine ⟨413594875588013673328941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275729917058675782219294307 413594875588013673328941461)
              ·
                refine ⟨19387259793188140937294131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413594875588013673328941461 19387259793188140937294131)
                ·
                  refine ⟨29080889689782211405941197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19387259793188140937294131 29080889689782211405941197)
                  ·
                    refine ⟨10905333633668329277227949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29080889689782211405941197 10905333633668329277227949)
                    ·
                      refine ⟨4089500112625623478960481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905333633668329277227949 4089500112625623478960481)
                      ·
                        rfl

theorem cell23_7964273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_7964273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964273 prefixEnd_7964273 := by exact prefixLift 7964273
  have htrace : WordTrace (prefixWord ++ tailWord_7964273) baseStart_7964273 baseEnd_7964273 := by
    simpa [prefixWord, tailWord_7964273, baseEnd_7964273] using wordTrace_append hprefix tailTrace_7964273
  have hstable : (prefixWord ++ tailWord_7964273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964273).length < 2 ^ (prefixWord ++ tailWord_7964273).sum := by decide
  have hdescent : baseEnd_7964273 < baseStart_7964273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964277 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7964277 : Nat := 118140960795 + 7964277 * 2 ^ 59
def prefixEnd_7964277 : Nat := 4983230072969 + 3 ^ 40 * 7964277 * 2
def baseEnd_7964277 : Nat := 4089502166548241463310463

theorem tailTrace_7964277 : CollatzResearch.WordTrace tailWord_7964277 prefixEnd_7964277 4089502166548241463310463 := by
  unfold tailWord_7964277
  simp only [CollatzResearch.WordTrace]
  refine ⟨290481046167792094066435085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193654030778528062710956723 290481046167792094066435085)
  ·
    refine ⟨108930392312922035274913157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290481046167792094066435085 108930392312922035274913157)
    ·
      refine ⟨20424448558672881614046217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108930392312922035274913157 20424448558672881614046217)
      ·
        refine ⟨15318336419004661210534663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20424448558672881614046217 15318336419004661210534663)
        ·
          refine ⟨22977504628506991815801995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318336419004661210534663 22977504628506991815801995)
          ·
            refine ⟨34466256942760487723702993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22977504628506991815801995 34466256942760487723702993)
            ·
              refine ⟨25849692707070365792777245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34466256942760487723702993 25849692707070365792777245)
              ·
                refine ⟨9693634765151387172291467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25849692707070365792777245 9693634765151387172291467)
                ·
                  refine ⟨14540452147727080758437201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693634765151387172291467 14540452147727080758437201)
                  ·
                    refine ⟨10905339110795310568827901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14540452147727080758437201 10905339110795310568827901)
                    ·
                      refine ⟨4089502166548241463310463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905339110795310568827901 4089502166548241463310463)
                      ·
                        rfl

theorem cell23_7964277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7964277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964277 prefixEnd_7964277 := by exact prefixLift 7964277
  have htrace : WordTrace (prefixWord ++ tailWord_7964277) baseStart_7964277 baseEnd_7964277 := by
    simpa [prefixWord, tailWord_7964277, baseEnd_7964277] using wordTrace_append hprefix tailTrace_7964277
  have hstable : (prefixWord ++ tailWord_7964277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964277).length < 2 ^ (prefixWord ++ tailWord_7964277).sum := by decide
  have hdescent : baseEnd_7964277 < baseStart_7964277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964300 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_7964300 : Nat := 118140960795 + 7964300 * 2 ^ 59
def prefixEnd_7964300 : Nat := 4983230072969 + 3 ^ 40 * 7964300 * 2
def baseEnd_7964300 : Nat := 4089513976603294873322857

theorem tailTrace_7964300 : CollatzResearch.WordTrace tailWord_7964300 prefixEnd_7964300 4089513976603294873322857 := by
  unfold tailWord_7964300
  simp only [CollatzResearch.WordTrace]
  refine ⟨145240942523354384497261177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193654590031139179329681569 145240942523354384497261177)
  ·
    refine ⟨108930706892515788372945883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145240942523354384497261177 108930706892515788372945883)
    ·
      refine ⟨163396060338773682559418825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108930706892515788372945883 163396060338773682559418825)
      ·
        refine ⟨122547045254080261919564119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163396060338773682559418825 122547045254080261919564119)
        ·
          refine ⟨183820567881120392879346179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122547045254080261919564119 183820567881120392879346179)
          ·
            refine ⟨275730851821680589319019269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183820567881120392879346179 275730851821680589319019269)
            ·
              refine ⟨51699534716565110497316113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275730851821680589319019269 51699534716565110497316113)
              ·
                refine ⟨38774651037423832872987085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51699534716565110497316113 38774651037423832872987085)
                ·
                  refine ⟨14540494139033937327370157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38774651037423832872987085 14540494139033937327370157)
                  ·
                    refine ⟨5452685302137726497763809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14540494139033937327370157 5452685302137726497763809)
                    ·
                      refine ⟨4089513976603294873322857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452685302137726497763809 4089513976603294873322857)
                      ·
                        rfl

theorem cell23_7964300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_7964300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964300 prefixEnd_7964300 := by exact prefixLift 7964300
  have htrace : WordTrace (prefixWord ++ tailWord_7964300) baseStart_7964300 baseEnd_7964300 := by
    simpa [prefixWord, tailWord_7964300, baseEnd_7964300] using wordTrace_append hprefix tailTrace_7964300
  have hstable : (prefixWord ++ tailWord_7964300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964300).length < 2 ^ (prefixWord ++ tailWord_7964300).sum := by decide
  have hdescent : baseEnd_7964300 < baseStart_7964300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964328 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7964328 : Nat := 118140960795 + 7964328 * 2 ^ 59
def prefixEnd_7964328 : Nat := 4983230072969 + 3 ^ 40 * 7964328 * 2
def baseEnd_7964328 : Nat := 4089528354061620763772729

theorem tailTrace_7964328 : CollatzResearch.WordTrace tailWord_7964328 prefixEnd_7964328 4089528354061620763772729 := by
  unfold tailWord_7964328
  simp only [CollatzResearch.WordTrace]
  refine ⟨145241453145303664888270819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193655270860404886517694425 145241453145303664888270819)
  ·
    refine ⟨217862179717955497332406229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145241453145303664888270819 217862179717955497332406229)
    ·
      refine ⟨5106144837139581968728271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 217862179717955497332406229 5106144837139581968728271)
      ·
        refine ⟨7659217255709372953092407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106144837139581968728271 7659217255709372953092407)
        ·
          refine ⟨11488825883564059429638611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659217255709372953092407 11488825883564059429638611)
          ·
            refine ⟨17233238825346089144457917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488825883564059429638611 17233238825346089144457917)
            ·
              refine ⟨6462464559504783429171719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17233238825346089144457917 6462464559504783429171719)
              ·
                refine ⟨9693696839257175143757579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462464559504783429171719 9693696839257175143757579)
                ·
                  refine ⟨14540545258885762715636369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693696839257175143757579 14540545258885762715636369)
                  ·
                    refine ⟨10905408944164322036727277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14540545258885762715636369 10905408944164322036727277)
                    ·
                      refine ⟨4089528354061620763772729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905408944164322036727277 4089528354061620763772729)
                      ·
                        rfl

theorem cell23_7964328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7964328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964328 prefixEnd_7964328 := by exact prefixLift 7964328
  have htrace : WordTrace (prefixWord ++ tailWord_7964328) baseStart_7964328 baseEnd_7964328 := by
    simpa [prefixWord, tailWord_7964328, baseEnd_7964328] using wordTrace_append hprefix tailTrace_7964328
  have hstable : (prefixWord ++ tailWord_7964328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964328).length < 2 ^ (prefixWord ++ tailWord_7964328).sum := by decide
  have hdescent : baseEnd_7964328 < baseStart_7964328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964350 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_7964350 : Nat := 118140960795 + 7964350 * 2 ^ 59
def prefixEnd_7964350 : Nat := 4983230072969 + 3 ^ 40 * 7964350 * 2
def baseEnd_7964350 : Nat := 4089539650636019677697627

theorem tailTrace_7964350 : CollatzResearch.WordTrace tailWord_7964350 prefixEnd_7964350 4089539650636019677697627 := by
  unfold tailWord_7964350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36310463587065953441730313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193655805797685085022561669 36310463587065953441730313)
  ·
    refine ⟨27232847690299465081297735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36310463587065953441730313 27232847690299465081297735)
    ·
      refine ⟨40849271535449197621946603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27232847690299465081297735 40849271535449197621946603)
      ·
        refine ⟨61273907303173796432919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40849271535449197621946603 61273907303173796432919905)
        ·
          refine ⟨45955430477380347324689929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61273907303173796432919905 45955430477380347324689929)
          ·
            refine ⟨34466572858035260493517447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45955430477380347324689929 34466572858035260493517447)
            ·
              refine ⟨51699859287052890740276171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34466572858035260493517447 51699859287052890740276171)
              ·
                refine ⟨77549788930579336110414257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51699859287052890740276171 77549788930579336110414257)
                ·
                  refine ⟨58162341697934502082810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77549788930579336110414257 58162341697934502082810693)
                  ·
                    refine ⟨10905439068362719140527005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58162341697934502082810693 10905439068362719140527005)
                    ·
                      refine ⟨4089539650636019677697627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905439068362719140527005 4089539650636019677697627)
                      ·
                        rfl

theorem cell23_7964350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_7964350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964350 prefixEnd_7964350 := by exact prefixLift 7964350
  have htrace : WordTrace (prefixWord ++ tailWord_7964350) baseStart_7964350 baseEnd_7964350 := by
    simpa [prefixWord, tailWord_7964350, baseEnd_7964350] using wordTrace_append hprefix tailTrace_7964350
  have hstable : (prefixWord ++ tailWord_7964350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964350).length < 2 ^ (prefixWord ++ tailWord_7964350).sum := by decide
  have hdescent : baseEnd_7964350 < baseStart_7964350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964364 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7964364 : Nat := 118140960795 + 7964364 * 2 ^ 59
def prefixEnd_7964364 : Nat := 4983230072969 + 3 ^ 40 * 7964364 * 2
def baseEnd_7964364 : Nat := 4089546839365182622922563

theorem tailTrace_7964364 : CollatzResearch.WordTrace tailWord_7964364 prefixEnd_7964364 4089546839365182622922563 := by
  unfold tailWord_7964364
  simp only [CollatzResearch.WordTrace]
  refine ⟨145242109659238453962426073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193656146212317938616568097 145242109659238453962426073)
  ·
    refine ⟨108931582244428840471819555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145242109659238453962426073 108931582244428840471819555)
    ·
      refine ⟨163397373366643260707729333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108931582244428840471819555 163397373366643260707729333)
      ·
        refine ⟨15318503753122805691349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163397373366643260707729333 15318503753122805691349625)
        ·
          refine ⟨11488877814842104268512219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15318503753122805691349625 11488877814842104268512219)
          ·
            refine ⟨17233316722263156402768329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488877814842104268512219 17233316722263156402768329)
            ·
              refine ⟨12924987541697367302076247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233316722263156402768329 12924987541697367302076247)
              ·
                refine ⟨19387481312546050953114371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12924987541697367302076247 19387481312546050953114371)
                ·
                  refine ⟨29081221968819076429671557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19387481312546050953114371 29081221968819076429671557)
                  ·
                    refine ⟨5452729119153576830563417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29081221968819076429671557 5452729119153576830563417)
                    ·
                      refine ⟨4089546839365182622922563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452729119153576830563417 4089546839365182622922563)
                      ·
                        rfl

theorem cell23_7964364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7964364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964364 prefixEnd_7964364 := by exact prefixLift 7964364
  have htrace : WordTrace (prefixWord ++ tailWord_7964364) baseStart_7964364 baseEnd_7964364 := by
    simpa [prefixWord, tailWord_7964364, baseEnd_7964364] using wordTrace_append hprefix tailTrace_7964364
  have hstable : (prefixWord ++ tailWord_7964364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964364).length < 2 ^ (prefixWord ++ tailWord_7964364).sum := by decide
  have hdescent : baseEnd_7964364 < baseStart_7964364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964370 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_7964370 : Nat := 118140960795 + 7964370 * 2 ^ 59
def prefixEnd_7964370 : Nat := 4983230072969 + 3 ^ 40 * 7964370 * 2
def baseEnd_7964370 : Nat := 454394435583234399938615

theorem tailTrace_7964370 : CollatzResearch.WordTrace tailWord_7964370 prefixEnd_7964370 454394435583234399938615 := by
  unfold tailWord_7964370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72621109539113792737392641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193656292104303447299713709 72621109539113792737392641)
  ·
    refine ⟨54465832154335344553044481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72621109539113792737392641 54465832154335344553044481)
    ·
      refine ⟨40849374115751508414783361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54465832154335344553044481 40849374115751508414783361)
      ·
        refine ⟨30637030586813631311087521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40849374115751508414783361 30637030586813631311087521)
        ·
          refine ⟨22977772940110223483315641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30637030586813631311087521 22977772940110223483315641)
          ·
            refine ⟨17233329705082667612486731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22977772940110223483315641 17233329705082667612486731)
            ·
              refine ⟨25849994557624001418730097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233329705082667612486731 25849994557624001418730097)
              ·
                refine ⟨19387495918218001064047573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25849994557624001418730097 19387495918218001064047573)
                ·
                  refine ⟨454394435583234399938615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19387495918218001064047573 454394435583234399938615)
                  ·
                    rfl

theorem cell23_7964370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_7964370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964370 prefixEnd_7964370 := by exact prefixLift 7964370
  have htrace : WordTrace (prefixWord ++ tailWord_7964370) baseStart_7964370 baseEnd_7964370 := by
    simpa [prefixWord, tailWord_7964370, baseEnd_7964370] using wordTrace_append hprefix tailTrace_7964370
  have hstable : (prefixWord ++ tailWord_7964370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964370).length < 2 ^ (prefixWord ++ tailWord_7964370).sum := by decide
  have hdescent : baseEnd_7964370 < baseStart_7964370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964383 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 7]
def baseStart_7964383 : Nat := 118140960795 + 7964383 * 2 ^ 59
def prefixEnd_7964383 : Nat := 4983230072969 + 3 ^ 40 * 7964383 * 2
def baseEnd_7964383 : Nat := 1363185531832539349528325

theorem tailTrace_7964383 : CollatzResearch.WordTrace tailWord_7964383 prefixEnd_7964383 1363185531832539349528325 := by
  unfold tailWord_7964383
  simp only [CollatzResearch.WordTrace]
  refine ⟨290484912305408074169793803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193656608203605382779862535 290484912305408074169793803)
  ·
    refine ⟨435727368458112111254690705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290484912305408074169793803 435727368458112111254690705)
    ·
      refine ⟨326795526343584083441018029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435727368458112111254690705 326795526343584083441018029)
      ·
        refine ⟨122548322378844031290381761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326795526343584083441018029 122548322378844031290381761)
        ·
          refine ⟨91911241784133023467786321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122548322378844031290381761 91911241784133023467786321)
          ·
            refine ⟨68933431338099767600839741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91911241784133023467786321 68933431338099767600839741)
            ·
              refine ⟨25850036751787412850314903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68933431338099767600839741 25850036751787412850314903)
              ·
                refine ⟨38775055127681119275472355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850036751787412850314903 38775055127681119275472355)
                ·
                  refine ⟨58162582691521678913208533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38775055127681119275472355 58162582691521678913208533)
                  ·
                    refine ⟨1363185531832539349528325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58162582691521678913208533 1363185531832539349528325)
                    ·
                      rfl

theorem cell23_7964383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_7964383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964383 prefixEnd_7964383 := by exact prefixLift 7964383
  have htrace : WordTrace (prefixWord ++ tailWord_7964383) baseStart_7964383 baseEnd_7964383 := by
    simpa [prefixWord, tailWord_7964383, baseEnd_7964383] using wordTrace_append hprefix tailTrace_7964383
  have hstable : (prefixWord ++ tailWord_7964383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964383).length < 2 ^ (prefixWord ++ tailWord_7964383).sum := by decide
  have hdescent : baseEnd_7964383 < baseStart_7964383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964404 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7964404 : Nat := 118140960795 + 7964404 * 2 ^ 59
def prefixEnd_7964404 : Nat := 4983230072969 + 3 ^ 40 * 7964404 * 2
def baseEnd_7964404 : Nat := 454396375399040274046931

theorem tailTrace_7964404 : CollatzResearch.WordTrace tailWord_7964404 prefixEnd_7964404 454396375399040274046931 := by
  unfold tailWord_7964404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145242839119165997378154133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193657118825554663170872177 145242839119165997378154133)
  ·
    refine ⟨6808258083710906127100975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145242839119165997378154133 6808258083710906127100975)
    ·
      refine ⟨10212387125566359190651463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6808258083710906127100975 10212387125566359190651463)
      ·
        refine ⟨15318580688349538785977195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212387125566359190651463 15318580688349538785977195)
        ·
          refine ⟨22977871032524308178965793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318580688349538785977195 22977871032524308178965793)
          ·
            refine ⟨17233403274393231134224345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22977871032524308178965793 17233403274393231134224345)
            ·
              refine ⟨12925052455794923350668259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233403274393231134224345 12925052455794923350668259)
              ·
                refine ⟨19387578683692385026002389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925052455794923350668259 19387578683692385026002389)
                ·
                  refine ⟨454396375399040274046931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19387578683692385026002389 454396375399040274046931)
                  ·
                    rfl

theorem cell23_7964404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7964404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964404 prefixEnd_7964404 := by exact prefixLift 7964404
  have htrace : WordTrace (prefixWord ++ tailWord_7964404) baseStart_7964404 baseEnd_7964404 := by
    simpa [prefixWord, tailWord_7964404, baseEnd_7964404] using wordTrace_append hprefix tailTrace_7964404
  have hstable : (prefixWord ++ tailWord_7964404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964404).length < 2 ^ (prefixWord ++ tailWord_7964404).sum := by decide
  have hdescent : baseEnd_7964404 < baseStart_7964404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964420 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7964420 : Nat := 118140960795 + 7964420 * 2 ^ 59
def prefixEnd_7964420 : Nat := 4983230072969 + 3 ^ 40 * 7964420 * 2
def baseEnd_7964420 : Nat := 4089575594281834403822305

theorem tailTrace_7964420 : CollatzResearch.WordTrace tailWord_7964420 prefixEnd_7964420 4089575594281834403822305 := by
  unfold tailWord_7964420
  simp only [CollatzResearch.WordTrace]
  refine ⟨145243130903137014744445357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193657507870849352992593809 145243130903137014744445357)
  ·
    refine ⟨54466174088676380529167009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145243130903137014744445357 54466174088676380529167009)
    ·
      refine ⟨40849630566507285396875257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54466174088676380529167009 40849630566507285396875257)
      ·
        refine ⟨30637222924880464047656443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40849630566507285396875257 30637222924880464047656443)
        ·
          refine ⟨45955834387320696071484665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30637222924880464047656443 45955834387320696071484665)
          ·
            refine ⟨34466875790490522053613499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45955834387320696071484665 34466875790490522053613499)
            ·
              refine ⟨51700313685735783080420249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34466875790490522053613499 51700313685735783080420249)
              ·
                refine ⟨38775235264301837310315187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51700313685735783080420249 38775235264301837310315187)
                ·
                  refine ⟨58162852896452755965472781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38775235264301837310315187 58162852896452755965472781)
                  ·
                    refine ⟨21811069836169783487052293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58162852896452755965472781 21811069836169783487052293)
                    ·
                      refine ⟨4089575594281834403822305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21811069836169783487052293 4089575594281834403822305)
                      ·
                        rfl

theorem cell23_7964420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7964420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964420 prefixEnd_7964420 := by exact prefixLift 7964420
  have htrace : WordTrace (prefixWord ++ tailWord_7964420) baseStart_7964420 baseEnd_7964420 := by
    simpa [prefixWord, tailWord_7964420, baseEnd_7964420] using wordTrace_append hprefix tailTrace_7964420
  have hstable : (prefixWord ++ tailWord_7964420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964420).length < 2 ^ (prefixWord ++ tailWord_7964420).sum := by decide
  have hdescent : baseEnd_7964420 < baseStart_7964420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964433 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_7964433 : Nat := 118140960795 + 7964433 * 2 ^ 59
def prefixEnd_7964433 : Nat := 4983230072969 + 3 ^ 40 * 7964433 * 2
def baseEnd_7964433 : Nat := 4089582269530342852959745

theorem tailTrace_7964433 : CollatzResearch.WordTrace tailWord_7964433 prefixEnd_7964433 4089582269530342852959745 := by
  unfold tailWord_7964433
  simp only [CollatzResearch.WordTrace]
  refine ⟨290486735955226932709113953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193657823970151288472742635 290486735955226932709113953)
  ·
    refine ⟨217865051966420199531835465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290486735955226932709113953 217865051966420199531835465)
    ·
      refine ⟨163398788974815149648876599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217865051966420199531835465 163398788974815149648876599)
      ·
        refine ⟨245098183462222724473314899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163398788974815149648876599 245098183462222724473314899)
        ·
          refine ⟨367647275193334086709972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245098183462222724473314899 367647275193334086709972349)
          ·
            refine ⟨137867728197500282516239631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367647275193334086709972349 137867728197500282516239631)
            ·
              refine ⟨206801592296250423774359447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137867728197500282516239631 206801592296250423774359447)
              ·
                refine ⟨310202388444375635661539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206801592296250423774359447 310202388444375635661539171)
                ·
                  refine ⟨465303582666563453492308757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310202388444375635661539171 465303582666563453492308757)
                  ·
                    refine ⟨21811105437495161882451973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 465303582666563453492308757 21811105437495161882451973)
                    ·
                      refine ⟨4089582269530342852959745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21811105437495161882451973 4089582269530342852959745)
                      ·
                        rfl

theorem cell23_7964433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_7964433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964433 prefixEnd_7964433 := by exact prefixLift 7964433
  have htrace : WordTrace (prefixWord ++ tailWord_7964433) baseStart_7964433 baseEnd_7964433 := by
    simpa [prefixWord, tailWord_7964433, baseEnd_7964433] using wordTrace_append hprefix tailTrace_7964433
  have hstable : (prefixWord ++ tailWord_7964433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964433).length < 2 ^ (prefixWord ++ tailWord_7964433).sum := by decide
  have hdescent : baseEnd_7964433 < baseStart_7964433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964440 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7964440 : Nat := 118140960795 + 7964440 * 2 ^ 59
def prefixEnd_7964440 : Nat := 4983230072969 + 3 ^ 40 * 7964440 * 2
def baseEnd_7964440 : Nat := 4089585863894924325572213

theorem tailTrace_7964440 : CollatzResearch.WordTrace tailWord_7964440 prefixEnd_7964440 4089585863894924325572213 := by
  unfold tailWord_7964440
  simp only [CollatzResearch.WordTrace]
  refine ⟨145243495633100786452309387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193657994177467715269745849 145243495633100786452309387)
  ·
    refine ⟨217865243449651179678464081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145243495633100786452309387 217865243449651179678464081)
    ·
      refine ⟨163398932587238384758848061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217865243449651179678464081 163398932587238384758848061)
      ·
        refine ⟨61274599720214394284568023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163398932587238384758848061 61274599720214394284568023)
        ·
          refine ⟨91911899580321591426852035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61274599720214394284568023 91911899580321591426852035)
          ·
            refine ⟨137867849370482387140278053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91911899580321591426852035 137867849370482387140278053)
            ·
              refine ⟨25850221756965447588802135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137867849370482387140278053 25850221756965447588802135)
              ·
                refine ⟨38775332635448171383203203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850221756965447588802135 38775332635448171383203203)
                ·
                  refine ⟨58162998953172257074804805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38775332635448171383203203 58162998953172257074804805)
                  ·
                    refine ⟨10905562303719798201525901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58162998953172257074804805 10905562303719798201525901)
                    ·
                      refine ⟨4089585863894924325572213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905562303719798201525901 4089585863894924325572213)
                      ·
                        rfl

theorem cell23_7964440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7964440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964440 prefixEnd_7964440 := by exact prefixLift 7964440
  have htrace : WordTrace (prefixWord ++ tailWord_7964440) baseStart_7964440 baseEnd_7964440 := by
    simpa [prefixWord, tailWord_7964440, baseEnd_7964440] using wordTrace_append hprefix tailTrace_7964440
  have hstable : (prefixWord ++ tailWord_7964440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964440).length < 2 ^ (prefixWord ++ tailWord_7964440).sum := by decide
  have hdescent : baseEnd_7964440 < baseStart_7964440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964477 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 6]
def baseStart_7964477 : Nat := 118140960795 + 7964477 * 2 ^ 59
def prefixEnd_7964477 : Nat := 4983230072969 + 3 ^ 40 * 7964477 * 2
def baseEnd_7964477 : Nat := 454400540297682297867727

theorem tailTrace_7964477 : CollatzResearch.WordTrace tailWord_7964477 prefixEnd_7964477 454400540297682297867727 := by
  unfold tailWord_7964477
  simp only [CollatzResearch.WordTrace]
  refine ⟨290488340767067528223715685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193658893844711685482477123 290488340767067528223715685)
  ·
    refine ⟨54466563893825161541946691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290488340767067528223715685 54466563893825161541946691)
    ·
      refine ⟨81699845840737742312920037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54466563893825161541946691 81699845840737742312920037)
      ·
        refine ⟨15318721095138326683672507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81699845840737742312920037 15318721095138326683672507)
        ·
          refine ⟨22978081642707490025508761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318721095138326683672507 22978081642707490025508761)
          ·
            refine ⟨17233561232030617519131571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22978081642707490025508761 17233561232030617519131571)
            ·
              refine ⟨25850341848045926278697357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233561232030617519131571 25850341848045926278697357)
              ·
                refine ⟨9693878193017222354511509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25850341848045926278697357 9693878193017222354511509)
                ·
                  refine ⟨454400540297682297867727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9693878193017222354511509 454400540297682297867727)
                  ·
                    rfl

theorem cell23_7964477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_7964477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964477 prefixEnd_7964477 := by exact prefixLift 7964477
  have htrace : WordTrace (prefixWord ++ tailWord_7964477) baseStart_7964477 baseEnd_7964477 := by
    simpa [prefixWord, tailWord_7964477, baseEnd_7964477] using wordTrace_append hprefix tailTrace_7964477
  have hstable : (prefixWord ++ tailWord_7964477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964477).length < 2 ^ (prefixWord ++ tailWord_7964477).sum := by decide
  have hdescent : baseEnd_7964477 < baseStart_7964477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964487 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_7964487 : Nat := 118140960795 + 7964487 * 2 ^ 59
def prefixEnd_7964487 : Nat := 4983230072969 + 3 ^ 40 * 7964487 * 2
def baseEnd_7964487 : Nat := 4089609997485685641684497

theorem tailTrace_7964487 : CollatzResearch.WordTrace tailWord_7964487 prefixEnd_7964487 4089609997485685641684497 := by
  unfold tailWord_7964487
  simp only [CollatzResearch.WordTrace]
  refine ⟨290488705497031299931579715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193659136998020866621053143 290488705497031299931579715)
  ·
    refine ⟨435733058245546949897369573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290488705497031299931579715 435733058245546949897369573)
    ·
      refine ⟨81699948421040053105756795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435733058245546949897369573 81699948421040053105756795)
      ·
        refine ⟨122549922631560079658635193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81699948421040053105756795 122549922631560079658635193)
        ·
          refine ⟨91912441973670059743976395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122549922631560079658635193 91912441973670059743976395)
          ·
            refine ⟨137868662960505089615964593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91912441973670059743976395 137868662960505089615964593)
            ·
              refine ⟨103401497220378817211973445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137868662960505089615964593 103401497220378817211973445)
              ·
                refine ⟨19387780728821028227245021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103401497220378817211973445 19387780728821028227245021)
                ·
                  refine ⟨7270417773307885585216883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19387780728821028227245021 7270417773307885585216883)
                  ·
                    refine ⟨10905626659961828377825325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270417773307885585216883 10905626659961828377825325)
                    ·
                      refine ⟨4089609997485685641684497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905626659961828377825325 4089609997485685641684497)
                      ·
                        rfl

theorem cell23_7964487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_7964487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964487 prefixEnd_7964487 := by exact prefixLift 7964487
  have htrace : WordTrace (prefixWord ++ tailWord_7964487) baseStart_7964487 baseEnd_7964487 := by
    simpa [prefixWord, tailWord_7964487, baseEnd_7964487] using wordTrace_append hprefix tailTrace_7964487
  have hstable : (prefixWord ++ tailWord_7964487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964487).length < 2 ^ (prefixWord ++ tailWord_7964487).sum := by decide
  have hdescent : baseEnd_7964487 < baseStart_7964487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964490 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_7964490 : Nat := 118140960795 + 7964490 * 2 ^ 59
def prefixEnd_7964490 : Nat := 4983230072969 + 3 ^ 40 * 7964490 * 2
def baseEnd_7964490 : Nat := 1363203845975883043315661

theorem tailTrace_7964490 : CollatzResearch.WordTrace tailWord_7964490 prefixEnd_7964490 1363203845975883043315661 := by
  unfold tailWord_7964490
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622203729005107860984731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193659209944013620962625949 72622203729005107860984731)
  ·
    refine ⟨108933305593507661791477097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72622203729005107860984731 108933305593507661791477097)
    ·
      refine ⟨81699979195130746343607823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108933305593507661791477097 81699979195130746343607823)
      ·
        refine ⟨122549968792696119515411735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81699979195130746343607823 122549968792696119515411735)
        ·
          refine ⟨183824953189044179273117603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122549968792696119515411735 183824953189044179273117603)
          ·
            refine ⟨275737429783566268909676405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183824953189044179273117603 275737429783566268909676405)
            ·
              refine ⟨25850384042209337710282163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275737429783566268909676405 25850384042209337710282163)
              ·
                refine ⟨38775576063314006565423245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850384042209337710282163 38775576063314006565423245)
                ·
                  refine ⟨14540841023742752462033717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38775576063314006565423245 14540841023742752462033717)
                  ·
                    refine ⟨1363203845975883043315661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14540841023742752462033717 1363203845975883043315661)
                    ·
                      rfl

theorem cell23_7964490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_7964490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964490 prefixEnd_7964490 := by exact prefixLift 7964490
  have htrace : WordTrace (prefixWord ++ tailWord_7964490) baseStart_7964490 baseEnd_7964490 := by
    simpa [prefixWord, tailWord_7964490, baseEnd_7964490] using wordTrace_append hprefix tailTrace_7964490
  have hstable : (prefixWord ++ tailWord_7964490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964490).length < 2 ^ (prefixWord ++ tailWord_7964490).sum := by decide
  have hdescent : baseEnd_7964490 < baseStart_7964490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964520 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_7964520 : Nat := 118140960795 + 7964520 * 2 ^ 59
def prefixEnd_7964520 : Nat := 4983230072969 + 3 ^ 40 * 7964520 * 2
def baseEnd_7964520 : Nat := 1363208980782428004190615

theorem tailTrace_7964520 : CollatzResearch.WordTrace tailWord_7964520 prefixEnd_7964520 1363208980782428004190615 := by
  unfold tailWord_7964520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145244954552955873283765507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193659939403941164378354009 145244954552955873283765507)
  ·
    refine ⟨217867431829433809925648261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145244954552955873283765507 217867431829433809925648261)
    ·
      refine ⟨40850143468018839361059049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217867431829433809925648261 40850143468018839361059049)
      ·
        refine ⟨30637607601014129520794287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40850143468018839361059049 30637607601014129520794287)
        ·
          refine ⟨45956411401521194281191431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30637607601014129520794287 45956411401521194281191431)
          ·
            refine ⟨68934617102281791421787147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45956411401521194281191431 68934617102281791421787147)
            ·
              refine ⟨103401925653422687132680721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68934617102281791421787147 103401925653422687132680721)
              ·
                refine ⟨77551444240067015349510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103401925653422687132680721 77551444240067015349510541)
                ·
                  refine ⟨29081791590025130756066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77551444240067015349510541 29081791590025130756066453)
                  ·
                    refine ⟨1363208980782428004190615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29081791590025130756066453 1363208980782428004190615)
                    ·
                      rfl

theorem cell23_7964520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_7964520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964520 prefixEnd_7964520 := by exact prefixLift 7964520
  have htrace : WordTrace (prefixWord ++ tailWord_7964520) baseStart_7964520 baseEnd_7964520 := by
    simpa [prefixWord, tailWord_7964520, baseEnd_7964520] using wordTrace_append hprefix tailTrace_7964520
  have hstable : (prefixWord ++ tailWord_7964520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964520).length < 2 ^ (prefixWord ++ tailWord_7964520).sum := by decide
  have hdescent : baseEnd_7964520 < baseStart_7964520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964530 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_7964530 : Nat := 118140960795 + 7964530 * 2 ^ 59
def prefixEnd_7964530 : Nat := 4983230072969 + 3 ^ 40 * 7964530 * 2
def baseEnd_7964530 : Nat := 4089632077153828973446799

theorem tailTrace_7964530 : CollatzResearch.WordTrace tailWord_7964530 prefixEnd_7964530 4089632077153828973446799 := by
  unfold tailWord_7964530
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622568458968879568848761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193660182557250345516930029 72622568458968879568848761)
  ·
    refine ⟨54466926344226659676636571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72622568458968879568848761 54466926344226659676636571)
    ·
      refine ⟨81700389516339989514954857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54466926344226659676636571 81700389516339989514954857)
      ·
        refine ⟨61275292137254992136216143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81700389516339989514954857 61275292137254992136216143)
        ·
          refine ⟨91912938205882488204324215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61275292137254992136216143 91912938205882488204324215)
          ·
            refine ⟨137869407308823732306486323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91912938205882488204324215 137869407308823732306486323)
            ·
              refine ⟨206804110963235598459729485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137869407308823732306486323 206804110963235598459729485)
              ·
                refine ⟨77551541611213349422398557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206804110963235598459729485 77551541611213349422398557)
                ·
                  refine ⟨29081828104205006033399459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77551541611213349422398557 29081828104205006033399459)
                  ·
                    refine ⟨43622742156307509050099189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29081828104205006033399459 43622742156307509050099189)
                    ·
                      refine ⟨4089632077153828973446799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43622742156307509050099189 4089632077153828973446799)
                      ·
                        rfl

theorem cell23_7964530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_7964530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964530 prefixEnd_7964530 := by exact prefixLift 7964530
  have htrace : WordTrace (prefixWord ++ tailWord_7964530) baseStart_7964530 baseEnd_7964530 := by
    simpa [prefixWord, tailWord_7964530, baseEnd_7964530] using wordTrace_append hprefix tailTrace_7964530
  have hstable : (prefixWord ++ tailWord_7964530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964530).length < 2 ^ (prefixWord ++ tailWord_7964530).sum := by decide
  have hdescent : baseEnd_7964530 < baseStart_7964530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964537 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_7964537 : Nat := 118140960795 + 7964537 * 2 ^ 59
def prefixEnd_7964537 : Nat := 4983230072969 + 3 ^ 40 * 7964537 * 2
def baseEnd_7964537 : Nat := 1363211890506136815353089

theorem tailTrace_7964537 : CollatzResearch.WordTrace tailWord_7964537 prefixEnd_7964537 1363211890506136815353089 := by
  unfold tailWord_7964537
  simp only [CollatzResearch.WordTrace]
  refine ⟨290490529146850158470899865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193660352764566772313933243 290490529146850158470899865)
  ·
    refine ⟨217867896860137618853174899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290490529146850158470899865 217867896860137618853174899)
    ·
      refine ⟨326801845290206428279762349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217867896860137618853174899 326801845290206428279762349)
      ·
        refine ⟨122550691983827410604910881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326801845290206428279762349 122550691983827410604910881)
        ·
          refine ⟨91913018987870557953683161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122550691983827410604910881 91913018987870557953683161)
          ·
            refine ⟨68934764240902918465262371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91913018987870557953683161 68934764240902918465262371)
            ·
              refine ⟨103402146361354377697893557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68934764240902918465262371 103402146361354377697893557)
              ·
                refine ⟨9693951221376972909177521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103402146361354377697893557 9693951221376972909177521)
                ·
                  refine ⟨7270463416032729681883141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9693951221376972909177521 7270463416032729681883141)
                  ·
                    refine ⟨1363211890506136815353089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7270463416032729681883141 1363211890506136815353089)
                    ·
                      rfl

theorem cell23_7964537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_7964537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964537 prefixEnd_7964537 := by exact prefixLift 7964537
  have htrace : WordTrace (prefixWord ++ tailWord_7964537) baseStart_7964537 baseEnd_7964537 := by
    simpa [prefixWord, tailWord_7964537, baseEnd_7964537] using wordTrace_append hprefix tailTrace_7964537
  have hstable : (prefixWord ++ tailWord_7964537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964537).length < 2 ^ (prefixWord ++ tailWord_7964537).sum := by decide
  have hdescent : baseEnd_7964537 < baseStart_7964537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964544 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2]
def baseStart_7964544 : Nat := 118140960795 + 7964544 * 2 ^ 59
def prefixEnd_7964544 : Nat := 4983230072969 + 3 ^ 40 * 7964544 * 2
def baseEnd_7964544 : Nat := 4089639265882991918671735

theorem tailTrace_7964544 : CollatzResearch.WordTrace tailWord_7964544 prefixEnd_7964544 4089639265882991918671735 := by
  unfold tailWord_7964544
  simp only [CollatzResearch.WordTrace]
  refine ⟨145245392228912399333202343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193660522971883199110936457 145245392228912399333202343)
  ·
    refine ⟨217868088343368598999803515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145245392228912399333202343 217868088343368598999803515)
    ·
      refine ⟨326802132515052898499705273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217868088343368598999803515 326802132515052898499705273)
      ·
        refine ⟨245101599386289673874778955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326802132515052898499705273 245101599386289673874778955)
        ·
          refine ⟨367652399079434510812168433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245101599386289673874778955 367652399079434510812168433)
          ·
            refine ⟨275739299309575883109126325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367652399079434510812168433 275739299309575883109126325)
            ·
              refine ⟨25850559310272739041480593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275739299309575883109126325 25850559310272739041480593)
              ·
                refine ⟨19387919482704554281110445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25850559310272739041480593 19387919482704554281110445)
                ·
                  refine ⟨7270469806014207855416417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19387919482704554281110445 7270469806014207855416417)
                  ·
                    refine ⟨5452852354510655891562313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270469806014207855416417 5452852354510655891562313)
                    ·
                      refine ⟨4089639265882991918671735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452852354510655891562313 4089639265882991918671735)
                      ·
                        rfl

theorem cell23_7964544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_7964544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964544 prefixEnd_7964544 := by exact prefixLift 7964544
  have htrace : WordTrace (prefixWord ++ tailWord_7964544) baseStart_7964544 baseEnd_7964544 := by
    simpa [prefixWord, tailWord_7964544, baseEnd_7964544] using wordTrace_append hprefix tailTrace_7964544
  have hstable : (prefixWord ++ tailWord_7964544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964544).length < 2 ^ (prefixWord ++ tailWord_7964544).sum := by decide
  have hdescent : baseEnd_7964544 < baseStart_7964544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964547 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3]
def baseStart_7964547 : Nat := 118140960795 + 7964547 * 2 ^ 59
def prefixEnd_7964547 : Nat := 4983230072969 + 3 ^ 40 * 7964547 * 2
def baseEnd_7964547 : Nat := 4089640806324955406934221

theorem tailTrace_7964547 : CollatzResearch.WordTrace tailWord_7964547 prefixEnd_7964547 4089640806324955406934221 := by
  unfold tailWord_7964547
  simp only [CollatzResearch.WordTrace]
  refine ⟨290490893876813930178763895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193660595917875953452509263 290490893876813930178763895)
  ·
    refine ⟨435736340815220895268145843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290490893876813930178763895 435736340815220895268145843)
    ·
      refine ⟨653604511222831342902218765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435736340815220895268145843 653604511222831342902218765)
      ·
        refine ⟨245101691708561753588332037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653604511222831342902218765 245101691708561753588332037)
        ·
          refine ⟨45956567195355328797812257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245101691708561753588332037 45956567195355328797812257)
          ·
            refine ⟨34467425396516496598359193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45956567195355328797812257 34467425396516496598359193)
            ·
              refine ⟨25850569047387372448769395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34467425396516496598359193 25850569047387372448769395)
              ·
                refine ⟨38775853571081058673154093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25850569047387372448769395 38775853571081058673154093)
                ·
                  refine ⟨14540945089155397002432785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38775853571081058673154093 14540945089155397002432785)
                  ·
                    refine ⟨10905708816866547751824589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14540945089155397002432785 10905708816866547751824589)
                    ·
                      refine ⟨4089640806324955406934221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905708816866547751824589 4089640806324955406934221)
                      ·
                        rfl

theorem cell23_7964547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_7964547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964547 prefixEnd_7964547 := by exact prefixLift 7964547
  have htrace : WordTrace (prefixWord ++ tailWord_7964547) baseStart_7964547 baseEnd_7964547 := by
    simpa [prefixWord, tailWord_7964547, baseEnd_7964547] using wordTrace_append hprefix tailTrace_7964547
  have hstable : (prefixWord ++ tailWord_7964547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964547).length < 2 ^ (prefixWord ++ tailWord_7964547).sum := by decide
  have hdescent : baseEnd_7964547 < baseStart_7964547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964558 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_7964558 : Nat := 118140960795 + 7964558 * 2 ^ 59
def prefixEnd_7964558 : Nat := 4983230072969 + 3 ^ 40 * 7964558 * 2
def baseEnd_7964558 : Nat := 1363215484870718287965557

theorem tailTrace_7964558 : CollatzResearch.WordTrace tailWord_7964558 prefixEnd_7964558 1363215484870718287965557 := by
  unfold tailWord_7964558
  simp only [CollatzResearch.WordTrace]
  refine ⟨36311411884971759882176791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193660863386516052704942885 36311411884971759882176791)
  ·
    refine ⟨54467117827457639823265187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36311411884971759882176791 54467117827457639823265187)
    ·
      refine ⟨81700676741186459734897781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54467117827457639823265187 81700676741186459734897781)
      ·
        refine ⟨7659438444486230600146667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81700676741186459734897781 7659438444486230600146667)
        ·
          refine ⟨11489157666729345900220001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659438444486230600146667 11489157666729345900220001)
          ·
            refine ⟨8616868250047009425165001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11489157666729345900220001 8616868250047009425165001)
            ·
              refine ⟨6462651187535257068873751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616868250047009425165001 6462651187535257068873751)
              ·
                refine ⟨9693976781302885603310627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462651187535257068873751 9693976781302885603310627)
                ·
                  refine ⟨14540965171954328404965941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9693976781302885603310627 14540965171954328404965941)
                  ·
                    refine ⟨1363215484870718287965557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14540965171954328404965941 1363215484870718287965557)
                    ·
                      rfl

theorem cell23_7964558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_7964558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964558 prefixEnd_7964558 := by exact prefixLift 7964558
  have htrace : WordTrace (prefixWord ++ tailWord_7964558) baseStart_7964558 baseEnd_7964558 := by
    simpa [prefixWord, tailWord_7964558, baseEnd_7964558] using wordTrace_append hprefix tailTrace_7964558
  have hstable : (prefixWord ++ tailWord_7964558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964558).length < 2 ^ (prefixWord ++ tailWord_7964558).sum := by decide
  have hdescent : baseEnd_7964558 < baseStart_7964558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964561 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_7964561 : Nat := 118140960795 + 7964561 * 2 ^ 59
def prefixEnd_7964561 : Nat := 4983230072969 + 3 ^ 40 * 7964561 * 2
def baseEnd_7964561 : Nat := 4089647995054118352159157

theorem tailTrace_7964561 : CollatzResearch.WordTrace tailWord_7964561 prefixEnd_7964561 4089647995054118352159157 := by
  unfold tailWord_7964561
  simp only [CollatzResearch.WordTrace]
  refine ⟨290491404498763210569773537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193660936332508807046515691 290491404498763210569773537)
  ·
    refine ⟨217868553374072407927330153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290491404498763210569773537 217868553374072407927330153)
    ·
      refine ⟨163401415030554305945497615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217868553374072407927330153 163401415030554305945497615)
      ·
        refine ⟨245102122545831458918246423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163401415030554305945497615 245102122545831458918246423)
        ·
          refine ⟨367653183818747188377369635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245102122545831458918246423 367653183818747188377369635)
          ·
            refine ⟨551479775728120782566054453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367653183818747188377369635 551479775728120782566054453)
            ·
              refine ⟨51701228974511323365567605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551479775728120782566054453 51701228974511323365567605)
              ·
                refine ⟨4846990216360436565521963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51701228974511323365567605 4846990216360436565521963)
                ·
                  refine ⟨7270485324540654848282945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4846990216360436565521963 7270485324540654848282945)
                  ·
                    refine ⟨5452863993405491136212209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270485324540654848282945 5452863993405491136212209)
                    ·
                      refine ⟨4089647995054118352159157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452863993405491136212209 4089647995054118352159157)
                      ·
                        rfl

theorem cell23_7964561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_7964561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964561 prefixEnd_7964561 := by exact prefixLift 7964561
  have htrace : WordTrace (prefixWord ++ tailWord_7964561) baseStart_7964561 baseEnd_7964561 := by
    simpa [prefixWord, tailWord_7964561, baseEnd_7964561] using wordTrace_append hprefix tailTrace_7964561
  have hstable : (prefixWord ++ tailWord_7964561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964561).length < 2 ^ (prefixWord ++ tailWord_7964561).sum := by decide
  have hdescent : baseEnd_7964561 < baseStart_7964561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964578 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7964578 : Nat := 118140960795 + 7964578 * 2 ^ 59
def prefixEnd_7964578 : Nat := 4983230072969 + 3 ^ 40 * 7964578 * 2
def baseEnd_7964578 : Nat := 4089656724225244785646579

theorem tailTrace_7964578 : CollatzResearch.WordTrace tailWord_7964578 prefixEnd_7964578 4089656724225244785646579 := by
  unfold tailWord_7964578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623006134925405618285597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193661349693134414982094925 72623006134925405618285597)
  ·
    refine ⟨27233627300597027106857099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72623006134925405618285597 27233627300597027106857099)
    ·
      refine ⟨40850440950895540660285649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27233627300597027106857099 40850440950895540660285649)
      ·
        refine ⟨30637830713171655495214237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40850440950895540660285649 30637830713171655495214237)
        ·
          refine ⟨11489186517439370810705339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30637830713171655495214237 11489186517439370810705339)
          ·
            refine ⟨17233779776159056216058009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489186517439370810705339 17233779776159056216058009)
            ·
              refine ⟨12925334832119292162043507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233779776159056216058009 12925334832119292162043507)
              ·
                refine ⟨19388002248178938243065261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925334832119292162043507 19388002248178938243065261)
                ·
                  refine ⟨7270500843067101841149473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19388002248178938243065261 7270500843067101841149473)
                  ·
                    refine ⟨5452875632300326380862105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270500843067101841149473 5452875632300326380862105)
                    ·
                      refine ⟨4089656724225244785646579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5452875632300326380862105 4089656724225244785646579)
                      ·
                        rfl

theorem cell23_7964578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7964578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964578 prefixEnd_7964578 := by exact prefixLift 7964578
  have htrace : WordTrace (prefixWord ++ tailWord_7964578) baseStart_7964578 baseEnd_7964578 := by
    simpa [prefixWord, tailWord_7964578, baseEnd_7964578] using wordTrace_append hprefix tailTrace_7964578
  have hstable : (prefixWord ++ tailWord_7964578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964578).length < 2 ^ (prefixWord ++ tailWord_7964578).sum := by decide
  have hdescent : baseEnd_7964578 < baseStart_7964578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964594 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_7964594 : Nat := 118140960795 + 7964594 * 2 ^ 59
def prefixEnd_7964594 : Nat := 4983230072969 + 3 ^ 40 * 7964594 * 2
def baseEnd_7964594 : Nat := 4089664939915716723046505

theorem tailTrace_7964594 : CollatzResearch.WordTrace tailWord_7964594 prefixEnd_7964594 4089664939915716723046505 := by
  unfold tailWord_7964594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72623152026910914301431209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193661738738429104803816557 72623152026910914301431209)
  ·
    refine ⟨54467364020183185726073407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72623152026910914301431209 54467364020183185726073407)
    ·
      refine ⟨81701046030274778589110111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54467364020183185726073407 81701046030274778589110111)
      ·
        refine ⟨122551569045412167883665167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81701046030274778589110111 122551569045412167883665167)
        ·
          refine ⟨183827353568118251825497751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122551569045412167883665167 183827353568118251825497751)
          ·
            refine ⟨275741030352177377738246627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183827353568118251825497751 275741030352177377738246627)
            ·
              refine ⟨413611545528266066607369941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275741030352177377738246627 413611545528266066607369941)
              ·
                refine ⟨9694020598318735936110233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 413611545528266066607369941 9694020598318735936110233)
                ·
                  refine ⟨7270515448739051952082675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694020598318735936110233 7270515448739051952082675)
                  ·
                    refine ⟨10905773173108577928124013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270515448739051952082675 10905773173108577928124013)
                    ·
                      refine ⟨4089664939915716723046505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10905773173108577928124013 4089664939915716723046505)
                      ·
                        rfl

theorem cell23_7964594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_7964594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964594 prefixEnd_7964594 := by exact prefixLift 7964594
  have htrace : WordTrace (prefixWord ++ tailWord_7964594) baseStart_7964594 baseEnd_7964594 := by
    simpa [prefixWord, tailWord_7964594, baseEnd_7964594] using wordTrace_append hprefix tailTrace_7964594
  have hstable : (prefixWord ++ tailWord_7964594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964594).length < 2 ^ (prefixWord ++ tailWord_7964594).sum := by decide
  have hdescent : baseEnd_7964594 < baseStart_7964594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964707 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7964707 : Nat := 118140960795 + 7964707 * 2 ^ 59
def prefixEnd_7964707 : Nat := 4983230072969 + 3 ^ 40 * 7964707 * 2
def baseEnd_7964707 : Nat := 4089722963229674780933485

theorem tailTrace_7964707 : CollatzResearch.WordTrace tailWord_7964707 prefixEnd_7964707 4089722963229674780933485 := by
  unfold tailWord_7964707
  simp only [CollatzResearch.WordTrace]
  refine ⟨290496729556234277504588375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193664486370822851669725583 290496729556234277504588375)
  ·
    refine ⟨435745094334351416256882563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290496729556234277504588375 435745094334351416256882563)
    ·
      refine ⟨653617641501527124385323845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435745094334351416256882563 653617641501527124385323845)
      ·
        refine ⟨122553307781536335822248221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 653617641501527124385323845 122553307781536335822248221)
        ·
          refine ⟨45957490418076125933343083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122553307781536335822248221 45957490418076125933343083)
          ·
            refine ⟨68936235627114188900014625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45957490418076125933343083 68936235627114188900014625)
            ·
              refine ⟨51702176720335641675010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68936235627114188900014625 51702176720335641675010969)
              ·
                refine ⟨38776632540251731256258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51702176720335641675010969 38776632540251731256258227)
                ·
                  refine ⟨58164948810377596884387341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38776632540251731256258227 58164948810377596884387341)
                  ·
                    refine ⟨21811855803891598831645253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58164948810377596884387341 21811855803891598831645253)
                    ·
                      refine ⟨4089722963229674780933485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21811855803891598831645253 4089722963229674780933485)
                      ·
                        rfl

theorem cell23_7964707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7964707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964707 prefixEnd_7964707 := by exact prefixLift 7964707
  have htrace : WordTrace (prefixWord ++ tailWord_7964707) baseStart_7964707 baseEnd_7964707 := by
    simpa [prefixWord, tailWord_7964707, baseEnd_7964707] using wordTrace_append hprefix tailTrace_7964707
  have hstable : (prefixWord ++ tailWord_7964707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964707).length < 2 ^ (prefixWord ++ tailWord_7964707).sum := by decide
  have hdescent : baseEnd_7964707 < baseStart_7964707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964808 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7964808 : Nat := 118140960795 + 7964808 * 2 ^ 59
def prefixEnd_7964808 : Nat := 4983230072969 + 3 ^ 40 * 7964808 * 2
def baseEnd_7964808 : Nat := 4089774824775778885770521

theorem tailTrace_7964808 : CollatzResearch.WordTrace tailWord_7964808 prefixEnd_7964808 4089774824775778885770521 := by
  unfold tailWord_7964808
  simp only [CollatzResearch.WordTrace]
  refine ⟨145250206664434185877007539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193666942219245581169343385 145250206664434185877007539)
  ·
    refine ⟨217875309996651278815511309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145250206664434185877007539 217875309996651278815511309)
    ·
      refine ⟨81703241248744229555816741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217875309996651278815511309 81703241248744229555816741)
      ·
        refine ⟨15319357734139543041715639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81703241248744229555816741 15319357734139543041715639)
        ·
          refine ⟨22979036601209314562573459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15319357734139543041715639 22979036601209314562573459)
          ·
            refine ⟨34468554901813971843860189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22979036601209314562573459 34468554901813971843860189)
            ·
              refine ⟨12925708088180239441447571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34468554901813971843860189 12925708088180239441447571)
              ·
                refine ⟨19388562132270359162171357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925708088180239441447571 19388562132270359162171357)
                ·
                  refine ⟨7270710799601384685814259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19388562132270359162171357 7270710799601384685814259)
                  ·
                    refine ⟨10906066199402077028721389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270710799601384685814259 10906066199402077028721389)
                    ·
                      refine ⟨4089774824775778885770521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906066199402077028721389 4089774824775778885770521)
                      ·
                        rfl

theorem cell23_7964808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7964808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964808 prefixEnd_7964808 := by exact prefixLift 7964808
  have htrace : WordTrace (prefixWord ++ tailWord_7964808) baseStart_7964808 baseEnd_7964808 := by
    simpa [prefixWord, tailWord_7964808, baseEnd_7964808] using wordTrace_append hprefix tailTrace_7964808
  have hstable : (prefixWord ++ tailWord_7964808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964808).length < 2 ^ (prefixWord ++ tailWord_7964808).sum := by decide
  have hdescent : baseEnd_7964808 < baseStart_7964808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_7964827 : Nat := 118140960795 + 7964827 * 2 ^ 59
def prefixEnd_7964827 : Nat := 4983230072969 + 3 ^ 40 * 7964827 * 2
def baseEnd_7964827 : Nat := 4089784580908214311432933

theorem tailTrace_7964827 : CollatzResearch.WordTrace tailWord_7964827 prefixEnd_7964827 4089784580908214311432933 := by
  unfold tailWord_7964827
  simp only [CollatzResearch.WordTrace]
  refine ⟨290501106315799537998956735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193667404210533025332637823 290501106315799537998956735)
  ·
    refine ⟨435751659473699306998435103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290501106315799537998956735 435751659473699306998435103)
    ·
      refine ⟨653627489210548960497652655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435751659473699306998435103 653627489210548960497652655)
      ·
        refine ⟨980441233815823440746478983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653627489210548960497652655 980441233815823440746478983)
        ·
          refine ⟨1470661850723735161119718475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980441233815823440746478983 1470661850723735161119718475)
          ·
            refine ⟨2205992776085602741679577713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470661850723735161119718475 2205992776085602741679577713)
            ·
              refine ⟨1654494582064202056259683285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205992776085602741679577713 1654494582064202056259683285)
              ·
                refine ⟨38777216767129735693586327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1654494582064202056259683285 38777216767129735693586327)
                ·
                  refine ⟨58165825150694603540379491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38777216767129735693586327 58165825150694603540379491)
                  ·
                    refine ⟨87248737726041905310569237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58165825150694603540379491 87248737726041905310569237)
                    ·
                      refine ⟨4089784580908214311432933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87248737726041905310569237 4089784580908214311432933)
                      ·
                        rfl

theorem cell23_7964827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_7964827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964827 prefixEnd_7964827 := by exact prefixLift 7964827
  have htrace : WordTrace (prefixWord ++ tailWord_7964827) baseStart_7964827 baseEnd_7964827 := by
    simpa [prefixWord, tailWord_7964827, baseEnd_7964827] using wordTrace_append hprefix tailTrace_7964827
  have hstable : (prefixWord ++ tailWord_7964827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964827).length < 2 ^ (prefixWord ++ tailWord_7964827).sum := by decide
  have hdescent : baseEnd_7964827 < baseStart_7964827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964831 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7964831 : Nat := 118140960795 + 7964831 * 2 ^ 59
def prefixEnd_7964831 : Nat := 4983230072969 + 3 ^ 40 * 7964831 * 2
def baseEnd_7964831 : Nat := 4089786634830832295782915

theorem tailTrace_7964831 : CollatzResearch.WordTrace tailWord_7964831 prefixEnd_7964831 4089786634830832295782915 := by
  unfold tailWord_7964831
  simp only [CollatzResearch.WordTrace]
  refine ⟨290501252207785046682102347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193667501471856697788068231 290501252207785046682102347)
  ·
    refine ⟨435751878311677570023153521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290501252207785046682102347 435751878311677570023153521)
    ·
      refine ⟨326813908733758177517365141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435751878311677570023153521 326813908733758177517365141)
      ·
        refine ⟨15319401971894914571126491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326813908733758177517365141 15319401971894914571126491)
        ·
          refine ⟨22979102957842371856689737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15319401971894914571126491 22979102957842371856689737)
          ·
            refine ⟨17234327218381778892517303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22979102957842371856689737 17234327218381778892517303)
            ·
              refine ⟨25851490827572668338775955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17234327218381778892517303 25851490827572668338775955)
              ·
                refine ⟨38777236241359002508163933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25851490827572668338775955 38777236241359002508163933)
                ·
                  refine ⟨14541463590509625940561475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38777236241359002508163933 14541463590509625940561475)
                  ·
                    refine ⟨21812195385764438910842213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14541463590509625940561475 21812195385764438910842213)
                    ·
                      refine ⟨4089786634830832295782915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21812195385764438910842213 4089786634830832295782915)
                      ·
                        rfl

theorem cell23_7964831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7964831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964831 prefixEnd_7964831 := by exact prefixLift 7964831
  have htrace : WordTrace (prefixWord ++ tailWord_7964831) baseStart_7964831 baseEnd_7964831 := by
    simpa [prefixWord, tailWord_7964831, baseEnd_7964831] using wordTrace_append hprefix tailTrace_7964831
  have hstable : (prefixWord ++ tailWord_7964831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964831).length < 2 ^ (prefixWord ++ tailWord_7964831).sum := by decide
  have hdescent : baseEnd_7964831 < baseStart_7964831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964837 : List Nat := [1, 3, 1, 2, 1, 3, 1, 11]
def baseStart_7964837 : Nat := 118140960795 + 7964837 * 2 ^ 59
def prefixEnd_7964837 : Nat := 4983230072969 + 3 ^ 40 * 7964837 * 2
def baseEnd_7964837 : Nat := 151473693174620713789181

theorem tailTrace_7964837 : CollatzResearch.WordTrace tailWord_7964837 prefixEnd_7964837 151473693174620713789181 := by
  unfold tailWord_7964837
  simp only [CollatzResearch.WordTrace]
  refine ⟨290501471045763309706820765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193667647363842206471213843 290501471045763309706820765)
  ·
    refine ⟨108938051642161241140057787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290501471045763309706820765 108938051642161241140057787)
    ·
      refine ⟨163407077463241861710086681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108938051642161241140057787 163407077463241861710086681)
      ·
        refine ⟨122555308097431396282565011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163407077463241861710086681 122555308097431396282565011)
        ·
          refine ⟨183832962146147094423847517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122555308097431396282565011 183832962146147094423847517)
          ·
            refine ⟨68937360804805160408942819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183832962146147094423847517 68937360804805160408942819)
            ·
              refine ⟨103406041207207740613414229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68937360804805160408942819 103406041207207740613414229)
              ·
                refine ⟨151473693174620713789181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103406041207207740613414229 151473693174620713789181)
                ·
                  rfl

theorem cell23_7964837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 11].length) (baseStart_7964837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964837 prefixEnd_7964837 := by exact prefixLift 7964837
  have htrace : WordTrace (prefixWord ++ tailWord_7964837) baseStart_7964837 baseEnd_7964837 := by
    simpa [prefixWord, tailWord_7964837, baseEnd_7964837] using wordTrace_append hprefix tailTrace_7964837
  have hstable : (prefixWord ++ tailWord_7964837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964837).length < 2 ^ (prefixWord ++ tailWord_7964837).sum := by decide
  have hdescent : baseEnd_7964837 < baseStart_7964837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964854 : List Nat := [5, 1, 3, 14]
def baseStart_7964854 : Nat := 118140960795 + 7964854 * 2 ^ 59
def prefixEnd_7964854 : Nat := 4983230072969 + 3 ^ 40 * 7964854 * 2
def baseEnd_7964854 : Nat := 1870049586138950940007

theorem tailTrace_7964854 : CollatzResearch.WordTrace tailWord_7964854 prefixEnd_7964854 1870049586138950940007 := by
  unfold tailWord_7964854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156380692918857600636851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193668060724467814406793077 18156380692918857600636851)
  ·
    refine ⟨27234571039378286400955277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18156380692918857600636851 27234571039378286400955277)
    ·
      refine ⟨10212964139766857400358229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27234571039378286400955277 10212964139766857400358229)
      ·
        refine ⟨1870049586138950940007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 10212964139766857400358229 1870049586138950940007)
        ·
          rfl

theorem cell23_7964854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 14].length) (baseStart_7964854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964854 prefixEnd_7964854 := by exact prefixLift 7964854
  have htrace : WordTrace (prefixWord ++ tailWord_7964854) baseStart_7964854 baseEnd_7964854 := by
    simpa [prefixWord, tailWord_7964854, baseEnd_7964854] using wordTrace_append hprefix tailTrace_7964854
  have hstable : (prefixWord ++ tailWord_7964854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964854).length < 2 ^ (prefixWord ++ tailWord_7964854).sum := by decide
  have hdescent : baseEnd_7964854 < baseStart_7964854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964899 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7964899 : Nat := 118140960795 + 7964899 * 2 ^ 59
def prefixEnd_7964899 : Nat := 4983230072969 + 3 ^ 40 * 7964899 * 2
def baseEnd_7964899 : Nat := 4089821551515338029732603

theorem tailTrace_7964899 : CollatzResearch.WordTrace tailWord_7964899 prefixEnd_7964899 4089821551515338029732603 := by
  unfold tailWord_7964899
  simp only [CollatzResearch.WordTrace]
  refine ⟨290503732371538694295577751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193669154914359129530385167 290503732371538694295577751)
  ·
    refine ⟨435755598557308041443366627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290503732371538694295577751 435755598557308041443366627)
    ·
      refine ⟨653633397835962062165049941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435755598557308041443366627 653633397835962062165049941)
      ·
        refine ⟨7659766380890180415996679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 653633397835962062165049941 7659766380890180415996679)
        ·
          refine ⟨11489649571335270623995019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659766380890180415996679 11489649571335270623995019)
          ·
            refine ⟨17234474357002905935992529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489649571335270623995019 17234474357002905935992529)
            ·
              refine ⟨12925855767752179451994397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17234474357002905935992529 12925855767752179451994397)
              ·
                refine ⟨4847195912907067294497899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12925855767752179451994397 4847195912907067294497899)
                ·
                  refine ⟨7270793869360600941746849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847195912907067294497899 7270793869360600941746849)
                  ·
                    refine ⟨5453095402020450706310137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7270793869360600941746849 5453095402020450706310137)
                    ·
                      refine ⟨4089821551515338029732603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453095402020450706310137 4089821551515338029732603)
                      ·
                        rfl

theorem cell23_7964899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7964899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964899 prefixEnd_7964899 := by exact prefixLift 7964899
  have htrace : WordTrace (prefixWord ++ tailWord_7964899) baseStart_7964899 baseEnd_7964899 := by
    simpa [prefixWord, tailWord_7964899, baseEnd_7964899] using wordTrace_append hprefix tailTrace_7964899
  have hstable : (prefixWord ++ tailWord_7964899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964899).length < 2 ^ (prefixWord ++ tailWord_7964899).sum := by decide
  have hdescent : baseEnd_7964899 < baseStart_7964899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964908 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_7964908 : Nat := 118140960795 + 7964908 * 2 ^ 59
def prefixEnd_7964908 : Nat := 4983230072969 + 3 ^ 40 * 7964908 * 2
def baseEnd_7964908 : Nat := 4089826172841228494520061

theorem tailTrace_7964908 : CollatzResearch.WordTrace tailWord_7964908 prefixEnd_7964908 4089826172841228494520061 := by
  unfold tailWord_7964908
  simp only [CollatzResearch.WordTrace]
  refine ⟨145252030314253044416327689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193669373752337392555103585 145252030314253044416327689)
  ·
    refine ⟨108939022735689783312245767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145252030314253044416327689 108939022735689783312245767)
    ·
      refine ⟨163408534103534674968368651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108939022735689783312245767 163408534103534674968368651)
      ·
        refine ⟨245112801155302012452552977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163408534103534674968368651 245112801155302012452552977)
        ·
          refine ⟨183834600866476509339414733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245112801155302012452552977 183834600866476509339414733)
          ·
            refine ⟨68937975324928691002280525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183834600866476509339414733 68937975324928691002280525)
            ·
              refine ⟨25851740746848259125855197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68937975324928691002280525 25851740746848259125855197)
              ·
                refine ⟨9694402780068097172195699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25851740746848259125855197 9694402780068097172195699)
                ·
                  refine ⟨14541604170102145758293549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9694402780068097172195699 14541604170102145758293549)
                  ·
                    refine ⟨5453101563788304659360081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14541604170102145758293549 5453101563788304659360081)
                    ·
                      refine ⟨4089826172841228494520061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453101563788304659360081 4089826172841228494520061)
                      ·
                        rfl

theorem cell23_7964908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_7964908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964908 prefixEnd_7964908 := by exact prefixLift 7964908
  have htrace : WordTrace (prefixWord ++ tailWord_7964908) baseStart_7964908 baseEnd_7964908 := by
    simpa [prefixWord, tailWord_7964908, baseEnd_7964908] using wordTrace_append hprefix tailTrace_7964908
  have hstable : (prefixWord ++ tailWord_7964908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964908).length < 2 ^ (prefixWord ++ tailWord_7964908).sum := by decide
  have hdescent : baseEnd_7964908 < baseStart_7964908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964932 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7964932 : Nat := 118140960795 + 7964932 * 2 ^ 59
def prefixEnd_7964932 : Nat := 4983230072969 + 3 ^ 40 * 7964932 * 2
def baseEnd_7964932 : Nat := 4089838496376936400619951

theorem tailTrace_7964932 : CollatzResearch.WordTrace tailWord_7964932 prefixEnd_7964932 4089838496376936400619951 := by
  unfold tailWord_7964932
  simp only [CollatzResearch.WordTrace]
  refine ⟨145252467990209570465764525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193669957320279427287686033 145252467990209570465764525)
  ·
    refine ⟨54469675496328588924661697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145252467990209570465764525 54469675496328588924661697)
    ·
      refine ⟨40852256622246441693496273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54469675496328588924661697 40852256622246441693496273)
      ·
        refine ⟨30639192466684831270122205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40852256622246441693496273 30639192466684831270122205)
        ·
          refine ⟨11489697175006811726295827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30639192466684831270122205 11489697175006811726295827)
          ·
            refine ⟨17234545762510217589443741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489697175006811726295827 17234545762510217589443741)
            ·
              refine ⟨6462954660941331596041403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17234545762510217589443741 6462954660941331596041403)
              ·
                refine ⟨9694431991411997394062105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462954660941331596041403 9694431991411997394062105)
                ·
                  refine ⟨7270823993558998045546579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694431991411997394062105 7270823993558998045546579)
                  ·
                    refine ⟨10906235990338497068319869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270823993558998045546579 10906235990338497068319869)
                    ·
                      refine ⟨4089838496376936400619951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906235990338497068319869 4089838496376936400619951)
                      ·
                        rfl

theorem cell23_7964932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7964932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964932 prefixEnd_7964932 := by exact prefixLift 7964932
  have htrace : WordTrace (prefixWord ++ tailWord_7964932) baseStart_7964932 baseEnd_7964932 := by
    simpa [prefixWord, tailWord_7964932, baseEnd_7964932] using wordTrace_append hprefix tailTrace_7964932
  have hstable : (prefixWord ++ tailWord_7964932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964932).length < 2 ^ (prefixWord ++ tailWord_7964932).sum := by decide
  have hdescent : baseEnd_7964932 < baseStart_7964932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964938 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7964938 : Nat := 118140960795 + 7964938 * 2 ^ 59
def prefixEnd_7964938 : Nat := 4983230072969 + 3 ^ 40 * 7964938 * 2
def baseEnd_7964938 : Nat := 4089841577260863377144923

theorem tailTrace_7964938 : CollatzResearch.WordTrace tailWord_7964938 prefixEnd_7964938 4089841577260863377144923 := by
  unfold tailWord_7964938
  simp only [CollatzResearch.WordTrace]
  refine ⟨72626288704599350989061867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193670103212264935970831645 72626288704599350989061867)
  ·
    refine ⟨108939433056899026483592801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72626288704599350989061867 108939433056899026483592801)
    ·
      refine ⟨81704574792674269862694601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108939433056899026483592801 81704574792674269862694601)
      ·
        refine ⟨61278431094505702397020951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81704574792674269862694601 61278431094505702397020951)
        ·
          refine ⟨91917646641758553595531427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61278431094505702397020951 91917646641758553595531427)
          ·
            refine ⟨137876469962637830393297141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91917646641758553595531427 137876469962637830393297141)
            ·
              refine ⟨12925919058997296599371607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137876469962637830393297141 12925919058997296599371607)
              ·
                refine ⟨19388878588495944899057411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925919058997296599371607 19388878588495944899057411)
                ·
                  refine ⟨29083317882743917348586117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19388878588495944899057411 29083317882743917348586117)
                  ·
                    refine ⟨5453122103014484502859897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29083317882743917348586117 5453122103014484502859897)
                    ·
                      refine ⟨4089841577260863377144923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453122103014484502859897 4089841577260863377144923)
                      ·
                        rfl

theorem cell23_7964938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7964938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964938 prefixEnd_7964938 := by exact prefixLift 7964938
  have htrace : WordTrace (prefixWord ++ tailWord_7964938) baseStart_7964938 baseEnd_7964938 := by
    simpa [prefixWord, tailWord_7964938, baseEnd_7964938] using wordTrace_append hprefix tailTrace_7964938
  have hstable : (prefixWord ++ tailWord_7964938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964938).length < 2 ^ (prefixWord ++ tailWord_7964938).sum := by decide
  have hdescent : baseEnd_7964938 < baseStart_7964938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964958 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7964958 : Nat := 118140960795 + 7964958 * 2 ^ 59
def prefixEnd_7964958 : Nat := 4983230072969 + 3 ^ 40 * 7964958 * 2
def baseEnd_7964958 : Nat := 4089851846873953298894831

theorem tailTrace_7964958 : CollatzResearch.WordTrace tailWord_7964958 prefixEnd_7964958 4089851846873953298894831 := by
  unfold tailWord_7964958
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313235534790618421496941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193670589518883298247983685 36313235534790618421496941)
  ·
    refine ⟨13617463325546481908061353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36313235534790618421496941 13617463325546481908061353)
    ·
      refine ⟨10213097494159861431046015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13617463325546481908061353 10213097494159861431046015)
      ·
        refine ⟨15319646241239792146569023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213097494159861431046015 15319646241239792146569023)
        ·
          refine ⟨22979469361859688219853535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15319646241239792146569023 22979469361859688219853535)
          ·
            refine ⟨34469204042789532329780303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22979469361859688219853535 34469204042789532329780303)
            ·
              refine ⟨51703806064184298494670455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34469204042789532329780303 51703806064184298494670455)
              ·
                refine ⟨77555709096276447742005683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51703806064184298494670455 77555709096276447742005683)
                ·
                  refine ⟨116333563644414671613008525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77555709096276447742005683 116333563644414671613008525)
                  ·
                    refine ⟨43625086366655501854878197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116333563644414671613008525 43625086366655501854878197)
                    ·
                      refine ⟨4089851846873953298894831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43625086366655501854878197 4089851846873953298894831)
                      ·
                        rfl

theorem cell23_7964958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7964958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964958 prefixEnd_7964958 := by exact prefixLift 7964958
  have htrace : WordTrace (prefixWord ++ tailWord_7964958) baseStart_7964958 baseEnd_7964958 := by
    simpa [prefixWord, tailWord_7964958, baseEnd_7964958] using wordTrace_append hprefix tailTrace_7964958
  have hstable : (prefixWord ++ tailWord_7964958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964958).length < 2 ^ (prefixWord ++ tailWord_7964958).sum := by decide
  have hdescent : baseEnd_7964958 < baseStart_7964958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964978 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_7964978 : Nat := 118140960795 + 7964978 * 2 ^ 59
def prefixEnd_7964978 : Nat := 4983230072969 + 3 ^ 40 * 7964978 * 2
def baseEnd_7964978 : Nat := 454429124054115913404971

theorem tailTrace_7964978 : CollatzResearch.WordTrace tailWord_7964978 prefixEnd_7964978 454429124054115913404971 := by
  unfold tailWord_7964978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72626653434563122696925897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193671075825501660525135725 72626653434563122696925897)
  ·
    refine ⟨54469990075922342022694423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72626653434563122696925897 54469990075922342022694423)
    ·
      refine ⟨81704985113883513034041635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54469990075922342022694423 81704985113883513034041635)
      ·
        refine ⟨122557477670825269551062453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81704985113883513034041635 122557477670825269551062453)
        ·
          refine ⟨11489763531639869020412105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122557477670825269551062453 11489763531639869020412105)
          ·
            refine ⟨8617322648729901765309079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11489763531639869020412105 8617322648729901765309079)
            ·
              refine ⟨12925983973094852647963619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617322648729901765309079 12925983973094852647963619)
              ·
                refine ⟨19388975959642278971945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925983973094852647963619 19388975959642278971945429)
                ·
                  refine ⟨454429124054115913404971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19388975959642278971945429 454429124054115913404971)
                  ·
                    rfl

theorem cell23_7964978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_7964978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964978 prefixEnd_7964978 := by exact prefixLift 7964978
  have htrace : WordTrace (prefixWord ++ tailWord_7964978) baseStart_7964978 baseEnd_7964978 := by
    simpa [prefixWord, tailWord_7964978, baseEnd_7964978] using wordTrace_append hprefix tailTrace_7964978
  have hstable : (prefixWord ++ tailWord_7964978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964978).length < 2 ^ (prefixWord ++ tailWord_7964978).sum := by decide
  have hdescent : baseEnd_7964978 < baseStart_7964978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7964984 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_7964984 : Nat := 118140960795 + 7964984 * 2 ^ 59
def prefixEnd_7964984 : Nat := 4983230072969 + 3 ^ 40 * 7964984 * 2
def baseEnd_7964984 : Nat := 4089865197370970197169711

theorem tailTrace_7964984 : CollatzResearch.WordTrace tailWord_7964984 prefixEnd_7964984 4089865197370970197169711 := by
  unfold tailWord_7964984
  simp only [CollatzResearch.WordTrace]
  refine ⟨145253416288115376906211003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193671221717487169208281337 145253416288115376906211003)
  ·
    refine ⟨217880124432173065359316505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145253416288115376906211003 217880124432173065359316505)
    ·
      refine ⟨163410093324129799019487379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217880124432173065359316505 163410093324129799019487379)
      ·
        refine ⟨245115139986194698529231069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163410093324129799019487379 245115139986194698529231069)
        ·
          refine ⟨91918177494823011948461651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245115139986194698529231069 91918177494823011948461651)
          ·
            refine ⟨137877266242234517922692477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91918177494823011948461651 137877266242234517922692477)
            ·
              refine ⟨51703974840837944221009679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137877266242234517922692477 51703974840837944221009679)
              ·
                refine ⟨77555962261256916331514519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51703974840837944221009679 77555962261256916331514519)
                ·
                  refine ⟨116333943391885374497271779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77555962261256916331514519 116333943391885374497271779)
                  ·
                    refine ⟨174500915087828061745907669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116333943391885374497271779 174500915087828061745907669)
                    ·
                      refine ⟨4089865197370970197169711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174500915087828061745907669 4089865197370970197169711)
                      ·
                        rfl

theorem cell23_7964984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_7964984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7964984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7964984 prefixEnd_7964984 := by exact prefixLift 7964984
  have htrace : WordTrace (prefixWord ++ tailWord_7964984) baseStart_7964984 baseEnd_7964984 := by
    simpa [prefixWord, tailWord_7964984, baseEnd_7964984] using wordTrace_append hprefix tailTrace_7964984
  have hstable : (prefixWord ++ tailWord_7964984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7964984).length < 2 ^ (prefixWord ++ tailWord_7964984).sum := by decide
  have hdescent : baseEnd_7964984 < baseStart_7964984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7964984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965011 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 6, 2]
def baseStart_7965011 : Nat := 118140960795 + 7965011 * 2 ^ 59
def prefixEnd_7965011 : Nat := 4983230072969 + 3 ^ 40 * 7965011 * 2
def baseEnd_7965011 : Nat := 4089879061348641591532087

theorem tailTrace_7965011 : CollatzResearch.WordTrace tailWord_7965011 prefixEnd_7965011 4089879061348641591532087 := by
  unfold tailWord_7965011
  simp only [CollatzResearch.WordTrace]
  refine ⟨290507817347132937423654887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193671878231421958282436591 290507817347132937423654887)
  ·
    refine ⟨435761726020699406135482331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290507817347132937423654887 435761726020699406135482331)
    ·
      refine ⟨653642589031049109203223497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435761726020699406135482331 653642589031049109203223497)
      ·
        refine ⟨490231941773286831902417623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653642589031049109203223497 490231941773286831902417623)
        ·
          refine ⟨735347912659930247853626435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490231941773286831902417623 735347912659930247853626435)
          ·
            refine ⟨1103021868989895371780439653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735347912659930247853626435 1103021868989895371780439653)
            ·
              refine ⟨206816600435605382208832435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1103021868989895371780439653 206816600435605382208832435)
              ·
                refine ⟨310224900653408073313248653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206816600435605382208832435 310224900653408073313248653)
                ·
                  refine ⟨116334337745028027492468245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310224900653408073313248653 116334337745028027492468245)
                  ·
                    refine ⟨5453172081798188788709449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116334337745028027492468245 5453172081798188788709449)
                    ·
                      refine ⟨4089879061348641591532087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453172081798188788709449 4089879061348641591532087)
                      ·
                        rfl

theorem cell23_7965011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6, 2].length) (baseStart_7965011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965011 prefixEnd_7965011 := by exact prefixLift 7965011
  have htrace : WordTrace (prefixWord ++ tailWord_7965011) baseStart_7965011 baseEnd_7965011 := by
    simpa [prefixWord, tailWord_7965011, baseEnd_7965011] using wordTrace_append hprefix tailTrace_7965011
  have hstable : (prefixWord ++ tailWord_7965011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965011).length < 2 ^ (prefixWord ++ tailWord_7965011).sum := by decide
  have hdescent : baseEnd_7965011 < baseStart_7965011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965028 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_7965028 : Nat := 118140960795 + 7965028 * 2 ^ 59
def prefixEnd_7965028 : Nat := 4983230072969 + 3 ^ 40 * 7965028 * 2
def baseEnd_7965028 : Nat := 4089887790519768025019509

theorem tailTrace_7965028 : CollatzResearch.WordTrace tailWord_7965028 prefixEnd_7965028 4089887790519768025019509 := by
  unfold tailWord_7965028
  simp only [CollatzResearch.WordTrace]
  refine ⟨145254218694035674663511869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193672291592047566218015825 145254218694035674663511869)
  ·
    refine ⟨54470332010263377998816951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145254218694035674663511869 54470332010263377998816951)
    ·
      refine ⟨81705498015395066998225427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54470332010263377998816951 81705498015395066998225427)
      ·
        refine ⟨122558247023092600497338141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81705498015395066998225427 122558247023092600497338141)
        ·
          refine ⟨45959342633659725186501803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122558247023092600497338141 45959342633659725186501803)
          ·
            refine ⟨68939013950489587779752705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45959342633659725186501803 68939013950489587779752705)
            ·
              refine ⟨51704260462867190834814529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68939013950489587779752705 51704260462867190834814529)
              ·
                refine ⟨38778195347150393126110897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51704260462867190834814529 38778195347150393126110897)
                ·
                  refine ⟨29083646510362794844583173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38778195347150393126110897 29083646510362794844583173)
                  ·
                    refine ⟨5453183720693024033359345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29083646510362794844583173 5453183720693024033359345)
                    ·
                      refine ⟨4089887790519768025019509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453183720693024033359345 4089887790519768025019509)
                      ·
                        rfl

theorem cell23_7965028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_7965028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965028 prefixEnd_7965028 := by exact prefixLift 7965028
  have htrace : WordTrace (prefixWord ++ tailWord_7965028) baseStart_7965028 baseEnd_7965028 := by
    simpa [prefixWord, tailWord_7965028, baseEnd_7965028] using wordTrace_append hprefix tailTrace_7965028
  have hstable : (prefixWord ++ tailWord_7965028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965028).length < 2 ^ (prefixWord ++ tailWord_7965028).sum := by decide
  have hdescent : baseEnd_7965028 < baseStart_7965028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965045 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7965045 : Nat := 118140960795 + 7965045 * 2 ^ 59
def prefixEnd_7965045 : Nat := 4983230072969 + 3 ^ 40 * 7965045 * 2
def baseEnd_7965045 : Nat := 4089896519690894458506931

theorem tailTrace_7965045 : CollatzResearch.WordTrace tailWord_7965045 prefixEnd_7965045 4089896519690894458506931 := by
  unfold tailWord_7965045
  simp only [CollatzResearch.WordTrace]
  refine ⟨290509057429009761230392589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193672704952673174153595059 290509057429009761230392589)
  ·
    refine ⟨108940896535878660461397221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290509057429009761230392589 108940896535878660461397221)
    ·
      refine ⟨20426418100477248836511979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108940896535878660461397221 20426418100477248836511979)
      ·
        refine ⟨30639627150715873254767969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20426418100477248836511979 30639627150715873254767969)
        ·
          refine ⟨22979720363036904941075977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30639627150715873254767969 22979720363036904941075977)
          ·
            refine ⟨17234790272277678705806983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22979720363036904941075977 17234790272277678705806983)
            ·
              refine ⟨25852185408416518058710475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17234790272277678705806983 25852185408416518058710475)
              ·
                refine ⟨38778278112624777088065713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25852185408416518058710475 38778278112624777088065713)
                ·
                  refine ⟨29083708584468582816049285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38778278112624777088065713 29083708584468582816049285)
                  ·
                    refine ⟨5453195359587859278009241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29083708584468582816049285 5453195359587859278009241)
                    ·
                      refine ⟨4089896519690894458506931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453195359587859278009241 4089896519690894458506931)
                      ·
                        rfl

theorem cell23_7965045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7965045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965045 prefixEnd_7965045 := by exact prefixLift 7965045
  have htrace : WordTrace (prefixWord ++ tailWord_7965045) baseStart_7965045 baseEnd_7965045 := by
    simpa [prefixWord, tailWord_7965045, baseEnd_7965045] using wordTrace_append hprefix tailTrace_7965045
  have hstable : (prefixWord ++ tailWord_7965045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965045).length < 2 ^ (prefixWord ++ tailWord_7965045).sum := by decide
  have hdescent : baseEnd_7965045 < baseStart_7965045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965051 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 6]
def baseStart_7965051 : Nat := 118140960795 + 7965051 * 2 ^ 59
def prefixEnd_7965051 : Nat := 4983230072969 + 3 ^ 40 * 7965051 * 2
def baseEnd_7965051 : Nat := 454433288952757937225767

theorem tailTrace_7965051 : CollatzResearch.WordTrace tailWord_7965051 prefixEnd_7965051 454433288952757937225767 := by
  unfold tailWord_7965051
  simp only [CollatzResearch.WordTrace]
  refine ⟨290509276266988024255111007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193672850844658682836740671 290509276266988024255111007)
  ·
    refine ⟨435763914400482036382666511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290509276266988024255111007 435763914400482036382666511)
    ·
      refine ⟨653645871600723054573999767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435763914400482036382666511 653645871600723054573999767)
      ·
        refine ⟨980468807401084581860999651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653645871600723054573999767 980468807401084581860999651)
        ·
          refine ⟨1470703211101626872791499477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980468807401084581860999651 1470703211101626872791499477)
          ·
            refine ⟨34469606510194379831050769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1470703211101626872791499477 34469606510194379831050769)
            ·
              refine ⟨25852204882645784873288077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34469606510194379831050769 25852204882645784873288077)
              ·
                refine ⟨9694576830992169327483029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25852204882645784873288077 9694576830992169327483029)
                ·
                  refine ⟨454433288952757937225767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9694576830992169327483029 454433288952757937225767)
                  ·
                    rfl

theorem cell23_7965051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 6].length) (baseStart_7965051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965051 prefixEnd_7965051 := by exact prefixLift 7965051
  have htrace : WordTrace (prefixWord ++ tailWord_7965051) baseStart_7965051 baseEnd_7965051 := by
    simpa [prefixWord, tailWord_7965051, baseEnd_7965051] using wordTrace_append hprefix tailTrace_7965051
  have hstable : (prefixWord ++ tailWord_7965051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965051).length < 2 ^ (prefixWord ++ tailWord_7965051).sum := by decide
  have hdescent : baseEnd_7965051 < baseStart_7965051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965065 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_7965065 : Nat := 118140960795 + 7965065 * 2 ^ 59
def prefixEnd_7965065 : Nat := 4983230072969 + 3 ^ 40 * 7965065 * 2
def baseEnd_7965065 : Nat := 4089906789303984380256839

theorem tailTrace_7965065 : CollatzResearch.WordTrace tailWord_7965065 prefixEnd_7965065 4089906789303984380256839 := by
  unfold tailWord_7965065
  simp only [CollatzResearch.WordTrace]
  refine ⟨290509786888937304646120649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193673191259291536430747099 290509786888937304646120649)
  ·
    refine ⟨217882340166702978484590487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290509786888937304646120649 217882340166702978484590487)
    ·
      refine ⟨326823510250054467726885731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217882340166702978484590487 326823510250054467726885731)
      ·
        refine ⟨490235265375081701590328597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326823510250054467726885731 490235265375081701590328597)
        ·
          refine ⟨22979778064456954762046653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 490235265375081701590328597 22979778064456954762046653)
          ·
            refine ⟨8617416774171358035767495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22979778064456954762046653 8617416774171358035767495)
            ·
              refine ⟨12926125161257037053651243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617416774171358035767495 12926125161257037053651243)
              ·
                refine ⟨19389187741885555580476865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926125161257037053651243 19389187741885555580476865)
                ·
                  refine ⟨14541890806414166685357649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19389187741885555580476865 14541890806414166685357649)
                  ·
                    refine ⟨10906418104810625014018237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14541890806414166685357649 10906418104810625014018237)
                    ·
                      refine ⟨4089906789303984380256839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906418104810625014018237 4089906789303984380256839)
                      ·
                        rfl

theorem cell23_7965065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_7965065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965065 prefixEnd_7965065 := by exact prefixLift 7965065
  have htrace : WordTrace (prefixWord ++ tailWord_7965065) baseStart_7965065 baseEnd_7965065 := by
    simpa [prefixWord, tailWord_7965065, baseEnd_7965065] using wordTrace_append hprefix tailTrace_7965065
  have hstable : (prefixWord ++ tailWord_7965065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965065).length < 2 ^ (prefixWord ++ tailWord_7965065).sum := by decide
  have hdescent : baseEnd_7965065 < baseStart_7965065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965085 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 6]
def baseStart_7965085 : Nat := 118140960795 + 7965085 * 2 ^ 59
def prefixEnd_7965085 : Nat := 4983230072969 + 3 ^ 40 * 7965085 * 2
def baseEnd_7965085 : Nat := 454435228768563811334083

theorem tailTrace_7965085 : CollatzResearch.WordTrace tailWord_7965085 prefixEnd_7965085 454435228768563811334083 := by
  unfold tailWord_7965085
  simp only [CollatzResearch.WordTrace]
  refine ⟨290510516348864848061848709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193673677565909898707899139 290510516348864848061848709)
  ·
    refine ⟨54470721815412159011596633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290510516348864848061848709 54470721815412159011596633)
    ·
      refine ⟨40853041361559119258697475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54470721815412159011596633 40853041361559119258697475)
      ·
        refine ⟨61279562042338678888046213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853041361559119258697475 61279562042338678888046213)
        ·
          refine ⟨11489917882938502291508665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61279562042338678888046213 11489917882938502291508665)
          ·
            refine ⟨8617438412203876718631499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11489917882938502291508665 8617438412203876718631499)
            ·
              refine ⟨12926157618305815077947249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617438412203876718631499 12926157618305815077947249)
              ·
                refine ⟨9694618213729361308460437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12926157618305815077947249 9694618213729361308460437)
                ·
                  refine ⟨454435228768563811334083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9694618213729361308460437 454435228768563811334083)
                  ·
                    rfl

theorem cell23_7965085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_7965085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965085 prefixEnd_7965085 := by exact prefixLift 7965085
  have htrace : WordTrace (prefixWord ++ tailWord_7965085) baseStart_7965085 baseEnd_7965085 := by
    simpa [prefixWord, tailWord_7965085, baseEnd_7965085] using wordTrace_append hprefix tailTrace_7965085
  have hstable : (prefixWord ++ tailWord_7965085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965085).length < 2 ^ (prefixWord ++ tailWord_7965085).sum := by decide
  have hdescent : baseEnd_7965085 < baseStart_7965085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965095 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7965095 : Nat := 118140960795 + 7965095 * 2 ^ 59
def prefixEnd_7965095 : Nat := 4983230072969 + 3 ^ 40 * 7965095 * 2
def baseEnd_7965095 : Nat := 4089922193723619262881701

theorem tailTrace_7965095 : CollatzResearch.WordTrace tailWord_7965095 prefixEnd_7965095 4089922193723619262881701 := by
  unfold tailWord_7965095
  simp only [CollatzResearch.WordTrace]
  refine ⟨290510881078828619769712739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193673920719219079846475159 290510881078828619769712739)
  ·
    refine ⟨435766321618242929654569109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290510881078828619769712739 435766321618242929654569109)
    ·
      refine ⟨20426546325855137327557927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435766321618242929654569109 20426546325855137327557927)
      ·
        refine ⟨30639819488782705991336891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20426546325855137327557927 30639819488782705991336891)
        ·
          refine ⟨45959729233174058987005337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30639819488782705991336891 45959729233174058987005337)
          ·
            refine ⟨34469796924880544240254003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45959729233174058987005337 34469796924880544240254003)
            ·
              refine ⟨51704695387320816360381005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34469796924880544240254003 51704695387320816360381005)
              ·
                refine ⟨19389260770245306135142877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51704695387320816360381005 19389260770245306135142877)
                ·
                  refine ⟨7270972788841989800678579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19389260770245306135142877 7270972788841989800678579)
                  ·
                    refine ⟨10906459183262984701017869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7270972788841989800678579 10906459183262984701017869)
                    ·
                      refine ⟨4089922193723619262881701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906459183262984701017869 4089922193723619262881701)
                      ·
                        rfl

theorem cell23_7965095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7965095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965095 prefixEnd_7965095 := by exact prefixLift 7965095
  have htrace : WordTrace (prefixWord ++ tailWord_7965095) baseStart_7965095 baseEnd_7965095 := by
    simpa [prefixWord, tailWord_7965095, baseEnd_7965095] using wordTrace_append hprefix tailTrace_7965095
  have hstable : (prefixWord ++ tailWord_7965095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965095).length < 2 ^ (prefixWord ++ tailWord_7965095).sum := by decide
  have hdescent : baseEnd_7965095 < baseStart_7965095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965118 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7965118 : Nat := 118140960795 + 7965118 * 2 ^ 59
def prefixEnd_7965118 : Nat := 4983230072969 + 3 ^ 40 * 7965118 * 2
def baseEnd_7965118 : Nat := 4089934003778672672894095

theorem tailTrace_7965118 : CollatzResearch.WordTrace tailWord_7965118 prefixEnd_7965118 4089934003778672672894095 := by
  unfold tailWord_7965118
  simp only [CollatzResearch.WordTrace]
  refine ⟨36313964994718161837225001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193674479971830196465200005 36313964994718161837225001)
  ·
    refine ⟨27235473746038621377918751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36313964994718161837225001 27235473746038621377918751)
    ·
      refine ⟨40853210619057932066878127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27235473746038621377918751 40853210619057932066878127)
      ·
        refine ⟨61279815928586898100317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853210619057932066878127 61279815928586898100317191)
        ·
          refine ⟨91919723892880347150475787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61279815928586898100317191 91919723892880347150475787)
          ·
            refine ⟨137879585839320520725713681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91919723892880347150475787 137879585839320520725713681)
            ·
              refine ⟨103409689379490390544285261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137879585839320520725713681 103409689379490390544285261)
              ·
                refine ⟨38778633517308896454106973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103409689379490390544285261 38778633517308896454106973)
                ·
                  refine ⟨14541987568990836170290115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38778633517308896454106973 14541987568990836170290115)
                  ·
                    refine ⟨21812981353486254255435173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14541987568990836170290115 21812981353486254255435173)
                    ·
                      refine ⟨4089934003778672672894095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21812981353486254255435173 4089934003778672672894095)
                      ·
                        rfl

theorem cell23_7965118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7965118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965118 prefixEnd_7965118 := by exact prefixLift 7965118
  have htrace : WordTrace (prefixWord ++ tailWord_7965118) baseStart_7965118 baseEnd_7965118 := by
    simpa [prefixWord, tailWord_7965118, baseEnd_7965118] using wordTrace_append hprefix tailTrace_7965118
  have hstable : (prefixWord ++ tailWord_7965118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965118).length < 2 ^ (prefixWord ++ tailWord_7965118).sum := by decide
  have hdescent : baseEnd_7965118 < baseStart_7965118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965128 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_7965128 : Nat := 118140960795 + 7965128 * 2 ^ 59
def prefixEnd_7965128 : Nat := 4983230072969 + 3 ^ 40 * 7965128 * 2
def baseEnd_7965128 : Nat := 1363313046195072544589683

theorem tailTrace_7965128 : CollatzResearch.WordTrace tailWord_7965128 prefixEnd_7965128 1363313046195072544589683 := by
  unfold tailWord_7965128
  simp only [CollatzResearch.WordTrace]
  refine ⟨145256042343854533202832019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193674723125139377603776025 145256042343854533202832019)
  ·
    refine ⟨217884063515781799804248029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145256042343854533202832019 217884063515781799804248029)
    ·
      refine ⟨81706523818418174926593011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217884063515781799804248029 81706523818418174926593011)
      ·
        refine ⟨122559785727627262389889517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81706523818418174926593011 122559785727627262389889517)
        ·
          refine ⟨45959919647860223396208569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122559785727627262389889517 45959919647860223396208569)
          ·
            refine ⟨34469939735895167547156427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45959919647860223396208569 34469939735895167547156427)
            ·
              refine ⟨51704909603842751320734641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34469939735895167547156427 51704909603842751320734641)
              ·
                refine ⟨38778682202882063490550981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51704909603842751320734641 38778682202882063490550981)
                ·
                  refine ⟨7271002913040386904478309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38778682202882063490550981 7271002913040386904478309)
                  ·
                    refine ⟨1363313046195072544589683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271002913040386904478309 1363313046195072544589683)
                    ·
                      rfl

theorem cell23_7965128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_7965128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965128 prefixEnd_7965128 := by exact prefixLift 7965128
  have htrace : WordTrace (prefixWord ++ tailWord_7965128) baseStart_7965128 baseEnd_7965128 := by
    simpa [prefixWord, tailWord_7965128, baseEnd_7965128] using wordTrace_append hprefix tailTrace_7965128
  have hstable : (prefixWord ++ tailWord_7965128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965128).length < 2 ^ (prefixWord ++ tailWord_7965128).sum := by decide
  have hdescent : baseEnd_7965128 < baseStart_7965128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965131 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_7965131 : Nat := 118140960795 + 7965131 * 2 ^ 59
def prefixEnd_7965131 : Nat := 4983230072969 + 3 ^ 40 * 7965131 * 2
def baseEnd_7965131 : Nat := 4089940679027181122031535

theorem tailTrace_7965131 : CollatzResearch.WordTrace tailWord_7965131 prefixEnd_7965131 4089940679027181122031535 := by
  unfold tailWord_7965131
  simp only [CollatzResearch.WordTrace]
  refine ⟨290512194106698197918023247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193674796071132131945348831 290512194106698197918023247)
  ·
    refine ⟨435768291160047296877034871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290512194106698197918023247 435768291160047296877034871)
    ·
      refine ⟨653652436740070945315552307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435768291160047296877034871 653652436740070945315552307)
      ·
        refine ⟨980478655110106417973328461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653652436740070945315552307 980478655110106417973328461)
        ·
          refine ⟨367679495666289906739998173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980478655110106417973328461 367679495666289906739998173)
          ·
            refine ⟨137879810874858715027499315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367679495666289906739998173 137879810874858715027499315)
            ·
              refine ⟨206819716312288072541248973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137879810874858715027499315 206819716312288072541248973)
              ·
                refine ⟨77557393617108027202968365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206819716312288072541248973 77557393617108027202968365)
                ·
                  refine ⟨29084022606415510201113137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77557393617108027202968365 29084022606415510201113137)
                  ·
                    refine ⟨21813016954811632650834853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29084022606415510201113137 21813016954811632650834853)
                    ·
                      refine ⟨4089940679027181122031535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21813016954811632650834853 4089940679027181122031535)
                      ·
                        rfl

theorem cell23_7965131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_7965131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965131 prefixEnd_7965131 := by exact prefixLift 7965131
  have htrace : WordTrace (prefixWord ++ tailWord_7965131) baseStart_7965131 baseEnd_7965131 := by
    simpa [prefixWord, tailWord_7965131, baseEnd_7965131] using wordTrace_append hprefix tailTrace_7965131
  have hstable : (prefixWord ++ tailWord_7965131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965131).length < 2 ^ (prefixWord ++ tailWord_7965131).sum := by decide
  have hdescent : baseEnd_7965131 < baseStart_7965131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965141 : List Nat := [1, 3, 2, 3, 1, 2, 11]
def baseStart_7965141 : Nat := 118140960795 + 7965141 * 2 ^ 59
def prefixEnd_7965141 : Nat := 4983230072969 + 3 ^ 40 * 7965141 * 2
def baseEnd_7965141 : Nat := 50493158195478099788969

theorem tailTrace_7965141 : CollatzResearch.WordTrace tailWord_7965141 prefixEnd_7965141 50493158195478099788969 := by
  unfold tailWord_7965141
  simp only [CollatzResearch.WordTrace]
  refine ⟨290512558836661969625887277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193675039224441313083924851 290512558836661969625887277)
  ·
    refine ⟨108942209563748238609707729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290512558836661969625887277 108942209563748238609707729)
    ·
      refine ⟨81706657172811178957280797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108942209563748238609707729 81706657172811178957280797)
      ·
        refine ⟨30639996439804192108980299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81706657172811178957280797 30639996439804192108980299)
        ·
          refine ⟨45959994659706288163470449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30639996439804192108980299 45959994659706288163470449)
          ·
            refine ⟨34469995994779716122602837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45959994659706288163470449 34469995994779716122602837)
            ·
              refine ⟨50493158195478099788969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34469995994779716122602837 50493158195478099788969)
              ·
                rfl

theorem cell23_7965141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 11].length) (baseStart_7965141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965141 prefixEnd_7965141 := by exact prefixLift 7965141
  have htrace : WordTrace (prefixWord ++ tailWord_7965141) baseStart_7965141 baseEnd_7965141 := by
    simpa [prefixWord, tailWord_7965141, baseEnd_7965141] using wordTrace_append hprefix tailTrace_7965141
  have hstable : (prefixWord ++ tailWord_7965141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965141).length < 2 ^ (prefixWord ++ tailWord_7965141).sum := by decide
  have hdescent : baseEnd_7965141 < baseStart_7965141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965162 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_7965162 : Nat := 118140960795 + 7965162 * 2 ^ 59
def prefixEnd_7965162 : Nat := 4983230072969 + 3 ^ 40 * 7965162 * 2
def baseEnd_7965162 : Nat := 1363318865642490166914631

theorem tailTrace_7965162 : CollatzResearch.WordTrace tailWord_7965162 prefixEnd_7965162 1363318865642490166914631 := by
  unfold tailWord_7965162
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628331192396472553100435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193675549846390593474934493 72628331192396472553100435)
  ·
    refine ⟨108942496788594708829650653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72628331192396472553100435 108942496788594708829650653)
    ·
      refine ⟨40853436295723015811118995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108942496788594708829650653 40853436295723015811118995)
      ·
        refine ⟨61280154443584523716678493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853436295723015811118995 61280154443584523716678493)
        ·
          refine ⟨22980057916344196393754435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61280154443584523716678493 22980057916344196393754435)
          ·
            refine ⟨34470086874516294590631653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980057916344196393754435 34470086874516294590631653)
            ·
              refine ⟨6463141288971805235743435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34470086874516294590631653 6463141288971805235743435)
              ·
                refine ⟨9694711933457707853615153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463141288971805235743435 9694711933457707853615153)
                ·
                  refine ⟨7271033950093280890211365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9694711933457707853615153 7271033950093280890211365)
                  ·
                    refine ⟨1363318865642490166914631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271033950093280890211365 1363318865642490166914631)
                    ·
                      rfl

theorem cell23_7965162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_7965162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965162 prefixEnd_7965162 := by exact prefixLift 7965162
  have htrace : WordTrace (prefixWord ++ tailWord_7965162) baseStart_7965162 baseEnd_7965162 := by
    simpa [prefixWord, tailWord_7965162, baseEnd_7965162] using wordTrace_append hprefix tailTrace_7965162
  have hstable : (prefixWord ++ tailWord_7965162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965162).length < 2 ^ (prefixWord ++ tailWord_7965162).sum := by decide
  have hdescent : baseEnd_7965162 < baseStart_7965162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
