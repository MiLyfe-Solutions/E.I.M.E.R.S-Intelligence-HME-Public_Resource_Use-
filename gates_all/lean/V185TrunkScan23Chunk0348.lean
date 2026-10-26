import V185TrunkScan23Chunk0347

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2058496 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 6]
def baseStart_2058496 : Nat := 118140960795 + 2058496 * 2 ^ 59
def prefixEnd_2058496 : Nat := 4983230072969 + 3 ^ 40 * 2058496 * 2
def baseEnd_2058496 : Nat := 117444208150853706514795

theorem tailTrace_2058496 : CollatzResearch.WordTrace tailWord_2058496 prefixEnd_2058496 117444208150853706514795 := by
  unfold tailWord_2058496
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539758575214014986269671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50053011433618686648359561 37539758575214014986269671)
  ·
    refine ⟨56309637862821022479404507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37539758575214014986269671 56309637862821022479404507)
    ·
      refine ⟨84464456794231533719106761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56309637862821022479404507 84464456794231533719106761)
      ·
        refine ⟨63348342595673650289330071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84464456794231533719106761 63348342595673650289330071)
        ·
          refine ⟨95022513893510475433995107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63348342595673650289330071 95022513893510475433995107)
          ·
            refine ⟨142533770840265713150992661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95022513893510475433995107 142533770840265713150992661)
            ·
              refine ⟨6681270508137455303952781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142533770840265713150992661 6681270508137455303952781)
              ·
                refine ⟨2505476440551545738982293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681270508137455303952781 2505476440551545738982293)
                ·
                  refine ⟨117444208150853706514795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2505476440551545738982293 117444208150853706514795)
                  ·
                    rfl

theorem cell23_2058496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_2058496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058496 prefixEnd_2058496 := by exact prefixLift 2058496
  have htrace : WordTrace (prefixWord ++ tailWord_2058496) baseStart_2058496 baseEnd_2058496 := by
    simpa [prefixWord, tailWord_2058496, baseEnd_2058496] using wordTrace_append hprefix tailTrace_2058496
  have hstable : (prefixWord ++ tailWord_2058496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058496).length < 2 ^ (prefixWord ++ tailWord_2058496).sum := by decide
  have hdescent : baseEnd_2058496 < baseStart_2058496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058500 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_2058500 : Nat := 118140960795 + 2058500 * 2 ^ 59
def prefixEnd_2058500 : Nat := 4983230072969 + 3 ^ 40 * 2058500 * 2
def baseEnd_2058500 : Nat := 352333309093433780994379

theorem tailTrace_2058500 : CollatzResearch.WordTrace tailWord_2058500 prefixEnd_2058500 352333309093433780994379 := by
  unfold tailWord_2058500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539831521206769327842477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50053108694942359103789969 37539831521206769327842477)
  ·
    refine ⟨14077436820452538497940929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37539831521206769327842477 14077436820452538497940929)
    ·
      refine ⟨10558077615339403873455697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14077436820452538497940929 10558077615339403873455697)
      ·
        refine ⟨7918558211504552905091773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10558077615339403873455697 7918558211504552905091773)
        ·
          refine ⟨2969459329314207339409415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7918558211504552905091773 2969459329314207339409415)
          ·
            refine ⟨4454188993971311009114123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969459329314207339409415 4454188993971311009114123)
            ·
              refine ⟨6681283490956966513671185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454188993971311009114123 6681283490956966513671185)
              ·
                refine ⟨5010962618217724885253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681283490956966513671185 5010962618217724885253389)
                ·
                  refine ⟨1879110981831646831970021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5010962618217724885253389 1879110981831646831970021)
                  ·
                    refine ⟨352333309093433780994379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879110981831646831970021 352333309093433780994379)
                    ·
                      rfl

theorem cell23_2058500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_2058500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058500 prefixEnd_2058500 := by exact prefixLift 2058500
  have htrace : WordTrace (prefixWord ++ tailWord_2058500) baseStart_2058500 baseEnd_2058500 := by
    simpa [prefixWord, tailWord_2058500, baseEnd_2058500] using wordTrace_append hprefix tailTrace_2058500
  have hstable : (prefixWord ++ tailWord_2058500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058500).length < 2 ^ (prefixWord ++ tailWord_2058500).sum := by decide
  have hdescent : baseEnd_2058500 < baseStart_2058500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058530 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2058530 : Nat := 118140960795 + 2058530 * 2 ^ 59
def prefixEnd_2058530 : Nat := 4983230072969 + 3 ^ 40 * 2058530 * 2
def baseEnd_2058530 : Nat := 117446147966659580623111

theorem tailTrace_2058530 : CollatzResearch.WordTrace tailWord_2058530 prefixEnd_2058530 117446147966659580623111 := by
  unfold tailWord_2058530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770189308076213444819261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50053838154869902519518029 18770189308076213444819261)
  ·
    refine ⟨7038820990528580041807223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18770189308076213444819261 7038820990528580041807223)
    ·
      refine ⟨10558231485792870062710835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038820990528580041807223 10558231485792870062710835)
      ·
        refine ⟨15837347228689305094066253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558231485792870062710835 15837347228689305094066253)
        ·
          refine ⟨5939005210758489410274845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15837347228689305094066253 5939005210758489410274845)
          ·
            refine ⟨2227126954034433528853067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5939005210758489410274845 2227126954034433528853067)
            ·
              refine ⟨3340690431051650293279601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227126954034433528853067 3340690431051650293279601)
              ·
                refine ⟨2505517823288737719959701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340690431051650293279601 2505517823288737719959701)
                ·
                  refine ⟨117446147966659580623111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2505517823288737719959701 117446147966659580623111)
                  ·
                    rfl

theorem cell23_2058530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2058530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058530 prefixEnd_2058530 := by exact prefixLift 2058530
  have htrace : WordTrace (prefixWord ++ tailWord_2058530) baseStart_2058530 baseEnd_2058530 := by
    simpa [prefixWord, tailWord_2058530, baseEnd_2058530] using wordTrace_append hprefix tailTrace_2058530
  have hstable : (prefixWord ++ tailWord_2058530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058530).length < 2 ^ (prefixWord ++ tailWord_2058530).sum := by decide
  have hdescent : baseEnd_2058530 < baseStart_2058530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058563 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 4]
def baseStart_2058563 : Nat := 118140960795 + 2058563 * 2 ^ 59
def prefixEnd_2058563 : Nat := 4983230072969 + 3 ^ 40 * 2058563 * 2
def baseEnd_2058563 : Nat := 1057032276561534596495347

theorem tailTrace_2058563 : CollatzResearch.WordTrace tailWord_2058563 prefixEnd_2058563 1057032276561534596495347 := by
  unfold tailWord_2058563
  simp only [CollatzResearch.WordTrace]
  refine ⟨75081960841185300415228343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50054640560790200276818895 75081960841185300415228343)
  ·
    refine ⟨112622941261777950622842515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75081960841185300415228343 112622941261777950622842515)
    ·
      refine ⟨168934411892666925934263773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112622941261777950622842515 168934411892666925934263773)
      ·
        refine ⟨63350404459750097225348915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168934411892666925934263773 63350404459750097225348915)
        ·
          refine ⟨95025606689625145838023373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63350404459750097225348915 95025606689625145838023373)
          ·
            refine ⟨35634602508609429689258765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95025606689625145838023373 35634602508609429689258765)
            ·
              refine ⟨13362975940728536133472037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35634602508609429689258765 13362975940728536133472037)
              ·
                refine ⟨2505557988886600525026007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13362975940728536133472037 2505557988886600525026007)
                ·
                  refine ⟨3758336983329900787539011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505557988886600525026007 3758336983329900787539011)
                  ·
                    refine ⟨5637505474994851181308517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758336983329900787539011 5637505474994851181308517)
                    ·
                      refine ⟨1057032276561534596495347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5637505474994851181308517 1057032276561534596495347)
                      ·
                        rfl

theorem cell23_2058563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_2058563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058563 prefixEnd_2058563 := by exact prefixLift 2058563
  have htrace : WordTrace (prefixWord ++ tailWord_2058563) baseStart_2058563 baseEnd_2058563 := by
    simpa [prefixWord, tailWord_2058563, baseEnd_2058563] using wordTrace_append hprefix tailTrace_2058563
  have hstable : (prefixWord ++ tailWord_2058563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058563).length < 2 ^ (prefixWord ++ tailWord_2058563).sum := by decide
  have hdescent : baseEnd_2058563 < baseStart_2058563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058580 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2058580 : Nat := 118140960795 + 2058580 * 2 ^ 59
def prefixEnd_2058580 : Nat := 4983230072969 + 3 ^ 40 * 2058580 * 2
def baseEnd_2058580 : Nat := 1057041005732661029982769

theorem tailTrace_2058580 : CollatzResearch.WordTrace tailWord_2058580 prefixEnd_2058580 1057041005732661029982769 := by
  unfold tailWord_2058580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37541290441061856159298597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50055053921415808212398129 37541290441061856159298597)
  ·
    refine ⟨7038991957699098029868487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37541290441061856159298597 7038991957699098029868487)
    ·
      refine ⟨10558487936548647044802731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038991957699098029868487 10558487936548647044802731)
      ·
        refine ⟨15837731904822970567204097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558487936548647044802731 15837731904822970567204097)
        ·
          refine ⟨11878298928617227925403073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15837731904822970567204097 11878298928617227925403073)
          ·
            refine ⟨8908724196462920944052305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878298928617227925403073 8908724196462920944052305)
            ·
              refine ⟨6681543147347190708039229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8908724196462920944052305 6681543147347190708039229)
              ·
                refine ⟨2505578680255196515514711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681543147347190708039229 2505578680255196515514711)
                ·
                  refine ⟨3758368020382794773272067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505578680255196515514711 3758368020382794773272067)
                  ·
                    refine ⟨5637552030574192159908101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758368020382794773272067 5637552030574192159908101)
                    ·
                      refine ⟨1057041005732661029982769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5637552030574192159908101 1057041005732661029982769)
                      ·
                        rfl

theorem cell23_2058580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2058580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058580 prefixEnd_2058580 := by exact prefixLift 2058580
  have htrace : WordTrace (prefixWord ++ tailWord_2058580) baseStart_2058580 baseEnd_2058580 := by
    simpa [prefixWord, tailWord_2058580, baseEnd_2058580] using wordTrace_append hprefix tailTrace_2058580
  have hstable : (prefixWord ++ tailWord_2058580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058580).length < 2 ^ (prefixWord ++ tailWord_2058580).sum := by decide
  have hdescent : baseEnd_2058580 < baseStart_2058580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058583 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_2058583 : Nat := 118140960795 + 2058583 * 2 ^ 59
def prefixEnd_2058583 : Nat := 4983230072969 + 3 ^ 40 * 2058583 * 2
def baseEnd_2058583 : Nat := 1057042546174624518245255

theorem tailTrace_2058583 : CollatzResearch.WordTrace tailWord_2058583 prefixEnd_2058583 1057042546174624518245255 := by
  unfold tailWord_2058583
  simp only [CollatzResearch.WordTrace]
  refine ⟨75082690301112843830956403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50055126867408562553970935 75082690301112843830956403)
  ·
    refine ⟨112624035451669265746434605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75082690301112843830956403 112624035451669265746434605)
    ·
      refine ⟨42234013294375974654912977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112624035451669265746434605 42234013294375974654912977)
      ·
        refine ⟨31675509970781980991184733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42234013294375974654912977 31675509970781980991184733)
        ·
          refine ⟨11878316239043242871694275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31675509970781980991184733 11878316239043242871694275)
          ·
            refine ⟨17817474358564864307541413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11878316239043242871694275 17817474358564864307541413)
            ·
              refine ⟨3340776442230912057664015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17817474358564864307541413 3340776442230912057664015)
              ·
                refine ⟨5011164663346368086496023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340776442230912057664015 5011164663346368086496023)
                ·
                  refine ⟨7516746995019552129744035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011164663346368086496023 7516746995019552129744035)
                  ·
                    refine ⟨11275120492529328194616053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516746995019552129744035 11275120492529328194616053)
                    ·
                      refine ⟨1057042546174624518245255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11275120492529328194616053 1057042546174624518245255)
                      ·
                        rfl

theorem cell23_2058583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_2058583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058583 prefixEnd_2058583 := by exact prefixLift 2058583
  have htrace : WordTrace (prefixWord ++ tailWord_2058583) baseStart_2058583 baseEnd_2058583 := by
    simpa [prefixWord, tailWord_2058583, baseEnd_2058583] using wordTrace_append hprefix tailTrace_2058583
  have hstable : (prefixWord ++ tailWord_2058583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058583).length < 2 ^ (prefixWord ++ tailWord_2058583).sum := by decide
  have hdescent : baseEnd_2058583 < baseStart_2058583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058597 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_2058597 : Nat := 118140960795 + 2058597 * 2 ^ 59
def prefixEnd_2058597 : Nat := 4983230072969 + 3 ^ 40 * 2058597 * 2
def baseEnd_2058597 : Nat := 1057049734903787463470191

theorem tailTrace_2058597 : CollatzResearch.WordTrace tailWord_2058597 prefixEnd_2058597 1057049734903787463470191 := by
  unfold tailWord_2058597
  simp only [CollatzResearch.WordTrace]
  refine ⟨75083200923062124221966045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50055467282041416147977363 75083200923062124221966045)
  ·
    refine ⟨28156200346148296583237267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75083200923062124221966045 28156200346148296583237267)
    ·
      refine ⟨42234300519222444874855901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28156200346148296583237267 42234300519222444874855901)
      ·
        refine ⟨15837862694708416828070963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42234300519222444874855901 15837862694708416828070963)
        ·
          refine ⟨23756794042062625242106445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837862694708416828070963 23756794042062625242106445)
          ·
            refine ⟨8908797765773484465789917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23756794042062625242106445 8908797765773484465789917)
            ·
              refine ⟨3340799162165056674671219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8908797765773484465789917 3340799162165056674671219)
              ·
                refine ⟨5011198743247585012006829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340799162165056674671219 5011198743247585012006829)
                ·
                  refine ⟨1879199528717844379502561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5011198743247585012006829 1879199528717844379502561)
                  ·
                    refine ⟨1409399646538383284626921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879199528717844379502561 1409399646538383284626921)
                    ·
                      refine ⟨1057049734903787463470191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409399646538383284626921 1057049734903787463470191)
                      ·
                        rfl

theorem cell23_2058597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_2058597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058597 prefixEnd_2058597 := by exact prefixLift 2058597
  have htrace : WordTrace (prefixWord ++ tailWord_2058597) baseStart_2058597 baseEnd_2058597 := by
    simpa [prefixWord, tailWord_2058597, baseEnd_2058597] using wordTrace_append hprefix tailTrace_2058597
  have hstable : (prefixWord ++ tailWord_2058597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058597).length < 2 ^ (prefixWord ++ tailWord_2058597).sum := by decide
  have hdescent : baseEnd_2058597 < baseStart_2058597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058623 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 7, 2]
def baseStart_2058623 : Nat := 118140960795 + 2058623 * 2 ^ 59
def prefixEnd_2058623 : Nat := 4983230072969 + 3 ^ 40 * 2058623 * 2
def baseEnd_2058623 : Nat := 1057063085400804361745071

theorem tailTrace_2058623 : CollatzResearch.WordTrace tailWord_2058623 prefixEnd_2058623 1057063085400804361745071 := by
  unfold tailWord_2058623
  simp only [CollatzResearch.WordTrace]
  refine ⟨75084149220967930662412523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50056099480645287108275015 75084149220967930662412523)
  ·
    refine ⟨112626223831451895993618785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75084149220967930662412523 112626223831451895993618785)
    ·
      refine ⟨84469667873588921995214089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112626223831451895993618785 84469667873588921995214089)
      ·
        refine ⟨63352250905191691496410567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84469667873588921995214089 63352250905191691496410567)
        ·
          refine ⟨95028376357787537244615851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63352250905191691496410567 95028376357787537244615851)
          ·
            refine ⟨142542564536681305866923777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95028376357787537244615851 142542564536681305866923777)
            ·
              refine ⟨106906923402510979400192833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142542564536681305866923777 106906923402510979400192833)
              ·
                refine ⟨80180192551883234550144625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106906923402510979400192833 80180192551883234550144625)
                ·
                  refine ⟨60135144413912425912608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80180192551883234550144625 60135144413912425912608469)
                  ·
                    refine ⟨1409417447201072482326761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60135144413912425912608469 1409417447201072482326761)
                    ·
                      refine ⟨1057063085400804361745071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409417447201072482326761 1057063085400804361745071)
                      ·
                        rfl

theorem cell23_2058623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_2058623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058623 prefixEnd_2058623 := by exact prefixLift 2058623
  have htrace : WordTrace (prefixWord ++ tailWord_2058623) baseStart_2058623 baseEnd_2058623 := by
    simpa [prefixWord, tailWord_2058623, baseEnd_2058623] using wordTrace_append hprefix tailTrace_2058623
  have hstable : (prefixWord ++ tailWord_2058623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058623).length < 2 ^ (prefixWord ++ tailWord_2058623).sum := by decide
  have hdescent : baseEnd_2058623 < baseStart_2058623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058634 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2058634 : Nat := 118140960795 + 2058634 * 2 ^ 59
def prefixEnd_2058634 : Nat := 4983230072969 + 3 ^ 40 * 2058634 * 2
def baseEnd_2058634 : Nat := 1057068733688003818707521

theorem tailTrace_2058634 : CollatzResearch.WordTrace tailWord_2058634 prefixEnd_2058634 1057068733688003818707521 := by
  unfold tailWord_2058634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18771137605982019885265739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50056366949285386360708637 18771137605982019885265739)
  ·
    refine ⟨28156706408973029827898609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18771137605982019885265739 28156706408973029827898609)
    ·
      refine ⟨21117529806729772370923957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28156706408973029827898609 21117529806729772370923957)
      ·
        refine ⟨1979768419380916159774121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21117529806729772370923957 1979768419380916159774121)
        ·
          refine ⟨1484826314535687119830591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979768419380916159774121 1484826314535687119830591)
          ·
            refine ⟨2227239471803530679745887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484826314535687119830591 2227239471803530679745887)
            ·
              refine ⟨3340859207705296019618831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227239471803530679745887 3340859207705296019618831)
              ·
                refine ⟨5011288811557944029428247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340859207705296019618831 5011288811557944029428247)
                ·
                  refine ⟨7516933217336916044142371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011288811557944029428247 7516933217336916044142371)
                  ·
                    refine ⟨11275399826005374066213557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516933217336916044142371 11275399826005374066213557)
                    ·
                      refine ⟨1057068733688003818707521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11275399826005374066213557 1057068733688003818707521)
                      ·
                        rfl

theorem cell23_2058634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2058634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058634 prefixEnd_2058634 := by exact prefixLift 2058634
  have htrace : WordTrace (prefixWord ++ tailWord_2058634) baseStart_2058634 baseEnd_2058634 := by
    simpa [prefixWord, tailWord_2058634, baseEnd_2058634] using wordTrace_append hprefix tailTrace_2058634
  have hstable : (prefixWord ++ tailWord_2058634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058634).length < 2 ^ (prefixWord ++ tailWord_2058634).sum := by decide
  have hdescent : baseEnd_2058634 < baseStart_2058634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058648 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2058648 : Nat := 118140960795 + 2058648 * 2 ^ 59
def prefixEnd_2058648 : Nat := 4983230072969 + 3 ^ 40 * 2058648 * 2
def baseEnd_2058648 : Nat := 1057075922417166763932457

theorem tailTrace_2058648 : CollatzResearch.WordTrace tailWord_2058648 prefixEnd_2058648 1057075922417166763932457 := by
  unfold tailWord_2058648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37542530522938679966036299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50056707363918239954715065 37542530522938679966036299)
  ·
    refine ⟨56313795784408019949054449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37542530522938679966036299 56313795784408019949054449)
    ·
      refine ⟨42235346838306014961790837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56313795784408019949054449 42235346838306014961790837)
      ·
        refine ⟨3959563766091188902667891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42235346838306014961790837 3959563766091188902667891)
        ·
          refine ⟨5939345649136783354001837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959563766091188902667891 5939345649136783354001837)
          ·
            refine ⟨2227254618426293757750689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5939345649136783354001837 2227254618426293757750689)
            ·
              refine ⟨1670440963819720318313017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227254618426293757750689 1670440963819720318313017)
              ·
                refine ⟨1252830722864790238734763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670440963819720318313017 1252830722864790238734763)
                ·
                  refine ⟨1879246084297185358102145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252830722864790238734763 1879246084297185358102145)
                  ·
                    refine ⟨1409434563222889018576609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879246084297185358102145 1409434563222889018576609)
                    ·
                      refine ⟨1057075922417166763932457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409434563222889018576609 1057075922417166763932457)
                      ·
                        rfl

theorem cell23_2058648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2058648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058648 prefixEnd_2058648 := by exact prefixLift 2058648
  have htrace : WordTrace (prefixWord ++ tailWord_2058648) baseStart_2058648 baseEnd_2058648 := by
    simpa [prefixWord, tailWord_2058648, baseEnd_2058648] using wordTrace_append hprefix tailTrace_2058648
  have hstable : (prefixWord ++ tailWord_2058648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058648).length < 2 ^ (prefixWord ++ tailWord_2058648).sum := by decide
  have hdescent : baseEnd_2058648 < baseStart_2058648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058663 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2058663 : Nat := 118140960795 + 2058663 * 2 ^ 59
def prefixEnd_2058663 : Nat := 4983230072969 + 3 ^ 40 * 2058663 * 2
def baseEnd_2058663 : Nat := 352361208208994735081629

theorem tailTrace_2058663 : CollatzResearch.WordTrace tailWord_2058663 prefixEnd_2058663 352361208208994735081629 := by
  unfold tailWord_2058663
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085608140823017493868643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50057072093882011662579095 75085608140823017493868643)
  ·
    refine ⟨112628412211234526240802965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085608140823017493868643 112628412211234526240802965)
    ·
      refine ⟨5279456822401618417537639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112628412211234526240802965 5279456822401618417537639)
      ·
        refine ⟨7919185233602427626306459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279456822401618417537639 7919185233602427626306459)
        ·
          refine ⟨11878777850403641439459689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919185233602427626306459 11878777850403641439459689)
          ·
            refine ⟨8909083387802731079594767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878777850403641439459689 8909083387802731079594767)
            ·
              refine ⟨13363625081704096619392151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909083387802731079594767 13363625081704096619392151)
              ·
                refine ⟨20045437622556144929088227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13363625081704096619392151 20045437622556144929088227)
                ·
                  refine ⟨30068156433834217393632341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20045437622556144929088227 30068156433834217393632341)
                  ·
                    refine ⟨352361208208994735081629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30068156433834217393632341 352361208208994735081629)
                    ·
                      rfl

theorem cell23_2058663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2058663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058663 prefixEnd_2058663 := by exact prefixLift 2058663
  have htrace : WordTrace (prefixWord ++ tailWord_2058663) baseStart_2058663 baseEnd_2058663 := by
    simpa [prefixWord, tailWord_2058663, baseEnd_2058663] using wordTrace_append hprefix tailTrace_2058663
  have hstable : (prefixWord ++ tailWord_2058663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058663).length < 2 ^ (prefixWord ++ tailWord_2058663).sum := by decide
  have hdescent : baseEnd_2058663 < baseStart_2058663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058664 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2058664 : Nat := 118140960795 + 2058664 * 2 ^ 59
def prefixEnd_2058664 : Nat := 4983230072969 + 3 ^ 40 * 2058664 * 2
def baseEnd_2058664 : Nat := 1057084138107638701332383

theorem tailTrace_2058664 : CollatzResearch.WordTrace tailWord_2058664 prefixEnd_2058664 1057084138107638701332383 := by
  unfold tailWord_2058664
  simp only [CollatzResearch.WordTrace]
  refine ⟨37542822306909697332327523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50057096409212929776436697 37542822306909697332327523)
  ·
    refine ⟨56314233460364545998491285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37542822306909697332327523 56314233460364545998491285)
    ·
      refine ⟨2639729693454588093679279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56314233460364545998491285 2639729693454588093679279)
      ·
        refine ⟨3959594540181882140518919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639729693454588093679279 3959594540181882140518919)
        ·
          refine ⟨5939391810272823210778379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959594540181882140518919 5939391810272823210778379)
          ·
            refine ⟨8909087715409234816167569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939391810272823210778379 8909087715409234816167569)
            ·
              refine ⟨6681815786556926112125677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909087715409234816167569 6681815786556926112125677)
              ·
                refine ⟨2505680919958847292047129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681815786556926112125677 2505680919958847292047129)
                ·
                  refine ⟨1879260689969135469035347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505680919958847292047129 1879260689969135469035347)
                  ·
                    refine ⟨2818891034953703203553021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1879260689969135469035347 2818891034953703203553021)
                    ·
                      refine ⟨1057084138107638701332383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2818891034953703203553021 1057084138107638701332383)
                      ·
                        rfl

theorem cell23_2058664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2058664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058664 prefixEnd_2058664 := by exact prefixLift 2058664
  have htrace : WordTrace (prefixWord ++ tailWord_2058664) baseStart_2058664 baseEnd_2058664 := by
    simpa [prefixWord, tailWord_2058664, baseEnd_2058664] using wordTrace_append hprefix tailTrace_2058664
  have hstable : (prefixWord ++ tailWord_2058664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058664).length < 2 ^ (prefixWord ++ tailWord_2058664).sum := by decide
  have hdescent : baseEnd_2058664 < baseStart_2058664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058817 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 6]
def baseStart_2058817 : Nat := 118140960795 + 2058817 * 2 ^ 59
def prefixEnd_2058817 : Nat := 4983230072969 + 3 ^ 40 * 2058817 * 2
def baseEnd_2058817 : Nat := 117462522294197400302131

theorem tailTrace_2058817 : CollatzResearch.WordTrace tailWord_2058817 prefixEnd_2058817 117462522294197400302131 := by
  unfold tailWord_2058817
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091224982265101794974705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50060816654843401196649803 75091224982265101794974705)
  ·
    refine ⟨56318418736698826346231029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75091224982265101794974705 56318418736698826346231029)
    ·
      refine ⟨5279851756565514969959159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56318418736698826346231029 5279851756565514969959159)
      ·
        refine ⟨7919777634848272454938739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279851756565514969959159 7919777634848272454938739)
        ·
          refine ⟨11879666452272408682408109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919777634848272454938739 11879666452272408682408109)
          ·
            refine ⟨4454874919602153255903041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11879666452272408682408109 4454874919602153255903041)
            ·
              refine ⟨3341156189701614941927281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454874919602153255903041 3341156189701614941927281)
              ·
                refine ⟨2505867142276211206445461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341156189701614941927281 2505867142276211206445461)
                ·
                  refine ⟨117462522294197400302131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2505867142276211206445461 117462522294197400302131)
                  ·
                    rfl

theorem cell23_2058817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_2058817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058817 prefixEnd_2058817 := by exact prefixLift 2058817
  have htrace : WordTrace (prefixWord ++ tailWord_2058817) baseStart_2058817 baseEnd_2058817 := by
    simpa [prefixWord, tailWord_2058817, baseEnd_2058817] using wordTrace_append hprefix tailTrace_2058817
  have hstable : (prefixWord ++ tailWord_2058817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058817).length < 2 ^ (prefixWord ++ tailWord_2058817).sum := by decide
  have hdescent : baseEnd_2058817 < baseStart_2058817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058821 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_2058821 : Nat := 118140960795 + 2058821 * 2 ^ 59
def prefixEnd_2058821 : Nat := 4983230072969 + 3 ^ 40 * 2058821 * 2
def baseEnd_2058821 : Nat := 352388251523464862356387

theorem tailTrace_2058821 : CollatzResearch.WordTrace tailWord_2058821 prefixEnd_2058821 352388251523464862356387 := by
  unfold tailWord_2058821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091370874250610478120317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50060913916167073652080211 75091370874250610478120317)
  ·
    refine ⟨28159264077843978929295119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75091370874250610478120317 28159264077843978929295119)
    ·
      refine ⟨42238896116765968393942679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28159264077843978929295119 42238896116765968393942679)
      ·
        refine ⟨63358344175148952590914019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42238896116765968393942679 63358344175148952590914019)
        ·
          refine ⟨95037516262723428886371029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63358344175148952590914019 95037516262723428886371029)
          ·
            refine ⟨2227441787407580364524321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95037516262723428886371029 2227441787407580364524321)
            ·
              refine ⟨1670581340555685273393241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227441787407580364524321 1670581340555685273393241)
              ·
                refine ⟨1252936005416763955044931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670581340555685273393241 1252936005416763955044931)
                ·
                  refine ⟨1879404008125145932567397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252936005416763955044931 1879404008125145932567397)
                  ·
                    refine ⟨352388251523464862356387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879404008125145932567397 352388251523464862356387)
                    ·
                      rfl

theorem cell23_2058821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_2058821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058821 prefixEnd_2058821 := by exact prefixLift 2058821
  have htrace : WordTrace (prefixWord ++ tailWord_2058821) baseStart_2058821 baseEnd_2058821 := by
    simpa [prefixWord, tailWord_2058821, baseEnd_2058821] using wordTrace_append hprefix tailTrace_2058821
  have hstable : (prefixWord ++ tailWord_2058821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058821).length < 2 ^ (prefixWord ++ tailWord_2058821).sum := by decide
  have hdescent : baseEnd_2058821 < baseStart_2058821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058830 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2058830 : Nat := 118140960795 + 2058830 * 2 ^ 59
def prefixEnd_2058830 : Nat := 4983230072969 + 3 ^ 40 * 2058830 * 2
def baseEnd_2058830 : Nat := 352389791965428350618873

theorem tailTrace_2058830 : CollatzResearch.WordTrace tailWord_2058830 prefixEnd_2058830 352389791965428350618873 := by
  unfold tailWord_2058830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9386462391402250626899743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50061132754145336676798629 9386462391402250626899743)
  ·
    refine ⟨14079693587103375940349615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9386462391402250626899743 14079693587103375940349615)
    ·
      refine ⟨21119540380655063910524423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14079693587103375940349615 21119540380655063910524423)
      ·
        refine ⟨31679310570982595865786635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21119540380655063910524423 31679310570982595865786635)
        ·
          refine ⟨47518965856473893798679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679310570982595865786635 47518965856473893798679953)
          ·
            refine ⟨35639224392355420349009965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47518965856473893798679953 35639224392355420349009965)
            ·
              refine ⟨13364709147133282630878737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35639224392355420349009965 13364709147133282630878737)
              ·
                refine ⟨10023531860349961973159053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13364709147133282630878737 10023531860349961973159053)
                ·
                  refine ⟨3758824447631235739934645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10023531860349961973159053 3758824447631235739934645)
                  ·
                    refine ⟨352389791965428350618873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3758824447631235739934645 352389791965428350618873)
                    ·
                      rfl

theorem cell23_2058830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2058830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058830 prefixEnd_2058830 := by exact prefixLift 2058830
  have htrace : WordTrace (prefixWord ++ tailWord_2058830) baseStart_2058830 baseEnd_2058830 := by
    simpa [prefixWord, tailWord_2058830, baseEnd_2058830] using wordTrace_append hprefix tailTrace_2058830
  have hstable : (prefixWord ++ tailWord_2058830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058830).length < 2 ^ (prefixWord ++ tailWord_2058830).sum := by decide
  have hdescent : baseEnd_2058830 < baseStart_2058830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058837 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2058837 : Nat := 118140960795 + 2058837 * 2 ^ 59
def prefixEnd_2058837 : Nat := 4983230072969 + 3 ^ 40 * 2058837 * 2
def baseEnd_2058837 : Nat := 1057172970260866524469087

theorem tailTrace_2058837 : CollatzResearch.WordTrace tailWord_2058837 prefixEnd_2058837 1057172970260866524469087 := by
  unfold tailWord_2058837
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091954442192645210702765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50061302961461763473801843 75091954442192645210702765)
  ·
    refine ⟨28159482915822241954013537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75091954442192645210702765 28159482915822241954013537)
    ·
      refine ⟨21119612186866681465510153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28159482915822241954013537 21119612186866681465510153)
      ·
        refine ⟨15839709140150011099132615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21119612186866681465510153 15839709140150011099132615)
        ·
          refine ⟨23759563710225016648698923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15839709140150011099132615 23759563710225016648698923)
          ·
            refine ⟨35639345565337524973048385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23759563710225016648698923 35639345565337524973048385)
            ·
              refine ⟨26729509174003143729786289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35639345565337524973048385 26729509174003143729786289)
              ·
                refine ⟨20047131880502357797339717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26729509174003143729786289 20047131880502357797339717)
                ·
                  refine ⟨3758837227594192087001197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20047131880502357797339717 3758837227594192087001197)
                  ·
                    refine ⟨1409563960347822032625449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758837227594192087001197 1409563960347822032625449)
                    ·
                      refine ⟨1057172970260866524469087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409563960347822032625449 1057172970260866524469087)
                      ·
                        rfl

theorem cell23_2058837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2058837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058837 prefixEnd_2058837 := by exact prefixLift 2058837
  have htrace : WordTrace (prefixWord ++ tailWord_2058837) baseStart_2058837 baseEnd_2058837 := by
    simpa [prefixWord, tailWord_2058837, baseEnd_2058837] using wordTrace_append hprefix tailTrace_2058837
  have hstable : (prefixWord ++ tailWord_2058837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058837).length < 2 ^ (prefixWord ++ tailWord_2058837).sum := by decide
  have hdescent : baseEnd_2058837 < baseStart_2058837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058860 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_2058860 : Nat := 118140960795 + 2058860 * 2 ^ 59
def prefixEnd_2058860 : Nat := 4983230072969 + 3 ^ 40 * 2058860 * 2
def baseEnd_2058860 : Nat := 352394926771973311493827

theorem tailTrace_2058860 : CollatzResearch.WordTrace tailWord_2058860 prefixEnd_2058860 352394926771973311493827 := by
  unfold tailWord_2058860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37546396660554660069395017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50061862214072880092526689 37546396660554660069395017)
  ·
    refine ⟨28159797495415995052046263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37546396660554660069395017 28159797495415995052046263)
    ·
      refine ⟨42239696243123992578069395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28159797495415995052046263 42239696243123992578069395)
      ·
        refine ⟨63359544364685988867104093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42239696243123992578069395 63359544364685988867104093)
        ·
          refine ⟨23759829136757245825164035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63359544364685988867104093 23759829136757245825164035)
          ·
            refine ⟨35639743705135868737746053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23759829136757245825164035 35639743705135868737746053)
            ·
              refine ⟨6682451944712975388327385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35639743705135868737746053 6682451944712975388327385)
              ·
                refine ⟨5011838958534731541245539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682451944712975388327385 5011838958534731541245539)
                ·
                  refine ⟨7517758437802097311868309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011838958534731541245539 7517758437802097311868309)
                  ·
                    refine ⟨352394926771973311493827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7517758437802097311868309 352394926771973311493827)
                    ·
                      rfl

theorem cell23_2058860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_2058860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058860 prefixEnd_2058860 := by exact prefixLift 2058860
  have htrace : WordTrace (prefixWord ++ tailWord_2058860) baseStart_2058860 baseEnd_2058860 := by
    simpa [prefixWord, tailWord_2058860, baseEnd_2058860] using wordTrace_append hprefix tailTrace_2058860
  have hstable : (prefixWord ++ tailWord_2058860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058860).length < 2 ^ (prefixWord ++ tailWord_2058860).sum := by decide
  have hdescent : baseEnd_2058860 < baseStart_2058860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058861 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2058861 : Nat := 118140960795 + 2058861 * 2 ^ 59
def prefixEnd_2058861 : Nat := 4983230072969 + 3 ^ 40 * 2058861 * 2
def baseEnd_2058861 : Nat := 1057185293796574430568977

theorem tailTrace_2058861 : CollatzResearch.WordTrace tailWord_2058861 prefixEnd_2058861 1057185293796574430568977 := by
  unfold tailWord_2058861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75092829794105697309576437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50061886529403798206384291 75092829794105697309576437)
  ·
    refine ⟨7039952793197409122772791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75092829794105697309576437 7039952793197409122772791)
    ·
      refine ⟨10559929189796113684159187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7039952793197409122772791 10559929189796113684159187)
      ·
        refine ⟨15839893784694170526238781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10559929189796113684159187 15839893784694170526238781)
        ·
          refine ⟨5939960169260313947339543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15839893784694170526238781 5939960169260313947339543)
          ·
            refine ⟨8909940253890470921009315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939960169260313947339543 8909940253890470921009315)
            ·
              refine ⟨13364910380835706381513973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909940253890470921009315 13364910380835706381513973)
              ·
                refine ⟨1252960348203347473266935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13364910380835706381513973 1252960348203347473266935)
                ·
                  refine ⟨1879440522305021209900403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252960348203347473266935 1879440522305021209900403)
                  ·
                    refine ⟨2819160783457531814850605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1879440522305021209900403 2819160783457531814850605)
                    ·
                      refine ⟨1057185293796574430568977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819160783457531814850605 1057185293796574430568977)
                      ·
                        rfl

theorem cell23_2058861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2058861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058861 prefixEnd_2058861 := by exact prefixLift 2058861
  have htrace : WordTrace (prefixWord ++ tailWord_2058861) baseStart_2058861 baseEnd_2058861 := by
    simpa [prefixWord, tailWord_2058861, baseEnd_2058861] using wordTrace_append hprefix tailTrace_2058861
  have hstable : (prefixWord ++ tailWord_2058861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058861).length < 2 ^ (prefixWord ++ tailWord_2058861).sum := by decide
  have hdescent : baseEnd_2058861 < baseStart_2058861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058904 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2058904 : Nat := 118140960795 + 2058904 * 2 ^ 59
def prefixEnd_2058904 : Nat := 4983230072969 + 3 ^ 40 * 2058904 * 2
def baseEnd_2058904 : Nat := 1057207373464717762331279

theorem tailTrace_2058904 : CollatzResearch.WordTrace tailWord_2058904 prefixEnd_2058904 1057207373464717762331279 := by
  unfold tailWord_2058904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547199066474957826695883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50062932088633277102261177 37547199066474957826695883)
  ·
    refine ⟨56320798599712436740043825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37547199066474957826695883 56320798599712436740043825)
    ·
      refine ⟨42240598949784327555032869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56320798599712436740043825 42240598949784327555032869)
      ·
        refine ⟨7920112303084561416568663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42240598949784327555032869 7920112303084561416568663)
        ·
          refine ⟨11880168454626842124852995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920112303084561416568663 11880168454626842124852995)
          ·
            refine ⟨17820252681940263187279493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11880168454626842124852995 17820252681940263187279493)
            ·
              refine ⟨3341297377863799347614905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17820252681940263187279493 3341297377863799347614905)
              ·
                refine ⟨2505973033397849510711179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341297377863799347614905 2505973033397849510711179)
                ·
                  refine ⟨3758959550096774266066769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505973033397849510711179 3758959550096774266066769)
                  ·
                    refine ⟨2819219662572580699550077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3758959550096774266066769 2819219662572580699550077)
                    ·
                      refine ⟨1057207373464717762331279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819219662572580699550077 1057207373464717762331279)
                      ·
                        rfl

theorem cell23_2058904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2058904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058904 prefixEnd_2058904 := by exact prefixLift 2058904
  have htrace : WordTrace (prefixWord ++ tailWord_2058904) baseStart_2058904 baseEnd_2058904 := by
    simpa [prefixWord, tailWord_2058904, baseEnd_2058904] using wordTrace_append hprefix tailTrace_2058904
  have hstable : (prefixWord ++ tailWord_2058904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058904).length < 2 ^ (prefixWord ++ tailWord_2058904).sum := by decide
  have hdescent : baseEnd_2058904 < baseStart_2058904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058930 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2058930 : Nat := 118140960795 + 2058930 * 2 ^ 59
def prefixEnd_2058930 : Nat := 4983230072969 + 3 ^ 40 * 2058930 * 2
def baseEnd_2058930 : Nat := 1057220723961734660606159

theorem tailTrace_2058930 : CollatzResearch.WordTrace tailWord_2058930 prefixEnd_2058930 1057220723961734660606159 := by
  unfold tailWord_2058930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773836607713930523459561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50063564287237148062558829 18773836607713930523459561)
  ·
    refine ⟨14080377455785447892594671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18773836607713930523459561 14080377455785447892594671)
    ·
      refine ⟨21120566183678171838892007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14080377455785447892594671 21120566183678171838892007)
      ·
        refine ⟨31680849275517257758338011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21120566183678171838892007 31680849275517257758338011)
        ·
          refine ⟨47521273913275886637507017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31680849275517257758338011 47521273913275886637507017)
          ·
            refine ⟨35640955434956914978130263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47521273913275886637507017 35640955434956914978130263)
            ·
              refine ⟨53461433152435372467195395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35640955434956914978130263 53461433152435372467195395)
              ·
                refine ⟨80192149728653058700793093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53461433152435372467195395 80192149728653058700793093)
                ·
                  refine ⟨15036028074122448506398705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80192149728653058700793093 15036028074122448506398705)
                  ·
                    refine ⟨11277021055591836379799029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15036028074122448506398705 11277021055591836379799029)
                    ·
                      refine ⟨1057220723961734660606159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11277021055591836379799029 1057220723961734660606159)
                      ·
                        rfl

theorem cell23_2058930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2058930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058930 prefixEnd_2058930 := by exact prefixLift 2058930
  have htrace : WordTrace (prefixWord ++ tailWord_2058930) baseStart_2058930 baseEnd_2058930 := by
    simpa [prefixWord, tailWord_2058930, baseEnd_2058930] using wordTrace_append hprefix tailTrace_2058930
  have hstable : (prefixWord ++ tailWord_2058930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058930).length < 2 ^ (prefixWord ++ tailWord_2058930).sum := by decide
  have hdescent : baseEnd_2058930 < baseStart_2058930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058935 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_2058935 : Nat := 118140960795 + 2058935 * 2 ^ 59
def prefixEnd_2058935 : Nat := 4983230072969 + 3 ^ 40 * 2058935 * 2
def baseEnd_2058935 : Nat := 1057223291365007141043637

theorem tailTrace_2058935 : CollatzResearch.WordTrace tailWord_2058935 prefixEnd_2058935 1057223291365007141043637 := by
  unfold tailWord_2058935
  simp only [CollatzResearch.WordTrace]
  refine ⟨75095528795837607947770259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50063685863891738631846839 75095528795837607947770259)
  ·
    refine ⟨112643293193756411921655389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75095528795837607947770259 112643293193756411921655389)
    ·
      refine ⟨42241234947658654470620771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112643293193756411921655389 42241234947658654470620771)
      ·
        refine ⟨63361852421487981705931157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42241234947658654470620771 63361852421487981705931157)
        ·
          refine ⟨2970086832257249142465523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63361852421487981705931157 2970086832257249142465523)
          ·
            refine ⟨4455130248385873713698285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970086832257249142465523 4455130248385873713698285)
            ·
              refine ⟨1670673843144702642636857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4455130248385873713698285 1670673843144702642636857)
              ·
                refine ⟨1253005382358526981977643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670673843144702642636857 1253005382358526981977643)
                ·
                  refine ⟨1879508073537790472966465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253005382358526981977643 1879508073537790472966465)
                  ·
                    refine ⟨1409631055153342854724849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879508073537790472966465 1409631055153342854724849)
                    ·
                      refine ⟨1057223291365007141043637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409631055153342854724849 1057223291365007141043637)
                      ·
                        rfl

theorem cell23_2058935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_2058935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058935 prefixEnd_2058935 := by exact prefixLift 2058935
  have htrace : WordTrace (prefixWord ++ tailWord_2058935) baseStart_2058935 baseEnd_2058935 := by
    simpa [prefixWord, tailWord_2058935, baseEnd_2058935] using wordTrace_append hprefix tailTrace_2058935
  have hstable : (prefixWord ++ tailWord_2058935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058935).length < 2 ^ (prefixWord ++ tailWord_2058935).sum := by decide
  have hdescent : baseEnd_2058935 < baseStart_2058935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058945 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2058945 : Nat := 118140960795 + 2058945 * 2 ^ 59
def prefixEnd_2058945 : Nat := 4983230072969 + 3 ^ 40 * 2058945 * 2
def baseEnd_2058945 : Nat := 352409475390517367306197

theorem tailTrace_2058945 : CollatzResearch.WordTrace tailWord_2058945 prefixEnd_2058945 352409475390517367306197 := by
  unfold tailWord_2058945
  simp only [CollatzResearch.WordTrace]
  refine ⟨75095893525801379655634289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50063929017200919770422859 75095893525801379655634289)
  ·
    refine ⟨56321920144351034741725717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75095893525801379655634289 56321920144351034741725717)
    ·
      refine ⟨2640090006766454753518393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56321920144351034741725717 2640090006766454753518393)
      ·
        refine ⟨1980067505074841065138795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2640090006766454753518393 1980067505074841065138795)
        ·
          refine ⟨2970101257612261597708193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980067505074841065138795 2970101257612261597708193)
          ·
            refine ⟨2227575943209196198281145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970101257612261597708193 2227575943209196198281145)
            ·
              refine ⟨1670681957406897148710859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227575943209196198281145 1670681957406897148710859)
              ·
                refine ⟨2506022936110345723066289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670681957406897148710859 2506022936110345723066289)
                ·
                  refine ⟨1879517202082759292299717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506022936110345723066289 1879517202082759292299717)
                  ·
                    refine ⟨352409475390517367306197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879517202082759292299717 352409475390517367306197)
                    ·
                      rfl

theorem cell23_2058945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2058945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058945 prefixEnd_2058945 := by exact prefixLift 2058945
  have htrace : WordTrace (prefixWord ++ tailWord_2058945) baseStart_2058945 baseEnd_2058945 := by
    simpa [prefixWord, tailWord_2058945, baseEnd_2058945] using wordTrace_append hprefix tailTrace_2058945
  have hstable : (prefixWord ++ tailWord_2058945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058945).length < 2 ^ (prefixWord ++ tailWord_2058945).sum := by decide
  have hdescent : baseEnd_2058945 < baseStart_2058945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058977 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2058977 : Nat := 118140960795 + 2058977 * 2 ^ 59
def prefixEnd_2058977 : Nat := 4983230072969 + 3 ^ 40 * 2058977 * 2
def baseEnd_2058977 : Nat := 1057244857552495976718443

theorem tailTrace_2058977 : CollatzResearch.WordTrace tailWord_2058977 prefixEnd_2058977 1057244857552495976718443 := by
  unfold tailWord_2058977
  simp only [CollatzResearch.WordTrace]
  refine ⟨75097060661685449120799185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50064707107790299413866123 75097060661685449120799185)
  ·
    refine ⟨56322795496264086840599389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75097060661685449120799185 56322795496264086840599389)
    ·
      refine ⟨21121048311099032565224771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56322795496264086840599389 21121048311099032565224771)
      ·
        refine ⟨31681572466648548847837157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121048311099032565224771 31681572466648548847837157)
        ·
          refine ⟨5940294837496602908969467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31681572466648548847837157 5940294837496602908969467)
          ·
            refine ⟨8910442256244904363454201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940294837496602908969467 8910442256244904363454201)
            ·
              refine ⟨6682831692183678272590651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910442256244904363454201 6682831692183678272590651)
              ·
                refine ⟨10024247538275517408885977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682831692183678272590651 10024247538275517408885977)
                ·
                  refine ⟨7518185653706638056664483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10024247538275517408885977 7518185653706638056664483)
                  ·
                    refine ⟨11277278480559957084996725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7518185653706638056664483 11277278480559957084996725)
                    ·
                      refine ⟨1057244857552495976718443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11277278480559957084996725 1057244857552495976718443)
                      ·
                        rfl

theorem cell23_2058977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2058977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058977 prefixEnd_2058977 := by exact prefixLift 2058977
  have htrace : WordTrace (prefixWord ++ tailWord_2058977) baseStart_2058977 baseEnd_2058977 := by
    simpa [prefixWord, tailWord_2058977, baseEnd_2058977] using wordTrace_append hprefix tailTrace_2058977
  have hstable : (prefixWord ++ tailWord_2058977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058977).length < 2 ^ (prefixWord ++ tailWord_2058977).sum := by decide
  have hdescent : baseEnd_2058977 < baseStart_2058977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058991 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 2, 2, 2]
def baseStart_2058991 : Nat := 118140960795 + 2058991 * 2 ^ 59
def prefixEnd_2058991 : Nat := 4983230072969 + 3 ^ 40 * 2058991 * 2
def baseEnd_2058991 : Nat := 1057252046281658921943379

theorem tailTrace_2058991 : CollatzResearch.WordTrace tailWord_2058991 prefixEnd_2058991 1057252046281658921943379 := by
  unfold tailWord_2058991
  simp only [CollatzResearch.WordTrace]
  refine ⟨75097571283634729511808827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50065047522423153007872551 75097571283634729511808827)
  ·
    refine ⟨112646356925452094267713241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75097571283634729511808827 112646356925452094267713241)
    ·
      refine ⟨84484767694089070700784931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112646356925452094267713241 84484767694089070700784931)
      ·
        refine ⟨126727151541133606051177397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84484767694089070700784931 126727151541133606051177397)
        ·
          refine ⟨11880670456981275567297881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126727151541133606051177397 11880670456981275567297881)
          ·
            refine ⟨8910502842735956675473411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11880670456981275567297881 8910502842735956675473411)
            ·
              refine ⟨13365754264103935013210117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8910502842735956675473411 13365754264103935013210117)
              ·
                refine ⟨2506078924519487814976897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13365754264103935013210117 2506078924519487814976897)
                ·
                  refine ⟨1879559193389615861232673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506078924519487814976897 1879559193389615861232673)
                  ·
                    refine ⟨1409669395042211895924505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879559193389615861232673 1409669395042211895924505)
                    ·
                      refine ⟨1057252046281658921943379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409669395042211895924505 1057252046281658921943379)
                      ·
                        rfl

theorem cell23_2058991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 2, 2].length) (baseStart_2058991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058991 prefixEnd_2058991 := by exact prefixLift 2058991
  have htrace : WordTrace (prefixWord ++ tailWord_2058991) baseStart_2058991 baseEnd_2058991 := by
    simpa [prefixWord, tailWord_2058991, baseEnd_2058991] using wordTrace_append hprefix tailTrace_2058991
  have hstable : (prefixWord ++ tailWord_2058991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058991).length < 2 ^ (prefixWord ++ tailWord_2058991).sum := by decide
  have hdescent : baseEnd_2058991 < baseStart_2058991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059031 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 5]
def baseStart_2059031 : Nat := 118140960795 + 2059031 * 2 ^ 59
def prefixEnd_2059031 : Nat := 4983230072969 + 3 ^ 40 * 2059031 * 2
def baseEnd_2059031 : Nat := 117474731723093196160355

theorem tailTrace_2059031 : CollatzResearch.WordTrace tailWord_2059031 prefixEnd_2059031 117474731723093196160355 := by
  unfold tailWord_2059031
  simp only [CollatzResearch.WordTrace]
  refine ⟨75099030203489816343264947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50066020135659877562176631 75099030203489816343264947)
  ·
    refine ⟨112648545305234724514897421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75099030203489816343264947 112648545305234724514897421)
    ·
      refine ⟨42243204489463021693086533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112648545305234724514897421 42243204489463021693086533)
      ·
        refine ⟨7920600841774316567453725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42243204489463021693086533 7920600841774316567453725)
        ·
          refine ⟨2970225315665368712795147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7920600841774316567453725 2970225315665368712795147)
          ·
            refine ⟨4455337973498053069192721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970225315665368712795147 4455337973498053069192721)
            ·
              refine ⟨3341503480123539801894541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455337973498053069192721 3341503480123539801894541)
              ·
                refine ⟨1253063805046327425710453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341503480123539801894541 1253063805046327425710453)
                ·
                  refine ⟨117474731723093196160355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1253063805046327425710453 117474731723093196160355)
                  ·
                    rfl

theorem cell23_2059031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 5].length) (baseStart_2059031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059031 prefixEnd_2059031 := by exact prefixLift 2059031
  have htrace : WordTrace (prefixWord ++ tailWord_2059031) baseStart_2059031 baseEnd_2059031 := by
    simpa [prefixWord, tailWord_2059031, baseEnd_2059031] using wordTrace_append hprefix tailTrace_2059031
  have hstable : (prefixWord ++ tailWord_2059031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059031).length < 2 ^ (prefixWord ++ tailWord_2059031).sum := by decide
  have hdescent : baseEnd_2059031 < baseStart_2059031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059064 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_2059064 : Nat := 118140960795 + 2059064 * 2 ^ 59
def prefixEnd_2059064 : Nat := 4983230072969 + 3 ^ 40 * 2059064 * 2
def baseEnd_2059064 : Nat := 1057289530369437136330543

theorem tailTrace_2059064 : CollatzResearch.WordTrace tailWord_2059064 prefixEnd_2059064 1057289530369437136330543 := by
  unfold tailWord_2059064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550116906185131489608123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50066822541580175319477497 37550116906185131489608123)
  ·
    refine ⟨56325175359277697234412185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37550116906185131489608123 56325175359277697234412185)
    ·
      refine ⟨42243881519458272925809139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56325175359277697234412185 42243881519458272925809139)
      ·
        refine ⟨63365822279187409388713709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42243881519458272925809139 63365822279187409388713709)
        ·
          refine ⟨23762183354695278520767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63365822279187409388713709 23762183354695278520767641)
          ·
            refine ⟨17821637516021458890575731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23762183354695278520767641 17821637516021458890575731)
            ·
              refine ⟨26732456274032188335863597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17821637516021458890575731 26732456274032188335863597)
              ·
                refine ⟨10024671102762070625948849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26732456274032188335863597 10024671102762070625948849)
                ·
                  refine ⟨7518503327071552969461637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10024671102762070625948849 7518503327071552969461637)
                  ·
                    refine ⟨1409719373825916181774057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7518503327071552969461637 1409719373825916181774057)
                    ·
                      refine ⟨1057289530369437136330543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409719373825916181774057 1057289530369437136330543)
                      ·
                        rfl

theorem cell23_2059064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_2059064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059064 prefixEnd_2059064 := by exact prefixLift 2059064
  have htrace : WordTrace (prefixWord ++ tailWord_2059064) baseStart_2059064 baseEnd_2059064 := by
    simpa [prefixWord, tailWord_2059064, baseEnd_2059064] using wordTrace_append hprefix tailTrace_2059064
  have hstable : (prefixWord ++ tailWord_2059064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059064).length < 2 ^ (prefixWord ++ tailWord_2059064).sum := by decide
  have hdescent : baseEnd_2059064 < baseStart_2059064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059084 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2059084 : Nat := 118140960795 + 2059084 * 2 ^ 59
def prefixEnd_2059084 : Nat := 4983230072969 + 3 ^ 40 * 2059084 * 2
def baseEnd_2059084 : Nat := 1057299799982527058080451

theorem tailTrace_2059084 : CollatzResearch.WordTrace tailWord_2059084 prefixEnd_2059084 1057299799982527058080451 := by
  unfold tailWord_2059084
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550481636148903197472153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50067308848198537596629537 37550481636148903197472153)
  ·
    refine ⟨28162861227111677398104115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37550481636148903197472153 28162861227111677398104115)
    ·
      refine ⟨42244291840667516097156173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28162861227111677398104115 42244291840667516097156173)
      ·
        refine ⟨15841609440250318536433565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42244291840667516097156173 15841609440250318536433565)
        ·
          refine ⟨5940603540093869451162587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15841609440250318536433565 5940603540093869451162587)
          ·
            refine ⟨8910905310140804176743881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940603540093869451162587 8910905310140804176743881)
            ·
              refine ⟨6683178982605603132557911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910905310140804176743881 6683178982605603132557911)
              ·
                refine ⟨10024768473908404698836867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683178982605603132557911 10024768473908404698836867)
                ·
                  refine ⟨15037152710862607048255301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024768473908404698836867 15037152710862607048255301)
                  ·
                    refine ⟨2819466133286738821547869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15037152710862607048255301 2819466133286738821547869)
                    ·
                      refine ⟨1057299799982527058080451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819466133286738821547869 1057299799982527058080451)
                      ·
                        rfl

theorem cell23_2059084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2059084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059084 prefixEnd_2059084 := by exact prefixLift 2059084
  have htrace : WordTrace (prefixWord ++ tailWord_2059084) baseStart_2059084 baseEnd_2059084 := by
    simpa [prefixWord, tailWord_2059084, baseEnd_2059084] using wordTrace_append hprefix tailTrace_2059084
  have hstable : (prefixWord ++ tailWord_2059084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059084).length < 2 ^ (prefixWord ++ tailWord_2059084).sum := by decide
  have hdescent : baseEnd_2059084 < baseStart_2059084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059117 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2059117 : Nat := 118140960795 + 2059117 * 2 ^ 59
def prefixEnd_2059117 : Nat := 4983230072969 + 3 ^ 40 * 2059117 * 2
def baseEnd_2059117 : Nat := 352438914948041809655933

theorem tailTrace_2059117 : CollatzResearch.WordTrace tailWord_2059117 prefixEnd_2059117 352438914948041809655933 := by
  unfold tailWord_2059117
  simp only [CollatzResearch.WordTrace]
  refine ⟨75102166881178253030895605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50068111254118835353930403 75102166881178253030895605)
  ·
    refine ⟨7040828145110461221646463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75102166881178253030895605 7040828145110461221646463)
    ·
      refine ⟨10561242217665691832469695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040828145110461221646463 10561242217665691832469695)
      ·
        refine ⟨15841863326498537748704543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561242217665691832469695 15841863326498537748704543)
        ·
          refine ⟨23762794989747806623056815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15841863326498537748704543 23762794989747806623056815)
          ·
            refine ⟨35644192484621709934585223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23762794989747806623056815 35644192484621709934585223)
            ·
              refine ⟨53466288726932564901877835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35644192484621709934585223 53466288726932564901877835)
              ·
                refine ⟨80199433090398847352816753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53466288726932564901877835 80199433090398847352816753)
                ·
                  refine ⟨60149574817799135514612565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80199433090398847352816753 60149574817799135514612565)
                  ·
                    refine ⟨352438914948041809655933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60149574817799135514612565 352438914948041809655933)
                    ·
                      rfl

theorem cell23_2059117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2059117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059117 prefixEnd_2059117 := by exact prefixLift 2059117
  have htrace : WordTrace (prefixWord ++ tailWord_2059117) baseStart_2059117 baseEnd_2059117 := by
    simpa [prefixWord, tailWord_2059117, baseEnd_2059117] using wordTrace_append hprefix tailTrace_2059117
  have hstable : (prefixWord ++ tailWord_2059117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059117).length < 2 ^ (prefixWord ++ tailWord_2059117).sum := by decide
  have hdescent : baseEnd_2059117 < baseStart_2059117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059121 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 6]
def baseStart_2059121 : Nat := 118140960795 + 2059121 * 2 ^ 59
def prefixEnd_2059121 : Nat := 4983230072969 + 3 ^ 40 * 2059121 * 2
def baseEnd_2059121 : Nat := 117479866529638157035309

theorem tailTrace_2059121 : CollatzResearch.WordTrace tailWord_2059121 prefixEnd_2059121 117479866529638157035309 := by
  unfold tailWord_2059121
  simp only [CollatzResearch.WordTrace]
  refine ⟨75102312773163761714041217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50068208515442507809360811 75102312773163761714041217)
  ·
    refine ⟨56326734579872821285530913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75102312773163761714041217 56326734579872821285530913)
    ·
      refine ⟨42245050934904615964148185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56326734579872821285530913 42245050934904615964148185)
      ·
        refine ⟨31683788201178461973111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42245050934904615964148185 31683788201178461973111139)
        ·
          refine ⟨47525682301767692959666709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31683788201178461973111139 47525682301767692959666709)
          ·
            refine ⟨2227766357895360607484377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47525682301767692959666709 2227766357895360607484377)
            ·
              refine ⟨1670824768421520455613283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227766357895360607484377 1670824768421520455613283)
              ·
                refine ⟨2506237152632280683419925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670824768421520455613283 2506237152632280683419925)
                ·
                  refine ⟨117479866529638157035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2506237152632280683419925 117479866529638157035309)
                  ·
                    rfl

theorem cell23_2059121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_2059121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059121 prefixEnd_2059121 := by exact prefixLift 2059121
  have htrace : WordTrace (prefixWord ++ tailWord_2059121) baseStart_2059121 baseEnd_2059121 := by
    simpa [prefixWord, tailWord_2059121, baseEnd_2059121] using wordTrace_append hprefix tailTrace_2059121
  have hstable : (prefixWord ++ tailWord_2059121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059121).length < 2 ^ (prefixWord ++ tailWord_2059121).sum := by decide
  have hdescent : baseEnd_2059121 < baseStart_2059121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059141 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_2059141 : Nat := 118140960795 + 2059141 * 2 ^ 59
def prefixEnd_2059141 : Nat := 4983230072969 + 3 ^ 40 * 2059141 * 2
def baseEnd_2059141 : Nat := 1057329068379833335067689

theorem tailTrace_2059141 : CollatzResearch.WordTrace tailWord_2059141 prefixEnd_2059141 1057329068379833335067689 := by
  unfold tailWord_2059141
  simp only [CollatzResearch.WordTrace]
  refine ⟨75103042233091305129769277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50068694822060870086512851 75103042233091305129769277)
  ·
    refine ⟨28163640837409239423663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75103042233091305129769277 28163640837409239423663479)
    ·
      refine ⟨42245461256113859135495219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28163640837409239423663479 42245461256113859135495219)
      ·
        refine ⟨63368191884170788703242829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42245461256113859135495219 63368191884170788703242829)
        ·
          refine ⟨23763071956564045763716061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63368191884170788703242829 23763071956564045763716061)
          ·
            refine ⟨8911151983711517161393523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23763071956564045763716061 8911151983711517161393523)
            ·
              refine ⟨13366727975567275742090285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911151983711517161393523 13366727975567275742090285)
              ·
                refine ⟨5012522990837728403283857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13366727975567275742090285 5012522990837728403283857)
                ·
                  refine ⟨3759392243128296302462893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012522990837728403283857 3759392243128296302462893)
                  ·
                    refine ⟨1409772091173111113423585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3759392243128296302462893 1409772091173111113423585)
                    ·
                      refine ⟨1057329068379833335067689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409772091173111113423585 1057329068379833335067689)
                      ·
                        rfl

theorem cell23_2059141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_2059141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059141 prefixEnd_2059141 := by exact prefixLift 2059141
  have htrace : WordTrace (prefixWord ++ tailWord_2059141) baseStart_2059141 baseEnd_2059141 := by
    simpa [prefixWord, tailWord_2059141, baseEnd_2059141] using wordTrace_append hprefix tailTrace_2059141
  have hstable : (prefixWord ++ tailWord_2059141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059141).length < 2 ^ (prefixWord ++ tailWord_2059141).sum := by decide
  have hdescent : baseEnd_2059141 < baseStart_2059141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059147 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 6]
def baseStart_2059147 : Nat := 118140960795 + 2059147 * 2 ^ 59
def prefixEnd_2059147 : Nat := 4983230072969 + 3 ^ 40 * 2059147 * 2
def baseEnd_2059147 : Nat := 352444049754586770530887

theorem tailTrace_2059147 : CollatzResearch.WordTrace tailWord_2059147 prefixEnd_2059147 352444049754586770530887 := by
  unfold tailWord_2059147
  simp only [CollatzResearch.WordTrace]
  refine ⟨75103261071069568154487695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50068840714046378769658463 75103261071069568154487695)
  ·
    refine ⟨112654891606604352231731543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75103261071069568154487695 112654891606604352231731543)
    ·
      refine ⟨168982337409906528347597315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112654891606604352231731543 168982337409906528347597315)
      ·
        refine ⟨253473506114859792521395973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168982337409906528347597315 253473506114859792521395973)
        ·
          refine ⟨47526282396536211097761745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253473506114859792521395973 47526282396536211097761745)
          ·
            refine ⟨35644711797402158323321309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47526282396536211097761745 35644711797402158323321309)
            ·
              refine ⟨13366766924025809371245491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35644711797402158323321309 13366766924025809371245491)
              ·
                refine ⟨20050150386038714056868237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366766924025809371245491 20050150386038714056868237)
                ·
                  refine ⟨7518806394764517771325589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20050150386038714056868237 7518806394764517771325589)
                  ·
                    refine ⟨352444049754586770530887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7518806394764517771325589 352444049754586770530887)
                    ·
                      rfl

theorem cell23_2059147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_2059147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059147 prefixEnd_2059147 := by exact prefixLift 2059147
  have htrace : WordTrace (prefixWord ++ tailWord_2059147) baseStart_2059147 baseEnd_2059147 := by
    simpa [prefixWord, tailWord_2059147, baseEnd_2059147] using wordTrace_append hprefix tailTrace_2059147
  have hstable : (prefixWord ++ tailWord_2059147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059147).length < 2 ^ (prefixWord ++ tailWord_2059147).sum := by decide
  have hdescent : baseEnd_2059147 < baseStart_2059147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059188 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2059188 : Nat := 118140960795 + 2059188 * 2 ^ 59
def prefixEnd_2059188 : Nat := 4983230072969 + 3 ^ 40 * 2059188 * 2
def baseEnd_2059188 : Nat := 1057353201970594651179973

theorem tailTrace_2059188 : CollatzResearch.WordTrace tailWord_2059188 prefixEnd_2059188 1057353201970594651179973 := by
  unfold tailWord_2059188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37552378231960516078365109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50069837642614021437820145 37552378231960516078365109)
  ·
    refine ⟨3520535459246298382346729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37552378231960516078365109 3520535459246298382346729)
    ·
      refine ⟨2640401594434723786760047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3520535459246298382346729 2640401594434723786760047)
      ·
        refine ⟨3960602391652085680140071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640401594434723786760047 3960602391652085680140071)
        ·
          refine ⟨5940903587478128520210107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960602391652085680140071 5940903587478128520210107)
          ·
            refine ⟨8911355381217192780315161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940903587478128520210107 8911355381217192780315161)
            ·
              refine ⟨6683516535912894585236371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911355381217192780315161 6683516535912894585236371)
              ·
                refine ⟨10025274803869341877854557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683516535912894585236371 10025274803869341877854557)
                ·
                  refine ⟨3759478051451003204195459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025274803869341877854557 3759478051451003204195459)
                  ·
                    refine ⟨5639217077176504806293189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759478051451003204195459 5639217077176504806293189)
                    ·
                      refine ⟨1057353201970594651179973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5639217077176504806293189 1057353201970594651179973)
                      ·
                        rfl

theorem cell23_2059188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2059188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059188 prefixEnd_2059188 := by exact prefixLift 2059188
  have htrace : WordTrace (prefixWord ++ tailWord_2059188) baseStart_2059188 baseEnd_2059188 := by
    simpa [prefixWord, tailWord_2059188, baseEnd_2059188] using wordTrace_append hprefix tailTrace_2059188
  have hstable : (prefixWord ++ tailWord_2059188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059188).length < 2 ^ (prefixWord ++ tailWord_2059188).sum := by decide
  have hdescent : baseEnd_2059188 < baseStart_2059188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059194 : List Nat := [3, 1, 1, 1, 2, 1, 7, 7]
def baseStart_2059194 : Nat := 118140960795 + 2059194 * 2 ^ 59
def prefixEnd_2059194 : Nat := 4983230072969 + 3 ^ 40 * 2059194 * 2
def baseEnd_2059194 : Nat := 39161343809426726952035

theorem tailTrace_2059194 : CollatzResearch.WordTrace tailWord_2059194 prefixEnd_2059194 39161343809426726952035 := by
  unfold tailWord_2059194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776243825474823795362159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50069983534599530120965757 18776243825474823795362159)
  ·
    refine ⟨28164365738212235693043239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18776243825474823795362159 28164365738212235693043239)
    ·
      refine ⟨42246548607318353539564859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28164365738212235693043239 42246548607318353539564859)
      ·
        refine ⟨63369822910977530309347289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42246548607318353539564859 63369822910977530309347289)
        ·
          refine ⟨47527367183233147732010467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63369822910977530309347289 47527367183233147732010467)
          ·
            refine ⟨71291050774849721598015701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47527367183233147732010467 71291050774849721598015701)
            ·
              refine ⟨1670884002535540349953493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71291050774849721598015701 1670884002535540349953493)
              ·
                refine ⟨39161343809426726952035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1670884002535540349953493 39161343809426726952035)
                ·
                  rfl

theorem cell23_2059194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_2059194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059194 prefixEnd_2059194 := by exact prefixLift 2059194
  have htrace : WordTrace (prefixWord ++ tailWord_2059194) baseStart_2059194 baseEnd_2059194 := by
    simpa [prefixWord, tailWord_2059194, baseEnd_2059194] using wordTrace_append hprefix tailTrace_2059194
  have hstable : (prefixWord ++ tailWord_2059194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059194).length < 2 ^ (prefixWord ++ tailWord_2059194).sum := by decide
  have hdescent : baseEnd_2059194 < baseStart_2059194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059208 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_2059208 : Nat := 118140960795 + 2059208 * 2 ^ 59
def prefixEnd_2059208 : Nat := 4983230072969 + 3 ^ 40 * 2059208 * 2
def baseEnd_2059208 : Nat := 1057363471583684572929881

theorem tailTrace_2059208 : CollatzResearch.WordTrace tailWord_2059208 prefixEnd_2059208 1057363471583684572929881 := by
  unfold tailWord_2059208
  simp only [CollatzResearch.WordTrace]
  refine ⟨37552742961924287786229139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50070323949232383714972185 37552742961924287786229139)
  ·
    refine ⟨56329114442886431679343709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37552742961924287786229139 56329114442886431679343709)
    ·
      refine ⟨21123417916082411879753891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56329114442886431679343709 21123417916082411879753891)
      ·
        refine ⟨31685126874123617819630837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21123417916082411879753891 31685126874123617819630837)
        ·
          refine ⟨2970480644449089170590391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31685126874123617819630837 2970480644449089170590391)
          ·
            refine ⟨4455720966673633755885587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970480644449089170590391 4455720966673633755885587)
            ·
              refine ⟨6683581450010450633828381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455720966673633755885587 6683581450010450633828381)
              ·
                refine ⟨2506343043753918987685643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683581450010450633828381 2506343043753918987685643)
                ·
                  refine ⟨3759514565630878481528465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506343043753918987685643 3759514565630878481528465)
                  ·
                    refine ⟨2819635924223158861146349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759514565630878481528465 2819635924223158861146349)
                    ·
                      refine ⟨1057363471583684572929881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819635924223158861146349 1057363471583684572929881)
                      ·
                        rfl

theorem cell23_2059208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_2059208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059208 prefixEnd_2059208 := by exact prefixLift 2059208
  have htrace : WordTrace (prefixWord ++ tailWord_2059208) baseStart_2059208 baseEnd_2059208 := by
    simpa [prefixWord, tailWord_2059208, baseEnd_2059208] using wordTrace_append hprefix tailTrace_2059208
  have hstable : (prefixWord ++ tailWord_2059208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059208).length < 2 ^ (prefixWord ++ tailWord_2059208).sum := by decide
  have hdescent : baseEnd_2059208 < baseStart_2059208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059222 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2059222 : Nat := 118140960795 + 2059222 * 2 ^ 59
def prefixEnd_2059222 : Nat := 4983230072969 + 3 ^ 40 * 2059222 * 2
def baseEnd_2059222 : Nat := 1057370660312847518154817

theorem tailTrace_2059222 : CollatzResearch.WordTrace tailWord_2059222 prefixEnd_2059222 1057370660312847518154817 := by
  unfold tailWord_2059222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694124784112365997716745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50070664363865237308978613 4694124784112365997716745)
  ·
    refine ⟨3520593588084274498287559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4694124784112365997716745 3520593588084274498287559)
    ·
      refine ⟨5280890382126411747431339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520593588084274498287559 5280890382126411747431339)
      ·
        refine ⟨7921335573189617621147009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280890382126411747431339 7921335573189617621147009)
        ·
          refine ⟨5941001679892213215860257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921335573189617621147009 5941001679892213215860257)
          ·
            refine ⟨4455751259919159911895193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941001679892213215860257 4455751259919159911895193)
            ·
              refine ⟨3341813444939369933921395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455751259919159911895193 3341813444939369933921395)
              ·
                refine ⟨5012720167409054900882093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341813444939369933921395 5012720167409054900882093)
                ·
                  refine ⟨1879770062778395587830785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5012720167409054900882093 1879770062778395587830785)
                  ·
                    refine ⟨1409827547083796690873089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879770062778395587830785 1409827547083796690873089)
                    ·
                      refine ⟨1057370660312847518154817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409827547083796690873089 1057370660312847518154817)
                      ·
                        rfl

theorem cell23_2059222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2059222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059222 prefixEnd_2059222 := by exact prefixLift 2059222
  have htrace : WordTrace (prefixWord ++ tailWord_2059222) baseStart_2059222 baseEnd_2059222 := by
    simpa [prefixWord, tailWord_2059222, baseEnd_2059222] using wordTrace_append hprefix tailTrace_2059222
  have hstable : (prefixWord ++ tailWord_2059222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059222).length < 2 ^ (prefixWord ++ tailWord_2059222).sum := by decide
  have hdescent : baseEnd_2059222 < baseStart_2059222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_2059261 : Nat := 118140960795 + 2059261 * 2 ^ 59
def prefixEnd_2059261 : Nat := 4983230072969 + 3 ^ 40 * 2059261 * 2
def baseEnd_2059261 : Nat := 1057390686058372865567137

theorem tailTrace_2059261 : CollatzResearch.WordTrace tailWord_2059261 prefixEnd_2059261 1057390686058372865567137 := by
  unfold tailWord_2059261
  simp only [CollatzResearch.WordTrace]
  refine ⟨75107418992656565624137637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50071612661771043749425091 75107418992656565624137637)
  ·
    refine ⟨14082641061123106054525807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75107418992656565624137637 14082641061123106054525807)
    ·
      refine ⟨21123961591684659081788711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14082641061123106054525807 21123961591684659081788711)
      ·
        refine ⟨31685942387526988622683067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21123961591684659081788711 31685942387526988622683067)
        ·
          refine ⟨47528913581290482934024601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31685942387526988622683067 47528913581290482934024601)
          ·
            refine ⟨35646685185967862200518451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47528913581290482934024601 35646685185967862200518451)
            ·
              refine ⟨53470027778951793300777677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35646685185967862200518451 53470027778951793300777677)
              ·
                refine ⟨20051260417106922487791629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53470027778951793300777677 20051260417106922487791629)
                ·
                  refine ⟨7519222656415095932921861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20051260417106922487791629 7519222656415095932921861)
                  ·
                    refine ⟨1409854248077830487422849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519222656415095932921861 1409854248077830487422849)
                    ·
                      refine ⟨1057390686058372865567137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409854248077830487422849 1057390686058372865567137)
                      ·
                        rfl

theorem cell23_2059261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_2059261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059261 prefixEnd_2059261 := by exact prefixLift 2059261
  have htrace : WordTrace (prefixWord ++ tailWord_2059261) baseStart_2059261 baseEnd_2059261 := by
    simpa [prefixWord, tailWord_2059261, baseEnd_2059261] using wordTrace_append hprefix tailTrace_2059261
  have hstable : (prefixWord ++ tailWord_2059261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059261).length < 2 ^ (prefixWord ++ tailWord_2059261).sum := by decide
  have hdescent : baseEnd_2059261 < baseStart_2059261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059295 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 2, 2, 2]
def baseStart_2059295 : Nat := 118140960795 + 2059295 * 2 ^ 59
def prefixEnd_2059295 : Nat := 4983230072969 + 3 ^ 40 * 2059295 * 2
def baseEnd_2059295 : Nat := 1057408144400625732541981

theorem tailTrace_2059295 : CollatzResearch.WordTrace tailWord_2059295 prefixEnd_2059295 1057408144400625732541981 := by
  unfold tailWord_2059295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75108659074533389430875339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50072439383022259620583559 75108659074533389430875339)
  ·
    refine ⟨112662988611800084146313009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75108659074533389430875339 112662988611800084146313009)
    ·
      refine ⟨84497241458850063109734757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112662988611800084146313009 84497241458850063109734757)
      ·
        refine ⟨15843232773534386833075267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84497241458850063109734757 15843232773534386833075267)
        ·
          refine ⟨23764849160301580249612901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15843232773534386833075267 23764849160301580249612901)
          ·
            refine ⟨4455909217556546296802419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23764849160301580249612901 4455909217556546296802419)
            ·
              refine ⟨6683863826334819445203629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455909217556546296802419 6683863826334819445203629)
              ·
                refine ⟨2506448934875557291951361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683863826334819445203629 2506448934875557291951361)
                ·
                  refine ⟨1879836701156667968963521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506448934875557291951361 1879836701156667968963521)
                  ·
                    refine ⟨1409877525867500976722641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1879836701156667968963521 1409877525867500976722641)
                    ·
                      refine ⟨1057408144400625732541981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409877525867500976722641 1057408144400625732541981)
                      ·
                        rfl

theorem cell23_2059295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_2059295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059295 prefixEnd_2059295 := by exact prefixLift 2059295
  have htrace : WordTrace (prefixWord ++ tailWord_2059295) baseStart_2059295 baseEnd_2059295 := by
    simpa [prefixWord, tailWord_2059295, baseEnd_2059295] using wordTrace_append hprefix tailTrace_2059295
  have hstable : (prefixWord ++ tailWord_2059295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059295).length < 2 ^ (prefixWord ++ tailWord_2059295).sum := by decide
  have hdescent : baseEnd_2059295 < baseStart_2059295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059335 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 5]
def baseStart_2059335 : Nat := 118140960795 + 2059335 * 2 ^ 59
def prefixEnd_2059335 : Nat := 4983230072969 + 3 ^ 40 * 2059335 * 2
def baseEnd_2059335 : Nat := 117492075958533952893533

theorem tailTrace_2059335 : CollatzResearch.WordTrace tailWord_2059335 prefixEnd_2059335 117492075958533952893533 := by
  unfold tailWord_2059335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75110117994388476262331459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50073411996258984174887639 75110117994388476262331459)
  ·
    refine ⟨112665176991582714393497189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75110117994388476262331459 112665176991582714393497189)
    ·
      refine ⟨21124720685921758948780723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112665176991582714393497189 21124720685921758948780723)
      ·
        refine ⟨31687081028882638423171085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124720685921758948780723 31687081028882638423171085)
        ·
          refine ⟨11882655385830989408689157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31687081028882638423171085 11882655385830989408689157)
          ·
            refine ⟨2227997884843310514129217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11882655385830989408689157 2227997884843310514129217)
            ·
              refine ⟨1670998413632482885596913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227997884843310514129217 1670998413632482885596913)
              ·
                refine ⟨1253248810224362164197685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670998413632482885596913 1253248810224362164197685)
                ·
                  refine ⟨117492075958533952893533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1253248810224362164197685 117492075958533952893533)
                  ·
                    rfl

theorem cell23_2059335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 5].length) (baseStart_2059335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059335 prefixEnd_2059335 := by exact prefixLift 2059335
  have htrace : WordTrace (prefixWord ++ tailWord_2059335) baseStart_2059335 baseEnd_2059335 := by
    simpa [prefixWord, tailWord_2059335, baseEnd_2059335] using wordTrace_append hprefix tailTrace_2059335
  have hstable : (prefixWord ++ tailWord_2059335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059335).length < 2 ^ (prefixWord ++ tailWord_2059335).sum := by decide
  have hdescent : baseEnd_2059335 < baseStart_2059335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059361 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2059361 : Nat := 118140960795 + 2059361 * 2 ^ 59
def prefixEnd_2059361 : Nat := 4983230072969 + 3 ^ 40 * 2059361 * 2
def baseEnd_2059361 : Nat := 352480678041274158105559

theorem tailTrace_2059361 : CollatzResearch.WordTrace tailWord_2059361 prefixEnd_2059361 352480678041274158105559 := by
  unfold tailWord_2059361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75111066292294282702777937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50074044194862855135185291 75111066292294282702777937)
  ·
    refine ⟨56333299719220712027083453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75111066292294282702777937 56333299719220712027083453)
    ·
      refine ⟨21124987394707767010156295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56333299719220712027083453 21124987394707767010156295)
      ·
        refine ⟨31687481092061650515234443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124987394707767010156295 31687481092061650515234443)
        ·
          refine ⟨47531221638092475772851665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31687481092061650515234443 47531221638092475772851665)
          ·
            refine ⟨35648416228569356829638749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47531221638092475772851665 35648416228569356829638749)
            ·
              refine ⟨13368156085713508811114531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35648416228569356829638749 13368156085713508811114531)
              ·
                refine ⟨20052234128570263216671797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13368156085713508811114531 20052234128570263216671797)
                ·
                  refine ⟨1879896949553462176562981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20052234128570263216671797 1879896949553462176562981)
                  ·
                    refine ⟨352480678041274158105559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879896949553462176562981 352480678041274158105559)
                    ·
                      rfl

theorem cell23_2059361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2059361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059361 prefixEnd_2059361 := by exact prefixLift 2059361
  have htrace : WordTrace (prefixWord ++ tailWord_2059361) baseStart_2059361 baseEnd_2059361 := by
    simpa [prefixWord, tailWord_2059361, baseEnd_2059361] using wordTrace_append hprefix tailTrace_2059361
  have hstable : (prefixWord ++ tailWord_2059361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059361).length < 2 ^ (prefixWord ++ tailWord_2059361).sum := by decide
  have hdescent : baseEnd_2059361 < baseStart_2059361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059446 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2059446 : Nat := 118140960795 + 2059446 * 2 ^ 59
def prefixEnd_2059446 : Nat := 4983230072969 + 3 ^ 40 * 2059446 * 2
def baseEnd_2059446 : Nat := 352495226659818213917929

theorem tailTrace_2059446 : CollatzResearch.WordTrace tailWord_2059446 prefixEnd_2059446 352495226659818213917929 := by
  unfold tailWord_2059446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694635406061646388726387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50076110997990894813081461 4694635406061646388726387)
  ·
    refine ⟨7041953109092469583089581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694635406061646388726387 7041953109092469583089581)
    ·
      refine ⟨2640732415909676093658593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7041953109092469583089581 2640732415909676093658593)
      ·
        refine ⟨1980549311932257070243945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2640732415909676093658593 1980549311932257070243945)
        ·
          refine ⟨1485411983949192802682959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1980549311932257070243945 1485411983949192802682959)
          ·
            refine ⟨2228117975923789204024439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485411983949192802682959 2228117975923789204024439)
            ·
              refine ⟨3342176963885683806036659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228117975923789204024439 3342176963885683806036659)
              ·
                refine ⟨5013265445828525709054989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342176963885683806036659 5013265445828525709054989)
                ·
                  refine ⟨1879974542185697140895621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5013265445828525709054989 1879974542185697140895621)
                  ·
                    refine ⟨352495226659818213917929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1879974542185697140895621 352495226659818213917929)
                    ·
                      rfl

theorem cell23_2059446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2059446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059446 prefixEnd_2059446 := by exact prefixLift 2059446
  have htrace : WordTrace (prefixWord ++ tailWord_2059446) baseStart_2059446 baseEnd_2059446 := by
    simpa [prefixWord, tailWord_2059446, baseEnd_2059446] using wordTrace_append hprefix tailTrace_2059446
  have hstable : (prefixWord ++ tailWord_2059446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059446).length < 2 ^ (prefixWord ++ tailWord_2059446).sum := by decide
  have hdescent : baseEnd_2059446 < baseStart_2059446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059452 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2059452 : Nat := 118140960795 + 2059452 * 2 ^ 59
def prefixEnd_2059452 : Nat := 4983230072969 + 3 ^ 40 * 2059452 * 2
def baseEnd_2059452 : Nat := 1057488760863381618278759

theorem tailTrace_2059452 : CollatzResearch.WordTrace tailWord_2059452 prefixEnd_2059452 1057488760863381618278759 := by
  unfold tailWord_2059452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557192667482302622170305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50076256889976403496227073 37557192667482302622170305)
  ·
    refine ⟨28167894500611726966627729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37557192667482302622170305 28167894500611726966627729)
    ·
      refine ⟨21125920875458795224970797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28167894500611726966627729 21125920875458795224970797)
      ·
        refine ⟨7922220328297048209364049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21125920875458795224970797 7922220328297048209364049)
        ·
          refine ⟨5941665246222786157023037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7922220328297048209364049 5941665246222786157023037)
          ·
            refine ⟨2228124467333544808883639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5941665246222786157023037 2228124467333544808883639)
            ·
              refine ⟨3342186701000317213325459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228124467333544808883639 3342186701000317213325459)
              ·
                refine ⟨5013280051500475819988189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342186701000317213325459 5013280051500475819988189)
                ·
                  refine ⟨1879980019312678432495571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5013280051500475819988189 1879980019312678432495571)
                  ·
                    refine ⟨2819970028969017648743357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1879980019312678432495571 2819970028969017648743357)
                    ·
                      refine ⟨1057488760863381618278759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819970028969017648743357 1057488760863381618278759)
                      ·
                        rfl

theorem cell23_2059452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2059452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059452 prefixEnd_2059452 := by exact prefixLift 2059452
  have htrace : WordTrace (prefixWord ++ tailWord_2059452) baseStart_2059452 baseEnd_2059452 := by
    simpa [prefixWord, tailWord_2059452, baseEnd_2059452] using wordTrace_append hprefix tailTrace_2059452
  have hstable : (prefixWord ++ tailWord_2059452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059452).length < 2 ^ (prefixWord ++ tailWord_2059452).sum := by decide
  have hdescent : baseEnd_2059452 < baseStart_2059452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059461 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_2059461 : Nat := 118140960795 + 2059461 * 2 ^ 59
def prefixEnd_2059461 : Nat := 4983230072969 + 3 ^ 40 * 2059461 * 2
def baseEnd_2059461 : Nat := 1057493382189272083066217

theorem tailTrace_2059461 : CollatzResearch.WordTrace tailWord_2059461 prefixEnd_2059461 1057493382189272083066217 := by
  unfold tailWord_2059461
  simp only [CollatzResearch.WordTrace]
  refine ⟨75114713591931999781418237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50076475727954666520945491 75114713591931999781418237)
  ·
    refine ⟨28168017596974499918031839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75114713591931999781418237 28168017596974499918031839)
    ·
      refine ⟨42252026395461749877047759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28168017596974499918031839 42252026395461749877047759)
      ·
        refine ⟨63378039593192624815571639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42252026395461749877047759 63378039593192624815571639)
        ·
          refine ⟨95067059389788937223357459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63378039593192624815571639 95067059389788937223357459)
          ·
            refine ⟨142600589084683405835036189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95067059389788937223357459 142600589084683405835036189)
            ·
              refine ⟨53475220906756277188138571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142600589084683405835036189 53475220906756277188138571)
              ·
                refine ⟨80212831360134415782207857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53475220906756277188138571 80212831360134415782207857)
                ·
                  refine ⟨60159623520100811836655893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80212831360134415782207857 60159623520100811836655893)
                  ·
                    refine ⟨2819982352504725554843245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60159623520100811836655893 2819982352504725554843245)
                    ·
                      refine ⟨1057493382189272083066217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2819982352504725554843245 1057493382189272083066217)
                      ·
                        rfl

theorem cell23_2059461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_2059461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059461 prefixEnd_2059461 := by exact prefixLift 2059461
  have htrace : WordTrace (prefixWord ++ tailWord_2059461) baseStart_2059461 baseEnd_2059461 := by
    simpa [prefixWord, tailWord_2059461, baseEnd_2059461] using wordTrace_append hprefix tailTrace_2059461
  have hstable : (prefixWord ++ tailWord_2059461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059461).length < 2 ^ (prefixWord ++ tailWord_2059461).sum := by decide
  have hdescent : baseEnd_2059461 < baseStart_2059461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059485 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2059485 : Nat := 118140960795 + 2059485 * 2 ^ 59
def prefixEnd_2059485 : Nat := 4983230072969 + 3 ^ 40 * 2059485 * 2
def baseEnd_2059485 : Nat := 352501901908326663055369

theorem tailTrace_2059485 : CollatzResearch.WordTrace tailWord_2059485 prefixEnd_2059485 352501901908326663055369 := by
  unfold tailWord_2059485
  simp only [CollatzResearch.WordTrace]
  refine ⟨75115588943845051880291909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50077059295896701253527939 75115588943845051880291909)
  ·
    refine ⟨14084172926970947227554733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75115588943845051880291909 14084172926970947227554733)
    ·
      refine ⟨5281564847614105210333025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14084172926970947227554733 5281564847614105210333025)
      ·
        refine ⟨3961173635710578907749769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5281564847614105210333025 3961173635710578907749769)
        ·
          refine ⟨2970880226782934180812327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3961173635710578907749769 2970880226782934180812327)
          ·
            refine ⟨4456320340174401271218491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970880226782934180812327 4456320340174401271218491)
            ·
              refine ⟨6684480510261601906827737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456320340174401271218491 6684480510261601906827737)
              ·
                refine ⟨5013360382696201430120803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684480510261601906827737 5013360382696201430120803)
                ·
                  refine ⟨7520040574044302145181205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013360382696201430120803 7520040574044302145181205)
                  ·
                    refine ⟨352501901908326663055369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7520040574044302145181205 352501901908326663055369)
                    ·
                      rfl

theorem cell23_2059485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2059485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059485 prefixEnd_2059485 := by exact prefixLift 2059485
  have htrace : WordTrace (prefixWord ++ tailWord_2059485) baseStart_2059485 baseEnd_2059485 := by
    simpa [prefixWord, tailWord_2059485, baseEnd_2059485] using wordTrace_append hprefix tailTrace_2059485
  have hstable : (prefixWord ++ tailWord_2059485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059485).length < 2 ^ (prefixWord ++ tailWord_2059485).sum := by decide
  have hdescent : baseEnd_2059485 < baseStart_2059485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059488 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2059488 : Nat := 118140960795 + 2059488 * 2 ^ 59
def prefixEnd_2059488 : Nat := 4983230072969 + 3 ^ 40 * 2059488 * 2
def baseEnd_2059488 : Nat := 1057507246166943477428593

theorem tailTrace_2059488 : CollatzResearch.WordTrace tailWord_2059488 prefixEnd_2059488 1057507246166943477428593 := by
  unfold tailWord_2059488
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557849181417091696325559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50077132241889455595100745 37557849181417091696325559)
  ·
    refine ⟨56336773772125637544488339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37557849181417091696325559 56336773772125637544488339)
    ·
      refine ⟨84505160658188456316732509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56336773772125637544488339 84505160658188456316732509)
      ·
        refine ⟨31689435246820671118774691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84505160658188456316732509 31689435246820671118774691)
        ·
          refine ⟨47534152870231006678162037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31689435246820671118774691 47534152870231006678162037)
          ·
            refine ⟨4456326831584156876077691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47534152870231006678162037 4456326831584156876077691)
            ·
              refine ⟨6684490247376235314116537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456326831584156876077691 6684490247376235314116537)
              ·
                refine ⟨5013367685532176485587403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684490247376235314116537 5013367685532176485587403)
                ·
                  refine ⟨7520051528298264728381105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013367685532176485587403 7520051528298264728381105)
                  ·
                    refine ⟨5640038646223698546285829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520051528298264728381105 5640038646223698546285829)
                    ·
                      refine ⟨1057507246166943477428593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5640038646223698546285829 1057507246166943477428593)
                      ·
                        rfl

theorem cell23_2059488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2059488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059488 prefixEnd_2059488 := by exact prefixLift 2059488
  have htrace : WordTrace (prefixWord ++ tailWord_2059488) baseStart_2059488 baseEnd_2059488 := by
    simpa [prefixWord, tailWord_2059488, baseEnd_2059488] using wordTrace_append hprefix tailTrace_2059488
  have hstable : (prefixWord ++ tailWord_2059488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059488).length < 2 ^ (prefixWord ++ tailWord_2059488).sum := by decide
  have hdescent : baseEnd_2059488 < baseStart_2059488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059522 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2059522 : Nat := 118140960795 + 2059522 * 2 ^ 59
def prefixEnd_2059522 : Nat := 4983230072969 + 3 ^ 40 * 2059522 * 2
def baseEnd_2059522 : Nat := 1057524704509196344403437

theorem tailTrace_2059522 : CollatzResearch.WordTrace tailWord_2059522 prefixEnd_2059522 1057524704509196344403437 := by
  unfold tailWord_2059522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779234611177751799847205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50077958963140671466259213 18779234611177751799847205)
  ·
    refine ⟨3521106489595828462471351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18779234611177751799847205 3521106489595828462471351)
    ·
      refine ⟨5281659734393742693707027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521106489595828462471351 5281659734393742693707027)
      ·
        refine ⟨7922489601590614040560541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281659734393742693707027 7922489601590614040560541)
        ·
          refine ⟨2970933600596480265210203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7922489601590614040560541 2970933600596480265210203)
          ·
            refine ⟨4456400400894720397815305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970933600596480265210203 4456400400894720397815305)
            ·
              refine ⟨3342300300671040298361479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456400400894720397815305 3342300300671040298361479)
              ·
                refine ⟨5013450451006560447542219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342300300671040298361479 5013450451006560447542219)
                ·
                  refine ⟨7520175676509840671313329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013450451006560447542219 7520175676509840671313329)
                  ·
                    refine ⟨5640131757382380503484997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520175676509840671313329 5640131757382380503484997)
                    ·
                      refine ⟨1057524704509196344403437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5640131757382380503484997 1057524704509196344403437)
                      ·
                        rfl

theorem cell23_2059522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2059522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059522 prefixEnd_2059522 := by exact prefixLift 2059522
  have htrace : WordTrace (prefixWord ++ tailWord_2059522) baseStart_2059522 baseEnd_2059522 := by
    simpa [prefixWord, tailWord_2059522, baseEnd_2059522] using wordTrace_append hprefix tailTrace_2059522
  have hstable : (prefixWord ++ tailWord_2059522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059522).length < 2 ^ (prefixWord ++ tailWord_2059522).sum := by decide
  have hdescent : baseEnd_2059522 < baseStart_2059522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059525 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_2059525 : Nat := 118140960795 + 2059525 * 2 ^ 59
def prefixEnd_2059525 : Nat := 4983230072969 + 3 ^ 40 * 2059525 * 2
def baseEnd_2059525 : Nat := 1057526244951159832665923

theorem tailTrace_2059525 : CollatzResearch.WordTrace tailWord_2059525 prefixEnd_2059525 1057526244951159832665923 := by
  unfold tailWord_2059525
  simp only [CollatzResearch.WordTrace]
  refine ⟨75117047863700138711748029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50078031909133425807832019 75117047863700138711748029)
  ·
    refine ⟨28168892948887552016905511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75117047863700138711748029 28168892948887552016905511)
    ·
      refine ⟨42253339423331328025358267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28168892948887552016905511 42253339423331328025358267)
      ·
        refine ⟨63380009134996992038037401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42253339423331328025358267 63380009134996992038037401)
        ·
          refine ⟨47535006851247744028528051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63380009134996992038037401 47535006851247744028528051)
          ·
            refine ⟨71302510276871616042792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47535006851247744028528051 71302510276871616042792077)
            ·
              refine ⟨26738441353826856016047029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71302510276871616042792077 26738441353826856016047029)
              ·
                refine ⟨2506728876921267751504409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26738441353826856016047029 2506728876921267751504409)
                ·
                  refine ⟨1880046657690950813628307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506728876921267751504409 1880046657690950813628307)
                  ·
                    refine ⟨2820069986536426220442461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880046657690950813628307 2820069986536426220442461)
                    ·
                      refine ⟨1057526244951159832665923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2820069986536426220442461 1057526244951159832665923)
                      ·
                        rfl

theorem cell23_2059525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_2059525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059525 prefixEnd_2059525 := by exact prefixLift 2059525
  have htrace : WordTrace (prefixWord ++ tailWord_2059525) baseStart_2059525 baseEnd_2059525 := by
    simpa [prefixWord, tailWord_2059525, baseEnd_2059525] using wordTrace_append hprefix tailTrace_2059525
  have hstable : (prefixWord ++ tailWord_2059525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059525).length < 2 ^ (prefixWord ++ tailWord_2059525).sum := by decide
  have hdescent : baseEnd_2059525 < baseStart_2059525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059541 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2059541 : Nat := 118140960795 + 2059541 * 2 ^ 59
def prefixEnd_2059541 : Nat := 4983230072969 + 3 ^ 40 * 2059541 * 2
def baseEnd_2059541 : Nat := 352511486880543923355283

theorem tailTrace_2059541 : CollatzResearch.WordTrace tailWord_2059541 prefixEnd_2059541 352511486880543923355283 := by
  unfold tailWord_2059541
  simp only [CollatzResearch.WordTrace]
  refine ⟨75117631431642173444330477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50078420954428115629553651 75117631431642173444330477)
  ·
    refine ⟨28169111786865815041623929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75117631431642173444330477 28169111786865815041623929)
    ·
      refine ⟨21126833840149361281217947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28169111786865815041623929 21126833840149361281217947)
      ·
        refine ⟨31690250760224041921826921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126833840149361281217947 31690250760224041921826921)
        ·
          refine ⟨23767688070168031441370191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31690250760224041921826921 23767688070168031441370191)
          ·
            refine ⟨35651532105252047162055287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23767688070168031441370191 35651532105252047162055287)
            ·
              refine ⟨53477298157878070743082931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35651532105252047162055287 53477298157878070743082931)
              ·
                refine ⟨80215947236817106114624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53477298157878070743082931 80215947236817106114624397)
                ·
                  refine ⟨30080980213806414792984149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80215947236817106114624397 30080980213806414792984149)
                  ·
                    refine ⟨352511486880543923355283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30080980213806414792984149 352511486880543923355283)
                    ·
                      rfl

theorem cell23_2059541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2059541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059541 prefixEnd_2059541 := by exact prefixLift 2059541
  have htrace : WordTrace (prefixWord ++ tailWord_2059541) baseStart_2059541 baseEnd_2059541 := by
    simpa [prefixWord, tailWord_2059541, baseEnd_2059541] using wordTrace_append hprefix tailTrace_2059541
  have hstable : (prefixWord ++ tailWord_2059541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059541).length < 2 ^ (prefixWord ++ tailWord_2059541).sum := by decide
  have hdescent : baseEnd_2059541 < baseStart_2059541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059578 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_2059578 : Nat := 118140960795 + 2059578 * 2 ^ 59
def prefixEnd_2059578 : Nat := 4983230072969 + 3 ^ 40 * 2059578 * 2
def baseEnd_2059578 : Nat := 1057553459425848125303179

theorem tailTrace_2059578 : CollatzResearch.WordTrace tailWord_2059578 prefixEnd_2059578 1057553459425848125303179 := by
  unfold tailWord_2059578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779745233127032190856847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50079320621672085842284925 18779745233127032190856847)
  ·
    refine ⟨28169617849690548286285271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779745233127032190856847 28169617849690548286285271)
    ·
      refine ⟨42254426774535822429427907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169617849690548286285271 42254426774535822429427907)
      ·
        refine ⟨63381640161803733644141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42254426774535822429427907 63381640161803733644141861)
        ·
          refine ⟨11884057530338200058276599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63381640161803733644141861 11884057530338200058276599)
          ·
            refine ⟨17826086295507300087414899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884057530338200058276599 17826086295507300087414899)
            ·
              refine ⟨26739129443260950131122349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826086295507300087414899 26739129443260950131122349)
              ·
                refine ⟨10027173541222856299170881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26739129443260950131122349 10027173541222856299170881)
                ·
                  refine ⟨7520380155917142224378161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10027173541222856299170881 7520380155917142224378161)
                  ·
                    refine ⟨5640285116937856668283621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520380155917142224378161 5640285116937856668283621)
                    ·
                      refine ⟨1057553459425848125303179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5640285116937856668283621 1057553459425848125303179)
                      ·
                        rfl

theorem cell23_2059578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_2059578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059578 prefixEnd_2059578 := by exact prefixLift 2059578
  have htrace : WordTrace (prefixWord ++ tailWord_2059578) baseStart_2059578 baseEnd_2059578 := by
    simpa [prefixWord, tailWord_2059578, baseEnd_2059578] using wordTrace_append hprefix tailTrace_2059578
  have hstable : (prefixWord ++ tailWord_2059578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059578).length < 2 ^ (prefixWord ++ tailWord_2059578).sum := by decide
  have hdescent : baseEnd_2059578 < baseStart_2059578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059628 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_2059628 : Nat := 118140960795 + 2059628 * 2 ^ 59
def prefixEnd_2059628 : Nat := 4983230072969 + 3 ^ 40 * 2059628 * 2
def baseEnd_2059628 : Nat := 1057579133458572929677949

theorem tailTrace_2059628 : CollatzResearch.WordTrace tailWord_2059628 prefixEnd_2059628 1057579133458572929677949 := by
  unfold tailWord_2059628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560402291163493651373769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50080536388217991535165025 37560402291163493651373769)
  ·
    refine ⟨28170301718372620238530327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37560402291163493651373769 28170301718372620238530327)
    ·
      refine ⟨42255452577558930357795491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28170301718372620238530327 42255452577558930357795491)
      ·
        refine ⟨63383178866338395536693237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255452577558930357795491 63383178866338395536693237)
        ·
          refine ⟨5942173018719224581564991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63383178866338395536693237 5942173018719224581564991)
          ·
            refine ⟨8913259528078836872347487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942173018719224581564991 8913259528078836872347487)
            ·
              refine ⟨13369889292118255308521231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913259528078836872347487 13369889292118255308521231)
              ·
                refine ⟨20054833938177382962781847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13369889292118255308521231 20054833938177382962781847)
                ·
                  refine ⟨30082250907266074444172771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20054833938177382962781847 30082250907266074444172771)
                  ·
                    refine ⟨45123376360899111666259157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30082250907266074444172771 45123376360899111666259157)
                    ·
                      refine ⟨1057579133458572929677949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45123376360899111666259157 1057579133458572929677949)
                      ·
                        rfl

theorem cell23_2059628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_2059628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059628 prefixEnd_2059628 := by exact prefixLift 2059628
  have htrace : WordTrace (prefixWord ++ tailWord_2059628) baseStart_2059628 baseEnd_2059628 := by
    simpa [prefixWord, tailWord_2059628, baseEnd_2059628] using wordTrace_append hprefix tailTrace_2059628
  have hstable : (prefixWord ++ tailWord_2059628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059628).length < 2 ^ (prefixWord ++ tailWord_2059628).sum := by decide
  have hdescent : baseEnd_2059628 < baseStart_2059628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059655 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2059655 : Nat := 118140960795 + 2059655 * 2 ^ 59
def prefixEnd_2059655 : Nat := 4983230072969 + 3 ^ 40 * 2059655 * 2
def baseEnd_2059655 : Nat := 1057592997436244324040325

theorem tailTrace_2059655 : CollatzResearch.WordTrace tailWord_2059655 prefixEnd_2059655 1057592997436244324040325 := by
  unfold tailWord_2059655
  simp only [CollatzResearch.WordTrace]
  refine ⟨75121789353229170913980419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50081192902152780609320279 75121789353229170913980419)
  ·
    refine ⟨112682684029843756370970629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75121789353229170913980419 112682684029843756370970629)
    ·
      refine ⟨21128003255595704319556993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112682684029843756370970629 21128003255595704319556993)
      ·
        refine ⟨15846002441696778239667745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21128003255595704319556993 15846002441696778239667745)
        ·
          refine ⟨11884501831272583679750809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15846002441696778239667745 11884501831272583679750809)
          ·
            refine ⟨8913376373454437759813107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11884501831272583679750809 8913376373454437759813107)
            ·
              refine ⟨13370064560181656639719661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913376373454437759813107 13370064560181656639719661)
              ·
                refine ⟨5013774210068121239894873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13370064560181656639719661 5013774210068121239894873)
                ·
                  refine ⟨3760330657551090929921155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5013774210068121239894873 3760330657551090929921155)
                  ·
                    refine ⟨5640495986326636394881733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3760330657551090929921155 5640495986326636394881733)
                    ·
                      refine ⟨1057592997436244324040325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5640495986326636394881733 1057592997436244324040325)
                      ·
                        rfl

theorem cell23_2059655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2059655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059655 prefixEnd_2059655 := by exact prefixLift 2059655
  have htrace : WordTrace (prefixWord ++ tailWord_2059655) baseStart_2059655 baseEnd_2059655 := by
    simpa [prefixWord, tailWord_2059655, baseEnd_2059655] using wordTrace_append hprefix tailTrace_2059655
  have hstable : (prefixWord ++ tailWord_2059655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059655).length < 2 ^ (prefixWord ++ tailWord_2059655).sum := by decide
  have hdescent : baseEnd_2059655 < baseStart_2059655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2059698 : Nat := 118140960795 + 2059698 * 2 ^ 59
def prefixEnd_2059698 : Nat := 4983230072969 + 3 ^ 40 * 2059698 * 2
def baseEnd_2059698 : Nat := 1057615077104387655802627

theorem tailTrace_2059698 : CollatzResearch.WordTrace tailWord_2059698 prefixEnd_2059698 1057615077104387655802627 := by
  unfold tailWord_2059698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18780839423018347314448937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50082238461382259505197165 18780839423018347314448937)
  ·
    refine ⟨14085629567263760485836703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18780839423018347314448937 14085629567263760485836703)
    ·
      refine ⟨21128444350895640728755055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14085629567263760485836703 21128444350895640728755055)
      ·
        refine ⟨31692666526343461093132583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21128444350895640728755055 31692666526343461093132583)
        ·
          refine ⟨47538999789515191639698875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31692666526343461093132583 47538999789515191639698875)
          ·
            refine ⟨71308499684272787459548313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47538999789515191639698875 71308499684272787459548313)
            ·
              refine ⟨53481374763204590594661235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71308499684272787459548313 53481374763204590594661235)
              ·
                refine ⟨80222062144806885891991853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53481374763204590594661235 80222062144806885891991853)
                ·
                  refine ⟨30083273304302582209496945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80222062144806885891991853 30083273304302582209496945)
                  ·
                    refine ⟨22562454978226936657122709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30083273304302582209496945 22562454978226936657122709)
                    ·
                      refine ⟨1057615077104387655802627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22562454978226936657122709 1057615077104387655802627)
                      ·
                        rfl

theorem cell23_2059698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2059698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059698 prefixEnd_2059698 := by exact prefixLift 2059698
  have htrace : WordTrace (prefixWord ++ tailWord_2059698) baseStart_2059698 baseEnd_2059698 := by
    simpa [prefixWord, tailWord_2059698, baseEnd_2059698] using wordTrace_append hprefix tailTrace_2059698
  have hstable : (prefixWord ++ tailWord_2059698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059698).length < 2 ^ (prefixWord ++ tailWord_2059698).sum := by decide
  have hdescent : baseEnd_2059698 < baseStart_2059698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059716 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2059716 : Nat := 118140960795 + 2059716 * 2 ^ 59
def prefixEnd_2059716 : Nat := 4983230072969 + 3 ^ 40 * 2059716 * 2
def baseEnd_2059716 : Nat := 352541439918722861792515

theorem tailTrace_2059716 : CollatzResearch.WordTrace tailWord_2059716 prefixEnd_2059716 352541439918722861792515 := by
  unfold tailWord_2059716
  simp only [CollatzResearch.WordTrace]
  refine ⟨37562007103004089165975501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50082676137338785554634001 37562007103004089165975501)
  ·
    refine ⟨14085752663626533437240813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37562007103004089165975501 14085752663626533437240813)
    ·
      refine ⟨5282157248859950038965305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14085752663626533437240813 5282157248859950038965305)
      ·
        refine ⟨3961617936644962529223979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5282157248859950038965305 3961617936644962529223979)
        ·
          refine ⟨5942426904967443793835969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961617936644962529223979 5942426904967443793835969)
          ·
            refine ⟨4456820178725582845376977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5942426904967443793835969 4456820178725582845376977)
            ·
              refine ⟨3342615134044187134032733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456820178725582845376977 3342615134044187134032733)
              ·
                refine ⟨1253480675266570175262275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342615134044187134032733 1253480675266570175262275)
                ·
                  refine ⟨1880221012899855262893413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253480675266570175262275 1880221012899855262893413)
                  ·
                    refine ⟨352541439918722861792515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880221012899855262893413 352541439918722861792515)
                    ·
                      rfl

theorem cell23_2059716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2059716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059716 prefixEnd_2059716 := by exact prefixLift 2059716
  have htrace : WordTrace (prefixWord ++ tailWord_2059716) baseStart_2059716 baseEnd_2059716 := by
    simpa [prefixWord, tailWord_2059716, baseEnd_2059716] using wordTrace_append hprefix tailTrace_2059716
  have hstable : (prefixWord ++ tailWord_2059716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059716).length < 2 ^ (prefixWord ++ tailWord_2059716).sum := by decide
  have hdescent : baseEnd_2059716 < baseStart_2059716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059805 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2059805 : Nat := 118140960795 + 2059805 * 2 ^ 59
def prefixEnd_2059805 : Nat := 4983230072969 + 3 ^ 40 * 2059805 * 2
def baseEnd_2059805 : Nat := 1057670019534418737164635

theorem tailTrace_2059805 : CollatzResearch.WordTrace tailWord_2059805 prefixEnd_2059805 1057670019534418737164635 := by
  unfold tailWord_2059805
  simp only [CollatzResearch.WordTrace]
  refine ⟨75127260302685746531940869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50084840201790497687960579 75127260302685746531940869)
  ·
    refine ⟨14086361306753577474738913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75127260302685746531940869 14086361306753577474738913)
    ·
      refine ⟨10564770980065183106054185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14086361306753577474738913 10564770980065183106054185)
      ·
        refine ⟨7923578235048887329540639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10564770980065183106054185 7923578235048887329540639)
        ·
          refine ⟨11885367352573330994310959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7923578235048887329540639 11885367352573330994310959)
          ·
            refine ⟨17828051028859996491466439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11885367352573330994310959 17828051028859996491466439)
            ·
              refine ⟨26742076543289994737199659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17828051028859996491466439 26742076543289994737199659)
              ·
                refine ⟨40113114814934992105799489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26742076543289994737199659 40113114814934992105799489)
                ·
                  refine ⟨30084836111201244079349617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40113114814934992105799489 30084836111201244079349617)
                  ·
                    refine ⟨22563627083400933059512213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30084836111201244079349617 22563627083400933059512213)
                    ·
                      refine ⟨1057670019534418737164635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22563627083400933059512213 1057670019534418737164635)
                      ·
                        rfl

theorem cell23_2059805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2059805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059805 prefixEnd_2059805 := by exact prefixLift 2059805
  have htrace : WordTrace (prefixWord ++ tailWord_2059805) baseStart_2059805 baseEnd_2059805 := by
    simpa [prefixWord, tailWord_2059805, baseEnd_2059805] using wordTrace_append hprefix tailTrace_2059805
  have hstable : (prefixWord ++ tailWord_2059805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059805).length < 2 ^ (prefixWord ++ tailWord_2059805).sum := by decide
  have hdescent : baseEnd_2059805 < baseStart_2059805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059845 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_2059845 : Nat := 118140960795 + 2059845 * 2 ^ 59
def prefixEnd_2059845 : Nat := 4983230072969 + 3 ^ 40 * 2059845 * 2
def baseEnd_2059845 : Nat := 352563519586866193554817

theorem tailTrace_2059845 : CollatzResearch.WordTrace tailWord_2059845 prefixEnd_2059845 352563519586866193554817 := by
  unfold tailWord_2059845
  simp only [CollatzResearch.WordTrace]
  refine ⟨75128719222540833363396989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50085812815027222242264659 75128719222540833363396989)
  ·
    refine ⟨28173269708452812511273871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75128719222540833363396989 28173269708452812511273871)
    ·
      refine ⟨42259904562679218766910807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28173269708452812511273871 42259904562679218766910807)
      ·
        refine ⟨63389856844018828150366211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42259904562679218766910807 63389856844018828150366211)
        ·
          refine ⟨95084785266028242225549317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63389856844018828150366211 95084785266028242225549317)
          ·
            refine ⟨17828397237380295417290497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95084785266028242225549317 17828397237380295417290497)
            ·
              refine ⟨13371297928035221562967873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17828397237380295417290497 13371297928035221562967873)
              ·
                refine ⟨10028473446026416172225905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13371297928035221562967873 10028473446026416172225905)
                ·
                  refine ⟨7521355084519812129169429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10028473446026416172225905 7521355084519812129169429)
                  ·
                    refine ⟨352563519586866193554817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7521355084519812129169429 352563519586866193554817)
                    ·
                      rfl

theorem cell23_2059845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_2059845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059845 prefixEnd_2059845 := by exact prefixLift 2059845
  have htrace : WordTrace (prefixWord ++ tailWord_2059845) baseStart_2059845 baseEnd_2059845 := by
    simpa [prefixWord, tailWord_2059845, baseEnd_2059845] using wordTrace_append hprefix tailTrace_2059845
  have hstable : (prefixWord ++ tailWord_2059845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059845).length < 2 ^ (prefixWord ++ tailWord_2059845).sum := by decide
  have hdescent : baseEnd_2059845 < baseStart_2059845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059847 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_2059847 : Nat := 118140960795 + 2059847 * 2 ^ 59
def prefixEnd_2059847 : Nat := 4983230072969 + 3 ^ 40 * 2059847 * 2
def baseEnd_2059847 : Nat := 1057691585721907572839443

theorem tailTrace_2059847 : CollatzResearch.WordTrace tailWord_2059847 prefixEnd_2059847 1057691585721907572839443 := by
  unfold tailWord_2059847
  simp only [CollatzResearch.WordTrace]
  refine ⟨75128792168533587704969795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50085861445689058469979863 75128792168533587704969795)
  ·
    refine ⟨112693188252800381557454693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75128792168533587704969795 112693188252800381557454693)
    ·
      refine ⟨21129972797400071542022755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112693188252800381557454693 21129972797400071542022755)
      ·
        refine ⟨31694959196100107313034133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21129972797400071542022755 31694959196100107313034133)
        ·
          refine ⟨1485701212317192530298475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31694959196100107313034133 1485701212317192530298475)
          ·
            refine ⟨2228551818475788795447713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485701212317192530298475 2228551818475788795447713)
            ·
              refine ⟨1671413863856841596585785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228551818475788795447713 1671413863856841596585785)
              ·
                refine ⟨1253560397892631197439339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671413863856841596585785 1253560397892631197439339)
                ·
                  refine ⟨1880340596838946796159009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253560397892631197439339 1880340596838946796159009)
                  ·
                    refine ⟨1410255447629210097119257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880340596838946796159009 1410255447629210097119257)
                    ·
                      refine ⟨1057691585721907572839443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410255447629210097119257 1057691585721907572839443)
                      ·
                        rfl

theorem cell23_2059847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_2059847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059847 prefixEnd_2059847 := by exact prefixLift 2059847
  have htrace : WordTrace (prefixWord ++ tailWord_2059847) baseStart_2059847 baseEnd_2059847 := by
    simpa [prefixWord, tailWord_2059847, baseEnd_2059847] using wordTrace_append hprefix tailTrace_2059847
  have hstable : (prefixWord ++ tailWord_2059847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059847).length < 2 ^ (prefixWord ++ tailWord_2059847).sum := by decide
  have hdescent : baseEnd_2059847 < baseStart_2059847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059875 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 9]
def baseStart_2059875 : Nat := 118140960795 + 2059875 * 2 ^ 59
def prefixEnd_2059875 : Nat := 4983230072969 + 3 ^ 40 * 2059875 * 2
def baseEnd_2059875 : Nat := 117522884797803718143257

theorem tailTrace_2059875 : CollatzResearch.WordTrace tailWord_2059875 prefixEnd_2059875 117522884797803718143257 := by
  unfold tailWord_2059875
  simp only [CollatzResearch.WordTrace]
  refine ⟨75129813412432148486989079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50086542274954765657992719 75129813412432148486989079)
  ·
    refine ⟨112694720118648222730483619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75129813412432148486989079 112694720118648222730483619)
    ·
      refine ⟨169042080177972334095725429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112694720118648222730483619 169042080177972334095725429)
      ·
        refine ⟨15847695016684906321474259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169042080177972334095725429 15847695016684906321474259)
        ·
          refine ⟨23771542525027359482211389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15847695016684906321474259 23771542525027359482211389)
          ·
            refine ⟨8914328446885259805829271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23771542525027359482211389 8914328446885259805829271)
            ·
              refine ⟨13371492670327889708743907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914328446885259805829271 13371492670327889708743907)
              ·
                refine ⟨20057239005491834563115861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371492670327889708743907 20057239005491834563115861)
                ·
                  refine ⟨117522884797803718143257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20057239005491834563115861 117522884797803718143257)
                  ·
                    rfl

theorem cell23_2059875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 9].length) (baseStart_2059875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059875 prefixEnd_2059875 := by exact prefixLift 2059875
  have htrace : WordTrace (prefixWord ++ tailWord_2059875) baseStart_2059875 baseEnd_2059875 := by
    simpa [prefixWord, tailWord_2059875, baseEnd_2059875] using wordTrace_append hprefix tailTrace_2059875
  have hstable : (prefixWord ++ tailWord_2059875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059875).length < 2 ^ (prefixWord ++ tailWord_2059875).sum := by decide
  have hdescent : baseEnd_2059875 < baseStart_2059875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059915 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_2059915 : Nat := 118140960795 + 2059915 * 2 ^ 59
def prefixEnd_2059915 : Nat := 4983230072969 + 3 ^ 40 * 2059915 * 2
def baseEnd_2059915 : Nat := 1057726502406413306789129

theorem tailTrace_2059915 : CollatzResearch.WordTrace tailWord_2059915 prefixEnd_2059915 1057726502406413306789129 := by
  unfold tailWord_2059915
  simp only [CollatzResearch.WordTrace]
  refine ⟨75131272332287235318445199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50087514888191490212296799 75131272332287235318445199)
  ·
    refine ⟨112696908498430852977667799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75131272332287235318445199 112696908498430852977667799)
    ·
      refine ⟨169045362747646279466501699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112696908498430852977667799 169045362747646279466501699)
      ·
        refine ⟨253568044121469419199752549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169045362747646279466501699 253568044121469419199752549)
        ·
          refine ⟨47544008272775516099953603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253568044121469419199752549 47544008272775516099953603)
          ·
            refine ⟨71316012409163274149930405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47544008272775516099953603 71316012409163274149930405)
            ·
              refine ⟨13371752326718113903111951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71316012409163274149930405 13371752326718113903111951)
              ·
                refine ⟨20057628490077170854667927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13371752326718113903111951 20057628490077170854667927)
                ·
                  refine ⟨30086442735115756282001891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20057628490077170854667927 30086442735115756282001891)
                  ·
                    refine ⟨45129664102673634423002837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30086442735115756282001891 45129664102673634423002837)
                    ·
                      refine ⟨1057726502406413306789129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45129664102673634423002837 1057726502406413306789129)
                      ·
                        rfl

theorem cell23_2059915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_2059915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059915 prefixEnd_2059915 := by exact prefixLift 2059915
  have htrace : WordTrace (prefixWord ++ tailWord_2059915) baseStart_2059915 baseEnd_2059915 := by
    simpa [prefixWord, tailWord_2059915, baseEnd_2059915] using wordTrace_append hprefix tailTrace_2059915
  have hstable : (prefixWord ++ tailWord_2059915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059915).length < 2 ^ (prefixWord ++ tailWord_2059915).sum := by decide
  have hdescent : baseEnd_2059915 < baseStart_2059915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059952 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_2059952 : Nat := 118140960795 + 2059952 * 2 ^ 59
def prefixEnd_2059952 : Nat := 4983230072969 + 3 ^ 40 * 2059952 * 2
def baseEnd_2059952 : Nat := 352581833730209887342153

theorem tailTrace_2059952 : CollatzResearch.WordTrace tailWord_2059952 prefixEnd_2059952 352581833730209887342153 := by
  unfold tailWord_2059952
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566310916576595318771055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50088414555435460425028073 37566310916576595318771055)
  ·
    refine ⟨56349466374864892978156583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37566310916576595318771055 56349466374864892978156583)
    ·
      refine ⟨84524199562297339467234875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56349466374864892978156583 84524199562297339467234875)
      ·
        refine ⟨126786299343446009200852313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84524199562297339467234875 126786299343446009200852313)
        ·
          refine ⟨95089724507584506900639235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126786299343446009200852313 95089724507584506900639235)
          ·
            refine ⟨142634586761376760350958853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95089724507584506900639235 142634586761376760350958853)
            ·
              refine ⟨26743985017758142565804785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142634586761376760350958853 26743985017758142565804785)
              ·
                refine ⟨20057988763318606924353589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26743985017758142565804785 20057988763318606924353589)
                ·
                  refine ⟨1880436446561119399158149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20057988763318606924353589 1880436446561119399158149)
                  ·
                    refine ⟨352581833730209887342153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880436446561119399158149 352581833730209887342153)
                    ·
                      rfl

theorem cell23_2059952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_2059952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059952 prefixEnd_2059952 := by exact prefixLift 2059952
  have htrace : WordTrace (prefixWord ++ tailWord_2059952) baseStart_2059952 baseEnd_2059952 := by
    simpa [prefixWord, tailWord_2059952, baseEnd_2059952] using wordTrace_append hprefix tailTrace_2059952
  have hstable : (prefixWord ++ tailWord_2059952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059952).length < 2 ^ (prefixWord ++ tailWord_2059952).sum := by decide
  have hdescent : baseEnd_2059952 < baseStart_2059952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059959 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_2059959 : Nat := 118140960795 + 2059959 * 2 ^ 59
def prefixEnd_2059959 : Nat := 4983230072969 + 3 ^ 40 * 2059959 * 2
def baseEnd_2059959 : Nat := 1057749095555211134638927

theorem tailTrace_2059959 : CollatzResearch.WordTrace tailWord_2059959 prefixEnd_2059959 1057749095555211134638927 := by
  unfold tailWord_2059959
  simp only [CollatzResearch.WordTrace]
  refine ⟨75132877144127830833046931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50088584762751887222031287 75132877144127830833046931)
  ·
    refine ⟨112699315716191746249570397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75132877144127830833046931 112699315716191746249570397)
    ·
      refine ⟨42262243393571904843588899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112699315716191746249570397 42262243393571904843588899)
      ·
        refine ⟨63393365090357857265383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42262243393571904843588899 63393365090357857265383349)
        ·
          refine ⟨5943127977221049118629689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63393365090357857265383349 5943127977221049118629689)
          ·
            refine ⟨4457345982915786838972267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5943127977221049118629689 4457345982915786838972267)
            ·
              refine ⟨6686018974373680258458401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457345982915786838972267 6686018974373680258458401)
              ·
                refine ⟨5014514230780260193843801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686018974373680258458401 5014514230780260193843801)
                ·
                  refine ⟨3760885673085195145382851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014514230780260193843801 3760885673085195145382851)
                  ·
                    refine ⟨5641328509627792718074277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3760885673085195145382851 5641328509627792718074277)
                    ·
                      refine ⟨1057749095555211134638927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5641328509627792718074277 1057749095555211134638927)
                      ·
                        rfl

theorem cell23_2059959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_2059959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2059959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2059959 prefixEnd_2059959 := by exact prefixLift 2059959
  have htrace : WordTrace (prefixWord ++ tailWord_2059959) baseStart_2059959 baseEnd_2059959 := by
    simpa [prefixWord, tailWord_2059959, baseEnd_2059959] using wordTrace_append hprefix tailTrace_2059959
  have hstable : (prefixWord ++ tailWord_2059959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059959).length < 2 ^ (prefixWord ++ tailWord_2059959).sum := by decide
  have hdescent : baseEnd_2059959 < baseStart_2059959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060049 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_2060049 : Nat := 118140960795 + 2060049 * 2 ^ 59
def prefixEnd_2060049 : Nat := 4983230072969 + 3 ^ 40 * 2060049 * 2
def baseEnd_2060049 : Nat := 1057795308814115782513513

theorem tailTrace_2060049 : CollatzResearch.WordTrace tailWord_2060049 prefixEnd_2060049 1057795308814115782513513 := by
  unfold tailWord_2060049
  simp only [CollatzResearch.WordTrace]
  refine ⟨75136159713801776203823201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50090773142534517469215467 75136159713801776203823201)
  ·
    refine ⟨56352119785351332152867401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75136159713801776203823201 56352119785351332152867401)
    ·
      refine ⟨42264089839013499114650551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56352119785351332152867401 42264089839013499114650551)
      ·
        refine ⟨63396134758520248671975827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42264089839013499114650551 63396134758520248671975827)
        ·
          refine ⟨95094202137780373007963741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63396134758520248671975827 95094202137780373007963741)
          ·
            refine ⟨35660325801667639877986403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95094202137780373007963741 35660325801667639877986403)
            ·
              refine ⟨53490488702501459816979605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35660325801667639877986403 53490488702501459816979605)
              ·
                refine ⟨2507366657929755928920919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53490488702501459816979605 2507366657929755928920919)
                ·
                  refine ⟨3761049986894633893381379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507366657929755928920919 3761049986894633893381379)
                  ·
                    refine ⟨5641574980341950840072069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761049986894633893381379 5641574980341950840072069)
                    ·
                      refine ⟨1057795308814115782513513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5641574980341950840072069 1057795308814115782513513)
                      ·
                        rfl

theorem cell23_2060049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_2060049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060049 prefixEnd_2060049 := by exact prefixLift 2060049
  have htrace : WordTrace (prefixWord ++ tailWord_2060049) baseStart_2060049 baseEnd_2060049 := by
    simpa [prefixWord, tailWord_2060049, baseEnd_2060049] using wordTrace_append hprefix tailTrace_2060049
  have hstable : (prefixWord ++ tailWord_2060049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060049).length < 2 ^ (prefixWord ++ tailWord_2060049).sum := by decide
  have hdescent : baseEnd_2060049 < baseStart_2060049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060053 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_2060053 : Nat := 118140960795 + 2060053 * 2 ^ 59
def prefixEnd_2060053 : Nat := 4983230072969 + 3 ^ 40 * 2060053 * 2
def baseEnd_2060053 : Nat := 1057797362736733766863495

theorem tailTrace_2060053 : CollatzResearch.WordTrace tailWord_2060053 prefixEnd_2060053 1057797362736733766863495 := by
  unfold tailWord_2060053
  simp only [CollatzResearch.WordTrace]
  refine ⟨75136305605787284886968813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50090870403858189924645875 75136305605787284886968813)
  ·
    refine ⟨28176114602170231832613305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75136305605787284886968813 28176114602170231832613305)
    ·
      refine ⟨21132085951627673874459979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28176114602170231832613305 21132085951627673874459979)
      ·
        refine ⟨31698128927441510811689969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21132085951627673874459979 31698128927441510811689969)
        ·
          refine ⟨23773596695581133108767477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31698128927441510811689969 23773596695581133108767477)
          ·
            refine ⟨2228774690210731228946951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23773596695581133108767477 2228774690210731228946951)
            ·
              refine ⟨3343162035316096843420427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228774690210731228946951 3343162035316096843420427)
              ·
                refine ⟨5014743052974145265130641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343162035316096843420427 5014743052974145265130641)
                ·
                  refine ⟨3761057289730608948847981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014743052974145265130641 3761057289730608948847981)
                  ·
                    refine ⟨1410396483648978355817993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761057289730608948847981 1410396483648978355817993)
                    ·
                      refine ⟨1057797362736733766863495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410396483648978355817993 1057797362736733766863495)
                      ·
                        rfl

theorem cell23_2060053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_2060053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060053 prefixEnd_2060053 := by exact prefixLift 2060053
  have htrace : WordTrace (prefixWord ++ tailWord_2060053) baseStart_2060053 baseEnd_2060053 := by
    simpa [prefixWord, tailWord_2060053, baseEnd_2060053] using wordTrace_append hprefix tailTrace_2060053
  have hstable : (prefixWord ++ tailWord_2060053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060053).length < 2 ^ (prefixWord ++ tailWord_2060053).sum := by decide
  have hdescent : baseEnd_2060053 < baseStart_2060053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060066 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2060066 : Nat := 118140960795 + 2060066 * 2 ^ 59
def prefixEnd_2060066 : Nat := 4983230072969 + 3 ^ 40 * 2060066 * 2
def baseEnd_2060066 : Nat := 1057804037985242216000935

theorem tailTrace_2060066 : CollatzResearch.WordTrace tailWord_2060066 prefixEnd_2060066 1057804037985242216000935 := by
  unfold tailWord_2060066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784194938685047026798013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50091186503160125404794701 18784194938685047026798013)
  ·
    refine ⟨7044073102006892635049255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18784194938685047026798013 7044073102006892635049255)
    ·
      refine ⟨10566109653010338952573883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044073102006892635049255 10566109653010338952573883)
      ·
        refine ⟨15849164479515508428860825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566109653010338952573883 15849164479515508428860825)
        ·
          refine ⟨11886873359636631321645619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15849164479515508428860825 11886873359636631321645619)
          ·
            refine ⟨17830310039454946982468429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886873359636631321645619 17830310039454946982468429)
            ·
              refine ⟨6686366264795605118425661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17830310039454946982468429 6686366264795605118425661)
              ·
                refine ⟨2507387349298351919409623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6686366264795605118425661 2507387349298351919409623)
                ·
                  refine ⟨3761081023947527879114435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507387349298351919409623 3761081023947527879114435)
                  ·
                    refine ⟨5641621535921291818671653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761081023947527879114435 5641621535921291818671653)
                    ·
                      refine ⟨1057804037985242216000935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5641621535921291818671653 1057804037985242216000935)
                      ·
                        rfl

theorem cell23_2060066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2060066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060066 prefixEnd_2060066 := by exact prefixLift 2060066
  have htrace : WordTrace (prefixWord ++ tailWord_2060066) baseStart_2060066 baseEnd_2060066 := by
    simpa [prefixWord, tailWord_2060066, baseEnd_2060066] using wordTrace_append hprefix tailTrace_2060066
  have hstable : (prefixWord ++ tailWord_2060066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060066).length < 2 ^ (prefixWord ++ tailWord_2060066).sum := by decide
  have hdescent : baseEnd_2060066 < baseStart_2060066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060076 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_2060076 : Nat := 118140960795 + 2060076 * 2 ^ 59
def prefixEnd_2060076 : Nat := 4983230072969 + 3 ^ 40 * 2060076 * 2
def baseEnd_2060076 : Nat := 352603057597262392291963

theorem tailTrace_2060076 : CollatzResearch.WordTrace tailWord_2060076 prefixEnd_2060076 352603057597262392291963 := by
  unfold tailWord_2060076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37568572242351979907528041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50091429656469306543370721 37568572242351979907528041)
  ·
    refine ⟨28176429181763984930646031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37568572242351979907528041 28176429181763984930646031)
    ·
      refine ⟨42264643772645977395969047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28176429181763984930646031 42264643772645977395969047)
      ·
        refine ⟨63396965658968966093953571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42264643772645977395969047 63396965658968966093953571)
        ·
          refine ⟨95095448488453449140930357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63396965658968966093953571 95095448488453449140930357)
          ·
            refine ⟨8915198295792510856962221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95095448488453449140930357 8915198295792510856962221)
            ·
              refine ⟨3343199360922191571360833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8915198295792510856962221 3343199360922191571360833)
              ·
                refine ⟨2507399520691643678520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343199360922191571360833 2507399520691643678520625)
                ·
                  refine ⟨1880549640518732758890469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507399520691643678520625 1880549640518732758890469)
                  ·
                    refine ⟨352603057597262392291963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880549640518732758890469 352603057597262392291963)
                    ·
                      rfl

theorem cell23_2060076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_2060076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060076 prefixEnd_2060076 := by exact prefixLift 2060076
  have htrace : WordTrace (prefixWord ++ tailWord_2060076) baseStart_2060076 baseEnd_2060076 := by
    simpa [prefixWord, tailWord_2060076, baseEnd_2060076] using wordTrace_append hprefix tailTrace_2060076
  have hstable : (prefixWord ++ tailWord_2060076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060076).length < 2 ^ (prefixWord ++ tailWord_2060076).sum := by decide
  have hdescent : baseEnd_2060076 < baseStart_2060076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060086 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2060086 : Nat := 118140960795 + 2060086 * 2 ^ 59
def prefixEnd_2060086 : Nat := 4983230072969 + 3 ^ 40 * 2060086 * 2
def baseEnd_2060086 : Nat := 1057814307598332137750843

theorem tailTrace_2060086 : CollatzResearch.WordTrace tailWord_2060086 prefixEnd_2060086 1057814307598332137750843 := by
  unfold tailWord_2060086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696094325916733220182507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50091672809778487681946741 4696094325916733220182507)
  ·
    refine ⟨7044141488875099830273761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696094325916733220182507 7044141488875099830273761)
    ·
      refine ⟨5283106116656324872705321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7044141488875099830273761 5283106116656324872705321)
      ·
        refine ⟨3962329587492243654528991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283106116656324872705321 3962329587492243654528991)
        ·
          refine ⟨5943494381238365481793487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962329587492243654528991 5943494381238365481793487)
          ·
            refine ⟨8915241571857548222690231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943494381238365481793487 8915241571857548222690231)
            ·
              refine ⟨13372862357786322334035347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915241571857548222690231 13372862357786322334035347)
              ·
                refine ⟨20059293536679483501053021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13372862357786322334035347 20059293536679483501053021)
                ·
                  refine ⟨7522235076254806312894883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20059293536679483501053021 7522235076254806312894883)
                  ·
                    refine ⟨11283352614382209469342325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522235076254806312894883 11283352614382209469342325)
                    ·
                      refine ⟨1057814307598332137750843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11283352614382209469342325 1057814307598332137750843)
                      ·
                        rfl

theorem cell23_2060086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2060086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060086 prefixEnd_2060086 := by exact prefixLift 2060086
  have htrace : WordTrace (prefixWord ++ tailWord_2060086) baseStart_2060086 baseEnd_2060086 := by
    simpa [prefixWord, tailWord_2060086, baseEnd_2060086] using wordTrace_append hprefix tailTrace_2060086
  have hstable : (prefixWord ++ tailWord_2060086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060086).length < 2 ^ (prefixWord ++ tailWord_2060086).sum := by decide
  have hdescent : baseEnd_2060086 < baseStart_2060086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060117 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2060117 : Nat := 118140960795 + 2060117 * 2 ^ 59
def prefixEnd_2060117 : Nat := 4983230072969 + 3 ^ 40 * 2060117 * 2
def baseEnd_2060117 : Nat := 1057830225498621516463201

theorem tailTrace_2060117 : CollatzResearch.WordTrace tailWord_2060117 prefixEnd_2060117 1057830225498621516463201 := by
  unfold tailWord_2060117
  simp only [CollatzResearch.WordTrace]
  refine ⟨75138639877555423817298605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50092426585036949211532403 75138639877555423817298605)
  ·
    refine ⟨28176989954083283931486977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75138639877555423817298605 28176989954083283931486977)
    ·
      refine ⟨21132742465562462948615233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28176989954083283931486977 21132742465562462948615233)
      ·
        refine ⟨15849556849171847211461425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21132742465562462948615233 15849556849171847211461425)
        ·
          refine ⟨11887167636878885408596069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15849556849171847211461425 11887167636878885408596069)
          ·
            refine ⟨2228843931914791014111763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11887167636878885408596069 2228843931914791014111763)
            ·
              refine ⟨3343265897872186521167645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228843931914791014111763 3343265897872186521167645)
              ·
                refine ⟨1253724711702069945437867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343265897872186521167645 1253724711702069945437867)
                ·
                  refine ⟨1880587067553104918156801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253724711702069945437867 1880587067553104918156801)
                  ·
                    refine ⟨1410440300664828688617601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880587067553104918156801 1410440300664828688617601)
                    ·
                      refine ⟨1057830225498621516463201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410440300664828688617601 1057830225498621516463201)
                      ·
                        rfl

theorem cell23_2060117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2060117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060117 prefixEnd_2060117 := by exact prefixLift 2060117
  have htrace : WordTrace (prefixWord ++ tailWord_2060117) baseStart_2060117 baseEnd_2060117 := by
    simpa [prefixWord, tailWord_2060117, baseEnd_2060117] using wordTrace_append hprefix tailTrace_2060117
  have hstable : (prefixWord ++ tailWord_2060117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060117).length < 2 ^ (prefixWord ++ tailWord_2060117).sum := by decide
  have hdescent : baseEnd_2060117 < baseStart_2060117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060149 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2060149 : Nat := 118140960795 + 2060149 * 2 ^ 59
def prefixEnd_2060149 : Nat := 4983230072969 + 3 ^ 40 * 2060149 * 2
def baseEnd_2060149 : Nat := 352615552293188463754351

theorem tailTrace_2060149 : CollatzResearch.WordTrace tailWord_2060149 prefixEnd_2060149 352615552293188463754351 := by
  unfold tailWord_2060149
  simp only [CollatzResearch.WordTrace]
  refine ⟨75139807013439493282463501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50093204675626328854975667 75139807013439493282463501)
  ·
    refine ⟨28177427630039809980923813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75139807013439493282463501 28177427630039809980923813)
    ·
      refine ⟨5283267680632464371423215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28177427630039809980923813 5283267680632464371423215)
      ·
        refine ⟨7924901520948696557134823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283267680632464371423215 7924901520948696557134823)
        ·
          refine ⟨11887352281423044835702235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924901520948696557134823 11887352281423044835702235)
          ·
            refine ⟨17831028422134567253553353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887352281423044835702235 17831028422134567253553353)
            ·
              refine ⟨13373271316600925440165015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17831028422134567253553353 13373271316600925440165015)
              ·
                refine ⟨20059906974901388160247523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13373271316600925440165015 20059906974901388160247523)
                ·
                  refine ⟨30089860462352082240371285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20059906974901388160247523 30089860462352082240371285)
                  ·
                    refine ⟨352615552293188463754351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30089860462352082240371285 352615552293188463754351)
                    ·
                      rfl

theorem cell23_2060149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2060149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060149 prefixEnd_2060149 := by exact prefixLift 2060149
  have htrace : WordTrace (prefixWord ++ tailWord_2060149) baseStart_2060149 baseEnd_2060149 := by
    simpa [prefixWord, tailWord_2060149, baseEnd_2060149] using wordTrace_append hprefix tailTrace_2060149
  have hstable : (prefixWord ++ tailWord_2060149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060149).length < 2 ^ (prefixWord ++ tailWord_2060149).sum := by decide
  have hdescent : baseEnd_2060149 < baseStart_2060149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060216 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_2060216 : Nat := 118140960795 + 2060216 * 2 ^ 59
def prefixEnd_2060216 : Nat := 4983230072969 + 3 ^ 40 * 2060216 * 2
def baseEnd_2060216 : Nat := 1057881060083416629125245

theorem tailTrace_2060216 : CollatzResearch.WordTrace tailWord_2060216 prefixEnd_2060216 1057881060083416629125245 := by
  unfold tailWord_2060216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37571125352098381862576251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50094833802797842483435001 37571125352098381862576251)
  ·
    refine ⟨56356688028147572793864377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37571125352098381862576251 56356688028147572793864377)
    ·
      refine ⟨42267516021110679595398283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56356688028147572793864377 42267516021110679595398283)
      ·
        refine ⟨63401274031666019393097425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42267516021110679595398283 63401274031666019393097425)
        ·
          refine ⟨47550955523749514544823069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63401274031666019393097425 47550955523749514544823069)
          ·
            refine ⟨17831608321406067954308651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47550955523749514544823069 17831608321406067954308651)
            ·
              refine ⟨26747412482109101931462977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17831608321406067954308651 26747412482109101931462977)
              ·
                refine ⟨20060559361581826448597233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26747412482109101931462977 20060559361581826448597233)
                ·
                  refine ⟨15045419521186369836447925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20060559361581826448597233 15045419521186369836447925)
                  ·
                    refine ⟨1410508080111222172166993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15045419521186369836447925 1410508080111222172166993)
                    ·
                      refine ⟨1057881060083416629125245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410508080111222172166993 1057881060083416629125245)
                      ·
                        rfl

theorem cell23_2060216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_2060216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060216 prefixEnd_2060216 := by exact prefixLift 2060216
  have htrace : WordTrace (prefixWord ++ tailWord_2060216) baseStart_2060216 baseEnd_2060216 := by
    simpa [prefixWord, tailWord_2060216, baseEnd_2060216] using wordTrace_append hprefix tailTrace_2060216
  have hstable : (prefixWord ++ tailWord_2060216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060216).length < 2 ^ (prefixWord ++ tailWord_2060216).sum := by decide
  have hdescent : baseEnd_2060216 < baseStart_2060216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060266 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2060266 : Nat := 118140960795 + 2060266 * 2 ^ 59
def prefixEnd_2060266 : Nat := 4983230072969 + 3 ^ 40 * 2060266 * 2
def baseEnd_2060266 : Nat := 1057906734116141433500015

theorem tailTrace_2060266 : CollatzResearch.WordTrace tailWord_2060266 prefixEnd_2060266 1057906734116141433500015 := by
  unfold tailWord_2060266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786018588503905566118163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50096049569343748176315101 18786018588503905566118163)
  ·
    refine ⟨28179027882755858349177245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18786018588503905566118163 28179027882755858349177245)
    ·
      refine ⟨10567135456033446880941467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28179027882755858349177245 10567135456033446880941467)
      ·
        refine ⟨15850703184050170321412201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567135456033446880941467 15850703184050170321412201)
        ·
          refine ⟨11888027388037627741059151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850703184050170321412201 11888027388037627741059151)
          ·
            refine ⟨17832041082056441611588727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888027388037627741059151 17832041082056441611588727)
            ·
              refine ⟨26748061623084662417383091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832041082056441611588727 26748061623084662417383091)
              ·
                refine ⟨40122092434626993626074637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26748061623084662417383091 40122092434626993626074637)
                ·
                  refine ⟨15045784662985122609777989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40122092434626993626074637 15045784662985122609777989)
                  ·
                    refine ⟨2821084624309710489333373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15045784662985122609777989 2821084624309710489333373)
                    ·
                      refine ⟨1057906734116141433500015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821084624309710489333373 1057906734116141433500015)
                      ·
                        rfl

theorem cell23_2060266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2060266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060266 prefixEnd_2060266 := by exact prefixLift 2060266
  have htrace : WordTrace (prefixWord ++ tailWord_2060266) baseStart_2060266 baseEnd_2060266 := by
    simpa [prefixWord, tailWord_2060266, baseEnd_2060266] using wordTrace_append hprefix tailTrace_2060266
  have hstable : (prefixWord ++ tailWord_2060266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060266).length < 2 ^ (prefixWord ++ tailWord_2060266).sum := by decide
  have hdescent : baseEnd_2060266 < baseStart_2060266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060294 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2060294 : Nat := 118140960795 + 2060294 * 2 ^ 59
def prefixEnd_2060294 : Nat := 4983230072969 + 3 ^ 40 * 2060294 * 2
def baseEnd_2060294 : Nat := 352640370524822441316629

theorem tailTrace_2060294 : CollatzResearch.WordTrace tailWord_2060294 prefixEnd_2060294 352640370524822441316629 := by
  unfold tailWord_2060294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348284237434818220202873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50096730398609455364327957 2348284237434818220202873)
  ·
    refine ⟨1761213178076113665152155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2348284237434818220202873 1761213178076113665152155)
    ·
      refine ⟨2641819767114170497728233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761213178076113665152155 2641819767114170497728233)
      ·
        refine ⟨1981364825335627873296175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2641819767114170497728233 1981364825335627873296175)
        ·
          refine ⟨2972047238003441809944263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981364825335627873296175 2972047238003441809944263)
          ·
            refine ⟨4458070857005162714916395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972047238003441809944263 4458070857005162714916395)
            ·
              refine ⟨6687106285507744072374593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458070857005162714916395 6687106285507744072374593)
              ·
                refine ⟨5015329714130808054280945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687106285507744072374593 5015329714130808054280945)
                ·
                  refine ⟨3761497285598106040710709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015329714130808054280945 3761497285598106040710709)
                  ·
                    refine ⟨352640370524822441316629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3761497285598106040710709 352640370524822441316629)
                    ·
                      rfl

theorem cell23_2060294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2060294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060294 prefixEnd_2060294 := by exact prefixLift 2060294
  have htrace : WordTrace (prefixWord ++ tailWord_2060294) baseStart_2060294 baseEnd_2060294 := by
    simpa [prefixWord, tailWord_2060294, baseEnd_2060294] using wordTrace_append hprefix tailTrace_2060294
  have hstable : (prefixWord ++ tailWord_2060294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060294).length < 2 ^ (prefixWord ++ tailWord_2060294).sum := by decide
  have hdescent : baseEnd_2060294 < baseStart_2060294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060323 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 4, 3, 2]
def baseStart_2060323 : Nat := 118140960795 + 2060323 * 2 ^ 59
def prefixEnd_2060323 : Nat := 4983230072969 + 3 ^ 40 * 2060323 * 2
def baseEnd_2060323 : Nat := 1057936002513447710487253

theorem tailTrace_2060323 : CollatzResearch.WordTrace tailWord_2060323 prefixEnd_2060323 1057936002513447710487253 := by
  unfold tailWord_2060323
  simp only [CollatzResearch.WordTrace]
  refine ⟨75146153314809120999297623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50097435543206080666198415 75146153314809120999297623)
  ·
    refine ⟨112719229972213681498946435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75146153314809120999297623 112719229972213681498946435)
    ·
      refine ⟨169078844958320522248419653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112719229972213681498946435 169078844958320522248419653)
      ·
        refine ⟨31702283429685097921578685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169078844958320522248419653 31702283429685097921578685)
        ·
          refine ⟨11888356286131911720592007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31702283429685097921578685 11888356286131911720592007)
          ·
            refine ⟨17832534429197867580888011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888356286131911720592007 17832534429197867580888011)
            ·
              refine ⟨26748801643796801371332017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832534429197867580888011 26748801643796801371332017)
              ·
                refine ⟨20061601232847601028499013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26748801643796801371332017 20061601232847601028499013)
                ·
                  refine ⟨3761550231158925192843565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20061601232847601028499013 3761550231158925192843565)
                  ·
                    refine ⟨1410581336684596947316337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761550231158925192843565 1410581336684596947316337)
                    ·
                      refine ⟨1057936002513447710487253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410581336684596947316337 1057936002513447710487253)
                      ·
                        rfl

theorem cell23_2060323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_2060323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060323 prefixEnd_2060323 := by exact prefixLift 2060323
  have htrace : WordTrace (prefixWord ++ tailWord_2060323) baseStart_2060323 baseEnd_2060323 := by
    simpa [prefixWord, tailWord_2060323, baseEnd_2060323] using wordTrace_append hprefix tailTrace_2060323
  have hstable : (prefixWord ++ tailWord_2060323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060323).length < 2 ^ (prefixWord ++ tailWord_2060323).sum := by decide
  have hdescent : baseEnd_2060323 < baseStart_2060323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060373 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2060373 : Nat := 118140960795 + 2060373 * 2 ^ 59
def prefixEnd_2060373 : Nat := 4983230072969 + 3 ^ 40 * 2060373 * 2
def baseEnd_2060373 : Nat := 1057961676546172514862023

theorem tailTrace_2060373 : CollatzResearch.WordTrace tailWord_2060373 prefixEnd_2060373 1057961676546172514862023 := by
  unfold tailWord_2060373
  simp only [CollatzResearch.WordTrace]
  refine ⟨75147976964627979538617773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50098651309751986359078515 75147976964627979538617773)
  ·
    refine ⟨28180491361735492326981665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75147976964627979538617773 28180491361735492326981665)
    ·
      refine ⟨21135368521301619245236249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28180491361735492326981665 21135368521301619245236249)
      ·
        refine ⟨15851526390976214433927187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21135368521301619245236249 15851526390976214433927187)
        ·
          refine ⟨23777289586464321650890781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15851526390976214433927187 23777289586464321650890781)
          ·
            refine ⟨8916483594924120619084043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23777289586464321650890781 8916483594924120619084043)
            ·
              refine ⟨13374725392386180928626065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916483594924120619084043 13374725392386180928626065)
              ·
                refine ⟨10031044044289635696469549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13374725392386180928626065 10031044044289635696469549)
                ·
                  refine ⟨3761641516608613386176081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10031044044289635696469549 3761641516608613386176081)
                  ·
                    refine ⟨2821231137456460039632061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761641516608613386176081 2821231137456460039632061)
                    ·
                      refine ⟨1057961676546172514862023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821231137456460039632061 1057961676546172514862023)
                      ·
                        rfl

theorem cell23_2060373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2060373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060373 prefixEnd_2060373 := by exact prefixLift 2060373
  have htrace : WordTrace (prefixWord ++ tailWord_2060373) baseStart_2060373 baseEnd_2060373 := by
    simpa [prefixWord, tailWord_2060373, baseEnd_2060373] using wordTrace_append hprefix tailTrace_2060373
  have hstable : (prefixWord ++ tailWord_2060373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060373).length < 2 ^ (prefixWord ++ tailWord_2060373).sum := by decide
  have hdescent : baseEnd_2060373 < baseStart_2060373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060376 : List Nat := [2, 1, 2, 2, 1, 4, 3, 8]
def baseStart_2060376 : Nat := 118140960795 + 2060376 * 2 ^ 59
def prefixEnd_2060376 : Nat := 4983230072969 + 3 ^ 40 * 2060376 * 2
def baseEnd_2060376 : Nat := 39183822851412444560167

theorem tailTrace_2060376 : CollatzResearch.WordTrace tailWord_2060376 prefixEnd_2060376 39183822851412444560167 := by
  unfold tailWord_2060376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574043191808555525488491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50098724255744740700651321 37574043191808555525488491)
  ·
    refine ⟨56361064787712833288232737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37574043191808555525488491 56361064787712833288232737)
    ·
      refine ⟨42270798590784624966174553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56361064787712833288232737 42270798590784624966174553)
      ·
        refine ⟨31703098943088468724630915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42270798590784624966174553 31703098943088468724630915)
        ·
          refine ⟨47554648414632703086946373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31703098943088468724630915 47554648414632703086946373)
          ·
            refine ⟨8916496577743631828802445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47554648414632703086946373 8916496577743631828802445)
            ·
              refine ⟨3343686216653861935800917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8916496577743631828802445 3343686216653861935800917)
              ·
                refine ⟨39183822851412444560167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3343686216653861935800917 39183822851412444560167)
                ·
                  rfl

theorem cell23_2060376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 8].length) (baseStart_2060376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060376 prefixEnd_2060376 := by exact prefixLift 2060376
  have htrace : WordTrace (prefixWord ++ tailWord_2060376) baseStart_2060376 baseEnd_2060376 := by
    simpa [prefixWord, tailWord_2060376, baseEnd_2060376] using wordTrace_append hprefix tailTrace_2060376
  have hstable : (prefixWord ++ tailWord_2060376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060376).length < 2 ^ (prefixWord ++ tailWord_2060376).sum := by decide
  have hdescent : baseEnd_2060376 < baseStart_2060376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060380 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2060380 : Nat := 118140960795 + 2060380 * 2 ^ 59
def prefixEnd_2060380 : Nat := 4983230072969 + 3 ^ 40 * 2060380 * 2
def baseEnd_2060380 : Nat := 352655090303584662491497

theorem tailTrace_2060380 : CollatzResearch.WordTrace tailWord_2060380 prefixEnd_2060380 352655090303584662491497 := by
  unfold tailWord_2060380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574116137801309867061297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50098821517068413156081729 37574116137801309867061297)
  ·
    refine ⟨28180587103350982400295973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37574116137801309867061297 28180587103350982400295973)
    ·
      refine ⟨5283860081878309200055495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28180587103350982400295973 5283860081878309200055495)
      ·
        refine ⟨7925790122817463800083243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283860081878309200055495 7925790122817463800083243)
        ·
          refine ⟨11888685184226195700124865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925790122817463800083243 11888685184226195700124865)
          ·
            refine ⟨8916513888169646775093649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11888685184226195700124865 8916513888169646775093649)
            ·
              refine ⟨6687385416127235081320237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916513888169646775093649 6687385416127235081320237)
              ·
                refine ⟨2507769531047713155495089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687385416127235081320237 2507769531047713155495089)
                ·
                  refine ⟨1880827148285784866621317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507769531047713155495089 1880827148285784866621317)
                  ·
                    refine ⟨352655090303584662491497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880827148285784866621317 352655090303584662491497)
                    ·
                      rfl

theorem cell23_2060380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2060380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060380 prefixEnd_2060380 := by exact prefixLift 2060380
  have htrace : WordTrace (prefixWord ++ tailWord_2060380) baseStart_2060380 baseEnd_2060380 := by
    simpa [prefixWord, tailWord_2060380, baseEnd_2060380] using wordTrace_append hprefix tailTrace_2060380
  have hstable : (prefixWord ++ tailWord_2060380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060380).length < 2 ^ (prefixWord ++ tailWord_2060380).sum := by decide
  have hdescent : baseEnd_2060380 < baseStart_2060380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060407 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_2060407 : Nat := 118140960795 + 2060407 * 2 ^ 59
def prefixEnd_2060407 : Nat := 4983230072969 + 3 ^ 40 * 2060407 * 2
def baseEnd_2060407 : Nat := 1057979134888425381836867

theorem tailTrace_2060407 : CollatzResearch.WordTrace tailWord_2060407 prefixEnd_2060407 1057979134888425381836867 := by
  unfold tailWord_2060407
  simp only [CollatzResearch.WordTrace]
  refine ⟨75149217046504803345355475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50099478031003202230236983 75149217046504803345355475)
  ·
    refine ⟨112723825569757205018033213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75149217046504803345355475 112723825569757205018033213)
    ·
      refine ⟨42271434588658951881762455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112723825569757205018033213 42271434588658951881762455)
      ·
        refine ⟨63407151882988427822643683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42271434588658951881762455 63407151882988427822643683)
        ·
          refine ⟨95110727824482641733965525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63407151882988427822643683 95110727824482641733965525)
          ·
            refine ⟨2229157683386311915639817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95110727824482641733965525 2229157683386311915639817)
            ·
              refine ⟨1671868262539733936729863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229157683386311915639817 1671868262539733936729863)
              ·
                refine ⟨2507802393809600905094795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671868262539733936729863 2507802393809600905094795)
                ·
                  refine ⟨3761703590714401357642193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507802393809600905094795 3761703590714401357642193)
                  ·
                    refine ⟨2821277693035801018231645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761703590714401357642193 2821277693035801018231645)
                    ·
                      refine ⟨1057979134888425381836867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821277693035801018231645 1057979134888425381836867)
                      ·
                        rfl

theorem cell23_2060407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_2060407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060407 prefixEnd_2060407 := by exact prefixLift 2060407
  have htrace : WordTrace (prefixWord ++ tailWord_2060407) baseStart_2060407 baseEnd_2060407 := by
    simpa [prefixWord, tailWord_2060407, baseEnd_2060407] using wordTrace_append hprefix tailTrace_2060407
  have hstable : (prefixWord ++ tailWord_2060407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060407).length < 2 ^ (prefixWord ++ tailWord_2060407).sum := by decide
  have hdescent : baseEnd_2060407 < baseStart_2060407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060420 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2060420 : Nat := 118140960795 + 2060420 * 2 ^ 59
def prefixEnd_2060420 : Nat := 4983230072969 + 3 ^ 40 * 2060420 * 2
def baseEnd_2060420 : Nat := 1057985810136933830974307

theorem tailTrace_2060420 : CollatzResearch.WordTrace tailWord_2060420 prefixEnd_2060420 1057985810136933830974307 := by
  unfold tailWord_2060420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574845597728853282789357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50099794130305137710385809 37574845597728853282789357)
  ·
    refine ⟨14090567099148319981046009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37574845597728853282789357 14090567099148319981046009)
    ·
      refine ⟨10567925324361239985784507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14090567099148319981046009 10567925324361239985784507)
      ·
        refine ⟨15851887986541859978676761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10567925324361239985784507 15851887986541859978676761)
        ·
          refine ⟨11888915989906394984007571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15851887986541859978676761 11888915989906394984007571)
          ·
            refine ⟨17833373984859592476011357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888915989906394984007571 17833373984859592476011357)
            ·
              refine ⟨6687515244322347178504259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17833373984859592476011357 6687515244322347178504259)
              ·
                refine ⟨10031272866483520767756389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687515244322347178504259 10031272866483520767756389)
                ·
                  refine ⟨1880863662465660143954323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10031272866483520767756389 1880863662465660143954323)
                  ·
                    refine ⟨2821295493698490215931485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880863662465660143954323 2821295493698490215931485)
                    ·
                      refine ⟨1057985810136933830974307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821295493698490215931485 1057985810136933830974307)
                      ·
                        rfl

theorem cell23_2060420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2060420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060420 prefixEnd_2060420 := by exact prefixLift 2060420
  have htrace : WordTrace (prefixWord ++ tailWord_2060420) baseStart_2060420 baseEnd_2060420 := by
    simpa [prefixWord, tailWord_2060420, baseEnd_2060420] using wordTrace_append hprefix tailTrace_2060420
  have hstable : (prefixWord ++ tailWord_2060420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060420).length < 2 ^ (prefixWord ++ tailWord_2060420).sum := by decide
  have hdescent : baseEnd_2060420 < baseStart_2060420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060437 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_2060437 : Nat := 118140960795 + 2060437 * 2 ^ 59
def prefixEnd_2060437 : Nat := 4983230072969 + 3 ^ 40 * 2060437 * 2
def baseEnd_2060437 : Nat := 1057994539308060264461729

theorem tailTrace_2060437 : CollatzResearch.WordTrace tailWord_2060437 prefixEnd_2060437 1057994539308060264461729 := by
  unfold tailWord_2060437
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150311236396118468947565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50100207490930745645965043 75150311236396118468947565)
  ·
    refine ⟨28181366713648544425855337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75150311236396118468947565 28181366713648544425855337)
    ·
      refine ⟨21136025035236408319391503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28181366713648544425855337 21136025035236408319391503)
      ·
        refine ⟨31704037552854612479087255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136025035236408319391503 31704037552854612479087255)
        ·
          refine ⟨47556056329281918718630883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31704037552854612479087255 47556056329281918718630883)
          ·
            refine ⟨71334084493922878077946325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47556056329281918718630883 71334084493922878077946325)
            ·
              refine ⟨1671892605326317454951867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71334084493922878077946325 1671892605326317454951867)
              ·
                refine ⟨2507838907989476182427801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671892605326317454951867 2507838907989476182427801)
                ·
                  refine ⟨1880879180992107136820851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507838907989476182427801 1880879180992107136820851)
                  ·
                    refine ⟨2821318771488160705231277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880879180992107136820851 2821318771488160705231277)
                    ·
                      refine ⟨1057994539308060264461729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821318771488160705231277 1057994539308060264461729)
                      ·
                        rfl

theorem cell23_2060437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_2060437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060437 prefixEnd_2060437 := by exact prefixLift 2060437
  have htrace : WordTrace (prefixWord ++ tailWord_2060437) baseStart_2060437 baseEnd_2060437 := by
    simpa [prefixWord, tailWord_2060437, baseEnd_2060437] using wordTrace_append hprefix tailTrace_2060437
  have hstable : (prefixWord ++ tailWord_2060437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060437).length < 2 ^ (prefixWord ++ tailWord_2060437).sum := by decide
  have hdescent : baseEnd_2060437 < baseStart_2060437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060438 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2060438 : Nat := 118140960795 + 2060438 * 2 ^ 59
def prefixEnd_2060438 : Nat := 4983230072969 + 3 ^ 40 * 2060438 * 2
def baseEnd_2060438 : Nat := 1057995052788714760549225

theorem tailTrace_2060438 : CollatzResearch.WordTrace tailWord_2060438 prefixEnd_2060438 1057995052788714760549225 := by
  unfold tailWord_2060438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696896731837030977483373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50100231806261663759822645 4696896731837030977483373)
  ·
    refine ⟨1761336274438886616556265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4696896731837030977483373 1761336274438886616556265)
    ·
      refine ⟨1321002205829164962417199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1761336274438886616556265 1321002205829164962417199)
      ·
        refine ⟨1981503308743747443625799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321002205829164962417199 1981503308743747443625799)
        ·
          refine ⟨2972254963115621165438699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981503308743747443625799 2972254963115621165438699)
          ·
            refine ⟨4458382444673431748158049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972254963115621165438699 4458382444673431748158049)
            ·
              refine ⟨3343786833505073811118537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458382444673431748158049 3343786833505073811118537)
              ·
                refine ⟨2507840125128805358338903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343786833505073811118537 2507840125128805358338903)
                ·
                  refine ⟨3761760187693208037508355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507840125128805358338903 3761760187693208037508355)
                  ·
                    refine ⟨5642640281539812056262533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761760187693208037508355 5642640281539812056262533)
                    ·
                      refine ⟨1057995052788714760549225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5642640281539812056262533 1057995052788714760549225)
                      ·
                        rfl

theorem cell23_2060438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2060438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060438 prefixEnd_2060438 := by exact prefixLift 2060438
  have htrace : WordTrace (prefixWord ++ tailWord_2060438) baseStart_2060438 baseEnd_2060438 := by
    simpa [prefixWord, tailWord_2060438, baseEnd_2060438] using wordTrace_append hprefix tailTrace_2060438
  have hstable : (prefixWord ++ tailWord_2060438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060438).length < 2 ^ (prefixWord ++ tailWord_2060438).sum := by decide
  have hdescent : baseEnd_2060438 < baseStart_2060438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 4, 2]
def baseStart_2060443 : Nat := 118140960795 + 2060443 * 2 ^ 59
def prefixEnd_2060443 : Nat := 4983230072969 + 3 ^ 40 * 2060443 * 2
def baseEnd_2060443 : Nat := 1057997620191987240986701

theorem tailTrace_2060443 : CollatzResearch.WordTrace tailWord_2060443 prefixEnd_2060443 1057997620191987240986701 := by
  unfold tailWord_2060443
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150530074374381493665983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50100353382916254329110655 75150530074374381493665983)
  ·
    refine ⟨112725795111561572240498975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75150530074374381493665983 112725795111561572240498975)
    ·
      refine ⟨169088692667342358360748463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112725795111561572240498975 169088692667342358360748463)
      ·
        refine ⟨253633039001013537541122695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169088692667342358360748463 253633039001013537541122695)
        ·
          refine ⟨380449558501520306311684043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253633039001013537541122695 380449558501520306311684043)
          ·
            refine ⟨570674337752280459467526065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380449558501520306311684043 570674337752280459467526065)
            ·
              refine ⟨428005753314210344600644549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570674337752280459467526065 428005753314210344600644549)
              ·
                refine ⟨80251078746414439612620853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428005753314210344600644549 80251078746414439612620853)
                ·
                  refine ⟨7523538632476353713683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80251078746414439612620853 7523538632476353713683205)
                  ·
                    refine ⟨1410663493589316321315601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7523538632476353713683205 1410663493589316321315601)
                    ·
                      refine ⟨1057997620191987240986701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410663493589316321315601 1057997620191987240986701)
                      ·
                        rfl

theorem cell23_2060443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4, 2].length) (baseStart_2060443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060443 prefixEnd_2060443 := by exact prefixLift 2060443
  have htrace : WordTrace (prefixWord ++ tailWord_2060443) baseStart_2060443 baseEnd_2060443 := by
    simpa [prefixWord, tailWord_2060443, baseEnd_2060443] using wordTrace_append hprefix tailTrace_2060443
  have hstable : (prefixWord ++ tailWord_2060443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060443).length < 2 ^ (prefixWord ++ tailWord_2060443).sum := by decide
  have hdescent : baseEnd_2060443 < baseStart_2060443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060447 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2060447 : Nat := 118140960795 + 2060447 * 2 ^ 59
def prefixEnd_2060447 : Nat := 4983230072969 + 3 ^ 40 * 2060447 * 2
def baseEnd_2060447 : Nat := 1057999674114605225336683

theorem tailTrace_2060447 : CollatzResearch.WordTrace tailWord_2060447 prefixEnd_2060447 1057999674114605225336683 := by
  unfold tailWord_2060447
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150675966359890176811595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50100450644239926784541063 75150675966359890176811595)
  ·
    refine ⟨112726013949539835265217393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75150675966359890176811595 112726013949539835265217393)
    ·
      refine ⟨84544510462154876448913045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112726013949539835265217393 84544510462154876448913045)
      ·
        refine ⟨3963023927913509833542799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84544510462154876448913045 3963023927913509833542799)
        ·
          refine ⟨5944535891870264750314199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963023927913509833542799 5944535891870264750314199)
          ·
            refine ⟨8916803837805397125471299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944535891870264750314199 8916803837805397125471299)
            ·
              refine ⟨13375205756708095688206949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916803837805397125471299 13375205756708095688206949)
              ·
                refine ⟨2507851079382767941538803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13375205756708095688206949 2507851079382767941538803)
                ·
                  refine ⟨3761776619074151912308205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507851079382767941538803 3761776619074151912308205)
                  ·
                    refine ⟨1410666232152806967115577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3761776619074151912308205 1410666232152806967115577)
                    ·
                      refine ⟨1057999674114605225336683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410666232152806967115577 1057999674114605225336683)
                      ·
                        rfl

theorem cell23_2060447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2060447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060447 prefixEnd_2060447 := by exact prefixLift 2060447
  have htrace : WordTrace (prefixWord ++ tailWord_2060447) baseStart_2060447 baseEnd_2060447 := by
    simpa [prefixWord, tailWord_2060447, baseEnd_2060447] using wordTrace_append hprefix tailTrace_2060447
  have hstable : (prefixWord ++ tailWord_2060447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060447).length < 2 ^ (prefixWord ++ tailWord_2060447).sum := by decide
  have hdescent : baseEnd_2060447 < baseStart_2060447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060477 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_2060477 : Nat := 118140960795 + 2060477 * 2 ^ 59
def prefixEnd_2060477 : Nat := 4983230072969 + 3 ^ 40 * 2060477 * 2
def baseEnd_2060477 : Nat := 1058015078534240107961545

theorem tailTrace_2060477 : CollatzResearch.WordTrace tailWord_2060477 prefixEnd_2060477 1058015078534240107961545 := by
  unfold tailWord_2060477
  simp only [CollatzResearch.WordTrace]
  refine ⟨75151770156251205300403685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50101180104167470200269123 75151770156251205300403685)
  ·
    refine ⟨14090956904297100993825691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75151770156251205300403685 14090956904297100993825691)
    ·
      refine ⟨21136435356445651490738537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090956904297100993825691 21136435356445651490738537)
      ·
        refine ⟨15852326517334238618053903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21136435356445651490738537 15852326517334238618053903)
        ·
          refine ⟨23778489776001357927080855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15852326517334238618053903 23778489776001357927080855)
          ·
            refine ⟨35667734664002036890621283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23778489776001357927080855 35667734664002036890621283)
            ·
              refine ⟨53501601996003055335931925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35667734664002036890621283 53501601996003055335931925)
              ·
                refine ⟨2507887593562643218871809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53501601996003055335931925 2507887593562643218871809)
                ·
                  refine ⟨1880915695171982414153857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507887593562643218871809 1880915695171982414153857)
                  ·
                    refine ⟨1410686771378986810615393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880915695171982414153857 1410686771378986810615393)
                    ·
                      refine ⟨1058015078534240107961545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410686771378986810615393 1058015078534240107961545)
                      ·
                        rfl

theorem cell23_2060477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_2060477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060477 prefixEnd_2060477 := by exact prefixLift 2060477
  have htrace : WordTrace (prefixWord ++ tailWord_2060477) baseStart_2060477 baseEnd_2060477 := by
    simpa [prefixWord, tailWord_2060477, baseEnd_2060477] using wordTrace_append hprefix tailTrace_2060477
  have hstable : (prefixWord ++ tailWord_2060477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060477).length < 2 ^ (prefixWord ++ tailWord_2060477).sum := by decide
  have hdescent : baseEnd_2060477 < baseStart_2060477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060494 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_2060494 : Nat := 118140960795 + 2060494 * 2 ^ 59
def prefixEnd_2060494 : Nat := 4983230072969 + 3 ^ 40 * 2060494 * 2
def baseEnd_2060494 : Nat := 1058023807705366541448967

theorem tailTrace_2060494 : CollatzResearch.WordTrace tailWord_2060494 prefixEnd_2060494 1058023807705366541448967 := by
  unfold tailWord_2060494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394048774648702150471567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50101593464793078135848357 9394048774648702150471567)
  ·
    refine ⟨14091073161973053225707351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9394048774648702150471567 14091073161973053225707351)
    ·
      refine ⟨21136609742959579838561027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091073161973053225707351 21136609742959579838561027)
      ·
        refine ⟨31704914614439369757841541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136609742959579838561027 31704914614439369757841541)
        ·
          refine ⟨5944671490207381829595289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31704914614439369757841541 5944671490207381829595289)
          ·
            refine ⟨4458503617655536372196467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944671490207381829595289 4458503617655536372196467)
            ·
              refine ⟨6687755426483304558294701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458503617655536372196467 6687755426483304558294701)
              ·
                refine ⟨2507908284931239209360513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687755426483304558294701 2507908284931239209360513)
                ·
                  refine ⟨1880931213698429407020385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2507908284931239209360513 1880931213698429407020385)
                  ·
                    refine ⟨1410698410273822055265289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880931213698429407020385 1410698410273822055265289)
                    ·
                      refine ⟨1058023807705366541448967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410698410273822055265289 1058023807705366541448967)
                      ·
                        rfl

theorem cell23_2060494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_2060494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060494 prefixEnd_2060494 := by exact prefixLift 2060494
  have htrace : WordTrace (prefixWord ++ tailWord_2060494) baseStart_2060494 baseEnd_2060494 := by
    simpa [prefixWord, tailWord_2060494, baseEnd_2060494] using wordTrace_append hprefix tailTrace_2060494
  have hstable : (prefixWord ++ tailWord_2060494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060494).length < 2 ^ (prefixWord ++ tailWord_2060494).sum := by decide
  have hdescent : baseEnd_2060494 < baseStart_2060494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060530 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2060530 : Nat := 118140960795 + 2060530 * 2 ^ 59
def prefixEnd_2060530 : Nat := 4983230072969 + 3 ^ 40 * 2060530 * 2
def baseEnd_2060530 : Nat := 352680764336309466866267

theorem tailTrace_2060530 : CollatzResearch.WordTrace tailWord_2060530 prefixEnd_2060530 352680764336309466866267 := by
  unfold tailWord_2060530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788425806264798838020761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50102468816706130234722029 18788425806264798838020761)
  ·
    refine ⟨14091319354698599128515571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18788425806264798838020761 14091319354698599128515571)
    ·
      refine ⟨21136979032047898692773357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091319354698599128515571 21136979032047898692773357)
      ·
        refine ⟨7926367137017962009790009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21136979032047898692773357 7926367137017962009790009)
        ·
          refine ⟨5944775352763471507342507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926367137017962009790009 5944775352763471507342507)
          ·
            refine ⟨8917163029145207261013761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944775352763471507342507 8917163029145207261013761)
            ·
              refine ⟨6687872271858905445760321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8917163029145207261013761 6687872271858905445760321)
              ·
                refine ⟨5015904203894179084320241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687872271858905445760321 5015904203894179084320241)
                ·
                  refine ⟨3761928152920634313240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015904203894179084320241 3761928152920634313240181)
                  ·
                    refine ⟨352680764336309466866267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3761928152920634313240181 352680764336309466866267)
                    ·
                      rfl

theorem cell23_2060530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2060530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060530 prefixEnd_2060530 := by exact prefixLift 2060530
  have htrace : WordTrace (prefixWord ++ tailWord_2060530) baseStart_2060530 baseEnd_2060530 := by
    simpa [prefixWord, tailWord_2060530, baseEnd_2060530] using wordTrace_append hprefix tailTrace_2060530
  have hstable : (prefixWord ++ tailWord_2060530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060530).length < 2 ^ (prefixWord ++ tailWord_2060530).sum := by decide
  have hdescent : baseEnd_2060530 < baseStart_2060530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060567 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2060567 : Nat := 118140960795 + 2060567 * 2 ^ 59
def prefixEnd_2060567 : Nat := 4983230072969 + 3 ^ 40 * 2060567 * 2
def baseEnd_2060567 : Nat := 1058061291793144755836131

theorem tailTrace_2060567 : CollatzResearch.WordTrace tailWord_2060567 prefixEnd_2060567 1058061291793144755836131 := by
  unfold tailWord_2060567
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155052725925150671179955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50103368483950100447453303 75155052725925150671179955)
  ·
    refine ⟨112732579088887726006769933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75155052725925150671179955 112732579088887726006769933)
    ·
      refine ⟨42274717158332897252538725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112732579088887726006769933 42274717158332897252538725)
      ·
        refine ⟨7926509467187418234851011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42274717158332897252538725 7926509467187418234851011)
        ·
          refine ⟨11889764200781127352276517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926509467187418234851011 11889764200781127352276517)
          ·
            refine ⟨2229330787646461378551847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11889764200781127352276517 2229330787646461378551847)
            ·
              refine ⟨3343996181469692067827771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229330787646461378551847 3343996181469692067827771)
              ·
                refine ⟨5015994272204538101741657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343996181469692067827771 5015994272204538101741657)
                ·
                  refine ⟨3761995704153403576306243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015994272204538101741657 3761995704153403576306243)
                  ·
                    refine ⟨5642993556230105364459365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761995704153403576306243 5642993556230105364459365)
                    ·
                      refine ⟨1058061291793144755836131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5642993556230105364459365 1058061291793144755836131)
                      ·
                        rfl

theorem cell23_2060567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2060567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060567 prefixEnd_2060567 := by exact prefixLift 2060567
  have htrace : WordTrace (prefixWord ++ tailWord_2060567) baseStart_2060567 baseEnd_2060567 := by
    simpa [prefixWord, tailWord_2060567, baseEnd_2060567] using wordTrace_append hprefix tailTrace_2060567
  have hstable : (prefixWord ++ tailWord_2060567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060567).length < 2 ^ (prefixWord ++ tailWord_2060567).sum := by decide
  have hdescent : baseEnd_2060567 < baseStart_2060567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060577 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2060577 : Nat := 118140960795 + 2060577 * 2 ^ 59
def prefixEnd_2060577 : Nat := 4983230072969 + 3 ^ 40 * 2060577 * 2
def baseEnd_2060577 : Nat := 352688808866563238903695

theorem tailTrace_2060577 : CollatzResearch.WordTrace tailWord_2060577 prefixEnd_2060577 352688808866563238903695 := by
  unfold tailWord_2060577
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155417455888922379043985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50103611637259281586029323 75155417455888922379043985)
  ·
    refine ⟨56366563091916691784282989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75155417455888922379043985 56366563091916691784282989)
    ·
      refine ⟨21137461159468759419106121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56366563091916691784282989 21137461159468759419106121)
      ·
        refine ⟨15853095869601569564329591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21137461159468759419106121 15853095869601569564329591)
        ·
          refine ⟨23779643804402354346494387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15853095869601569564329591 23779643804402354346494387)
          ·
            refine ⟨35669465706603531519741581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23779643804402354346494387 35669465706603531519741581)
            ·
              refine ⟨13376049639976324319903093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35669465706603531519741581 13376049639976324319903093)
              ·
                refine ⟨1254004653747780404990915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13376049639976324319903093 1254004653747780404990915)
                ·
                  refine ⟨1881006980621670607486373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254004653747780404990915 1881006980621670607486373)
                  ·
                    refine ⟨352688808866563238903695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881006980621670607486373 352688808866563238903695)
                    ·
                      rfl

theorem cell23_2060577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2060577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060577 prefixEnd_2060577 := by exact prefixLift 2060577
  have htrace : WordTrace (prefixWord ++ tailWord_2060577) baseStart_2060577 baseEnd_2060577 := by
    simpa [prefixWord, tailWord_2060577, baseEnd_2060577] using wordTrace_append hprefix tailTrace_2060577
  have hstable : (prefixWord ++ tailWord_2060577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060577).length < 2 ^ (prefixWord ++ tailWord_2060577).sum := by decide
  have hdescent : baseEnd_2060577 < baseStart_2060577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060633 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_2060633 : Nat := 118140960795 + 2060633 * 2 ^ 59
def prefixEnd_2060633 : Nat := 4983230072969 + 3 ^ 40 * 2060633 * 2
def baseEnd_2060633 : Nat := 352698393838780499203609

theorem tailTrace_2060633 : CollatzResearch.WordTrace tailWord_2060633 prefixEnd_2060633 352698393838780499203609 := by
  unfold tailWord_2060633
  simp only [CollatzResearch.WordTrace]
  refine ⟨75157459943686043943082553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50104973295790695962055035 75157459943686043943082553)
  ·
    refine ⟨56368094957764532957311915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75157459943686043943082553 56368094957764532957311915)
    ·
      refine ⟨84552142436646799435967873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56368094957764532957311915 84552142436646799435967873)
      ·
        refine ⟨63414106827485099576975905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84552142436646799435967873 63414106827485099576975905)
        ·
          refine ⟨47560580120613824682731929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63414106827485099576975905 47560580120613824682731929)
          ·
            refine ⟨35670435090460368512048947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47560580120613824682731929 35670435090460368512048947)
            ·
              refine ⟨53505652635690552768073421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35670435090460368512048947 53505652635690552768073421)
              ·
                refine ⟨20064619738383957288027533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53505652635690552768073421 20064619738383957288027533)
                ·
                  refine ⟨7524232401893983983010325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20064619738383957288027533 7524232401893983983010325)
                  ·
                    refine ⟨352698393838780499203609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7524232401893983983010325 352698393838780499203609)
                    ·
                      rfl

theorem cell23_2060633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_2060633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060633 prefixEnd_2060633 := by exact prefixLift 2060633
  have htrace : WordTrace (prefixWord ++ tailWord_2060633) baseStart_2060633 baseEnd_2060633 := by
    simpa [prefixWord, tailWord_2060633, baseEnd_2060633] using wordTrace_append hprefix tailTrace_2060633
  have hstable : (prefixWord ++ tailWord_2060633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060633).length < 2 ^ (prefixWord ++ tailWord_2060633).sum := by decide
  have hdescent : baseEnd_2060633 < baseStart_2060633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060667 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 2, 4]
def baseStart_2060667 : Nat := 118140960795 + 2060667 * 2 ^ 59
def prefixEnd_2060667 : Nat := 4983230072969 + 3 ^ 40 * 2060667 * 2
def baseEnd_2060667 : Nat := 352704213286198121528557

theorem tailTrace_2060667 : CollatzResearch.WordTrace tailWord_2060667 prefixEnd_2060667 352704213286198121528557 := by
  unfold tailWord_2060667
  simp only [CollatzResearch.WordTrace]
  refine ⟨75158700025562867749820255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50105800017041911833213503 75158700025562867749820255)
  ·
    refine ⟨112738050038344301624730383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75158700025562867749820255 112738050038344301624730383)
    ·
      refine ⟨169107075057516452437095575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112738050038344301624730383 169107075057516452437095575)
      ·
        refine ⟨253660612586274678655643363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169107075057516452437095575 253660612586274678655643363)
        ·
          refine ⟨380490918879412017983465045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253660612586274678655643363 380490918879412017983465045)
          ·
            refine ⟨4458877955618109585743731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 380490918879412017983465045 4458877955618109585743731)
            ·
              refine ⟨6688316933427164378615597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458877955618109585743731 6688316933427164378615597)
              ·
                refine ⟨2508118850035186641980849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6688316933427164378615597 2508118850035186641980849)
                ·
                  refine ⟨1881089137526389981485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508118850035186641980849 1881089137526389981485637)
                  ·
                    refine ⟨352704213286198121528557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881089137526389981485637 352704213286198121528557)
                    ·
                      rfl

theorem cell23_2060667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 4].length) (baseStart_2060667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060667 prefixEnd_2060667 := by exact prefixLift 2060667
  have htrace : WordTrace (prefixWord ++ tailWord_2060667) baseStart_2060667 baseEnd_2060667 := by
    simpa [prefixWord, tailWord_2060667, baseEnd_2060667] using wordTrace_append hprefix tailTrace_2060667
  have hstable : (prefixWord ++ tailWord_2060667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060667).length < 2 ^ (prefixWord ++ tailWord_2060667).sum := by decide
  have hdescent : baseEnd_2060667 < baseStart_2060667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060708 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_2060708 : Nat := 118140960795 + 2060708 * 2 ^ 59
def prefixEnd_2060708 : Nat := 4983230072969 + 3 ^ 40 * 2060708 * 2
def baseEnd_2060708 : Nat := 1058133692565428704172983

theorem tailTrace_2060708 : CollatzResearch.WordTrace tailWord_2060708 prefixEnd_2060708 1058133692565428704172983 := by
  unfold tailWord_2060708
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580097709207165876031389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50106796945609554501375185 37580097709207165876031389)
  ·
    refine ⟨14092536640952687203511771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37580097709207165876031389 14092536640952687203511771)
    ·
      refine ⟨21138804961429030805267657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092536640952687203511771 21138804961429030805267657)
      ·
        refine ⟨15854103721071773103950743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21138804961429030805267657 15854103721071773103950743)
        ·
          refine ⟨23781155581607659655926115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15854103721071773103950743 23781155581607659655926115)
          ·
            refine ⟨35671733372411489483889173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23781155581607659655926115 35671733372411489483889173)
            ·
              refine ⟨1672112501831788569557305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35671733372411489483889173 1672112501831788569557305)
              ·
                refine ⟨1254084376373841427167979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672112501831788569557305 1254084376373841427167979)
                ·
                  refine ⟨1881126564560762140751969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254084376373841427167979 1881126564560762140751969)
                  ·
                    refine ⟨1410844923420571605563977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881126564560762140751969 1410844923420571605563977)
                    ·
                      refine ⟨1058133692565428704172983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410844923420571605563977 1058133692565428704172983)
                      ·
                        rfl

theorem cell23_2060708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_2060708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060708 prefixEnd_2060708 := by exact prefixLift 2060708
  have htrace : WordTrace (prefixWord ++ tailWord_2060708) baseStart_2060708 baseEnd_2060708 := by
    simpa [prefixWord, tailWord_2060708, baseEnd_2060708] using wordTrace_append hprefix tailTrace_2060708
  have hstable : (prefixWord ++ tailWord_2060708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060708).length < 2 ^ (prefixWord ++ tailWord_2060708).sum := by decide
  have hdescent : baseEnd_2060708 < baseStart_2060708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060734 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_2060734 : Nat := 118140960795 + 2060734 * 2 ^ 59
def prefixEnd_2060734 : Nat := 4983230072969 + 3 ^ 40 * 2060734 * 2
def baseEnd_2060734 : Nat := 1058147043062445602447863

theorem tailTrace_2060734 : CollatzResearch.WordTrace tailWord_2060734 prefixEnd_2060734 1058147043062445602447863 := by
  unfold tailWord_2060734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395142964540017274063657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50107429144213425461672837 9395142964540017274063657)
  ·
    refine ⟨7046357223405012955547743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9395142964540017274063657 7046357223405012955547743)
    ·
      refine ⟨10569535835107519433321615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7046357223405012955547743 10569535835107519433321615)
      ·
        refine ⟨15854303752661279149982423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10569535835107519433321615 15854303752661279149982423)
        ·
          refine ⟨23781455628991918724973635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15854303752661279149982423 23781455628991918724973635)
          ·
            refine ⟨35672183443487878087460453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23781455628991918724973635 35672183443487878087460453)
            ·
              refine ⟨6688534395653977141398835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35672183443487878087460453 6688534395653977141398835)
              ·
                refine ⟨10032801593480965712098253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6688534395653977141398835 10032801593480965712098253)
                ·
                  refine ⟨3762300597555362142036845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10032801593480965712098253 3762300597555362142036845)
                  ·
                    refine ⟨1410862724083260803263817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3762300597555362142036845 1410862724083260803263817)
                    ·
                      refine ⟨1058147043062445602447863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410862724083260803263817 1058147043062445602447863)
                      ·
                        rfl

theorem cell23_2060734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_2060734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060734 prefixEnd_2060734 := by exact prefixLift 2060734
  have htrace : WordTrace (prefixWord ++ tailWord_2060734) baseStart_2060734 baseEnd_2060734 := by
    simpa [prefixWord, tailWord_2060734, baseEnd_2060734] using wordTrace_append hprefix tailTrace_2060734
  have hstable : (prefixWord ++ tailWord_2060734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060734).length < 2 ^ (prefixWord ++ tailWord_2060734).sum := by decide
  have hdescent : baseEnd_2060734 < baseStart_2060734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060750 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2060750 : Nat := 118140960795 + 2060750 * 2 ^ 59
def prefixEnd_2060750 : Nat := 4983230072969 + 3 ^ 40 * 2060750 * 2
def baseEnd_2060750 : Nat := 1058155258752917539847789

theorem tailTrace_2060750 : CollatzResearch.WordTrace tailWord_2060750 prefixEnd_2060750 1058155258752917539847789 := by
  unfold tailWord_2060750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395215910532771615636463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50107818189508115283394469 9395215910532771615636463)
  ·
    refine ⟨14092823865799157423454695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395215910532771615636463 14092823865799157423454695)
    ·
      refine ⟨21139235798698736135182043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092823865799157423454695 21139235798698736135182043)
      ·
        refine ⟨31708853698048104202773065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21139235798698736135182043 31708853698048104202773065)
        ·
          refine ⟨23781640273536078152079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31708853698048104202773065 23781640273536078152079799)
          ·
            refine ⟨35672460410304117228119699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23781640273536078152079799 35672460410304117228119699)
            ·
              refine ⟨53508690615456175842179549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35672460410304117228119699 53508690615456175842179549)
              ·
                refine ⟨20065758980796065940817331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53508690615456175842179549 20065758980796065940817331)
                ·
                  refine ⟨30098638471194098911225997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20065758980796065940817331 30098638471194098911225997)
                  ·
                    refine ⟨11286989426697787091709749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30098638471194098911225997 11286989426697787091709749)
                    ·
                      refine ⟨1058155258752917539847789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11286989426697787091709749 1058155258752917539847789)
                      ·
                        rfl

theorem cell23_2060750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2060750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060750 prefixEnd_2060750 := by exact prefixLift 2060750
  have htrace : WordTrace (prefixWord ++ tailWord_2060750) baseStart_2060750 baseEnd_2060750 := by
    simpa [prefixWord, tailWord_2060750, baseEnd_2060750] using wordTrace_append hprefix tailTrace_2060750
  have hstable : (prefixWord ++ tailWord_2060750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060750).length < 2 ^ (prefixWord ++ tailWord_2060750).sum := by decide
  have hdescent : baseEnd_2060750 < baseStart_2060750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060781 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2060781 : Nat := 118140960795 + 2060781 * 2 ^ 59
def prefixEnd_2060781 : Nat := 4983230072969 + 3 ^ 40 * 2060781 * 2
def baseEnd_2060781 : Nat := 1058171176653206918560147

theorem tailTrace_2060781 : CollatzResearch.WordTrace tailWord_2060781 prefixEnd_2060781 1058171176653206918560147 := by
  unfold tailWord_2060781
  simp only [CollatzResearch.WordTrace]
  refine ⟨75162857947149865219470197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50108571964766576812980131 75162857947149865219470197)
  ·
    refine ⟨7046517932545299864325331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75162857947149865219470197 7046517932545299864325331)
    ·
      refine ⟨10569776898817949796487997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7046517932545299864325331 10569776898817949796487997)
      ·
        refine ⟨3963666337056731173682999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10569776898817949796487997 3963666337056731173682999)
        ·
          refine ⟨5945499505585096760524499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963666337056731173682999 5945499505585096760524499)
          ·
            refine ⟨8918249258377645140786749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945499505585096760524499 8918249258377645140786749)
            ·
              refine ⟨3344343471891616927795031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8918249258377645140786749 3344343471891616927795031)
              ·
                refine ⟨5016515207837425391692547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344343471891616927795031 5016515207837425391692547)
                ·
                  refine ⟨7524772811756138087538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016515207837425391692547 7524772811756138087538821)
                  ·
                    refine ⟨1410894902204275891413529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524772811756138087538821 1410894902204275891413529)
                    ·
                      refine ⟨1058171176653206918560147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410894902204275891413529 1058171176653206918560147)
                      ·
                        rfl

theorem cell23_2060781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2060781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060781 prefixEnd_2060781 := by exact prefixLift 2060781
  have htrace : WordTrace (prefixWord ++ tailWord_2060781) baseStart_2060781 baseEnd_2060781 := by
    simpa [prefixWord, tailWord_2060781, baseEnd_2060781] using wordTrace_append hprefix tailTrace_2060781
  have hstable : (prefixWord ++ tailWord_2060781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060781).length < 2 ^ (prefixWord ++ tailWord_2060781).sum := by decide
  have hdescent : baseEnd_2060781 < baseStart_2060781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_2060800 : Nat := 118140960795 + 2060800 * 2 ^ 59
def prefixEnd_2060800 : Nat := 4983230072969 + 3 ^ 40 * 2060800 * 2
def baseEnd_2060800 : Nat := 352726977595214114740853

theorem tailTrace_2060800 : CollatzResearch.WordTrace tailWord_2060800 prefixEnd_2060800 352726977595214114740853 := by
  unfold tailWord_2060800
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581775467040515732205927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50109033956054020976274569 37581775467040515732205927)
  ·
    refine ⟨56372663200560773598308891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37581775467040515732205927 56372663200560773598308891)
    ·
      refine ⟨84558994800841160397463337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56372663200560773598308891 84558994800841160397463337)
      ·
        refine ⟨63419246100630870298097503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84558994800841160397463337 63419246100630870298097503)
        ·
          refine ⟨95128869150946305447146255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63419246100630870298097503 95128869150946305447146255)
          ·
            refine ⟨142693303726419458170719383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95128869150946305447146255 142693303726419458170719383)
            ·
              refine ⟨214039955589629187256079075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142693303726419458170719383 214039955589629187256079075)
              ·
                refine ⟨321059933384443780884118613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214039955589629187256079075 321059933384443780884118613)
                ·
                  refine ⟨3762421094348950557235765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 321059933384443780884118613 3762421094348950557235765)
                  ·
                    refine ⟨352726977595214114740853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3762421094348950557235765 352726977595214114740853)
                    ·
                      rfl

theorem cell23_2060800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_2060800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060800 prefixEnd_2060800 := by exact prefixLift 2060800
  have htrace : WordTrace (prefixWord ++ tailWord_2060800) baseStart_2060800 baseEnd_2060800 := by
    simpa [prefixWord, tailWord_2060800, baseEnd_2060800] using wordTrace_append hprefix tailTrace_2060800
  have hstable : (prefixWord ++ tailWord_2060800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060800).length < 2 ^ (prefixWord ++ tailWord_2060800).sum := by decide
  have hdescent : baseEnd_2060800 < baseStart_2060800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060832 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2060832 : Nat := 118140960795 + 2060832 * 2 ^ 59
def prefixEnd_2060832 : Nat := 4983230072969 + 3 ^ 40 * 2060832 * 2
def baseEnd_2060832 : Nat := 1058197364166586219022413

theorem tailTrace_2060832 : CollatzResearch.WordTrace tailWord_2060832 prefixEnd_2060832 1058197364166586219022413 := by
  unfold tailWord_2060832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37582359034982550464788375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50109812046643400619717833 37582359034982550464788375)
  ·
    refine ⟨56373538552473825697182563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37582359034982550464788375 56373538552473825697182563)
    ·
      refine ⟨84560307828710738545773845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56373538552473825697182563 84560307828710738545773845)
      ·
        refine ⟨3963764429470815869333149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84560307828710738545773845 3963764429470815869333149)
        ·
          refine ⟨1486411661051555950999931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3963764429470815869333149 1486411661051555950999931)
          ·
            refine ⟨2229617491577333926499897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486411661051555950999931 2229617491577333926499897)
            ·
              refine ⟨1672213118683000444874923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229617491577333926499897 1672213118683000444874923)
              ·
                refine ⟨2508319678024500667312385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672213118683000444874923 2508319678024500667312385)
                ·
                  refine ⟨1881239758518375500484289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508319678024500667312385 1881239758518375500484289)
                  ·
                    refine ⟨1410929818888781625363217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881239758518375500484289 1410929818888781625363217)
                    ·
                      refine ⟨1058197364166586219022413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1410929818888781625363217 1058197364166586219022413)
                      ·
                        rfl

theorem cell23_2060832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2060832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060832 prefixEnd_2060832 := by exact prefixLift 2060832
  have htrace : WordTrace (prefixWord ++ tailWord_2060832) baseStart_2060832 baseEnd_2060832 := by
    simpa [prefixWord, tailWord_2060832, baseEnd_2060832] using wordTrace_append hprefix tailTrace_2060832
  have hstable : (prefixWord ++ tailWord_2060832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060832).length < 2 ^ (prefixWord ++ tailWord_2060832).sum := by decide
  have hdescent : baseEnd_2060832 < baseStart_2060832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060874 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2060874 : Nat := 118140960795 + 2060874 * 2 ^ 59
def prefixEnd_2060874 : Nat := 4983230072969 + 3 ^ 40 * 2060874 * 2
def baseEnd_2060874 : Nat := 1058218930354075054697219

theorem tailTrace_2060874 : CollatzResearch.WordTrace tailWord_2060874 prefixEnd_2060874 1058218930354075054697219 := by
  unfold tailWord_2060874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18791562483953235525651419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50110833290541961401737117 18791562483953235525651419)
  ·
    refine ⟨28187343725929853288477129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18791562483953235525651419 28187343725929853288477129)
    ·
      refine ⟨21140507794447389966357847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28187343725929853288477129 21140507794447389966357847)
      ·
        refine ⟨31710761691671084949536771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21140507794447389966357847 31710761691671084949536771)
        ·
          refine ⟨47566142537506627424305157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710761691671084949536771 47566142537506627424305157)
          ·
            refine ⟨8918651725782492642057217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47566142537506627424305157 8918651725782492642057217)
            ·
              refine ⟨6688988794336869481542913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8918651725782492642057217 6688988794336869481542913)
              ·
                refine ⟨5016741595752652111157185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6688988794336869481542913 5016741595752652111157185)
                ·
                  refine ⟨3762556196814489083367889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016741595752652111157185 3762556196814489083367889)
                  ·
                    refine ⟨2821917147610866812525917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3762556196814489083367889 2821917147610866812525917)
                    ·
                      refine ⟨1058218930354075054697219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2821917147610866812525917 1058218930354075054697219)
                      ·
                        rfl

theorem cell23_2060874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2060874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060874 prefixEnd_2060874 := by exact prefixLift 2060874
  have htrace : WordTrace (prefixWord ++ tailWord_2060874) baseStart_2060874 baseEnd_2060874 := by
    simpa [prefixWord, tailWord_2060874, baseEnd_2060874] using wordTrace_append hprefix tailTrace_2060874
  have hstable : (prefixWord ++ tailWord_2060874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060874).length < 2 ^ (prefixWord ++ tailWord_2060874).sum := by decide
  have hdescent : baseEnd_2060874 < baseStart_2060874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060881 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2060881 : Nat := 118140960795 + 2060881 * 2 ^ 59
def prefixEnd_2060881 : Nat := 4983230072969 + 3 ^ 40 * 2060881 * 2
def baseEnd_2060881 : Nat := 352740841572885509103229

theorem tailTrace_2060881 : CollatzResearch.WordTrace tailWord_2060881 prefixEnd_2060881 352740841572885509103229 := by
  unfold tailWord_2060881
  simp only [CollatzResearch.WordTrace]
  refine ⟨75166505246787582298110497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50111003497858388198740331 75166505246787582298110497)
  ·
    refine ⟨56374878935090686723582873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75166505246787582298110497 56374878935090686723582873)
    ·
      refine ⟨42281159201318015042687155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56374878935090686723582873 42281159201318015042687155)
      ·
        refine ⟨63421738801977022564030733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42281159201318015042687155 63421738801977022564030733)
        ·
          refine ⟨23783152050741383461511525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63421738801977022564030733 23783152050741383461511525)
          ·
            refine ⟨4459341009514009399033411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23783152050741383461511525 4459341009514009399033411)
            ·
              refine ⟨6689011514271014098550117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459341009514009399033411 6689011514271014098550117)
              ·
                refine ⟨1254189658925815143478147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6689011514271014098550117 1254189658925815143478147)
                ·
                  refine ⟨1881284488388722715217221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254189658925815143478147 1881284488388722715217221)
                  ·
                    refine ⟨352740841572885509103229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881284488388722715217221 352740841572885509103229)
                    ·
                      rfl

theorem cell23_2060881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2060881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060881 prefixEnd_2060881 := by exact prefixLift 2060881
  have htrace : WordTrace (prefixWord ++ tailWord_2060881) baseStart_2060881 baseEnd_2060881 := by
    simpa [prefixWord, tailWord_2060881, baseEnd_2060881] using wordTrace_append hprefix tailTrace_2060881
  have hstable : (prefixWord ++ tailWord_2060881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060881).length < 2 ^ (prefixWord ++ tailWord_2060881).sum := by decide
  have hdescent : baseEnd_2060881 < baseStart_2060881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060898 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2060898 : Nat := 118140960795 + 2060898 * 2 ^ 59
def prefixEnd_2060898 : Nat := 4983230072969 + 3 ^ 40 * 2060898 * 2
def baseEnd_2060898 : Nat := 352743751296594320265703

theorem tailTrace_2060898 : CollatzResearch.WordTrace tailWord_2060898 prefixEnd_2060898 352743751296594320265703 := by
  unfold tailWord_2060898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18791781321931498550369837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50111416858483996134319565 18791781321931498550369837)
  ·
    refine ⟨7046917995724311956388689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18791781321931498550369837 7046917995724311956388689)
    ·
      refine ⟨5285188496793233967291517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046917995724311956388689 5285188496793233967291517)
      ·
        refine ⟨1981945686297462737734319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5285188496793233967291517 1981945686297462737734319)
        ·
          refine ⟨2972918529446194106601479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981945686297462737734319 2972918529446194106601479)
          ·
            refine ⟨4459377794169291159902219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972918529446194106601479 4459377794169291159902219)
            ·
              refine ⟨6689066691253936739853329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459377794169291159902219 6689066691253936739853329)
              ·
                refine ⟨5016800018440452554889997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689066691253936739853329 5016800018440452554889997)
                ·
                  refine ⟨1881300006915169708083749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5016800018440452554889997 1881300006915169708083749)
                  ·
                    refine ⟨352743751296594320265703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881300006915169708083749 352743751296594320265703)
                    ·
                      rfl

theorem cell23_2060898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2060898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060898 prefixEnd_2060898 := by exact prefixLift 2060898
  have htrace : WordTrace (prefixWord ++ tailWord_2060898) baseStart_2060898 baseEnd_2060898 := by
    simpa [prefixWord, tailWord_2060898, baseEnd_2060898] using wordTrace_append hprefix tailTrace_2060898
  have hstable : (prefixWord ++ tailWord_2060898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060898).length < 2 ^ (prefixWord ++ tailWord_2060898).sum := by decide
  have hdescent : baseEnd_2060898 < baseStart_2060898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060927 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_2060927 : Nat := 118140960795 + 2060927 * 2 ^ 59
def prefixEnd_2060927 : Nat := 4983230072969 + 3 ^ 40 * 2060927 * 2
def baseEnd_2060927 : Nat := 1058246144828763347334475

theorem tailTrace_2060927 : CollatzResearch.WordTrace tailWord_2060927 prefixEnd_2060927 1058246144828763347334475 := by
  unfold tailWord_2060927
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168183004620932154285035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50112122003080621436190023 75168183004620932154285035)
  ·
    refine ⟨112752274506931398231427553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75168183004620932154285035 112752274506931398231427553)
    ·
      refine ⟨84564205880198548673570665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112752274506931398231427553 84564205880198548673570665)
      ·
        refine ⟨63423154410148911505177999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84564205880198548673570665 63423154410148911505177999)
        ·
          refine ⟨95134731615223367257766999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63423154410148911505177999 95134731615223367257766999)
          ·
            refine ⟨142702097422835050886650499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95134731615223367257766999 142702097422835050886650499)
            ·
              refine ⟨214053146134252576329975749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142702097422835050886650499 214053146134252576329975749)
              ·
                refine ⟨40134964900172358061870453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214053146134252576329975749 40134964900172358061870453)
                ·
                  refine ⟨3762652959391158568300355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40134964900172358061870453 3762652959391158568300355)
                  ·
                    refine ⟨5643979439086737852450533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3762652959391158568300355 5643979439086737852450533)
                    ·
                      refine ⟨1058246144828763347334475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5643979439086737852450533 1058246144828763347334475)
                      ·
                        rfl

theorem cell23_2060927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_2060927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060927 prefixEnd_2060927 := by exact prefixLift 2060927
  have htrace : WordTrace (prefixWord ++ tailWord_2060927) baseStart_2060927 baseEnd_2060927 := by
    simpa [prefixWord, tailWord_2060927, baseEnd_2060927] using wordTrace_append hprefix tailTrace_2060927
  have hstable : (prefixWord ++ tailWord_2060927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060927).length < 2 ^ (prefixWord ++ tailWord_2060927).sum := by decide
  have hdescent : baseEnd_2060927 < baseStart_2060927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060938 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2060938 : Nat := 118140960795 + 2060938 * 2 ^ 59
def prefixEnd_2060938 : Nat := 4983230072969 + 3 ^ 40 * 2060938 * 2
def baseEnd_2060938 : Nat := 1058251793115962804296925

theorem tailTrace_2060938 : CollatzResearch.WordTrace tailWord_2060938 prefixEnd_2060938 1058251793115962804296925 := by
  unfold tailWord_2060938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792146051895270258233867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50112389471720720688623645 18792146051895270258233867)
  ·
    refine ⟨28188219077842905387350801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18792146051895270258233867 28188219077842905387350801)
    ·
      refine ⟨21141164308382179040513101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28188219077842905387350801 21141164308382179040513101)
      ·
        refine ⟨7927936615643317140192413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21141164308382179040513101 7927936615643317140192413)
        ·
          refine ⟨2972976230866243927572155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927936615643317140192413 2972976230866243927572155)
          ·
            refine ⟨4459464346299365891358233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972976230866243927572155 4459464346299365891358233)
            ·
              refine ⟨3344598259724524418518675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459464346299365891358233 3344598259724524418518675)
              ·
                refine ⟨5016897389586786627778013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344598259724524418518675 5016897389586786627778013)
                ·
                  refine ⟨1881336521095044985416755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5016897389586786627778013 1881336521095044985416755)
                  ·
                    refine ⟨2822004781642567478125133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881336521095044985416755 2822004781642567478125133)
                    ·
                      refine ⟨1058251793115962804296925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822004781642567478125133 1058251793115962804296925)
                      ·
                        rfl

theorem cell23_2060938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2060938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060938 prefixEnd_2060938 := by exact prefixLift 2060938
  have htrace : WordTrace (prefixWord ++ tailWord_2060938) baseStart_2060938 baseEnd_2060938 := by
    simpa [prefixWord, tailWord_2060938, baseEnd_2060938] using wordTrace_append hprefix tailTrace_2060938
  have hstable : (prefixWord ++ tailWord_2060938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060938).length < 2 ^ (prefixWord ++ tailWord_2060938).sum := by decide
  have hdescent : baseEnd_2060938 < baseStart_2060938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_2060947 : Nat := 118140960795 + 2060947 * 2 ^ 59
def prefixEnd_2060947 : Nat := 4983230072969 + 3 ^ 40 * 2060947 * 2
def baseEnd_2060947 : Nat := 1058256414441853269084383

theorem tailTrace_2060947 : CollatzResearch.WordTrace tailWord_2060947 prefixEnd_2060947 1058256414441853269084383 := by
  unfold tailWord_2060947
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168912464548475570013095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50112608309698983713342063 75168912464548475570013095)
  ·
    refine ⟨112753368696822713355019643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75168912464548475570013095 112753368696822713355019643)
    ·
      refine ⟨169130053045234070032529465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112753368696822713355019643 169130053045234070032529465)
      ·
        refine ⟨126847539783925552524397099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169130053045234070032529465 126847539783925552524397099)
        ·
          refine ⟨190271309675888328786595649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126847539783925552524397099 190271309675888328786595649)
          ·
            refine ⟨142703482256916246589946737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190271309675888328786595649 142703482256916246589946737)
            ·
              refine ⟨107027611692687184942460053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142703482256916246589946737 107027611692687184942460053)
              ·
                refine ⟨5016919298094711794177815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107027611692687184942460053 5016919298094711794177815)
                ·
                  refine ⟨7525378947142067691266723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016919298094711794177815 7525378947142067691266723)
                  ·
                    refine ⟨11288068420713101536900085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525378947142067691266723 11288068420713101536900085)
                    ·
                      refine ⟨1058256414441853269084383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11288068420713101536900085 1058256414441853269084383)
                      ·
                        rfl

theorem cell23_2060947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_2060947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060947 prefixEnd_2060947 := by exact prefixLift 2060947
  have htrace : WordTrace (prefixWord ++ tailWord_2060947) baseStart_2060947 baseEnd_2060947 := by
    simpa [prefixWord, tailWord_2060947, baseEnd_2060947] using wordTrace_append hprefix tailTrace_2060947
  have hstable : (prefixWord ++ tailWord_2060947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060947).length < 2 ^ (prefixWord ++ tailWord_2060947).sum := by decide
  have hdescent : baseEnd_2060947 < baseStart_2060947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060981 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2060981 : Nat := 118140960795 + 2060981 * 2 ^ 59
def prefixEnd_2060981 : Nat := 4983230072969 + 3 ^ 40 * 2060981 * 2
def baseEnd_2060981 : Nat := 1058273872784106136059227

theorem tailTrace_2060981 : CollatzResearch.WordTrace tailWord_2060981 prefixEnd_2060981 1058273872784106136059227 := by
  unfold tailWord_2060981
  simp only [CollatzResearch.WordTrace]
  refine ⟨75170152546425299376750797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50113435030950199584500531 75170152546425299376750797)
  ·
    refine ⟨28188807204909487266281549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75170152546425299376750797 28188807204909487266281549)
    ·
      refine ⟨10570802701841057724855581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28188807204909487266281549 10570802701841057724855581)
      ·
        refine ⟨3964051013190396646820843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10570802701841057724855581 3964051013190396646820843)
        ·
          refine ⟨5946076519785594970231265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964051013190396646820843 5946076519785594970231265)
          ·
            refine ⟨4459557389839196227673449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5946076519785594970231265 4459557389839196227673449)
            ·
              refine ⟨3344668042379397170755087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459557389839196227673449 3344668042379397170755087)
              ·
                refine ⟨5017002063569095756132631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344668042379397170755087 5017002063569095756132631)
                ·
                  refine ⟨7525503095353643634198947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017002063569095756132631 7525503095353643634198947)
                  ·
                    refine ⟨11288254643030465451298421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7525503095353643634198947 11288254643030465451298421)
                    ·
                      refine ⟨1058273872784106136059227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11288254643030465451298421 1058273872784106136059227)
                      ·
                        rfl

theorem cell23_2060981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2060981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2060981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2060981 prefixEnd_2060981 := by exact prefixLift 2060981
  have htrace : WordTrace (prefixWord ++ tailWord_2060981) baseStart_2060981 baseEnd_2060981 := by
    simpa [prefixWord, tailWord_2060981, baseEnd_2060981] using wordTrace_append hprefix tailTrace_2060981
  have hstable : (prefixWord ++ tailWord_2060981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060981).length < 2 ^ (prefixWord ++ tailWord_2060981).sum := by decide
  have hdescent : baseEnd_2060981 < baseStart_2060981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061005 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2061005 : Nat := 118140960795 + 2061005 * 2 ^ 59
def prefixEnd_2061005 : Nat := 4983230072969 + 3 ^ 40 * 2061005 * 2
def baseEnd_2061005 : Nat := 352762065439938014053039

theorem tailTrace_2061005 : CollatzResearch.WordTrace tailWord_2061005 prefixEnd_2061005 352762065439938014053039 := by
  unfold tailWord_2061005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75171027898338351475624469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50114018598892234317082979 75171027898338351475624469)
  ·
    refine ⟨3523641932734610225419897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75171027898338351475624469 3523641932734610225419897)
    ·
      refine ⟨2642731449550957669064923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3523641932734610225419897 2642731449550957669064923)
      ·
        refine ⟨3964097174326436503597385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642731449550957669064923 3964097174326436503597385)
        ·
          refine ⟨2973072880744827377698039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964097174326436503597385 2973072880744827377698039)
          ·
            refine ⟨4459609321117241066547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973072880744827377698039 4459609321117241066547059)
            ·
              refine ⟨6689413981675861599820589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459609321117241066547059 6689413981675861599820589)
              ·
                refine ⟨2508530243128448099932721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6689413981675861599820589 2508530243128448099932721)
                ·
                  refine ⟨1881397682346336074949541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508530243128448099932721 1881397682346336074949541)
                  ·
                    refine ⟨352762065439938014053039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881397682346336074949541 352762065439938014053039)
                    ·
                      rfl

theorem cell23_2061005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2061005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061005 prefixEnd_2061005 := by exact prefixLift 2061005
  have htrace : WordTrace (prefixWord ++ tailWord_2061005) baseStart_2061005 baseEnd_2061005 := by
    simpa [prefixWord, tailWord_2061005, baseEnd_2061005] using wordTrace_append hprefix tailTrace_2061005
  have hstable : (prefixWord ++ tailWord_2061005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061005).length < 2 ^ (prefixWord ++ tailWord_2061005).sum := by decide
  have hdescent : baseEnd_2061005 < baseStart_2061005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061047 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2061047 : Nat := 118140960795 + 2061047 * 2 ^ 59
def prefixEnd_2061047 : Nat := 4983230072969 + 3 ^ 40 * 2061047 * 2
def baseEnd_2061047 : Nat := 1058307762507302877833923

theorem tailTrace_2061047 : CollatzResearch.WordTrace tailWord_2061047 prefixEnd_2061047 1058307762507302877833923 := by
  unfold tailWord_2061047
  simp only [CollatzResearch.WordTrace]
  refine ⟨75172559764186192648653395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50115039842790795099102263 75172559764186192648653395)
  ·
    refine ⟨112758839646279288972980093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75172559764186192648653395 112758839646279288972980093)
    ·
      refine ⟨42284564867354733364867535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112758839646279288972980093 42284564867354733364867535)
      ·
        refine ⟨63426847301032100047301303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42284564867354733364867535 63426847301032100047301303)
        ·
          refine ⟨95140270951548150070951955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63426847301032100047301303 95140270951548150070951955)
          ·
            refine ⟨142710406427322225106427933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95140270951548150070951955 142710406427322225106427933)
            ·
              refine ⟨53516402410245834414910475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142710406427322225106427933 53516402410245834414910475)
              ·
                refine ⟨80274603615368751622365713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53516402410245834414910475 80274603615368751622365713)
                ·
                  refine ⟨60205952711526563716774285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80274603615368751622365713 60205952711526563716774285)
                  ·
                    refine ⟨22577232266822461393790357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60205952711526563716774285 22577232266822461393790357)
                    ·
                      refine ⟨1058307762507302877833923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22577232266822461393790357 1058307762507302877833923)
                      ·
                        rfl

theorem cell23_2061047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2061047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061047 prefixEnd_2061047 := by exact prefixLift 2061047
  have htrace : WordTrace (prefixWord ++ tailWord_2061047) baseStart_2061047 baseEnd_2061047 := by
    simpa [prefixWord, tailWord_2061047, baseEnd_2061047] using wordTrace_append hprefix tailTrace_2061047
  have hstable : (prefixWord ++ tailWord_2061047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061047).length < 2 ^ (prefixWord ++ tailWord_2061047).sum := by decide
  have hdescent : baseEnd_2061047 < baseStart_2061047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061051 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 8, 2, 2]
def baseStart_2061051 : Nat := 118140960795 + 2061051 * 2 ^ 59
def prefixEnd_2061051 : Nat := 4983230072969 + 3 ^ 40 * 2061051 * 2
def baseEnd_2061051 : Nat := 1058309816429920862183905

theorem tailTrace_2061051 : CollatzResearch.WordTrace tailWord_2061051 prefixEnd_2061051 1058309816429920862183905 := by
  unfold tailWord_2061051
  simp only [CollatzResearch.WordTrace]
  refine ⟨75172705656171701331799007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50115137104114467554532671 75172705656171701331799007)
  ·
    refine ⟨112759058484257551997698511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75172705656171701331799007 112759058484257551997698511)
    ·
      refine ⟨169138587726386327996547767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112759058484257551997698511 169138587726386327996547767)
      ·
        refine ⟨253707881589579491994821651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169138587726386327996547767 253707881589579491994821651)
        ·
          refine ⟨380561822384369237992232477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253707881589579491994821651 380561822384369237992232477)
          ·
            refine ⟨142710683394138464247087179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380561822384369237992232477 142710683394138464247087179)
            ·
              refine ⟨214066025091207696370630769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142710683394138464247087179 214066025091207696370630769)
              ·
                refine ⟨160549518818405772277973077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214066025091207696370630769 160549518818405772277973077)
                ·
                  refine ⟨1881439673653192643882497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 160549518818405772277973077 1881439673653192643882497)
                  ·
                    refine ⟨1411079755239894482911873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881439673653192643882497 1411079755239894482911873)
                    ·
                      refine ⟨1058309816429920862183905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411079755239894482911873 1058309816429920862183905)
                      ·
                        rfl

theorem cell23_2061051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2, 2].length) (baseStart_2061051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061051 prefixEnd_2061051 := by exact prefixLift 2061051
  have htrace : WordTrace (prefixWord ++ tailWord_2061051) baseStart_2061051 baseEnd_2061051 := by
    simpa [prefixWord, tailWord_2061051, baseEnd_2061051] using wordTrace_append hprefix tailTrace_2061051
  have hstable : (prefixWord ++ tailWord_2061051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061051).length < 2 ^ (prefixWord ++ tailWord_2061051).sum := by decide
  have hdescent : baseEnd_2061051 < baseStart_2061051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061064 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2061064 : Nat := 118140960795 + 2061064 * 2 ^ 59
def prefixEnd_2061064 : Nat := 4983230072969 + 3 ^ 40 * 2061064 * 2
def baseEnd_2061064 : Nat := 1058316491678429311321345

theorem tailTrace_2061064 : CollatzResearch.WordTrace tailWord_2061064 prefixEnd_2061064 1058316491678429311321345 := by
  unfold tailWord_2061064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37586589902562302276011123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50115453203416403034681497 37586589902562302276011123)
  ·
    refine ⟨56379884853843453414016685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37586589902562302276011123 56379884853843453414016685)
    ·
      refine ⟨21142456820191295030256257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56379884853843453414016685 21142456820191295030256257)
      ·
        refine ⟨15856842615143471272692193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21142456820191295030256257 15856842615143471272692193)
        ·
          refine ⟨11892631961357603454519145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15856842615143471272692193 11892631961357603454519145)
          ·
            refine ⟨8919473971018202590889359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11892631961357603454519145 8919473971018202590889359)
            ·
              refine ⟨13379210956527303886334039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919473971018202590889359 13379210956527303886334039)
              ·
                refine ⟨20068816434790955829501059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13379210956527303886334039 20068816434790955829501059)
                ·
                  refine ⟨30103224652186433744251589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20068816434790955829501059 30103224652186433744251589)
                  ·
                    refine ⟨5644354622284956327047173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30103224652186433744251589 5644354622284956327047173)
                    ·
                      refine ⟨1058316491678429311321345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5644354622284956327047173 1058316491678429311321345)
                      ·
                        rfl

theorem cell23_2061064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2061064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061064 prefixEnd_2061064 := by exact prefixLift 2061064
  have htrace : WordTrace (prefixWord ++ tailWord_2061064) baseStart_2061064 baseEnd_2061064 := by
    simpa [prefixWord, tailWord_2061064, baseEnd_2061064] using wordTrace_append hprefix tailTrace_2061064
  have hstable : (prefixWord ++ tailWord_2061064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061064).length < 2 ^ (prefixWord ++ tailWord_2061064).sum := by decide
  have hdescent : baseEnd_2061064 < baseStart_2061064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061102 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2061102 : Nat := 118140960795 + 2061102 * 2 ^ 59
def prefixEnd_2061102 : Nat := 4983230072969 + 3 ^ 40 * 2061102 * 2
def baseEnd_2061102 : Nat := 1058336003943300162646171

theorem tailTrace_2061102 : CollatzResearch.WordTrace tailWord_2061102 prefixEnd_2061102 1058336003943300162646171 := by
  unfold tailWord_2061102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9396820722373367130238195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50116377185991291361270373 9396820722373367130238195)
  ·
    refine ⟨14095231083560050695357293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9396820722373367130238195 14095231083560050695357293)
    ·
      refine ⟨5285711656335019010758985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14095231083560050695357293 5285711656335019010758985)
      ·
        refine ⟨3964283742251264258069239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5285711656335019010758985 3964283742251264258069239)
        ·
          refine ⟨5946425613376896387103859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964283742251264258069239 5946425613376896387103859)
          ·
            refine ⟨8919638420065344580655789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946425613376896387103859 8919638420065344580655789)
            ·
              refine ⟨3344864407524504217745921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8919638420065344580655789 3344864407524504217745921)
              ·
                refine ⟨2508648305643378163309441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344864407524504217745921 2508648305643378163309441)
                ·
                  refine ⟨1881486229232533622482081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508648305643378163309441 1881486229232533622482081)
                  ·
                    refine ⟨1411114671924400216861561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881486229232533622482081 1411114671924400216861561)
                    ·
                      refine ⟨1058336003943300162646171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411114671924400216861561 1058336003943300162646171)
                      ·
                        rfl

theorem cell23_2061102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2061102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061102 prefixEnd_2061102 := by exact prefixLift 2061102
  have htrace : WordTrace (prefixWord ++ tailWord_2061102) baseStart_2061102 baseEnd_2061102 := by
    simpa [prefixWord, tailWord_2061102, baseEnd_2061102] using wordTrace_append hprefix tailTrace_2061102
  have hstable : (prefixWord ++ tailWord_2061102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061102).length < 2 ^ (prefixWord ++ tailWord_2061102).sum := by decide
  have hdescent : baseEnd_2061102 < baseStart_2061102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061104 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_2061104 : Nat := 118140960795 + 2061104 * 2 ^ 59
def prefixEnd_2061104 : Nat := 4983230072969 + 3 ^ 40 * 2061104 * 2
def baseEnd_2061104 : Nat := 352779010301536384940387

theorem tailTrace_2061104 : CollatzResearch.WordTrace tailWord_2061104 prefixEnd_2061104 352779010301536384940387 := by
  unfold tailWord_2061104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587319362489845691739183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50116425816653127588985577 37587319362489845691739183)
  ·
    refine ⟨56380979043734768537608775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37587319362489845691739183 56380979043734768537608775)
    ·
      refine ⟨84571468565602152806413163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56380979043734768537608775 84571468565602152806413163)
      ·
        refine ⟨126857202848403229209619745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84571468565602152806413163 126857202848403229209619745)
        ·
          refine ⟨95142902136302421907214809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126857202848403229209619745 95142902136302421907214809)
          ·
            refine ⟨71357176602226816430411107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95142902136302421907214809 71357176602226816430411107)
            ·
              refine ⟨107035764903340224645616661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71357176602226816430411107 107035764903340224645616661)
              ·
                refine ⟨5017301479844073030263281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107035764903340224645616661 5017301479844073030263281)
                ·
                  refine ⟨3762976109883054772697461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017301479844073030263281 3762976109883054772697461)
                  ·
                    refine ⟨352779010301536384940387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3762976109883054772697461 352779010301536384940387)
                    ·
                      rfl

theorem cell23_2061104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_2061104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061104 prefixEnd_2061104 := by exact prefixLift 2061104
  have htrace : WordTrace (prefixWord ++ tailWord_2061104) baseStart_2061104 baseEnd_2061104 := by
    simpa [prefixWord, tailWord_2061104, baseEnd_2061104] using wordTrace_append hprefix tailTrace_2061104
  have hstable : (prefixWord ++ tailWord_2061104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061104).length < 2 ^ (prefixWord ++ tailWord_2061104).sum := by decide
  have hdescent : baseEnd_2061104 < baseStart_2061104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061108 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2061108 : Nat := 118140960795 + 2061108 * 2 ^ 59
def prefixEnd_2061108 : Nat := 4983230072969 + 3 ^ 40 * 2061108 * 2
def baseEnd_2061108 : Nat := 117593231647469682130127

theorem tailTrace_2061108 : CollatzResearch.WordTrace tailWord_2061108 prefixEnd_2061108 117593231647469682130127 := by
  unfold tailWord_2061108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587392308482600033311989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50116523077976800044415985 37587392308482600033311989)
  ·
    refine ⟨3523818028920243753122999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37587392308482600033311989 3523818028920243753122999)
    ·
      refine ⟨5285727043380365629684499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523818028920243753122999 5285727043380365629684499)
      ·
        refine ⟨7928590565070548444526749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285727043380365629684499 7928590565070548444526749)
        ·
          refine ⟨2973221461901455666697531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7928590565070548444526749 2973221461901455666697531)
          ·
            refine ⟨4459832192852183500046297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973221461901455666697531 4459832192852183500046297)
            ·
              refine ⟨3344874144639137625034723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459832192852183500046297 3344874144639137625034723)
              ·
                refine ⟨5017311216958706437552085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344874144639137625034723 5017311216958706437552085)
                ·
                  refine ⟨117593231647469682130127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5017311216958706437552085 117593231647469682130127)
                  ·
                    rfl

theorem cell23_2061108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2061108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061108 prefixEnd_2061108 := by exact prefixLift 2061108
  have htrace : WordTrace (prefixWord ++ tailWord_2061108) baseStart_2061108 baseEnd_2061108 := by
    simpa [prefixWord, tailWord_2061108, baseEnd_2061108] using wordTrace_append hprefix tailTrace_2061108
  have hstable : (prefixWord ++ tailWord_2061108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061108).length < 2 ^ (prefixWord ++ tailWord_2061108).sum := by decide
  have hdescent : baseEnd_2061108 < baseStart_2061108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061141 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2061141 : Nat := 118140960795 + 2061141 * 2 ^ 59
def prefixEnd_2061141 : Nat := 4983230072969 + 3 ^ 40 * 2061141 * 2
def baseEnd_2061141 : Nat := 1058356029688825510058491

theorem tailTrace_2061141 : CollatzResearch.WordTrace tailWord_2061141 prefixEnd_2061141 1058356029688825510058491 := by
  unfold tailWord_2061141
  simp only [CollatzResearch.WordTrace]
  refine ⟨75175988225845646702575277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50117325483897097801716851 75175988225845646702575277)
  ·
    refine ⟨28190995584692117513465729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75175988225845646702575277 28190995584692117513465729)
    ·
      refine ⟨21143246688519088135099297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28190995584692117513465729 21143246688519088135099297)
      ·
        refine ⟨15857435016389316101324473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21143246688519088135099297 15857435016389316101324473)
        ·
          refine ⟨11893076262291987075993355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15857435016389316101324473 11893076262291987075993355)
          ·
            refine ⟨17839614393437980613990033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893076262291987075993355 17839614393437980613990033)
            ·
              refine ⟨13379710795078485460492525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17839614393437980613990033 13379710795078485460492525)
              ·
                refine ⟨5017391548154432047684697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13379710795078485460492525 5017391548154432047684697)
                ·
                  refine ⟨3763043661115824035763523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017391548154432047684697 3763043661115824035763523)
                  ·
                    refine ⟨5644565491673736053645285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3763043661115824035763523 5644565491673736053645285)
                    ·
                      refine ⟨1058356029688825510058491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5644565491673736053645285 1058356029688825510058491)
                      ·
                        rfl

theorem cell23_2061141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2061141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061141 prefixEnd_2061141 := by exact prefixLift 2061141
  have htrace : WordTrace (prefixWord ++ tailWord_2061141) baseStart_2061141 baseEnd_2061141 := by
    simpa [prefixWord, tailWord_2061141, baseEnd_2061141] using wordTrace_append hprefix tailTrace_2061141
  have hstable : (prefixWord ++ tailWord_2061141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061141).length < 2 ^ (prefixWord ++ tailWord_2061141).sum := by decide
  have hdescent : baseEnd_2061141 < baseStart_2061141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061164 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 8]
def baseStart_2061164 : Nat := 118140960795 + 2061164 * 2 ^ 59
def prefixEnd_2061164 : Nat := 4983230072969 + 3 ^ 40 * 2061164 * 2
def baseEnd_2061164 : Nat := 117596426638208768896765

theorem tailTrace_2061164 : CollatzResearch.WordTrace tailWord_2061164 prefixEnd_2061164 117596426638208768896765 := by
  unfold tailWord_2061164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588413552381160815331273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50117884736508214420441697 37588413552381160815331273)
  ·
    refine ⟨28191310164285870611498455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37588413552381160815331273 28191310164285870611498455)
    ·
      refine ⟨42286965246428805917247683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28191310164285870611498455 42286965246428805917247683)
      ·
        refine ⟨63430447869643208875871525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42286965246428805917247683 63430447869643208875871525)
        ·
          refine ⟨11893208975558101664225911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63430447869643208875871525 11893208975558101664225911)
          ·
            refine ⟨17839813463337152496338867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11893208975558101664225911 17839813463337152496338867)
            ·
              refine ⟨26759720195005728744508301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17839813463337152496338867 26759720195005728744508301)
              ·
                refine ⟨10034895073127148279190613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26759720195005728744508301 10034895073127148279190613)
                ·
                  refine ⟨117596426638208768896765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10034895073127148279190613 117596426638208768896765)
                  ·
                    rfl

theorem cell23_2061164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_2061164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061164 prefixEnd_2061164 := by exact prefixLift 2061164
  have htrace : WordTrace (prefixWord ++ tailWord_2061164) baseStart_2061164 baseEnd_2061164 := by
    simpa [prefixWord, tailWord_2061164, baseEnd_2061164] using wordTrace_append hprefix tailTrace_2061164
  have hstable : (prefixWord ++ tailWord_2061164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061164).length < 2 ^ (prefixWord ++ tailWord_2061164).sum := by decide
  have hdescent : baseEnd_2061164 < baseStart_2061164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061168 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 1, 4]
def baseStart_2061168 : Nat := 118140960795 + 2061168 * 2 ^ 59
def prefixEnd_2061168 : Nat := 4983230072969 + 3 ^ 40 * 2061168 * 2
def baseEnd_2061168 : Nat := 352789964555498968140289

theorem tailTrace_2061168 : CollatzResearch.WordTrace tailWord_2061168 prefixEnd_2061168 352789964555498968140289 := by
  unfold tailWord_2061168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588486498373915156904079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50117981997831886875872105 37588486498373915156904079)
  ·
    refine ⟨56382729747560872735356119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37588486498373915156904079 56382729747560872735356119)
    ·
      refine ⟨84574094621341309103034179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56382729747560872735356119 84574094621341309103034179)
      ·
        refine ⟨126861141932011963654551269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84574094621341309103034179 126861141932011963654551269)
        ·
          refine ⟨23786464112252243185228363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126861141932011963654551269 23786464112252243185228363)
          ·
            refine ⟨35679696168378364777842545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23786464112252243185228363 35679696168378364777842545)
            ·
              refine ⟨26759772126283773583381909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35679696168378364777842545 26759772126283773583381909)
              ·
                refine ⟨1254364318419551886721027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26759772126283773583381909 1254364318419551886721027)
                ·
                  refine ⟨1881546477629327830081541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254364318419551886721027 1881546477629327830081541)
                  ·
                    refine ⟨352789964555498968140289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881546477629327830081541 352789964555498968140289)
                    ·
                      rfl

theorem cell23_2061168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_2061168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061168 prefixEnd_2061168 := by exact prefixLift 2061168
  have htrace : WordTrace (prefixWord ++ tailWord_2061168) baseStart_2061168 baseEnd_2061168 := by
    simpa [prefixWord, tailWord_2061168, baseEnd_2061168] using wordTrace_append hprefix tailTrace_2061168
  have hstable : (prefixWord ++ tailWord_2061168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061168).length < 2 ^ (prefixWord ++ tailWord_2061168).sum := by decide
  have hdescent : baseEnd_2061168 < baseStart_2061168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061225 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 1, 1, 3]
def baseStart_2061225 : Nat := 118140960795 + 2061225 * 2 ^ 59
def prefixEnd_2061225 : Nat := 4983230072969 + 3 ^ 40 * 2061225 * 2
def baseEnd_2061225 : Nat := 1058399162063803181408105

theorem tailTrace_2061225 : CollatzResearch.WordTrace tailWord_2061225 prefixEnd_2061225 1058399162063803181408105 := by
  unfold tailWord_2061225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75179051957541329048633129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50119367971694219365755419 75179051957541329048633129)
  ·
    refine ⟨56384288968155996786474847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75179051957541329048633129 56384288968155996786474847)
    ·
      refine ⟨84576433452233995179712271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56384288968155996786474847 84576433452233995179712271)
      ·
        refine ⟨126864650178350992769568407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84576433452233995179712271 126864650178350992769568407)
        ·
          refine ⟨190296975267526489154352611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126864650178350992769568407 190296975267526489154352611)
          ·
            refine ⟨285445462901289733731528917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190296975267526489154352611 285445462901289733731528917)
            ·
              refine ⟨6690128036748978134332709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285445462901289733731528917 6690128036748978134332709)
              ·
                refine ⟨1254399006890433400187383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6690128036748978134332709 1254399006890433400187383)
                ·
                  refine ⟨1881598510335650100281075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254399006890433400187383 1881598510335650100281075)
                  ·
                    refine ⟨2822397765503475150421613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881598510335650100281075 2822397765503475150421613)
                    ·
                      refine ⟨1058399162063803181408105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822397765503475150421613 1058399162063803181408105)
                      ·
                        rfl

theorem cell23_2061225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 1, 3].length) (baseStart_2061225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061225 prefixEnd_2061225 := by exact prefixLift 2061225
  have htrace : WordTrace (prefixWord ++ tailWord_2061225) baseStart_2061225 baseEnd_2061225 := by
    simpa [prefixWord, tailWord_2061225, baseEnd_2061225] using wordTrace_append hprefix tailTrace_2061225
  have hstable : (prefixWord ++ tailWord_2061225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061225).length < 2 ^ (prefixWord ++ tailWord_2061225).sum := by decide
  have hdescent : baseEnd_2061225 < baseStart_2061225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061241 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_2061241 : Nat := 118140960795 + 2061241 * 2 ^ 59
def prefixEnd_2061241 : Nat := 4983230072969 + 3 ^ 40 * 2061241 * 2
def baseEnd_2061241 : Nat := 352802459251425039602677

theorem tailTrace_2061241 : CollatzResearch.WordTrace tailWord_2061241 prefixEnd_2061241 352802459251425039602677 := by
  unfold tailWord_2061241
  simp only [CollatzResearch.WordTrace]
  refine ⟨75179635525483363781215577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50119757016988909187477051 75179635525483363781215577)
  ·
    refine ⟨56384726644112522835911683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75179635525483363781215577 56384726644112522835911683)
    ·
      refine ⟨84577089966168784253867525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56384726644112522835911683 84577089966168784253867525)
      ·
        refine ⟨15858204368656647047600161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84577089966168784253867525 15858204368656647047600161)
        ·
          refine ⟨11893653276492485285700121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15858204368656647047600161 11893653276492485285700121)
          ·
            refine ⟨8920239957369363964275091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11893653276492485285700121 8920239957369363964275091)
            ·
              refine ⟨13380359936054045946412637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920239957369363964275091 13380359936054045946412637)
              ·
                refine ⟨5017634976020267229904739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13380359936054045946412637 5017634976020267229904739)
                ·
                  refine ⟨7526452464030400844857109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017634976020267229904739 7526452464030400844857109)
                  ·
                    refine ⟨352802459251425039602677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7526452464030400844857109 352802459251425039602677)
                    ·
                      rfl

theorem cell23_2061241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_2061241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061241 prefixEnd_2061241 := by exact prefixLift 2061241
  have htrace : WordTrace (prefixWord ++ tailWord_2061241) baseStart_2061241 baseEnd_2061241 := by
    simpa [prefixWord, tailWord_2061241, baseEnd_2061241] using wordTrace_append hprefix tailTrace_2061241
  have hstable : (prefixWord ++ tailWord_2061241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061241).length < 2 ^ (prefixWord ++ tailWord_2061241).sum := by decide
  have hdescent : baseEnd_2061241 < baseStart_2061241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061252 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2061252 : Nat := 118140960795 + 2061252 * 2 ^ 59
def prefixEnd_2061252 : Nat := 4983230072969 + 3 ^ 40 * 2061252 * 2
def baseEnd_2061252 : Nat := 1058413026041474575770481

theorem tailTrace_2061252 : CollatzResearch.WordTrace tailWord_2061252 prefixEnd_2061252 1058413026041474575770481 := by
  unfold tailWord_2061252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37590018364221756329933005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50120024485629008439910673 37590018364221756329933005)
  ·
    refine ⟨14096256886583158623724877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37590018364221756329933005 14096256886583158623724877)
    ·
      refine ⟨5286096332468684483896829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14096256886583158623724877 5286096332468684483896829)
      ·
        refine ⟨1982286124675756681461311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5286096332468684483896829 1982286124675756681461311)
        ·
          refine ⟨2973429187013635022191967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982286124675756681461311 2973429187013635022191967)
          ·
            refine ⟨4460143780520452533287951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973429187013635022191967 4460143780520452533287951)
            ·
              refine ⟨6690215670780678799931927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460143780520452533287951 6690215670780678799931927)
              ·
                refine ⟨10035323506171018199897891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690215670780678799931927 10035323506171018199897891)
                ·
                  refine ⟨15052985259256527299846837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10035323506171018199897891 15052985259256527299846837)
                  ·
                    refine ⟨1411217368055299434360641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15052985259256527299846837 1411217368055299434360641)
                    ·
                      refine ⟨1058413026041474575770481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411217368055299434360641 1058413026041474575770481)
                      ·
                        rfl

theorem cell23_2061252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2061252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061252 prefixEnd_2061252 := by exact prefixLift 2061252
  have htrace : WordTrace (prefixWord ++ tailWord_2061252) baseStart_2061252 baseEnd_2061252 := by
    simpa [prefixWord, tailWord_2061252, baseEnd_2061252] using wordTrace_append hprefix tailTrace_2061252
  have hstable : (prefixWord ++ tailWord_2061252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061252).length < 2 ^ (prefixWord ++ tailWord_2061252).sum := by decide
  have hdescent : baseEnd_2061252 < baseStart_2061252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061285 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2061285 : Nat := 118140960795 + 2061285 * 2 ^ 59
def prefixEnd_2061285 : Nat := 4983230072969 + 3 ^ 40 * 2061285 * 2
def baseEnd_2061285 : Nat := 1058429970903072946657829

theorem tailTrace_2061285 : CollatzResearch.WordTrace tailWord_2061285 prefixEnd_2061285 1058429970903072946657829 := by
  unfold tailWord_2061285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75181240337323959295817309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50120826891549306197211539 75181240337323959295817309)
  ·
    refine ⟨28192965126496484735931491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75181240337323959295817309 28192965126496484735931491)
    ·
      refine ⟨42289447689744727103897237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28192965126496484735931491 42289447689744727103897237)
      ·
        refine ⟨1982317860456784082995183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42289447689744727103897237 1982317860456784082995183)
        ·
          refine ⟨2973476790685176124492775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982317860456784082995183 2973476790685176124492775)
          ·
            refine ⟨4460215186027764186739163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973476790685176124492775 4460215186027764186739163)
            ·
              refine ⟨6690322779041646280108745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460215186027764186739163 6690322779041646280108745)
              ·
                refine ⟨5017742084281234710081559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6690322779041646280108745 5017742084281234710081559)
                ·
                  refine ⟨7526613126421852065122339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017742084281234710081559 7526613126421852065122339)
                  ·
                    refine ⟨11289919689632778097683509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526613126421852065122339 11289919689632778097683509)
                    ·
                      refine ⟨1058429970903072946657829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11289919689632778097683509 1058429970903072946657829)
                      ·
                        rfl

theorem cell23_2061285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2061285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061285 prefixEnd_2061285 := by exact prefixLift 2061285
  have htrace : WordTrace (prefixWord ++ tailWord_2061285) baseStart_2061285 baseEnd_2061285 := by
    simpa [prefixWord, tailWord_2061285, baseEnd_2061285] using wordTrace_append hprefix tailTrace_2061285
  have hstable : (prefixWord ++ tailWord_2061285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061285).length < 2 ^ (prefixWord ++ tailWord_2061285).sum := by decide
  have hdescent : baseEnd_2061285 < baseStart_2061285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061302 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2061302 : Nat := 118140960795 + 2061302 * 2 ^ 59
def prefixEnd_2061302 : Nat := 4983230072969 + 3 ^ 40 * 2061302 * 2
def baseEnd_2061302 : Nat := 1058438700074199380145251

theorem tailTrace_2061302 : CollatzResearch.WordTrace tailWord_2061302 prefixEnd_2061302 1058438700074199380145251 := by
  unfold tailWord_2061302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698866273641398199949135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50121240252174914132790773 4698866273641398199949135)
  ·
    refine ⟨7048299410462097299923703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698866273641398199949135 7048299410462097299923703)
    ·
      refine ⟨10572449115693145949885555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048299410462097299923703 10572449115693145949885555)
      ·
        refine ⟨15858673673539718924828333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572449115693145949885555 15858673673539718924828333)
        ·
          refine ⟨5947002627577394596810625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15858673673539718924828333 5947002627577394596810625)
          ·
            refine ⟨4460251970683045947607969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947002627577394596810625 4460251970683045947607969)
            ·
              refine ⟨3345188978012284460705977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460251970683045947607969 3345188978012284460705977)
              ·
                refine ⟨2508891733509213345529483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345188978012284460705977 2508891733509213345529483)
                ·
                  refine ⟨3763337600263820018294225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508891733509213345529483 3763337600263820018294225)
                  ·
                    refine ⟨2822503200197865013720669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763337600263820018294225 2822503200197865013720669)
                    ·
                      refine ⟨1058438700074199380145251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822503200197865013720669 1058438700074199380145251)
                      ·
                        rfl

theorem cell23_2061302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2061302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061302 prefixEnd_2061302 := by exact prefixLift 2061302
  have htrace : WordTrace (prefixWord ++ tailWord_2061302) baseStart_2061302 baseEnd_2061302 := by
    simpa [prefixWord, tailWord_2061302, baseEnd_2061302] using wordTrace_append hprefix tailTrace_2061302
  have hstable : (prefixWord ++ tailWord_2061302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061302).length < 2 ^ (prefixWord ++ tailWord_2061302).sum := by decide
  have hdescent : baseEnd_2061302 < baseStart_2061302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061358 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2061358 : Nat := 118140960795 + 2061358 * 2 ^ 59
def prefixEnd_2061358 : Nat := 4983230072969 + 3 ^ 40 * 2061358 * 2
def baseEnd_2061358 : Nat := 1058467454990851161044993

theorem tailTrace_2061358 : CollatzResearch.WordTrace tailWord_2061358 prefixEnd_2061358 1058467454990851161044993 := by
  unfold tailWord_2061358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397987858257436595403091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50122601910706328508816485 9397987858257436595403091)
  ·
    refine ⟨14096981787386154893104637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9397987858257436595403091 14096981787386154893104637)
    ·
      refine ⟨5286368170269808084914239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14096981787386154893104637 5286368170269808084914239)
      ·
        refine ⟨7929552255404712127371359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286368170269808084914239 7929552255404712127371359)
        ·
          refine ⟨11894328383107068191057039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929552255404712127371359 11894328383107068191057039)
          ·
            refine ⟨17841492574660602286585559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894328383107068191057039 17841492574660602286585559)
            ·
              refine ⟨26762238861990903429878339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17841492574660602286585559 26762238861990903429878339)
              ·
                refine ⟨40143358292986355144817509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26762238861990903429878339 40143358292986355144817509)
                ·
                  refine ⟨7526879679934941589653283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40143358292986355144817509 7526879679934941589653283)
                  ·
                    refine ⟨11290319519902412384479925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526879679934941589653283 11290319519902412384479925)
                    ·
                      refine ⟨1058467454990851161044993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11290319519902412384479925 1058467454990851161044993)
                      ·
                        rfl

theorem cell23_2061358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2061358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061358 prefixEnd_2061358 := by exact prefixLift 2061358
  have htrace : WordTrace (prefixWord ++ tailWord_2061358) baseStart_2061358 baseEnd_2061358 := by
    simpa [prefixWord, tailWord_2061358, baseEnd_2061358] using wordTrace_append hprefix tailTrace_2061358
  have hstable : (prefixWord ++ tailWord_2061358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061358).length < 2 ^ (prefixWord ++ tailWord_2061358).sum := by decide
  have hdescent : baseEnd_2061358 < baseStart_2061358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061361 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 9]
def baseStart_2061361 : Nat := 118140960795 + 2061361 * 2 ^ 59
def prefixEnd_2061361 : Nat := 4983230072969 + 3 ^ 40 * 2061361 * 2
def baseEnd_2061361 : Nat := 117607666159201627700831

theorem tailTrace_2061361 : CollatzResearch.WordTrace tailWord_2061361 prefixEnd_2061361 117607666159201627700831 := by
  unfold tailWord_2061361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75184012285048624275583937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50122674856699082850389291 75184012285048624275583937)
  ·
    refine ⟨56388009213786468206687953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75184012285048624275583937 56388009213786468206687953)
    ·
      refine ⟨42291006910339851155015965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56388009213786468206687953 42291006910339851155015965)
      ·
        refine ⟨15859127591377444183130987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42291006910339851155015965 15859127591377444183130987)
        ·
          refine ⟨23788691387066166274696481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859127591377444183130987 23788691387066166274696481)
          ·
            refine ⟨17841518540299624706022361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23788691387066166274696481 17841518540299624706022361)
            ·
              refine ⟨13381138905224718529516771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841518540299624706022361 13381138905224718529516771)
              ·
                refine ⟨20071708357837077794275157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381138905224718529516771 20071708357837077794275157)
                ·
                  refine ⟨117607666159201627700831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20071708357837077794275157 117607666159201627700831)
                  ·
                    rfl

theorem cell23_2061361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_2061361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061361 prefixEnd_2061361 := by exact prefixLift 2061361
  have htrace : WordTrace (prefixWord ++ tailWord_2061361) baseStart_2061361 baseEnd_2061361 := by
    simpa [prefixWord, tailWord_2061361, baseEnd_2061361] using wordTrace_append hprefix tailTrace_2061361
  have hstable : (prefixWord ++ tailWord_2061361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061361).length < 2 ^ (prefixWord ++ tailWord_2061361).sum := by decide
  have hdescent : baseEnd_2061361 < baseStart_2061361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061388 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2061388 : Nat := 118140960795 + 2061388 * 2 ^ 59
def prefixEnd_2061388 : Nat := 4983230072969 + 3 ^ 40 * 2061388 * 2
def baseEnd_2061388 : Nat := 1058482859410486043669855

theorem tailTrace_2061388 : CollatzResearch.WordTrace tailWord_2061388 prefixEnd_2061388 1058482859410486043669855 := by
  unfold tailWord_2061388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37592498527975403943408409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50123331370633871924544545 37592498527975403943408409)
  ·
    refine ⟨28194373895981552957556307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37592498527975403943408409 28194373895981552957556307)
    ·
      refine ⟨42291560843972329436334461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28194373895981552957556307 42291560843972329436334461)
      ·
        refine ⟨15859335316489623538625423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42291560843972329436334461 15859335316489623538625423)
        ·
          refine ⟨23789002974734435307938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859335316489623538625423 23789002974734435307938135)
          ·
            refine ⟨35683504462101652961907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23789002974734435307938135 35683504462101652961907203)
            ·
              refine ⟨53525256693152479442860805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35683504462101652961907203 53525256693152479442860805)
              ·
                refine ⟨10035985629966089895536401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53525256693152479442860805 10035985629966089895536401)
                ·
                  refine ⟨7526989222474567421652301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035985629966089895536401 7526989222474567421652301)
                  ·
                    refine ⟨2822620958427962783119613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7526989222474567421652301 2822620958427962783119613)
                    ·
                      refine ⟨1058482859410486043669855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822620958427962783119613 1058482859410486043669855)
                      ·
                        rfl

theorem cell23_2061388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2061388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061388 prefixEnd_2061388 := by exact prefixLift 2061388
  have htrace : WordTrace (prefixWord ++ tailWord_2061388) baseStart_2061388 baseEnd_2061388 := by
    simpa [prefixWord, tailWord_2061388, baseEnd_2061388] using wordTrace_append hprefix tailTrace_2061388
  have hstable : (prefixWord ++ tailWord_2061388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061388).length < 2 ^ (prefixWord ++ tailWord_2061388).sum := by decide
  have hdescent : baseEnd_2061388 < baseStart_2061388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061389 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2061389 : Nat := 118140960795 + 2061389 * 2 ^ 59
def prefixEnd_2061389 : Nat := 4983230072969 + 3 ^ 40 * 2061389 * 2
def baseEnd_2061389 : Nat := 1058483372891140539757351

theorem tailTrace_2061389 : CollatzResearch.WordTrace tailWord_2061389 prefixEnd_2061389 1058483372891140539757351 := by
  unfold tailWord_2061389
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185033528947185057603221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50123355685964790038402147 75185033528947185057603221)
  ·
    refine ⟨3524298446669399299575151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75185033528947185057603221 3524298446669399299575151)
    ·
      refine ⟨5286447670004098949362727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524298446669399299575151 5286447670004098949362727)
      ·
        refine ⟨7929671505006148424044091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286447670004098949362727 7929671505006148424044091)
        ·
          refine ⟨11894507257509222636066137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929671505006148424044091 11894507257509222636066137)
          ·
            refine ⟨8920880443131916977049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11894507257509222636066137 8920880443131916977049603)
            ·
              refine ⟨13381320664697875465574405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920880443131916977049603 13381320664697875465574405)
              ·
                refine ⟨2508997624630851649795201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13381320664697875465574405 2508997624630851649795201)
                ·
                  refine ⟨1881748218473138737346401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508997624630851649795201 1881748218473138737346401)
                  ·
                    refine ⟨1411311163854854053009801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881748218473138737346401 1411311163854854053009801)
                    ·
                      refine ⟨1058483372891140539757351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411311163854854053009801 1058483372891140539757351)
                      ·
                        rfl

theorem cell23_2061389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2061389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061389 prefixEnd_2061389 := by exact prefixLift 2061389
  have htrace : WordTrace (prefixWord ++ tailWord_2061389) baseStart_2061389 baseEnd_2061389 := by
    simpa [prefixWord, tailWord_2061389, baseEnd_2061389] using wordTrace_append hprefix tailTrace_2061389
  have hstable : (prefixWord ++ tailWord_2061389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061389).length < 2 ^ (prefixWord ++ tailWord_2061389).sum := by decide
  have hdescent : baseEnd_2061389 < baseStart_2061389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061401 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2061401 : Nat := 118140960795 + 2061401 * 2 ^ 59
def prefixEnd_2061401 : Nat := 4983230072969 + 3 ^ 40 * 2061401 * 2
def baseEnd_2061401 : Nat := 1058489534658994492807295

theorem tailTrace_2061401 : CollatzResearch.WordTrace tailWord_2061401 prefixEnd_2061401 1058489534658994492807295 := by
  unfold tailWord_2061401
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185471204903711107040057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50123647469935807404693371 75185471204903711107040057)
  ·
    refine ⟨56389103403677783330280043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75185471204903711107040057 56389103403677783330280043)
    ·
      refine ⟨84583655105516674995420065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56389103403677783330280043 84583655105516674995420065)
      ·
        refine ⟨63437741329137506246565049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84583655105516674995420065 63437741329137506246565049)
        ·
          refine ⟨47578305996853129684923787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63437741329137506246565049 47578305996853129684923787)
          ·
            refine ⟨71367458995279694527385681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47578305996853129684923787 71367458995279694527385681)
            ·
              refine ⟨53525594246459770895539261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71367458995279694527385681 53525594246459770895539261)
              ·
                refine ⟨20072097842422414085827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53525594246459770895539261 20072097842422414085827223)
                ·
                  refine ⟨30108146763633621128740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20072097842422414085827223 30108146763633621128740835)
                  ·
                    refine ⟨45162220145450431693111253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30108146763633621128740835 45162220145450431693111253)
                    ·
                      refine ⟨1058489534658994492807295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45162220145450431693111253 1058489534658994492807295)
                      ·
                        rfl

theorem cell23_2061401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2061401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061401 prefixEnd_2061401 := by exact prefixLift 2061401
  have htrace : WordTrace (prefixWord ++ tailWord_2061401) baseStart_2061401 baseEnd_2061401 := by
    simpa [prefixWord, tailWord_2061401, baseEnd_2061401] using wordTrace_append hprefix tailTrace_2061401
  have hstable : (prefixWord ++ tailWord_2061401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061401).length < 2 ^ (prefixWord ++ tailWord_2061401).sum := by decide
  have hdescent : baseEnd_2061401 < baseStart_2061401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061406 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2061406 : Nat := 118140960795 + 2061406 * 2 ^ 59
def prefixEnd_2061406 : Nat := 4983230072969 + 3 ^ 40 * 2061406 * 2
def baseEnd_2061406 : Nat := 1058492102062266973244773

theorem tailTrace_2061406 : CollatzResearch.WordTrace tailWord_2061406 prefixEnd_2061406 1058492102062266973244773 := by
  unfold tailWord_2061406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398206696235699620121509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50123769046590397973981381 9398206696235699620121509)
  ·
    refine ⟨1762163755544193678772783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9398206696235699620121509 1762163755544193678772783)
    ·
      refine ⟨2643245633316290518159175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762163755544193678772783 2643245633316290518159175)
      ·
        refine ⟨3964868449974435777238763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643245633316290518159175 3964868449974435777238763)
        ·
          refine ⟨5947302674961653665858145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964868449974435777238763 5947302674961653665858145)
          ·
            refine ⟨4460477006221240249393609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947302674961653665858145 4460477006221240249393609)
            ·
              refine ⟨3345357754665930187045207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460477006221240249393609 3345357754665930187045207)
              ·
                refine ⟨5018036631998895280567811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345357754665930187045207 5018036631998895280567811)
                ·
                  refine ⟨7527054947998342920851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018036631998895280567811 7527054947998342920851717)
                  ·
                    refine ⟨1411322802749689297659697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7527054947998342920851717 1411322802749689297659697)
                    ·
                      refine ⟨1058492102062266973244773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411322802749689297659697 1058492102062266973244773)
                      ·
                        rfl

theorem cell23_2061406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2061406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061406 prefixEnd_2061406 := by exact prefixLift 2061406
  have htrace : WordTrace (prefixWord ++ tailWord_2061406) baseStart_2061406 baseEnd_2061406 := by
    simpa [prefixWord, tailWord_2061406, baseEnd_2061406] using wordTrace_append hprefix tailTrace_2061406
  have hstable : (prefixWord ++ tailWord_2061406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061406).length < 2 ^ (prefixWord ++ tailWord_2061406).sum := by decide
  have hdescent : baseEnd_2061406 < baseStart_2061406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061429 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 5]
def baseStart_2061429 : Nat := 118140960795 + 2061429 * 2 ^ 59
def prefixEnd_2061429 : Nat := 4983230072969 + 3 ^ 40 * 2061429 * 2
def baseEnd_2061429 : Nat := 117611545790813375917463

theorem tailTrace_2061429 : CollatzResearch.WordTrace tailWord_2061429 prefixEnd_2061429 117611545790813375917463 := by
  unfold tailWord_2061429
  simp only [CollatzResearch.WordTrace]
  refine ⟨75186492448802271889059341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50124328299201514592706227 75186492448802271889059341)
  ·
    refine ⟨28194934668300851958397253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75186492448802271889059341 28194934668300851958397253)
    ·
      refine ⟨5286550250306409742199485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28194934668300851958397253 5286550250306409742199485)
      ·
        refine ⟨1982456343864903653324807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5286550250306409742199485 1982456343864903653324807)
        ·
          refine ⟨2973684515797355479987211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982456343864903653324807 2973684515797355479987211)
          ·
            refine ⟨4460526773696033219980817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973684515797355479987211 4460526773696033219980817)
            ·
              refine ⟨3345395080272024914985613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460526773696033219980817 3345395080272024914985613)
              ·
                refine ⟨1254523155102009343119605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3345395080272024914985613 1254523155102009343119605)
                ·
                  refine ⟨117611545790813375917463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1254523155102009343119605 117611545790813375917463)
                  ·
                    rfl

theorem cell23_2061429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_2061429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061429 prefixEnd_2061429 := by exact prefixLift 2061429
  have htrace : WordTrace (prefixWord ++ tailWord_2061429) baseStart_2061429 baseEnd_2061429 := by
    simpa [prefixWord, tailWord_2061429, baseEnd_2061429] using wordTrace_append hprefix tailTrace_2061429
  have hstable : (prefixWord ++ tailWord_2061429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061429).length < 2 ^ (prefixWord ++ tailWord_2061429).sum := by decide
  have hdescent : baseEnd_2061429 < baseStart_2061429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061482 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2061482 : Nat := 118140960795 + 2061482 * 2 ^ 59
def prefixEnd_2061482 : Nat := 4983230072969 + 3 ^ 40 * 2061482 * 2
def baseEnd_2061482 : Nat := 1058531126592008675894423

theorem tailTrace_2061482 : CollatzResearch.WordTrace tailWord_2061482 prefixEnd_2061482 1058531126592008675894423 := by
  unfold tailWord_2061482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797106379402565485184675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50125617011740174627159133 18797106379402565485184675)
  ·
    refine ⟨28195659569103848227777013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18797106379402565485184675 28195659569103848227777013)
    ·
      refine ⟨2643343084603485771354095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28195659569103848227777013 2643343084603485771354095)
      ·
        refine ⟨3965014626905228657031143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643343084603485771354095 3965014626905228657031143)
        ·
          refine ⟨5947521940357842985546715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965014626905228657031143 5947521940357842985546715)
          ·
            refine ⟨8921282910536764478320073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947521940357842985546715 8921282910536764478320073)
            ·
              refine ⟨6690962182902573358740055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8921282910536764478320073 6690962182902573358740055)
              ·
                refine ⟨10036443274353860038110083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690962182902573358740055 10036443274353860038110083)
                ·
                  refine ⟨15054664911530790057165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036443274353860038110083 15054664911530790057165125)
                  ·
                    refine ⟨2822749670912023135718461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15054664911530790057165125 2822749670912023135718461)
                    ·
                      refine ⟨1058531126592008675894423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822749670912023135718461 1058531126592008675894423)
                      ·
                        rfl

theorem cell23_2061482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2061482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061482 prefixEnd_2061482 := by exact prefixLift 2061482
  have htrace : WordTrace (prefixWord ++ tailWord_2061482) baseStart_2061482 baseEnd_2061482 := by
    simpa [prefixWord, tailWord_2061482, baseEnd_2061482] using wordTrace_append hprefix tailTrace_2061482
  have hstable : (prefixWord ++ tailWord_2061482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061482).length < 2 ^ (prefixWord ++ tailWord_2061482).sum := by decide
  have hdescent : baseEnd_2061482 < baseStart_2061482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061489 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 1, 4]
def baseStart_2061489 : Nat := 118140960795 + 2061489 * 2 ^ 59
def prefixEnd_2061489 : Nat := 4983230072969 + 3 ^ 40 * 2061489 * 2
def baseEnd_2061489 : Nat := 352844906985530049502297

theorem tailTrace_2061489 : CollatzResearch.WordTrace tailWord_2061489 prefixEnd_2061489 352844906985530049502297 := by
  unfold tailWord_2061489
  simp only [CollatzResearch.WordTrace]
  refine ⟨75188680828584902136243521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50125787219056601424162347 75188680828584902136243521)
  ·
    refine ⟨56391510621438676602182641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75188680828584902136243521 56391510621438676602182641)
    ·
      refine ⟨42293632966079007451636981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56391510621438676602182641 42293632966079007451636981)
      ·
        refine ⟨3965028090569906948590967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42293632966079007451636981 3965028090569906948590967)
        ·
          refine ⟨5947542135854860422886451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965028090569906948590967 5947542135854860422886451)
          ·
            refine ⟨8921313203782290634329677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947542135854860422886451 8921313203782290634329677)
            ·
              refine ⟨3345492451418358987873629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8921313203782290634329677 3345492451418358987873629)
              ·
                refine ⟨1254559669281884620452611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3345492451418358987873629 1254559669281884620452611)
                ·
                  refine ⟨1881839503922826930678917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254559669281884620452611 1881839503922826930678917)
                  ·
                    refine ⟨352844906985530049502297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881839503922826930678917 352844906985530049502297)
                    ·
                      rfl

theorem cell23_2061489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_2061489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061489 prefixEnd_2061489 := by exact prefixLift 2061489
  have htrace : WordTrace (prefixWord ++ tailWord_2061489) baseStart_2061489 baseEnd_2061489 := by
    simpa [prefixWord, tailWord_2061489, baseEnd_2061489] using wordTrace_append hprefix tailTrace_2061489
  have hstable : (prefixWord ++ tailWord_2061489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061489).length < 2 ^ (prefixWord ++ tailWord_2061489).sum := by decide
  have hdescent : baseEnd_2061489 < baseStart_2061489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061498 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_2061498 : Nat := 118140960795 + 2061498 * 2 ^ 59
def prefixEnd_2061498 : Nat := 4983230072969 + 3 ^ 40 * 2061498 * 2
def baseEnd_2061498 : Nat := 352846447427493537764783

theorem tailTrace_2061498 : CollatzResearch.WordTrace tailWord_2061498 prefixEnd_2061498 352846447427493537764783 := by
  unfold tailWord_2061498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797252271388074168330287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50126006057034864448880765 18797252271388074168330287)
  ·
    refine ⟨28195878407082111252495431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18797252271388074168330287 28195878407082111252495431)
    ·
      refine ⟨42293817610623166878743147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28195878407082111252495431 42293817610623166878743147)
      ·
        refine ⟨63440726415934750318114721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42293817610623166878743147 63440726415934750318114721)
        ·
          refine ⟨47580544811951062738586041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63440726415934750318114721 47580544811951062738586041)
          ·
            refine ⟨35685408608963297053939531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47580544811951062738586041 35685408608963297053939531)
            ·
              refine ⟨53528112913444945580909297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35685408608963297053939531 53528112913444945580909297)
              ·
                refine ⟨40146084685083709185681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53528112913444945580909297 40146084685083709185681973)
                ·
                  refine ⟨3763695439226597736157685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40146084685083709185681973 3763695439226597736157685)
                  ·
                    refine ⟨352846447427493537764783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3763695439226597736157685 352846447427493537764783)
                    ·
                      rfl

theorem cell23_2061498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_2061498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061498 prefixEnd_2061498 := by exact prefixLift 2061498
  have htrace : WordTrace (prefixWord ++ tailWord_2061498) baseStart_2061498 baseEnd_2061498 := by
    simpa [prefixWord, tailWord_2061498, baseEnd_2061498] using wordTrace_append hprefix tailTrace_2061498
  have hstable : (prefixWord ++ tailWord_2061498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061498).length < 2 ^ (prefixWord ++ tailWord_2061498).sum := by decide
  have hdescent : baseEnd_2061498 < baseStart_2061498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061512 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_2061512 : Nat := 118140960795 + 2061512 * 2 ^ 59
def prefixEnd_2061512 : Nat := 4983230072969 + 3 ^ 40 * 2061512 * 2
def baseEnd_2061512 : Nat := 1058546531011643558519285

theorem tailTrace_2061512 : CollatzResearch.WordTrace tailWord_2061512 prefixEnd_2061512 1058546531011643558519285 := by
  unfold tailWord_2061512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37594759853750788532165395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50126346471667718042887193 37594759853750788532165395)
  ·
    refine ⟨56392139780626182798248093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37594759853750788532165395 56392139780626182798248093)
    ·
      refine ⟨21147052417734818549343035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56392139780626182798248093 21147052417734818549343035)
      ·
        refine ⟨31720578626602227824014553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21147052417734818549343035 31720578626602227824014553)
        ·
          refine ⟨23790433969951670868010915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31720578626602227824014553 23790433969951670868010915)
          ·
            refine ⟨35685650954927506302016373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790433969951670868010915 35685650954927506302016373)
            ·
              refine ⟨3345529777024453715814035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35685650954927506302016373 3345529777024453715814035)
              ·
                refine ⟨5018294665536680573721053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345529777024453715814035 5018294665536680573721053)
                ·
                  refine ⟨1881860499576255215145395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5018294665536680573721053 1881860499576255215145395)
                  ·
                    refine ⟨2822790749364382822718093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881860499576255215145395 2822790749364382822718093)
                    ·
                      refine ⟨1058546531011643558519285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822790749364382822718093 1058546531011643558519285)
                      ·
                        rfl

theorem cell23_2061512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_2061512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061512 prefixEnd_2061512 := by exact prefixLift 2061512
  have htrace : WordTrace (prefixWord ++ tailWord_2061512) baseStart_2061512 baseEnd_2061512 := by
    simpa [prefixWord, tailWord_2061512, baseEnd_2061512] using wordTrace_append hprefix tailTrace_2061512
  have hstable : (prefixWord ++ tailWord_2061512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061512).length < 2 ^ (prefixWord ++ tailWord_2061512).sum := by decide
  have hdescent : baseEnd_2061512 < baseStart_2061512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061522 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2061522 : Nat := 118140960795 + 2061522 * 2 ^ 59
def prefixEnd_2061522 : Nat := 4983230072969 + 3 ^ 40 * 2061522 * 2
def baseEnd_2061522 : Nat := 1058551665818188519394239

theorem tailTrace_2061522 : CollatzResearch.WordTrace tailWord_2061522 prefixEnd_2061522 1058551665818188519394239 := by
  unfold tailWord_2061522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797471109366337193048705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50126589624976899181463213 18797471109366337193048705)
  ·
    refine ⟨14098103332024752894786529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18797471109366337193048705 14098103332024752894786529)
    ·
      refine ⟨10573577499018564671089897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14098103332024752894786529 10573577499018564671089897)
      ·
        refine ⟨7930183124263923503317423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573577499018564671089897 7930183124263923503317423)
        ·
          refine ⟨11895274686395885254976135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930183124263923503317423 11895274686395885254976135)
          ·
            refine ⟨17842912029593827882464203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895274686395885254976135 17842912029593827882464203)
            ·
              refine ⟨26764368044390741823696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17842912029593827882464203 26764368044390741823696305)
              ·
                refine ⟨20073276033293056367772229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26764368044390741823696305 20073276033293056367772229)
                ·
                  refine ⟨3763739256242448068957293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20073276033293056367772229 3763739256242448068957293)
                  ·
                    refine ⟨1411402221090918025858985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3763739256242448068957293 1411402221090918025858985)
                    ·
                      refine ⟨1058551665818188519394239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411402221090918025858985 1058551665818188519394239)
                      ·
                        rfl

theorem cell23_2061522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2061522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061522 prefixEnd_2061522 := by exact prefixLift 2061522
  have htrace : WordTrace (prefixWord ++ tailWord_2061522) baseStart_2061522 baseEnd_2061522 := by
    simpa [prefixWord, tailWord_2061522, baseEnd_2061522] using wordTrace_append hprefix tailTrace_2061522
  have hstable : (prefixWord ++ tailWord_2061522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061522).length < 2 ^ (prefixWord ++ tailWord_2061522).sum := by decide
  have hdescent : baseEnd_2061522 < baseStart_2061522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061535 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 6, 2]
def baseStart_2061535 : Nat := 118140960795 + 2061535 * 2 ^ 59
def prefixEnd_2061535 : Nat := 4983230072969 + 3 ^ 40 * 2061535 * 2
def baseEnd_2061535 : Nat := 1058558341066696968531679

theorem tailTrace_2061535 : CollatzResearch.WordTrace tailWord_2061535 prefixEnd_2061535 1058558341066696968531679 := by
  unfold tailWord_2061535
  simp only [CollatzResearch.WordTrace]
  refine ⟨75190358586418251992418059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50126905724278834661612039 75190358586418251992418059)
  ·
    refine ⟨112785537879627377988627089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75190358586418251992418059 112785537879627377988627089)
    ·
      refine ⟨84589153409720533491470317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112785537879627377988627089 84589153409720533491470317)
      ·
        refine ⟨31720932528645200059301369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84589153409720533491470317 31720932528645200059301369)
        ·
          refine ⟨23790699396483900044476027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31720932528645200059301369 23790699396483900044476027)
          ·
            refine ⟨35686049094725850066714041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790699396483900044476027 35686049094725850066714041)
            ·
              refine ⟨26764536821044387550035531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35686049094725850066714041 26764536821044387550035531)
              ·
                refine ⟨40146805231566581325053297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26764536821044387550035531 40146805231566581325053297)
                ·
                  refine ⟨30110103923674935993789973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40146805231566581325053297 30110103923674935993789973)
                  ·
                    refine ⟨1411411121422262624708905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30110103923674935993789973 1411411121422262624708905)
                    ·
                      refine ⟨1058558341066696968531679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411411121422262624708905 1058558341066696968531679)
                      ·
                        rfl

theorem cell23_2061535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_2061535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061535 prefixEnd_2061535 := by exact prefixLift 2061535
  have htrace : WordTrace (prefixWord ++ tailWord_2061535) baseStart_2061535 baseEnd_2061535 := by
    simpa [prefixWord, tailWord_2061535, baseEnd_2061535] using wordTrace_append hprefix tailTrace_2061535
  have hstable : (prefixWord ++ tailWord_2061535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061535).length < 2 ^ (prefixWord ++ tailWord_2061535).sum := by decide
  have hdescent : baseEnd_2061535 < baseStart_2061535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061549 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2061549 : Nat := 118140960795 + 2061549 * 2 ^ 59
def prefixEnd_2061549 : Nat := 4983230072969 + 3 ^ 40 * 2061549 * 2
def baseEnd_2061549 : Nat := 352855176598619971252205

theorem tailTrace_2061549 : CollatzResearch.WordTrace tailWord_2061549 prefixEnd_2061549 352855176598619971252205 := by
  unfold tailWord_2061549
  simp only [CollatzResearch.WordTrace]
  refine ⟨75190869208367532383427701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50127246138911688255618467 75190869208367532383427701)
  ·
    refine ⟨7049143988284456160946347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75190869208367532383427701 7049143988284456160946347)
    ·
      refine ⟨10573715982426684241419521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7049143988284456160946347 10573715982426684241419521)
      ·
        refine ⟨7930286986820013181064641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573715982426684241419521 7930286986820013181064641)
        ·
          refine ⟨5947715240115009885798481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930286986820013181064641 5947715240115009885798481)
          ·
            refine ⟨4460786430086257414348861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947715240115009885798481 4460786430086257414348861)
            ·
              refine ⟨1672794911282346530380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4460786430086257414348861 1672794911282346530380823)
              ·
                refine ⟨2509192366923519795571235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672794911282346530380823 2509192366923519795571235)
                ·
                  refine ⟨3763788550385279693356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509192366923519795571235 3763788550385279693356853)
                  ·
                    refine ⟨352855176598619971252205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3763788550385279693356853 352855176598619971252205)
                    ·
                      rfl

theorem cell23_2061549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2061549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061549 prefixEnd_2061549 := by exact prefixLift 2061549
  have htrace : WordTrace (prefixWord ++ tailWord_2061549) baseStart_2061549 baseEnd_2061549 := by
    simpa [prefixWord, tailWord_2061549, baseEnd_2061549] using wordTrace_append hprefix tailTrace_2061549
  have hstable : (prefixWord ++ tailWord_2061549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061549).length < 2 ^ (prefixWord ++ tailWord_2061549).sum := by decide
  have hdescent : baseEnd_2061549 < baseStart_2061549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061555 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5]
def baseStart_2061555 : Nat := 118140960795 + 2061555 * 2 ^ 59
def prefixEnd_2061555 : Nat := 4983230072969 + 3 ^ 40 * 2061555 * 2
def baseEnd_2061555 : Nat := 1058568610679786890281587

theorem tailTrace_2061555 : CollatzResearch.WordTrace tailWord_2061555 prefixEnd_2061555 1058568610679786890281587 := by
  unfold tailWord_2061555
  simp only [CollatzResearch.WordTrace]
  refine ⟨75191088046345795408146119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50127392030897196938764079 75191088046345795408146119)
  ·
    refine ⟨112786632069518693112219179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75191088046345795408146119 112786632069518693112219179)
    ·
      refine ⟨169179948104278039668328769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112786632069518693112219179 169179948104278039668328769)
      ·
        refine ⟨126884961078208529751246577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169179948104278039668328769 126884961078208529751246577)
        ·
          refine ⟨95163720808656397313434933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126884961078208529751246577 95163720808656397313434933)
          ·
            refine ⟨8921598825811537248134525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95163720808656397313434933 8921598825811537248134525)
            ·
              refine ⟨3345599559679326468050447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8921598825811537248134525 3345599559679326468050447)
              ·
                refine ⟨5018399339518989702075671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345599559679326468050447 5018399339518989702075671)
                ·
                  refine ⟨7527599009278484553113507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018399339518989702075671 7527599009278484553113507)
                  ·
                    refine ⟨11291398513917726829670261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7527599009278484553113507 11291398513917726829670261)
                    ·
                      refine ⟨1058568610679786890281587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11291398513917726829670261 1058568610679786890281587)
                      ·
                        rfl

theorem cell23_2061555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_2061555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061555 prefixEnd_2061555 := by exact prefixLift 2061555
  have htrace : WordTrace (prefixWord ++ tailWord_2061555) baseStart_2061555 baseEnd_2061555 := by
    simpa [prefixWord, tailWord_2061555, baseEnd_2061555] using wordTrace_append hprefix tailTrace_2061555
  have hstable : (prefixWord ++ tailWord_2061555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061555).length < 2 ^ (prefixWord ++ tailWord_2061555).sum := by decide
  have hdescent : baseEnd_2061555 < baseStart_2061555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061562 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_2061562 : Nat := 118140960795 + 2061562 * 2 ^ 59
def prefixEnd_2061562 : Nat := 4983230072969 + 3 ^ 40 * 2061562 * 2
def baseEnd_2061562 : Nat := 352857401681456120964685

theorem tailTrace_2061562 : CollatzResearch.WordTrace tailWord_2061562 prefixEnd_2061562 352857401681456120964685 := by
  unfold tailWord_2061562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18797835839330108900912735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50127562238213623735767293 18797835839330108900912735)
  ·
    refine ⟨28196753758995163351369103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18797835839330108900912735 28196753758995163351369103)
    ·
      refine ⟨42295130638492745027053655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28196753758995163351369103 42295130638492745027053655)
      ·
        refine ⟨63442695957739117540580483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42295130638492745027053655 63442695957739117540580483)
        ·
          refine ⟨95164043936608676310870725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63442695957739117540580483 95164043936608676310870725)
          ·
            refine ⟨17843258238114126808288261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95164043936608676310870725 17843258238114126808288261)
            ·
              refine ⟨3345610919646398776554049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17843258238114126808288261 3345610919646398776554049)
              ·
                refine ⟨2509208189734799082415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345610919646398776554049 2509208189734799082415537)
                ·
                  refine ⟨1881906142301099311811653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2509208189734799082415537 1881906142301099311811653)
                  ·
                    refine ⟨352857401681456120964685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881906142301099311811653 352857401681456120964685)
                    ·
                      rfl

theorem cell23_2061562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_2061562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061562 prefixEnd_2061562 := by exact prefixLift 2061562
  have htrace : WordTrace (prefixWord ++ tailWord_2061562) baseStart_2061562 baseEnd_2061562 := by
    simpa [prefixWord, tailWord_2061562, baseEnd_2061562] using wordTrace_append hprefix tailTrace_2061562
  have hstable : (prefixWord ++ tailWord_2061562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061562).length < 2 ^ (prefixWord ++ tailWord_2061562).sum := by decide
  have hdescent : baseEnd_2061562 < baseStart_2061562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061572 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2061572 : Nat := 118140960795 + 2061572 * 2 ^ 59
def prefixEnd_2061572 : Nat := 4983230072969 + 3 ^ 40 * 2061572 * 2
def baseEnd_2061572 : Nat := 1058577339850913323769009

theorem tailTrace_2061572 : CollatzResearch.WordTrace tailWord_2061572 prefixEnd_2061572 1058577339850913323769009 := by
  unfold tailWord_2061572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595854043642103655757485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50127805391522804874343313 37595854043642103655757485)
  ·
    refine ⟨14098445266365788870909057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37595854043642103655757485 14098445266365788870909057)
    ·
      refine ⟨10573833949774341653181793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14098445266365788870909057 10573833949774341653181793)
      ·
        refine ⟨7930375462330756239886345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573833949774341653181793 7930375462330756239886345)
        ·
          refine ⟨5947781596748067179914759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930375462330756239886345 5947781596748067179914759)
          ·
            refine ⟨8921672395122100769872139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947781596748067179914759 8921672395122100769872139)
            ·
              refine ⟨13382508592683151154808209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921672395122100769872139 13382508592683151154808209)
              ·
                refine ⟨10036881444512363366106157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382508592683151154808209 10036881444512363366106157)
                ·
                  refine ⟨3763830541692136262289809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10036881444512363366106157 3763830541692136262289809)
                  ·
                    refine ⟨2822872906269102196717357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3763830541692136262289809 2822872906269102196717357)
                    ·
                      refine ⟨1058577339850913323769009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822872906269102196717357 1058577339850913323769009)
                      ·
                        rfl

theorem cell23_2061572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2061572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061572 prefixEnd_2061572 := by exact prefixLift 2061572
  have htrace : WordTrace (prefixWord ++ tailWord_2061572) baseStart_2061572 baseEnd_2061572 := by
    simpa [prefixWord, tailWord_2061572, baseEnd_2061572] using wordTrace_append hprefix tailTrace_2061572
  have hstable : (prefixWord ++ tailWord_2061572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061572).length < 2 ^ (prefixWord ++ tailWord_2061572).sum := by decide
  have hdescent : baseEnd_2061572 < baseStart_2061572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061582 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2061582 : Nat := 118140960795 + 2061582 * 2 ^ 59
def prefixEnd_2061582 : Nat := 4983230072969 + 3 ^ 40 * 2061582 * 2
def baseEnd_2061582 : Nat := 1058582474657458284643963

theorem tailTrace_2061582 : CollatzResearch.WordTrace tailWord_2061582 prefixEnd_2061582 1058582474657458284643963 := by
  unfold tailWord_2061582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399009102155997377422375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50128048544831986012919333 9399009102155997377422375)
  ·
    refine ⟨14098513653233996066133563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399009102155997377422375 14098513653233996066133563)
    ·
      refine ⟨21147770479850994099200345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098513653233996066133563 21147770479850994099200345)
      ·
        refine ⟨15860827859888245574400259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21147770479850994099200345 15860827859888245574400259)
        ·
          refine ⟨23791241789832368361600389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15860827859888245574400259 23791241789832368361600389)
          ·
            refine ⟨4460857835593569067800073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23791241789832368361600389 4460857835593569067800073)
            ·
              refine ⟨3345643376695176800850055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460857835593569067800073 3345643376695176800850055)
              ·
                refine ⟨5018465065042765201275083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345643376695176800850055 5018465065042765201275083)
                ·
                  refine ⟨7527697597564147801912625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018465065042765201275083 7527697597564147801912625)
                  ·
                    refine ⟨5645773198173110851434469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527697597564147801912625 5645773198173110851434469)
                    ·
                      refine ⟨1058582474657458284643963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5645773198173110851434469 1058582474657458284643963)
                      ·
                        rfl

theorem cell23_2061582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2061582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061582 prefixEnd_2061582 := by exact prefixLift 2061582
  have htrace : WordTrace (prefixWord ++ tailWord_2061582) baseStart_2061582 baseEnd_2061582 := by
    simpa [prefixWord, tailWord_2061582, baseEnd_2061582] using wordTrace_append hprefix tailTrace_2061582
  have hstable : (prefixWord ++ tailWord_2061582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061582).length < 2 ^ (prefixWord ++ tailWord_2061582).sum := by decide
  have hdescent : baseEnd_2061582 < baseStart_2061582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061619 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 3]
def baseStart_2061619 : Nat := 118140960795 + 2061619 * 2 ^ 59
def prefixEnd_2061619 : Nat := 4983230072969 + 3 ^ 40 * 2061619 * 2
def baseEnd_2061619 : Nat := 1058601473441674639881293

theorem tailTrace_2061619 : CollatzResearch.WordTrace tailWord_2061619 prefixEnd_2061619 1058601473441674639881293 := by
  unfold tailWord_2061619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75193422318113934338475911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50128948212075956225650607 75193422318113934338475911)
  ·
    refine ⟨112790133477170901507713867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75193422318113934338475911 112790133477170901507713867)
    ·
      refine ⟨169185200215756352261570801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112790133477170901507713867 169185200215756352261570801)
      ·
        refine ⟨126888900161817264196178101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169185200215756352261570801 126888900161817264196178101)
        ·
          refine ⟨11895834390170368518391697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126888900161817264196178101 11895834390170368518391697)
          ·
            refine ⟨8921875792627776388793773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11895834390170368518391697 8921875792627776388793773)
            ·
              refine ⟨3345703422235416145797665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8921875792627776388793773 3345703422235416145797665)
              ·
                refine ⟨2509277566676562109348249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345703422235416145797665 2509277566676562109348249)
                ·
                  refine ⟨1881958175007421582011187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2509277566676562109348249 1881958175007421582011187)
                  ·
                    refine ⟨2822937262511132373016781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881958175007421582011187 2822937262511132373016781)
                    ·
                      refine ⟨1058601473441674639881293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822937262511132373016781 1058601473441674639881293)
                      ·
                        rfl

theorem cell23_2061619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_2061619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061619 prefixEnd_2061619 := by exact prefixLift 2061619
  have htrace : WordTrace (prefixWord ++ tailWord_2061619) baseStart_2061619 baseEnd_2061619 := by
    simpa [prefixWord, tailWord_2061619, baseEnd_2061619] using wordTrace_append hprefix tailTrace_2061619
  have hstable : (prefixWord ++ tailWord_2061619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061619).length < 2 ^ (prefixWord ++ tailWord_2061619).sum := by decide
  have hdescent : baseEnd_2061619 < baseStart_2061619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061636 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2061636 : Nat := 118140960795 + 2061636 * 2 ^ 59
def prefixEnd_2061636 : Nat := 4983230072969 + 3 ^ 40 * 2061636 * 2
def baseEnd_2061636 : Nat := 1058610202612801073368715

theorem tailTrace_2061636 : CollatzResearch.WordTrace tailWord_2061636 prefixEnd_2061636 1058610202612801073368715 := by
  unfold tailWord_2061636
  simp only [CollatzResearch.WordTrace]
  refine ⟨37597021179526173120922381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50129361572701564161229841 37597021179526173120922381)
  ·
    refine ⟨14098882942322314920345893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37597021179526173120922381 14098882942322314920345893)
    ·
      refine ⟨2643540551685434047564855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14098882942322314920345893 2643540551685434047564855)
      ·
        refine ⟨3965310827528151071347283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643540551685434047564855 3965310827528151071347283)
        ·
          refine ⟨5947966241292226607020925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965310827528151071347283 5947966241292226607020925)
          ·
            refine ⟨2230487340484584977632847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5947966241292226607020925 2230487340484584977632847)
            ·
              refine ⟨3345731010726877466449271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230487340484584977632847 3345731010726877466449271)
              ·
                refine ⟨5018596516090316199673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345731010726877466449271 5018596516090316199673907)
                ·
                  refine ⟨7527894774135474299510861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018596516090316199673907 7527894774135474299510861)
                  ·
                    refine ⟨2822960540300802862316573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7527894774135474299510861 2822960540300802862316573)
                    ·
                      refine ⟨1058610202612801073368715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2822960540300802862316573 1058610202612801073368715)
                      ·
                        rfl

theorem cell23_2061636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2061636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061636 prefixEnd_2061636 := by exact prefixLift 2061636
  have htrace : WordTrace (prefixWord ++ tailWord_2061636) baseStart_2061636 baseEnd_2061636 := by
    simpa [prefixWord, tailWord_2061636, baseEnd_2061636] using wordTrace_append hprefix tailTrace_2061636
  have hstable : (prefixWord ++ tailWord_2061636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061636).length < 2 ^ (prefixWord ++ tailWord_2061636).sum := by decide
  have hdescent : baseEnd_2061636 < baseStart_2061636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061749 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_2061749 : Nat := 118140960795 + 2061749 * 2 ^ 59
def prefixEnd_2061749 : Nat := 4983230072969 + 3 ^ 40 * 2061749 * 2
def baseEnd_2061749 : Nat := 1058668225926759131255695

theorem tailTrace_2061749 : CollatzResearch.WordTrace tailWord_2061749 prefixEnd_2061749 1058668225926759131255695 := by
  unfold tailWord_2061749
  simp only [CollatzResearch.WordTrace]
  refine ⟨75198163807642966540708301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50132109205095311027138867 75198163807642966540708301)
  ·
    refine ⟨28199311427866112452765613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75198163807642966540708301 28199311427866112452765613)
    ·
      refine ⟨10574741785449792169787105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28199311427866112452765613 10574741785449792169787105)
      ·
        refine ⟨7931056339087344127340329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10574741785449792169787105 7931056339087344127340329)
        ·
          refine ⟨5948292254315508095505247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931056339087344127340329 5948292254315508095505247)
          ·
            refine ⟨8922438381473262143257871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948292254315508095505247 8922438381473262143257871)
            ·
              refine ⟨13383657572209893214886807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922438381473262143257871 13383657572209893214886807)
              ·
                refine ⟨20075486358314839822330211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13383657572209893214886807 20075486358314839822330211)
                ·
                  refine ⟨30113229537472259733495317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20075486358314839822330211 30113229537472259733495317)
                  ·
                    refine ⟨1411557634569012175007593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30113229537472259733495317 1411557634569012175007593)
                    ·
                      refine ⟨1058668225926759131255695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411557634569012175007593 1058668225926759131255695)
                      ·
                        rfl

theorem cell23_2061749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_2061749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061749 prefixEnd_2061749 := by exact prefixLift 2061749
  have htrace : WordTrace (prefixWord ++ tailWord_2061749) baseStart_2061749 baseEnd_2061749 := by
    simpa [prefixWord, tailWord_2061749, baseEnd_2061749] using wordTrace_append hprefix tailTrace_2061749
  have hstable : (prefixWord ++ tailWord_2061749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061749).length < 2 ^ (prefixWord ++ tailWord_2061749).sum := by decide
  have hdescent : baseEnd_2061749 < baseStart_2061749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061752 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_2061752 : Nat := 118140960795 + 2061752 * 2 ^ 59
def prefixEnd_2061752 : Nat := 4983230072969 + 3 ^ 40 * 2061752 * 2
def baseEnd_2061752 : Nat := 1058669766368722619518181

theorem tailTrace_2061752 : CollatzResearch.WordTrace tailWord_2061752 prefixEnd_2061752 1058669766368722619518181 := by
  unfold tailWord_2061752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37599136613316049026533755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50132182151088065368711673 37599136613316049026533755)
  ·
    refine ⟨56398704919974073539800633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37599136613316049026533755 56398704919974073539800633)
    ·
      refine ⟨42299028689980555154850475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56398704919974073539800633 42299028689980555154850475)
      ·
        refine ⟨63448543034970832732275713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42299028689980555154850475 63448543034970832732275713)
        ·
          refine ⟨47586407276228124549206785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63448543034970832732275713 47586407276228124549206785)
          ·
            refine ⟨35689805457171093411905089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47586407276228124549206785 35689805457171093411905089)
            ·
              refine ⟨26767354092878320058928817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35689805457171093411905089 26767354092878320058928817)
              ·
                refine ⟨20075515569658740044196613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26767354092878320058928817 20075515569658740044196613)
                ·
                  refine ⟨3764159169311013758286865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20075515569658740044196613 3764159169311013758286865)
                  ·
                    refine ⟨2823119376983260318715149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3764159169311013758286865 2823119376983260318715149)
                    ·
                      refine ⟨1058669766368722619518181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2823119376983260318715149 1058669766368722619518181)
                      ·
                        rfl

theorem cell23_2061752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_2061752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061752 prefixEnd_2061752 := by exact prefixLift 2061752
  have htrace : WordTrace (prefixWord ++ tailWord_2061752) baseStart_2061752 baseEnd_2061752 := by
    simpa [prefixWord, tailWord_2061752, baseEnd_2061752] using wordTrace_append hprefix tailTrace_2061752
  have hstable : (prefixWord ++ tailWord_2061752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061752).length < 2 ^ (prefixWord ++ tailWord_2061752).sum := by decide
  have hdescent : baseEnd_2061752 < baseStart_2061752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061789 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2061789 : Nat := 118140960795 + 2061789 * 2 ^ 59
def prefixEnd_2061789 : Nat := 4983230072969 + 3 ^ 40 * 2061789 * 2
def baseEnd_2061789 : Nat := 117632085016993219417279

theorem tailTrace_2061789 : CollatzResearch.WordTrace tailWord_2061789 prefixEnd_2061789 117632085016993219417279 := by
  unfold tailWord_2061789
  simp only [CollatzResearch.WordTrace]
  refine ⟨75199622727498053372164421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50133081818332035581442947 75199622727498053372164421)
  ·
    refine ⟨14099929261405885007280829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75199622727498053372164421 14099929261405885007280829)
    ·
      refine ⟨5287473473027206877730311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14099929261405885007280829 5287473473027206877730311)
      ·
        refine ⟨7931210209540810316595467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287473473027206877730311 7931210209540810316595467)
        ·
          refine ⟨11896815314311215474893201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931210209540810316595467 11896815314311215474893201)
          ·
            refine ⟨8922611485733411606169901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896815314311215474893201 8922611485733411606169901)
            ·
              refine ⟨3345979307150029352313713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8922611485733411606169901 3345979307150029352313713)
              ·
                refine ⟨2509484480362522014235285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345979307150029352313713 2509484480362522014235285)
                ·
                  refine ⟨117632085016993219417279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2509484480362522014235285 117632085016993219417279)
                  ·
                    rfl

theorem cell23_2061789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2061789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061789 prefixEnd_2061789 := by exact prefixLift 2061789
  have htrace : WordTrace (prefixWord ++ tailWord_2061789) baseStart_2061789 baseEnd_2061789 := by
    simpa [prefixWord, tailWord_2061789, baseEnd_2061789] using wordTrace_append hprefix tailTrace_2061789
  have hstable : (prefixWord ++ tailWord_2061789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061789).length < 2 ^ (prefixWord ++ tailWord_2061789).sum := by decide
  have hdescent : baseEnd_2061789 < baseStart_2061789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061809 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_2061809 : Nat := 118140960795 + 2061809 * 2 ^ 59
def prefixEnd_2061809 : Nat := 4983230072969 + 3 ^ 40 * 2061809 * 2
def baseEnd_2061809 : Nat := 1058699034766028896505419

theorem tailTrace_2061809 : CollatzResearch.WordTrace tailWord_2061809 prefixEnd_2061809 1058699034766028896505419 := by
  unfold tailWord_2061809
  simp only [CollatzResearch.WordTrace]
  refine ⟨75200352187425596787892481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50133568124950397858594987 75200352187425596787892481)
  ·
    refine ⟨56400264140569197590919361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75200352187425596787892481 56400264140569197590919361)
    ·
      refine ⟨42300198105426898193189521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56400264140569197590919361 42300198105426898193189521)
      ·
        refine ⟨31725148579070173644892141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42300198105426898193189521 31725148579070173644892141)
        ·
          refine ⟨11896930717151315116834553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31725148579070173644892141 11896930717151315116834553)
          ·
            refine ⟨8922698037863486337625915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896930717151315116834553 8922698037863486337625915)
            ·
              refine ⟨13384047056795229506438873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922698037863486337625915 13384047056795229506438873)
              ·
                refine ⟨10038035292596422129829155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13384047056795229506438873 10038035292596422129829155)
                ·
                  refine ⟨15057052938894633194743733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10038035292596422129829155 15057052938894633194743733)
                  ·
                    refine ⟨1411598713021371862007225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15057052938894633194743733 1411598713021371862007225)
                    ·
                      refine ⟨1058699034766028896505419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411598713021371862007225 1058699034766028896505419)
                      ·
                        rfl

theorem cell23_2061809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_2061809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061809 prefixEnd_2061809 := by exact prefixLift 2061809
  have htrace : WordTrace (prefixWord ++ tailWord_2061809) baseStart_2061809 baseEnd_2061809 := by
    simpa [prefixWord, tailWord_2061809, baseEnd_2061809] using wordTrace_append hprefix tailTrace_2061809
  have hstable : (prefixWord ++ tailWord_2061809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061809).length < 2 ^ (prefixWord ++ tailWord_2061809).sum := by decide
  have hdescent : baseEnd_2061809 < baseStart_2061809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061832 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_2061832 : Nat := 118140960795 + 2061832 * 2 ^ 59
def prefixEnd_2061832 : Nat := 4983230072969 + 3 ^ 40 * 2061832 * 2
def baseEnd_2061832 : Nat := 352903614940360768839271

theorem tailTrace_2061832 : CollatzResearch.WordTrace tailWord_2061832 prefixEnd_2061832 352903614940360768839271 := by
  unfold tailWord_2061832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600595533171135857989875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50134127377561514477319833 37600595533171135857989875)
  ·
    refine ⟨56400893299756703786984813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37600595533171135857989875 56400893299756703786984813)
    ·
      refine ⟨21150334987408763920119305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56400893299756703786984813 21150334987408763920119305)
      ·
        refine ⟨15862751240556572940089479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21150334987408763920119305 15862751240556572940089479)
        ·
          refine ⟨23794126860834859410134219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15862751240556572940089479 23794126860834859410134219)
          ·
            refine ⟨35691190291252289115201329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23794126860834859410134219 35691190291252289115201329)
            ·
              refine ⟨26768392718439216836400997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35691190291252289115201329 26768392718439216836400997)
              ·
                refine ⟨5019073634707353156825187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26768392718439216836400997 5019073634707353156825187)
                ·
                  refine ⟨7528610452061029735237781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019073634707353156825187 7528610452061029735237781)
                  ·
                    refine ⟨352903614940360768839271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7528610452061029735237781 352903614940360768839271)
                    ·
                      rfl

theorem cell23_2061832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_2061832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061832 prefixEnd_2061832 := by exact prefixLift 2061832
  have htrace : WordTrace (prefixWord ++ tailWord_2061832) baseStart_2061832 baseEnd_2061832 := by
    simpa [prefixWord, tailWord_2061832, baseEnd_2061832] using wordTrace_append hprefix tailTrace_2061832
  have hstable : (prefixWord ++ tailWord_2061832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061832).length < 2 ^ (prefixWord ++ tailWord_2061832).sum := by decide
  have hdescent : baseEnd_2061832 < baseStart_2061832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061852 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2061852 : Nat := 118140960795 + 2061852 * 2 ^ 59
def prefixEnd_2061852 : Nat := 4983230072969 + 3 ^ 40 * 2061852 * 2
def baseEnd_2061852 : Nat := 1058721114434172228267721

theorem tailTrace_2061852 : CollatzResearch.WordTrace tailWord_2061852 prefixEnd_2061852 1058721114434172228267721 := by
  unfold tailWord_2061852
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600960263134907565853905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50134613684179876754471873 37600960263134907565853905)
  ·
    refine ⟨28200720197351180674390429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37600960263134907565853905 28200720197351180674390429)
    ·
      refine ⟨10575270074006692752896411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28200720197351180674390429 10575270074006692752896411)
      ·
        refine ⟨15862905111010039129344617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575270074006692752896411 15862905111010039129344617)
        ·
          refine ⟨11897178833257529347008463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15862905111010039129344617 11897178833257529347008463)
          ·
            refine ⟨17845768249886294020512695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11897178833257529347008463 17845768249886294020512695)
            ·
              refine ⟨26768652374829441030769043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17845768249886294020512695 26768652374829441030769043)
              ·
                refine ⟨40152978562244161546153565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26768652374829441030769043 40152978562244161546153565)
                ·
                  refine ⟨15057366960841560579807587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40152978562244161546153565 15057366960841560579807587)
                  ·
                    refine ⟨22586050441262340869711381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15057366960841560579807587 22586050441262340869711381)
                    ·
                      refine ⟨1058721114434172228267721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22586050441262340869711381 1058721114434172228267721)
                      ·
                        rfl

theorem cell23_2061852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2061852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061852 prefixEnd_2061852 := by exact prefixLift 2061852
  have htrace : WordTrace (prefixWord ++ tailWord_2061852) baseStart_2061852 baseEnd_2061852 := by
    simpa [prefixWord, tailWord_2061852, baseEnd_2061852] using wordTrace_append hprefix tailTrace_2061852
  have hstable : (prefixWord ++ tailWord_2061852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061852).length < 2 ^ (prefixWord ++ tailWord_2061852).sum := by decide
  have hdescent : baseEnd_2061852 < baseStart_2061852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061866 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2061866 : Nat := 118140960795 + 2061866 * 2 ^ 59
def prefixEnd_2061866 : Nat := 4983230072969 + 3 ^ 40 * 2061866 * 2
def baseEnd_2061866 : Nat := 352909434387778391164219

theorem tailTrace_2061866 : CollatzResearch.WordTrace tailWord_2061866 prefixEnd_2061866 352909434387778391164219 := by
  unfold tailWord_2061866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800607787054773880679363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50134954098812730348478301 18800607787054773880679363)
  ·
    refine ⟨28200911680582160821019045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18800607787054773880679363 28200911680582160821019045)
    ·
      refine ⟨5287670940109155153941071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28200911680582160821019045 5287670940109155153941071)
      ·
        refine ⟨7931506410163732730911607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287670940109155153941071 7931506410163732730911607)
        ·
          refine ⟨11897259615245599096367411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931506410163732730911607 11897259615245599096367411)
          ·
            refine ⟨17845889422868398644551117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11897259615245599096367411 17845889422868398644551117)
            ·
              refine ⟨6692208533575649491706669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17845889422868398644551117 6692208533575649491706669)
              ·
                refine ⟨2509578200090868559390001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6692208533575649491706669 2509578200090868559390001)
                ·
                  refine ⟨1882183650068151419542501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2509578200090868559390001 1882183650068151419542501)
                  ·
                    refine ⟨352909434387778391164219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882183650068151419542501 352909434387778391164219)
                    ·
                      rfl

theorem cell23_2061866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2061866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061866 prefixEnd_2061866 := by exact prefixLift 2061866
  have htrace : WordTrace (prefixWord ++ tailWord_2061866) baseStart_2061866 baseEnd_2061866 := by
    simpa [prefixWord, tailWord_2061866, baseEnd_2061866] using wordTrace_append hprefix tailTrace_2061866
  have hstable : (prefixWord ++ tailWord_2061866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061866).length < 2 ^ (prefixWord ++ tailWord_2061866).sum := by decide
  have hdescent : baseEnd_2061866 < baseStart_2061866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061952 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 9]
def baseStart_2061952 : Nat := 118140960795 + 2061952 * 2 ^ 59
def prefixEnd_2061952 : Nat := 4983230072969 + 3 ^ 40 * 2061952 * 2
def baseEnd_2061952 : Nat := 117641384722180204113029

theorem tailTrace_2061952 : CollatzResearch.WordTrace tailWord_2061952 prefixEnd_2061952 117641384722180204113029 := by
  unfold tailWord_2061952
  simp only [CollatzResearch.WordTrace]
  refine ⟨37602783912953766105174055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50137045217271688140232073 37602783912953766105174055)
  ·
    refine ⟨56404175869430649157761083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37602783912953766105174055 56404175869430649157761083)
    ·
      refine ⟨84606263804145973736641625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56404175869430649157761083 84606263804145973736641625)
      ·
        refine ⟨63454697853109480302481219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84606263804145973736641625 63454697853109480302481219)
        ·
          refine ⟨95182046779664220453721829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63454697853109480302481219 95182046779664220453721829)
          ·
            refine ⟨17846633771187041335072843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95182046779664220453721829 17846633771187041335072843)
            ·
              refine ⟨26769950656780562002609265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846633771187041335072843 26769950656780562002609265)
              ·
                refine ⟨20077462992585421501956949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26769950656780562002609265 20077462992585421501956949)
                ·
                  refine ⟨117641384722180204113029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20077462992585421501956949 117641384722180204113029)
                  ·
                    rfl

theorem cell23_2061952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_2061952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061952 prefixEnd_2061952 := by exact prefixLift 2061952
  have htrace : WordTrace (prefixWord ++ tailWord_2061952) baseStart_2061952 baseEnd_2061952 := by
    simpa [prefixWord, tailWord_2061952, baseEnd_2061952] using wordTrace_append hprefix tailTrace_2061952
  have hstable : (prefixWord ++ tailWord_2061952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061952).length < 2 ^ (prefixWord ++ tailWord_2061952).sum := by decide
  have hdescent : baseEnd_2061952 < baseStart_2061952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061959 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2061959 : Nat := 118140960795 + 2061959 * 2 ^ 59
def prefixEnd_2061959 : Nat := 4983230072969 + 3 ^ 40 * 2061959 * 2
def baseEnd_2061959 : Nat := 1058776056864203309629729

theorem tailTrace_2061959 : CollatzResearch.WordTrace tailWord_2061959 prefixEnd_2061959 1058776056864203309629729 := by
  unfold tailWord_2061959
  simp only [CollatzResearch.WordTrace]
  refine ⟨75205823136882172405852931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50137215424588114937235287 75205823136882172405852931)
  ·
    refine ⟨112808734705323258608779397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75205823136882172405852931 112808734705323258608779397)
    ·
      refine ⟨21151637757248110989146137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112808734705323258608779397 21151637757248110989146137)
      ·
        refine ⟨15863728317936083241859603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21151637757248110989146137 15863728317936083241859603)
        ·
          refine ⟨23795592476904124862789405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15863728317936083241859603 23795592476904124862789405)
          ·
            refine ⟨8923347178839046823546027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23795592476904124862789405 8923347178839046823546027)
            ·
              refine ⟨13385020768258570235319041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923347178839046823546027 13385020768258570235319041)
              ·
                refine ⟨10038765576193927676489281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13385020768258570235319041 10038765576193927676489281)
                ·
                  refine ⟨7529074182145445757366961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038765576193927676489281 7529074182145445757366961)
                  ·
                    refine ⟨5646805636609084318025221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7529074182145445757366961 5646805636609084318025221)
                    ·
                      refine ⟨1058776056864203309629729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5646805636609084318025221 1058776056864203309629729)
                      ·
                        rfl

theorem cell23_2061959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2061959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061959 prefixEnd_2061959 := by exact prefixLift 2061959
  have htrace : WordTrace (prefixWord ++ tailWord_2061959) baseStart_2061959 baseEnd_2061959 := by
    simpa [prefixWord, tailWord_2061959, baseEnd_2061959] using wordTrace_append hprefix tailTrace_2061959
  have hstable : (prefixWord ++ tailWord_2061959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061959).length < 2 ^ (prefixWord ++ tailWord_2061959).sum := by decide
  have hdescent : baseEnd_2061959 < baseStart_2061959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061980 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2061980 : Nat := 118140960795 + 2061980 * 2 ^ 59
def prefixEnd_2061980 : Nat := 4983230072969 + 3 ^ 40 * 2061980 * 2
def baseEnd_2061980 : Nat := 1058786839957947727467133

theorem tailTrace_2061980 : CollatzResearch.WordTrace tailWord_2061980 prefixEnd_2061980 1058786839957947727467133 := by
  unfold tailWord_2061980
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603294534903046496183697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50137726046537395328244929 37603294534903046496183697)
  ·
    refine ⟨28202470901177284872137773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37603294534903046496183697 28202470901177284872137773)
    ·
      refine ⟨10575926587941481827051665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28202470901177284872137773 10575926587941481827051665)
      ·
        refine ⟨7931944940956111370288749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10575926587941481827051665 7931944940956111370288749)
        ·
          refine ⟨2974479352858541763858281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7931944940956111370288749 2974479352858541763858281)
          ·
            refine ⟨2230859514643906322893711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974479352858541763858281 2230859514643906322893711)
            ·
              refine ⟨3346289271965859484340567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230859514643906322893711 3346289271965859484340567)
              ·
                refine ⟨5019433907948789226510851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346289271965859484340567 5019433907948789226510851)
                ·
                  refine ⟨7529150861923183839766277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019433907948789226510851 7529150861923183839766277)
                  ·
                    refine ⟨1411715786610596969956177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529150861923183839766277 1411715786610596969956177)
                    ·
                      refine ⟨1058786839957947727467133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411715786610596969956177 1058786839957947727467133)
                      ·
                        rfl

theorem cell23_2061980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2061980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061980 prefixEnd_2061980 := by exact prefixLift 2061980
  have htrace : WordTrace (prefixWord ++ tailWord_2061980) baseStart_2061980 baseEnd_2061980 := by
    simpa [prefixWord, tailWord_2061980, baseEnd_2061980] using wordTrace_append hprefix tailTrace_2061980
  have hstable : (prefixWord ++ tailWord_2061980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061980).length < 2 ^ (prefixWord ++ tailWord_2061980).sum := by decide
  have hdescent : baseEnd_2061980 < baseStart_2061980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061999 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 2, 5]
def baseStart_2061999 : Nat := 118140960795 + 2061999 * 2 ^ 59
def prefixEnd_2061999 : Nat := 4983230072969 + 3 ^ 40 * 2061999 * 2
def baseEnd_2061999 : Nat := 352932198696794384376515

theorem tailTrace_2061999 : CollatzResearch.WordTrace tailWord_2061999 prefixEnd_2061999 352932198696794384376515 := by
  unfold tailWord_2061999
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207282056737259237309051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50138188037824839491539367 75207282056737259237309051)
  ·
    refine ⟨112810923085105888855963577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207282056737259237309051 112810923085105888855963577)
    ·
      refine ⟨84608192313829416641972683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112810923085105888855963577 84608192313829416641972683)
      ·
        refine ⟨126912288470744124962959025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84608192313829416641972683 126912288470744124962959025)
        ·
          refine ⟨95184216353058093722219269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126912288470744124962959025 95184216353058093722219269)
          ·
            refine ⟨17847040566198392572916113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95184216353058093722219269 17847040566198392572916113)
            ·
              refine ⟨13385280424648794429687085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17847040566198392572916113 13385280424648794429687085)
              ·
                refine ⟨5019480159243297911132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13385280424648794429687085 5019480159243297911132657)
                ·
                  refine ⟨3764610119432473433349493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5019480159243297911132657 3764610119432473433349493)
                  ·
                    refine ⟨352932198696794384376515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3764610119432473433349493 352932198696794384376515)
                    ·
                      rfl

theorem cell23_2061999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_2061999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2061999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2061999 prefixEnd_2061999 := by exact prefixLift 2061999
  have htrace : WordTrace (prefixWord ++ tailWord_2061999) baseStart_2061999 baseEnd_2061999 := by
    simpa [prefixWord, tailWord_2061999, baseEnd_2061999] using wordTrace_append hprefix tailTrace_2061999
  have hstable : (prefixWord ++ tailWord_2061999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061999).length < 2 ^ (prefixWord ++ tailWord_2061999).sum := by decide
  have hdescent : baseEnd_2061999 < baseStart_2061999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062026 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2062026 : Nat := 118140960795 + 2062026 * 2 ^ 59
def prefixEnd_2062026 : Nat := 4983230072969 + 3 ^ 40 * 2062026 * 2
def baseEnd_2062026 : Nat := 1058810460068054547491921

theorem tailTrace_2062026 : CollatzResearch.WordTrace tailWord_2062026 prefixEnd_2062026 1058810460068054547491921 := by
  unfold tailWord_2062026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18802066706909860712135483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50138844551759628565694621 18802066706909860712135483)
  ·
    refine ⟨28203100060364791068203225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18802066706909860712135483 28203100060364791068203225)
    ·
      refine ⟨21152325045273593301152419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28203100060364791068203225 21152325045273593301152419)
      ·
        refine ⟨31728487567910389951728629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152325045273593301152419 31728487567910389951728629)
        ·
          refine ⟨2974545709491599057974559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31728487567910389951728629 2974545709491599057974559)
          ·
            refine ⟨4461818564237398586961839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974545709491599057974559 4461818564237398586961839)
            ·
              refine ⟨6692727846356097880442759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461818564237398586961839 6692727846356097880442759)
              ·
                refine ⟨10039091769534146820664139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692727846356097880442759 10039091769534146820664139)
                ·
                  refine ⟨15058637654301220230996209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039091769534146820664139 15058637654301220230996209)
                  ·
                    refine ⟨11293978240725915173247157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15058637654301220230996209 11293978240725915173247157)
                    ·
                      refine ⟨1058810460068054547491921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11293978240725915173247157 1058810460068054547491921)
                      ·
                        rfl

theorem cell23_2062026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2062026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062026 prefixEnd_2062026 := by exact prefixLift 2062026
  have htrace : WordTrace (prefixWord ++ tailWord_2062026) baseStart_2062026 baseEnd_2062026 := by
    simpa [prefixWord, tailWord_2062026, baseEnd_2062026] using wordTrace_append hprefix tailTrace_2062026
  have hstable : (prefixWord ++ tailWord_2062026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062026).length < 2 ^ (prefixWord ++ tailWord_2062026).sum := by decide
  have hdescent : baseEnd_2062026 < baseStart_2062026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062063 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 1, 4]
def baseStart_2062063 : Nat := 118140960795 + 2062063 * 2 ^ 59
def prefixEnd_2062063 : Nat := 4983230072969 + 3 ^ 40 * 2062063 * 2
def baseEnd_2062063 : Nat := 352943152950756967576417

theorem tailTrace_2062063 : CollatzResearch.WordTrace tailWord_2062063 prefixEnd_2062063 352943152950756967576417 := by
  unfold tailWord_2062063
  simp only [CollatzResearch.WordTrace]
  refine ⟨75209616328505398167638843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50139744219003598778425895 75209616328505398167638843)
  ·
    refine ⟨112814424492758097251458265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75209616328505398167638843 112814424492758097251458265)
    ·
      refine ⟨84610818369568572938593699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112814424492758097251458265 84610818369568572938593699)
      ·
        refine ⟨126916227554352859407890549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84610818369568572938593699 126916227554352859407890549)
        ·
          refine ⟨11898396333220580569489739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126916227554352859407890549 11898396333220580569489739)
          ·
            refine ⟨17847594499830870854234609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898396333220580569489739 17847594499830870854234609)
            ·
              refine ⟨13385695874873153140675957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17847594499830870854234609 13385695874873153140675957)
              ·
                refine ⟨1254908988269358106938371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13385695874873153140675957 1254908988269358106938371)
                ·
                  refine ⟨1882363482404037160407557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254908988269358106938371 1882363482404037160407557)
                  ·
                    refine ⟨352943152950756967576417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882363482404037160407557 352943152950756967576417)
                    ·
                      rfl

theorem cell23_2062063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_2062063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062063 prefixEnd_2062063 := by exact prefixLift 2062063
  have htrace : WordTrace (prefixWord ++ tailWord_2062063) baseStart_2062063 baseEnd_2062063 := by
    simpa [prefixWord, tailWord_2062063, baseEnd_2062063] using wordTrace_append hprefix tailTrace_2062063
  have hstable : (prefixWord ++ tailWord_2062063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062063).length < 2 ^ (prefixWord ++ tailWord_2062063).sum := by decide
  have hdescent : baseEnd_2062063 < baseStart_2062063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062076 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 6]
def baseStart_2062076 : Nat := 118140960795 + 2062076 * 2 ^ 59
def prefixEnd_2062076 : Nat := 4983230072969 + 3 ^ 40 * 2062076 * 2
def baseEnd_2062076 : Nat := 117648459344531039096299

theorem tailTrace_2062076 : CollatzResearch.WordTrace tailWord_2062076 prefixEnd_2062076 117648459344531039096299 := by
  unfold tailWord_2062076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37605045238729150693931041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50140060318305534258574721 37605045238729150693931041)
  ·
    refine ⟨28203783929046863020448281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37605045238729150693931041 28203783929046863020448281)
    ·
      refine ⟨21152837946785147265336211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28203783929046863020448281 21152837946785147265336211)
      ·
        refine ⟨31729256920177720898004317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152837946785147265336211 31729256920177720898004317)
        ·
          refine ⟨11898471345066645336751619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31729256920177720898004317 11898471345066645336751619)
          ·
            refine ⟨17847707017599968005127429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898471345066645336751619 17847707017599968005127429)
            ·
              refine ⟨3346445065799994000961393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17847707017599968005127429 3346445065799994000961393)
              ·
                refine ⟨2509833799349995500721045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346445065799994000961393 2509833799349995500721045)
                ·
                  refine ⟨117648459344531039096299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2509833799349995500721045 117648459344531039096299)
                  ·
                    rfl

theorem cell23_2062076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_2062076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062076 prefixEnd_2062076 := by exact prefixLift 2062076
  have htrace : WordTrace (prefixWord ++ tailWord_2062076) baseStart_2062076 baseEnd_2062076 := by
    simpa [prefixWord, tailWord_2062076, baseEnd_2062076] using wordTrace_append hprefix tailTrace_2062076
  have hstable : (prefixWord ++ tailWord_2062076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062076).length < 2 ^ (prefixWord ++ tailWord_2062076).sum := by decide
  have hdescent : baseEnd_2062076 < baseStart_2062076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062103 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2062103 : Nat := 118140960795 + 2062103 * 2 ^ 59
def prefixEnd_2062103 : Nat := 4983230072969 + 3 ^ 40 * 2062103 * 2
def baseEnd_2062103 : Nat := 1058849998078450746229067

theorem tailTrace_2062103 : CollatzResearch.WordTrace tailWord_2062103 prefixEnd_2062103 1058849998078450746229067 := by
  unfold tailWord_2062103
  simp only [CollatzResearch.WordTrace]
  refine ⟨75211075248360484999094963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50140716832240323332729975 75211075248360484999094963)
  ·
    refine ⟨112816612872540727498642445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75211075248360484999094963 112816612872540727498642445)
    ·
      refine ⟨42306229827202772811990917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112816612872540727498642445 42306229827202772811990917)
      ·
        refine ⟨7932418092600519902248297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42306229827202772811990917 7932418092600519902248297)
        ·
          refine ⟨5949313569450389926686223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932418092600519902248297 5949313569450389926686223)
          ·
            refine ⟨8923970354175584890029335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949313569450389926686223 8923970354175584890029335)
            ·
              refine ⟨13385955531263377335044003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923970354175584890029335 13385955531263377335044003)
              ·
                refine ⟨20078933296895066002566005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385955531263377335044003 20078933296895066002566005)
                ·
                  refine ⟨1882399996583912437740563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20078933296895066002566005 1882399996583912437740563)
                  ·
                    refine ⟨2823599994875868656610845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882399996583912437740563 2823599994875868656610845)
                    ·
                      refine ⟨1058849998078450746229067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2823599994875868656610845 1058849998078450746229067)
                      ·
                        rfl

theorem cell23_2062103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2062103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062103 prefixEnd_2062103 := by exact prefixLift 2062103
  have htrace : WordTrace (prefixWord ++ tailWord_2062103) baseStart_2062103 baseEnd_2062103 := by
    simpa [prefixWord, tailWord_2062103, baseEnd_2062103] using wordTrace_append hprefix tailTrace_2062103
  have hstable : (prefixWord ++ tailWord_2062103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062103).length < 2 ^ (prefixWord ++ tailWord_2062103).sum := by decide
  have hdescent : baseEnd_2062103 < baseStart_2062103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062106 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_2062106 : Nat := 118140960795 + 2062106 * 2 ^ 59
def prefixEnd_2062106 : Nat := 4983230072969 + 3 ^ 40 * 2062106 * 2
def baseEnd_2062106 : Nat := 352950512840138078163851

theorem tailTrace_2062106 : CollatzResearch.WordTrace tailWord_2062106 prefixEnd_2062106 352950512840138078163851 := by
  unfold tailWord_2062106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18802796166837404127863543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50140789778233077674302781 18802796166837404127863543)
  ·
    refine ⟨28204194250256106191795315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18802796166837404127863543 28204194250256106191795315)
    ·
      refine ⟨42306291375384159287692973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28204194250256106191795315 42306291375384159287692973)
      ·
        refine ⟨15864859265769059732884865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42306291375384159287692973 15864859265769059732884865)
        ·
          refine ⟨11898644449326794799663649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15864859265769059732884865 11898644449326794799663649)
          ·
            refine ⟨8923983336995096099747737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898644449326794799663649 8923983336995096099747737)
            ·
              refine ⟨6692987502746322074810803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923983336995096099747737 6692987502746322074810803)
              ·
                refine ⟨10039481254119483112216205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692987502746322074810803 10039481254119483112216205)
                ·
                  refine ⟨3764805470294806167081077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10039481254119483112216205 3764805470294806167081077)
                  ·
                    refine ⟨352950512840138078163851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3764805470294806167081077 352950512840138078163851)
                    ·
                      rfl

theorem cell23_2062106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_2062106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062106 prefixEnd_2062106 := by exact prefixLift 2062106
  have htrace : WordTrace (prefixWord ++ tailWord_2062106) baseStart_2062106 baseEnd_2062106 := by
    simpa [prefixWord, tailWord_2062106, baseEnd_2062106] using wordTrace_append hprefix tailTrace_2062106
  have hstable : (prefixWord ++ tailWord_2062106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062106).length < 2 ^ (prefixWord ++ tailWord_2062106).sum := by decide
  have hdescent : baseEnd_2062106 < baseStart_2062106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062113 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2062113 : Nat := 118140960795 + 2062113 * 2 ^ 59
def prefixEnd_2062113 : Nat := 4983230072969 + 3 ^ 40 * 2062113 * 2
def baseEnd_2062113 : Nat := 1058855132884995707104021

theorem tailTrace_2062113 : CollatzResearch.WordTrace tailWord_2062113 prefixEnd_2062113 1058855132884995707104021 := by
  unfold tailWord_2062113
  simp only [CollatzResearch.WordTrace]
  refine ⟨75211439978324256706958993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50140959985549504471305995 75211439978324256706958993)
  ·
    refine ⟨56408579983743192530219245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75211439978324256706958993 56408579983743192530219245)
    ·
      refine ⟨21153217493903697198832217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56408579983743192530219245 21153217493903697198832217)
      ·
        refine ⟨15864913120427772899124163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21153217493903697198832217 15864913120427772899124163)
        ·
          refine ⟨23797369680641659348686245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864913120427772899124163 23797369680641659348686245)
          ·
            refine ⟨4462006815120311127878671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23797369680641659348686245 4462006815120311127878671)
            ·
              refine ⟨6693010222680466691818007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462006815120311127878671 6693010222680466691818007)
              ·
                refine ⟨10039515334020700037727011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693010222680466691818007 10039515334020700037727011)
                ·
                  refine ⟨15059273001031050056590517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039515334020700037727011 15059273001031050056590517)
                  ·
                    refine ⟨1411806843846660942805361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15059273001031050056590517 1411806843846660942805361)
                    ·
                      refine ⟨1058855132884995707104021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411806843846660942805361 1058855132884995707104021)
                      ·
                        rfl

theorem cell23_2062113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2062113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062113 prefixEnd_2062113 := by exact prefixLift 2062113
  have htrace : WordTrace (prefixWord ++ tailWord_2062113) baseStart_2062113 baseEnd_2062113 := by
    simpa [prefixWord, tailWord_2062113, baseEnd_2062113] using wordTrace_append hprefix tailTrace_2062113
  have hstable : (prefixWord ++ tailWord_2062113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062113).length < 2 ^ (prefixWord ++ tailWord_2062113).sum := by decide
  have hdescent : baseEnd_2062113 < baseStart_2062113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062137 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2062137 : Nat := 118140960795 + 2062137 * 2 ^ 59
def prefixEnd_2062137 : Nat := 4983230072969 + 3 ^ 40 * 2062137 * 2
def baseEnd_2062137 : Nat := 1058867456420703613203911

theorem tailTrace_2062137 : CollatzResearch.WordTrace tailWord_2062137 prefixEnd_2062137 1058867456420703613203911 := by
  unfold tailWord_2062137
  simp only [CollatzResearch.WordTrace]
  refine ⟨75212315330237308805832665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50141543553491539203888443 75212315330237308805832665)
  ·
    refine ⟨56409236497677981604374499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75212315330237308805832665 56409236497677981604374499)
    ·
      refine ⟨84613854746516972406561749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56409236497677981604374499 84613854746516972406561749)
      ·
        refine ⟨1983137220621491540778791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84613854746516972406561749 1983137220621491540778791)
        ·
          refine ⟨2974705830932237311168187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983137220621491540778791 2974705830932237311168187)
          ·
            refine ⟨4462058746398355966752281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974705830932237311168187 4462058746398355966752281)
            ·
              refine ⟨3346544059798766975064211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462058746398355966752281 3346544059798766975064211)
              ·
                refine ⟨5019816089698150462596317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346544059798766975064211 5019816089698150462596317)
                ·
                  refine ⟨1882431033636806423473619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5019816089698150462596317 1882431033636806423473619)
                  ·
                    refine ⟨2823646550455209635210429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882431033636806423473619 2823646550455209635210429)
                    ·
                      refine ⟨1058867456420703613203911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2823646550455209635210429 1058867456420703613203911)
                      ·
                        rfl

theorem cell23_2062137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2062137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062137 prefixEnd_2062137 := by exact prefixLift 2062137
  have htrace : WordTrace (prefixWord ++ tailWord_2062137) baseStart_2062137 baseEnd_2062137 := by
    simpa [prefixWord, tailWord_2062137, baseEnd_2062137] using wordTrace_append hprefix tailTrace_2062137
  have hstable : (prefixWord ++ tailWord_2062137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062137).length < 2 ^ (prefixWord ++ tailWord_2062137).sum := by decide
  have hdescent : baseEnd_2062137 < baseStart_2062137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062149 : List Nat := [1, 3, 1, 1, 1, 2, 4, 10]
def baseStart_2062149 : Nat := 118140960795 + 2062149 * 2 ^ 59
def prefixEnd_2062149 : Nat := 4983230072969 + 3 ^ 40 * 2062149 * 2
def baseEnd_2062149 : Nat := 39217541414391020972365

theorem tailTrace_2062149 : CollatzResearch.WordTrace tailWord_2062149 prefixEnd_2062149 39217541414391020972365 := by
  unfold tailWord_2062149
  simp only [CollatzResearch.WordTrace]
  refine ⟨75212753006193834855269501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50141835337462556570179667 75212753006193834855269501)
  ·
    refine ⟨28204782377322688070726063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75212753006193834855269501 28204782377322688070726063)
    ·
      refine ⟨42307173565984032106089095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28204782377322688070726063 42307173565984032106089095)
      ·
        refine ⟨63460760348976048159133643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42307173565984032106089095 63460760348976048159133643)
        ·
          refine ⟨95191140523464072238700465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63460760348976048159133643 95191140523464072238700465)
          ·
            refine ⟨71393355392598054179025349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95191140523464072238700465 71393355392598054179025349)
            ·
              refine ⟨13386254136112135158567253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71393355392598054179025349 13386254136112135158567253)
              ·
                refine ⟨39217541414391020972365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13386254136112135158567253 39217541414391020972365)
                ·
                  rfl

theorem cell23_2062149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 10].length) (baseStart_2062149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062149 prefixEnd_2062149 := by exact prefixLift 2062149
  have htrace : WordTrace (prefixWord ++ tailWord_2062149) baseStart_2062149 baseEnd_2062149 := by
    simpa [prefixWord, tailWord_2062149, baseEnd_2062149] using wordTrace_append hprefix tailTrace_2062149
  have hstable : (prefixWord ++ tailWord_2062149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062149).length < 2 ^ (prefixWord ++ tailWord_2062149).sum := by decide
  have hdescent : baseEnd_2062149 < baseStart_2062149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062193 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_2062193 : Nat := 118140960795 + 2062193 * 2 ^ 59
def prefixEnd_2062193 : Nat := 4983230072969 + 3 ^ 40 * 2062193 * 2
def baseEnd_2062193 : Nat := 1058896211337355394103653

theorem tailTrace_2062193 : CollatzResearch.WordTrace tailWord_2062193 prefixEnd_2062193 1058896211337355394103653 := by
  unfold tailWord_2062193
  simp only [CollatzResearch.WordTrace]
  refine ⟨75214357818034430369871233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50142905212022953579914155 75214357818034430369871233)
  ·
    refine ⟨56410768363525822777403425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75214357818034430369871233 56410768363525822777403425)
    ·
      refine ⟨42308076272644367083052569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56410768363525822777403425 42308076272644367083052569)
      ·
        refine ⟨31731057204483275312289427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42308076272644367083052569 31731057204483275312289427)
        ·
          refine ⟨47596585806724912968434141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731057204483275312289427 47596585806724912968434141)
          ·
            refine ⟨17848719677521842363162803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47596585806724912968434141 17848719677521842363162803)
            ·
              refine ⟨26773079516282763544744205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17848719677521842363162803 26773079516282763544744205)
              ·
                refine ⟨10039904818606036329279077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26773079516282763544744205 10039904818606036329279077)
                ·
                  refine ⟨1882482153488631811739827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10039904818606036329279077 1882482153488631811739827)
                  ·
                    refine ⟨2823723230232947717609741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882482153488631811739827 2823723230232947717609741)
                    ·
                      refine ⟨1058896211337355394103653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2823723230232947717609741 1058896211337355394103653)
                      ·
                        rfl

theorem cell23_2062193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_2062193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062193 prefixEnd_2062193 := by exact prefixLift 2062193
  have htrace : WordTrace (prefixWord ++ tailWord_2062193) baseStart_2062193 baseEnd_2062193 := by
    simpa [prefixWord, tailWord_2062193, baseEnd_2062193] using wordTrace_append hprefix tailTrace_2062193
  have hstable : (prefixWord ++ tailWord_2062193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062193).length < 2 ^ (prefixWord ++ tailWord_2062193).sum := by decide
  have hdescent : baseEnd_2062193 < baseStart_2062193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 3, 3, 2]
def baseStart_2062203 : Nat := 118140960795 + 2062203 * 2 ^ 59
def prefixEnd_2062203 : Nat := 4983230072969 + 3 ^ 40 * 2062203 * 2
def baseEnd_2062203 : Nat := 1058901346143900354978607

theorem tailTrace_2062203 : CollatzResearch.WordTrace tailWord_2062203 prefixEnd_2062203 1058901346143900354978607 := by
  unfold tailWord_2062203
  simp only [CollatzResearch.WordTrace]
  refine ⟨75214722547998202077735263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50143148365332134718490175 75214722547998202077735263)
  ·
    refine ⟨112822083821997303116602895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75214722547998202077735263 112822083821997303116602895)
    ·
      refine ⟨169233125732995954674904343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112822083821997303116602895 169233125732995954674904343)
      ·
        refine ⟨253849688599493932012356515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169233125732995954674904343 253849688599493932012356515)
        ·
          refine ⟨380774532899240898018534773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253849688599493932012356515 380774532899240898018534773)
          ·
            refine ⟨35697612459303834189237635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380774532899240898018534773 35697612459303834189237635)
            ·
              refine ⟨53546418688955751283856453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35697612459303834189237635 53546418688955751283856453)
              ·
                refine ⟨10039953504179203365723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53546418688955751283856453 10039953504179203365723085)
                ·
                  refine ⟨3764982564067201262146157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10039953504179203365723085 3764982564067201262146157)
                  ·
                    refine ⟨1411868461525200473304809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3764982564067201262146157 1411868461525200473304809)
                    ·
                      refine ⟨1058901346143900354978607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411868461525200473304809 1058901346143900354978607)
                      ·
                        rfl

theorem cell23_2062203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3, 2].length) (baseStart_2062203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062203 prefixEnd_2062203 := by exact prefixLift 2062203
  have htrace : WordTrace (prefixWord ++ tailWord_2062203) baseStart_2062203 baseEnd_2062203 := by
    simpa [prefixWord, tailWord_2062203, baseEnd_2062203] using wordTrace_append hprefix tailTrace_2062203
  have hstable : (prefixWord ++ tailWord_2062203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062203).length < 2 ^ (prefixWord ++ tailWord_2062203).sum := by decide
  have hdescent : baseEnd_2062203 < baseStart_2062203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062233 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 4, 2]
def baseStart_2062233 : Nat := 118140960795 + 2062233 * 2 ^ 59
def prefixEnd_2062233 : Nat := 4983230072969 + 3 ^ 40 * 2062233 * 2
def baseEnd_2062233 : Nat := 1058916750563535237603469

theorem tailTrace_2062233 : CollatzResearch.WordTrace tailWord_2062233 prefixEnd_2062233 1058916750563535237603469 := by
  unfold tailWord_2062233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75215816737889517201327353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50143877825259678134218235 75215816737889517201327353)
  ·
    refine ⟨56411862553417137900995515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75215816737889517201327353 56411862553417137900995515)
    ·
      refine ⟨84617793830125706851493273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56411862553417137900995515 84617793830125706851493273)
      ·
        refine ⟨63463345372594280138619955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84617793830125706851493273 63463345372594280138619955)
        ·
          refine ⟨95195018058891420207929933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63463345372594280138619955 95195018058891420207929933)
          ·
            refine ⟨35698131772084282577973725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95195018058891420207929933 35698131772084282577973725)
            ·
              refine ⟨13386799414531605966740147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35698131772084282577973725 13386799414531605966740147)
              ·
                refine ⟨20080199121797408950110221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13386799414531605966740147 20080199121797408950110221)
                ·
                  refine ⟨7530074670674028356291333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20080199121797408950110221 7530074670674028356291333)
                  ·
                    refine ⟨1411889000751380316804625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530074670674028356291333 1411889000751380316804625)
                    ·
                      refine ⟨1058916750563535237603469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411889000751380316804625 1058916750563535237603469)
                      ·
                        rfl

theorem cell23_2062233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_2062233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062233 prefixEnd_2062233 := by exact prefixLift 2062233
  have htrace : WordTrace (prefixWord ++ tailWord_2062233) baseStart_2062233 baseEnd_2062233 := by
    simpa [prefixWord, tailWord_2062233, baseEnd_2062233] using wordTrace_append hprefix tailTrace_2062233
  have hstable : (prefixWord ++ tailWord_2062233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062233).length < 2 ^ (prefixWord ++ tailWord_2062233).sum := by decide
  have hdescent : baseEnd_2062233 < baseStart_2062233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062301 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_2062301 : Nat := 118140960795 + 2062301 * 2 ^ 59
def prefixEnd_2062301 : Nat := 4983230072969 + 3 ^ 40 * 2062301 * 2
def baseEnd_2062301 : Nat := 1058951667248040971553157

theorem tailTrace_2062301 : CollatzResearch.WordTrace tailWord_2062301 prefixEnd_2062301 1058951667248040971553157 := by
  unfold tailWord_2062301
  simp only [CollatzResearch.WordTrace]
  refine ⟨75218296901643164814802757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50145531267762109876535171 75218296901643164814802757)
  ·
    refine ⟨14103430669058093402775517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75218296901643164814802757 14103430669058093402775517)
    ·
      refine ⟨5288786500896785026040819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14103430669058093402775517 5288786500896785026040819)
      ·
        refine ⟨7933179751345177539061229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288786500896785026040819 7933179751345177539061229)
        ·
          refine ⟨2974942406754441577147961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7933179751345177539061229 2974942406754441577147961)
          ·
            refine ⟨2231206805065831182860971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974942406754441577147961 2231206805065831182860971)
            ·
              refine ⟨3346810207598746774291457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231206805065831182860971 3346810207598746774291457)
              ·
                refine ⟨2510107655699060080718593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346810207598746774291457 2510107655699060080718593)
                ·
                  refine ⟨1882580741774295060538945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2510107655699060080718593 1882580741774295060538945)
                  ·
                    refine ⟨1411935556330721295404209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1882580741774295060538945 1411935556330721295404209)
                    ·
                      refine ⟨1058951667248040971553157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1411935556330721295404209 1058951667248040971553157)
                      ·
                        rfl

theorem cell23_2062301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_2062301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062301 prefixEnd_2062301 := by exact prefixLift 2062301
  have htrace : WordTrace (prefixWord ++ tailWord_2062301) baseStart_2062301 baseEnd_2062301 := by
    simpa [prefixWord, tailWord_2062301, baseEnd_2062301] using wordTrace_append hprefix tailTrace_2062301
  have hstable : (prefixWord ++ tailWord_2062301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062301).length < 2 ^ (prefixWord ++ tailWord_2062301).sum := by decide
  have hdescent : baseEnd_2062301 < baseStart_2062301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062336 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_2062336 : Nat := 118140960795 + 2062336 * 2 ^ 59
def prefixEnd_2062336 : Nat := 4983230072969 + 3 ^ 40 * 2062336 * 2
def baseEnd_2062336 : Nat := 1058969639070948334615495

theorem tailTrace_2062336 : CollatzResearch.WordTrace tailWord_2062336 prefixEnd_2062336 1058969639070948334615495 := by
  unfold tailWord_2062336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37609786728258182896163431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50146382304344243861551241 37609786728258182896163431)
  ·
    refine ⟨56414680092387274344245147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37609786728258182896163431 56414680092387274344245147)
    ·
      refine ⟨84622020138580911516367721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56414680092387274344245147 84622020138580911516367721)
      ·
        refine ⟨63466515103935683637275791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84622020138580911516367721 63466515103935683637275791)
        ·
          refine ⟨95199772655903525455913687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63466515103935683637275791 95199772655903525455913687)
          ·
            refine ⟨142799658983855288183870531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95199772655903525455913687 142799658983855288183870531)
            ·
              refine ⟨214199488475782932275805797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142799658983855288183870531 214199488475782932275805797)
              ·
                refine ⟨40162404089209299801713587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214199488475782932275805797 40162404089209299801713587)
                ·
                  refine ⟨60243606133813949702570381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40162404089209299801713587 60243606133813949702570381)
                  ·
                    refine ⟨22591352300180231138463893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60243606133813949702570381 22591352300180231138463893)
                    ·
                      refine ⟨1058969639070948334615495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22591352300180231138463893 1058969639070948334615495)
                      ·
                        rfl

theorem cell23_2062336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_2062336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062336 prefixEnd_2062336 := by exact prefixLift 2062336
  have htrace : WordTrace (prefixWord ++ tailWord_2062336) baseStart_2062336 baseEnd_2062336 := by
    simpa [prefixWord, tailWord_2062336, baseEnd_2062336] using wordTrace_append hprefix tailTrace_2062336
  have hstable : (prefixWord ++ tailWord_2062336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062336).length < 2 ^ (prefixWord ++ tailWord_2062336).sum := by decide
  have hdescent : baseEnd_2062336 < baseStart_2062336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062360 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2062360 : Nat := 118140960795 + 2062360 * 2 ^ 59
def prefixEnd_2062360 : Nat := 4983230072969 + 3 ^ 40 * 2062360 * 2
def baseEnd_2062360 : Nat := 1058981962606656240715385

theorem tailTrace_2062360 : CollatzResearch.WordTrace tailWord_2062360 prefixEnd_2062360 1058981962606656240715385 := by
  unfold tailWord_2062360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37610224404214708945600267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50146965872286278594133689 37610224404214708945600267)
  ·
    refine ⟨56415336606322063418400401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37610224404214708945600267 56415336606322063418400401)
    ·
      refine ⟨42311502454741547563800301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56415336606322063418400401 42311502454741547563800301)
      ·
        refine ⟨15866813420528080336425113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42311502454741547563800301 15866813420528080336425113)
        ·
          refine ⟨11900110065396060252318835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15866813420528080336425113 11900110065396060252318835)
          ·
            refine ⟨17850165098094090378478253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900110065396060252318835 17850165098094090378478253)
            ·
              refine ⟨6693811911785283891929345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17850165098094090378478253 6693811911785283891929345)
              ·
                refine ⟨5020358933838962918947009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6693811911785283891929345 5020358933838962918947009)
                ·
                  refine ⟨3765269200379222189210257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5020358933838962918947009 3765269200379222189210257)
                  ·
                    refine ⟨2823951900284416641907693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765269200379222189210257 2823951900284416641907693)
                    ·
                      refine ⟨1058981962606656240715385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2823951900284416641907693 1058981962606656240715385)
                      ·
                        rfl

theorem cell23_2062360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2062360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062360 prefixEnd_2062360 := by exact prefixLift 2062360
  have htrace : WordTrace (prefixWord ++ tailWord_2062360) baseStart_2062360 baseEnd_2062360 := by
    simpa [prefixWord, tailWord_2062360, baseEnd_2062360] using wordTrace_append hprefix tailTrace_2062360
  have hstable : (prefixWord ++ tailWord_2062360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062360).length < 2 ^ (prefixWord ++ tailWord_2062360).sum := by decide
  have hdescent : baseEnd_2062360 < baseStart_2062360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062418 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2062418 : Nat := 118140960795 + 2062418 * 2 ^ 59
def prefixEnd_2062418 : Nat := 4983230072969 + 3 ^ 40 * 2062418 * 2
def baseEnd_2062418 : Nat := 353003914828205671263373

theorem tailTrace_2062418 : CollatzResearch.WordTrace tailWord_2062418 prefixEnd_2062418 353003914828205671263373 := by
  unfold tailWord_2062418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805641060554823449202977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50148376161479529197874605 18805641060554823449202977)
  ·
    refine ⟨14104230795416117586902233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18805641060554823449202977 14104230795416117586902233)
    ·
      refine ⟨10578173096562088190176675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14104230795416117586902233 10578173096562088190176675)
      ·
        refine ⟨15867259644843132285265013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578173096562088190176675 15867259644843132285265013)
        ·
          refine ⟨1487555591704043651743595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15867259644843132285265013 1487555591704043651743595)
          ·
            refine ⟨2231333387556065477615393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487555591704043651743595 2231333387556065477615393)
            ·
              refine ⟨1673500040667049108211545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231333387556065477615393 1673500040667049108211545)
              ·
                refine ⟨1255125030500286831158659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673500040667049108211545 1255125030500286831158659)
                ·
                  refine ⟨1882687545750430246737989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255125030500286831158659 1882687545750430246737989)
                  ·
                    refine ⟨353003914828205671263373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882687545750430246737989 353003914828205671263373)
                    ·
                      rfl

theorem cell23_2062418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2062418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062418 prefixEnd_2062418 := by exact prefixLift 2062418
  have htrace : WordTrace (prefixWord ++ tailWord_2062418) baseStart_2062418 baseEnd_2062418 := by
    simpa [prefixWord, tailWord_2062418, baseEnd_2062418] using wordTrace_append hprefix tailTrace_2062418
  have hstable : (prefixWord ++ tailWord_2062418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062418).length < 2 ^ (prefixWord ++ tailWord_2062418).sum := by decide
  have hdescent : baseEnd_2062418 < baseStart_2062418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062424 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_2062424 : Nat := 118140960795 + 2062424 * 2 ^ 59
def prefixEnd_2062424 : Nat := 4983230072969 + 3 ^ 40 * 2062424 * 2
def baseEnd_2062424 : Nat := 1059014825368543990315091

theorem tailTrace_2062424 : CollatzResearch.WordTrace tailWord_2062424 prefixEnd_2062424 1059014825368543990315091 := by
  unfold tailWord_2062424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37611391540098778410765163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50148522053465037881020217 37611391540098778410765163)
  ·
    refine ⟨56417087310148167616147745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37611391540098778410765163 56417087310148167616147745)
    ·
      refine ⟨42312815482611125712110809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56417087310148167616147745 42312815482611125712110809)
      ·
        refine ⟨31734611611958344284083107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42312815482611125712110809 31734611611958344284083107)
        ·
          refine ⟨47601917417937516426124661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31734611611958344284083107 47601917417937516426124661)
          ·
            refine ⟨4462679757931642164949187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47601917417937516426124661 4462679757931642164949187)
            ·
              refine ⟨6694019636897463247423781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462679757931642164949187 6694019636897463247423781)
              ·
                refine ⟨1255128681918274358891959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6694019636897463247423781 1255128681918274358891959)
                ·
                  refine ⟨1882693022877411538337939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255128681918274358891959 1882693022877411538337939)
                  ·
                    refine ⟨2824039534316117307506909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1882693022877411538337939 2824039534316117307506909)
                    ·
                      refine ⟨1059014825368543990315091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824039534316117307506909 1059014825368543990315091)
                      ·
                        rfl

theorem cell23_2062424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_2062424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062424 prefixEnd_2062424 := by exact prefixLift 2062424
  have htrace : WordTrace (prefixWord ++ tailWord_2062424) baseStart_2062424 baseEnd_2062424 := by
    simpa [prefixWord, tailWord_2062424, baseEnd_2062424] using wordTrace_append hprefix tailTrace_2062424
  have hstable : (prefixWord ++ tailWord_2062424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062424).length < 2 ^ (prefixWord ++ tailWord_2062424).sum := by decide
  have hdescent : baseEnd_2062424 < baseStart_2062424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2062433 : Nat := 118140960795 + 2062433 * 2 ^ 59
def prefixEnd_2062433 : Nat := 4983230072969 + 3 ^ 40 * 2062433 * 2
def baseEnd_2062433 : Nat := 1059019446694434455102549

theorem tailTrace_2062433 : CollatzResearch.WordTrace tailWord_2062433 prefixEnd_2062433 1059019446694434455102549 := by
  unfold tailWord_2062433
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223111337164951358607953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50148740891443300905738635 75223111337164951358607953)
  ·
    refine ⟨56417333502873713518955965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75223111337164951358607953 56417333502873713518955965)
    ·
      refine ⟨21156500063577642569608487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56417333502873713518955965 21156500063577642569608487)
      ·
        refine ⟨31734750095366463854412731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156500063577642569608487 31734750095366463854412731)
        ·
          refine ⟨47602125143049695781619097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31734750095366463854412731 47602125143049695781619097)
          ·
            refine ⟨35701593857287271836214323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47602125143049695781619097 35701593857287271836214323)
            ·
              refine ⟨53552390785930907754321485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35701593857287271836214323 53552390785930907754321485)
              ·
                refine ⟨20082146544724090407870557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53552390785930907754321485 20082146544724090407870557)
                ·
                  refine ⟨7530804954271533902951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20082146544724090407870557 7530804954271533902951459)
                  ·
                    refine ⟨11296207431407300854427189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530804954271533902951459 11296207431407300854427189)
                    ·
                      refine ⟨1059019446694434455102549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11296207431407300854427189 1059019446694434455102549)
                      ·
                        rfl

theorem cell23_2062433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2062433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062433 prefixEnd_2062433 := by exact prefixLift 2062433
  have htrace : WordTrace (prefixWord ++ tailWord_2062433) baseStart_2062433 baseEnd_2062433 := by
    simpa [prefixWord, tailWord_2062433, baseEnd_2062433] using wordTrace_append hprefix tailTrace_2062433
  have hstable : (prefixWord ++ tailWord_2062433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062433).length < 2 ^ (prefixWord ++ tailWord_2062433).sum := by decide
  have hdescent : baseEnd_2062433 < baseStart_2062433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062447 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 5, 2, 2]
def baseStart_2062447 : Nat := 118140960795 + 2062447 * 2 ^ 59
def prefixEnd_2062447 : Nat := 4983230072969 + 3 ^ 40 * 2062447 * 2
def baseEnd_2062447 : Nat := 1059026635423597400327485

theorem tailTrace_2062447 : CollatzResearch.WordTrace tailWord_2062447 prefixEnd_2062447 1059026635423597400327485 := by
  unfold tailWord_2062447
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223621959114231749617595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50149081306076154499745063 75223621959114231749617595)
  ·
    refine ⟨112835432938671347624426393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75223621959114231749617595 112835432938671347624426393)
    ·
      refine ⟨84626574704003510718319795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112835432938671347624426393 84626574704003510718319795)
      ·
        refine ⟨126939862056005266077479693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84626574704003510718319795 126939862056005266077479693)
        ·
          refine ⟨47602448271001974779054885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126939862056005266077479693 47602448271001974779054885)
          ·
            refine ⟨8925459050812870271072791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47602448271001974779054885 8925459050812870271072791)
            ·
              refine ⟨13388188576219305406609187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925459050812870271072791 13388188576219305406609187)
              ·
                refine ⟨20082282864328958109913781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388188576219305406609187 20082282864328958109913781)
                ·
                  refine ⟨1882714018530839822804417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20082282864328958109913781 1882714018530839822804417)
                  ·
                    refine ⟨1412035513898129867103313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1882714018530839822804417 1412035513898129867103313)
                    ·
                      refine ⟨1059026635423597400327485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412035513898129867103313 1059026635423597400327485)
                      ·
                        rfl

theorem cell23_2062447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2, 2].length) (baseStart_2062447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062447 prefixEnd_2062447 := by exact prefixLift 2062447
  have htrace : WordTrace (prefixWord ++ tailWord_2062447) baseStart_2062447 baseEnd_2062447 := by
    simpa [prefixWord, tailWord_2062447, baseEnd_2062447] using wordTrace_append hprefix tailTrace_2062447
  have hstable : (prefixWord ++ tailWord_2062447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062447).length < 2 ^ (prefixWord ++ tailWord_2062447).sum := by decide
  have hdescent : baseEnd_2062447 < baseStart_2062447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062460 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_2062460 : Nat := 118140960795 + 2062460 * 2 ^ 59
def prefixEnd_2062460 : Nat := 4983230072969 + 3 ^ 40 * 2062460 * 2
def baseEnd_2062460 : Nat := 1059033310672105849464925

theorem tailTrace_2062460 : CollatzResearch.WordTrace tailWord_2062460 prefixEnd_2062460 1059033310672105849464925 := by
  unfold tailWord_2062460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612048054033567484920417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50149397405378089979893889 37612048054033567484920417)
  ·
    refine ⟨28209036040525175613690313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37612048054033567484920417 28209036040525175613690313)
    ·
      refine ⟨21156777030393881710267735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28209036040525175613690313 21156777030393881710267735)
      ·
        refine ⟨31735165545590822565401603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156777030393881710267735 31735165545590822565401603)
        ·
          refine ⟨47602748318386233848102405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31735165545590822565401603 47602748318386233848102405)
          ·
            refine ⟨8925515309697418846519201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47602748318386233848102405 8925515309697418846519201)
            ·
              refine ⟨6694136482273064134889401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8925515309697418846519201 6694136482273064134889401)
              ·
                refine ⟨5020602361704798101167051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694136482273064134889401 5020602361704798101167051)
                ·
                  refine ⟨7530903542557197151750577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020602361704798101167051 7530903542557197151750577)
                  ·
                    refine ⟨5648177656917897863812933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530903542557197151750577 5648177656917897863812933)
                    ·
                      refine ⟨1059033310672105849464925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5648177656917897863812933 1059033310672105849464925)
                      ·
                        rfl

theorem cell23_2062460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_2062460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062460 prefixEnd_2062460 := by exact prefixLift 2062460
  have htrace : WordTrace (prefixWord ++ tailWord_2062460) baseStart_2062460 baseEnd_2062460 := by
    simpa [prefixWord, tailWord_2062460, baseEnd_2062460] using wordTrace_append hprefix tailTrace_2062460
  have hstable : (prefixWord ++ tailWord_2062460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062460).length < 2 ^ (prefixWord ++ tailWord_2062460).sum := by decide
  have hdescent : baseEnd_2062460 < baseStart_2062460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062467 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 3]
def baseStart_2062467 : Nat := 118140960795 + 2062467 * 2 ^ 59
def prefixEnd_2062467 : Nat := 4983230072969 + 3 ^ 40 * 2062467 * 2
def baseEnd_2062467 : Nat := 1059036905036687322077393

theorem tailTrace_2062467 : CollatzResearch.WordTrace tailWord_2062467 prefixEnd_2062467 1059036905036687322077393 := by
  unfold tailWord_2062467
  simp only [CollatzResearch.WordTrace]
  refine ⟨75224351419041775165345655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50149567612694516776897103 75224351419041775165345655)
  ·
    refine ⟨112836527128562662748018483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75224351419041775165345655 112836527128562662748018483)
    ·
      refine ⟨169254790692843994122027725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112836527128562662748018483 169254790692843994122027725)
      ·
        refine ⟨63470546509816497795760397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169254790692843994122027725 63470546509816497795760397)
        ·
          refine ⟨23801454941181186673410149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63470546509816497795760397 23801454941181186673410149)
          ·
            refine ⟨4462772801471472501264403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23801454941181186673410149 4462772801471472501264403)
            ·
              refine ⟨6694159202207208751896605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462772801471472501264403 6694159202207208751896605)
              ·
                refine ⟨2510309700827703281961227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6694159202207208751896605 2510309700827703281961227)
                ·
                  refine ⟨3765464551241554922941841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510309700827703281961227 3765464551241554922941841)
                  ·
                    refine ⟨2824098413431166192206381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765464551241554922941841 2824098413431166192206381)
                    ·
                      refine ⟨1059036905036687322077393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824098413431166192206381 1059036905036687322077393)
                      ·
                        rfl

theorem cell23_2062467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_2062467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062467 prefixEnd_2062467 := by exact prefixLift 2062467
  have htrace : WordTrace (prefixWord ++ tailWord_2062467) baseStart_2062467 baseEnd_2062467 := by
    simpa [prefixWord, tailWord_2062467, baseEnd_2062467] using wordTrace_append hprefix tailTrace_2062467
  have hstable : (prefixWord ++ tailWord_2062467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062467).length < 2 ^ (prefixWord ++ tailWord_2062467).sum := by decide
  have hdescent : baseEnd_2062467 < baseStart_2062467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062474 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_2062474 : Nat := 118140960795 + 2062474 * 2 ^ 59
def prefixEnd_2062474 : Nat := 4983230072969 + 3 ^ 40 * 2062474 * 2
def baseEnd_2062474 : Nat := 353013499800422931563287

theorem tailTrace_2062474 : CollatzResearch.WordTrace tailWord_2062474 prefixEnd_2062474 353013499800422931563287 := by
  unfold tailWord_2062474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806151682504103840212619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50149737820010943573900317 18806151682504103840212619)
  ·
    refine ⟨28209227523756155760318929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18806151682504103840212619 28209227523756155760318929)
    ·
      refine ⟨21156920642817116820239197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28209227523756155760318929 21156920642817116820239197)
      ·
        refine ⟨7933845241056418807589699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21156920642817116820239197 7933845241056418807589699)
        ·
          refine ⟨11900767861584628211384549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933845241056418807589699 11900767861584628211384549)
          ·
            refine ⟨2231393974047117789634603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11900767861584628211384549 2231393974047117789634603)
            ·
              refine ⟨3347090961070676684451905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231393974047117789634603 3347090961070676684451905)
              ·
                refine ⟨2510318220803007513338929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347090961070676684451905 2510318220803007513338929)
                ·
                  refine ⟨1882738665602255635004197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2510318220803007513338929 1882738665602255635004197)
                  ·
                    refine ⟨353013499800422931563287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882738665602255635004197 353013499800422931563287)
                    ·
                      rfl

theorem cell23_2062474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_2062474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062474 prefixEnd_2062474 := by exact prefixLift 2062474
  have htrace : WordTrace (prefixWord ++ tailWord_2062474) baseStart_2062474 baseEnd_2062474 := by
    simpa [prefixWord, tailWord_2062474, baseEnd_2062474] using wordTrace_append hprefix tailTrace_2062474
  have hstable : (prefixWord ++ tailWord_2062474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062474).length < 2 ^ (prefixWord ++ tailWord_2062474).sum := by decide
  have hdescent : baseEnd_2062474 < baseStart_2062474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062484 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2062484 : Nat := 118140960795 + 2062484 * 2 ^ 59
def prefixEnd_2062484 : Nat := 4983230072969 + 3 ^ 40 * 2062484 * 2
def baseEnd_2062484 : Nat := 1059045634207813755564815

theorem tailTrace_2062484 : CollatzResearch.WordTrace tailWord_2062484 prefixEnd_2062484 1059045634207813755564815 := by
  unfold tailWord_2062484
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612485729990093534357253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50149980973320124712476337 37612485729990093534357253)
  ·
    refine ⟨7052341074373142537691985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37612485729990093534357253 7052341074373142537691985)
    ·
      refine ⟨5289255805779856903268989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7052341074373142537691985 5289255805779856903268989)
      ·
        refine ⟨1983470927167446338725871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5289255805779856903268989 1983470927167446338725871)
        ·
          refine ⟨2975206390751169508088807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983470927167446338725871 2975206390751169508088807)
          ·
            refine ⟨4462809586126754262133211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975206390751169508088807 4462809586126754262133211)
            ·
              refine ⟨6694214379190131393199817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462809586126754262133211 6694214379190131393199817)
              ·
                refine ⟨5020660784392598544899863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694214379190131393199817 5020660784392598544899863)
                ·
                  refine ⟨7530991176588897817349795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020660784392598544899863 7530991176588897817349795)
                  ·
                    refine ⟨11296486764883346726024693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530991176588897817349795 11296486764883346726024693)
                    ·
                      refine ⟨1059045634207813755564815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11296486764883346726024693 1059045634207813755564815)
                      ·
                        rfl

theorem cell23_2062484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2062484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062484 prefixEnd_2062484 := by exact prefixLift 2062484
  have htrace : WordTrace (prefixWord ++ tailWord_2062484) baseStart_2062484 baseEnd_2062484 := by
    simpa [prefixWord, tailWord_2062484, baseEnd_2062484] using wordTrace_append hprefix tailTrace_2062484
  have hstable : (prefixWord ++ tailWord_2062484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062484).length < 2 ^ (prefixWord ++ tailWord_2062484).sum := by decide
  have hdescent : baseEnd_2062484 < baseStart_2062484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062497 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2062497 : Nat := 118140960795 + 2062497 * 2 ^ 59
def prefixEnd_2062497 : Nat := 4983230072969 + 3 ^ 40 * 2062497 * 2
def baseEnd_2062497 : Nat := 1059052309456322204702255

theorem tailTrace_2062497 : CollatzResearch.WordTrace tailWord_2062497 prefixEnd_2062497 1059052309456322204702255 := by
  unfold tailWord_2062497
  simp only [CollatzResearch.WordTrace]
  refine ⟨75225445608933090288937745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50150297072622060192625163 75225445608933090288937745)
  ·
    refine ⟨56419084206699817716703309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75225445608933090288937745 56419084206699817716703309)
    ·
      refine ⟨21157156577512431643763741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56419084206699817716703309 21157156577512431643763741)
      ·
        refine ⟨7933933716567161866411403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21157156577512431643763741 7933933716567161866411403)
        ·
          refine ⟨11900900574850742799617105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933933716567161866411403 11900900574850742799617105)
          ·
            refine ⟨8925675431138057099712829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900900574850742799617105 8925675431138057099712829)
            ·
              refine ⟨3347128286676771412392311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8925675431138057099712829 3347128286676771412392311)
              ·
                refine ⟨5020692430015157118588467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347128286676771412392311 5020692430015157118588467)
                ·
                  refine ⟨7531038645022735677882701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020692430015157118588467 7531038645022735677882701)
                  ·
                    refine ⟨2824139491883525879206013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7531038645022735677882701 2824139491883525879206013)
                    ·
                      refine ⟨1059052309456322204702255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824139491883525879206013 1059052309456322204702255)
                      ·
                        rfl

theorem cell23_2062497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2062497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062497 prefixEnd_2062497 := by exact prefixLift 2062497
  have htrace : WordTrace (prefixWord ++ tailWord_2062497) baseStart_2062497 baseEnd_2062497 := by
    simpa [prefixWord, tailWord_2062497, baseEnd_2062497] using wordTrace_append hprefix tailTrace_2062497
  have hstable : (prefixWord ++ tailWord_2062497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062497).length < 2 ^ (prefixWord ++ tailWord_2062497).sum := by decide
  have hdescent : baseEnd_2062497 < baseStart_2062497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062557 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2062557 : Nat := 118140960795 + 2062557 * 2 ^ 59
def prefixEnd_2062557 : Nat := 4983230072969 + 3 ^ 40 * 2062557 * 2
def baseEnd_2062557 : Nat := 1059083118295591969951979

theorem tailTrace_2062557 : CollatzResearch.WordTrace tailWord_2062557 prefixEnd_2062557 1059083118295591969951979 := by
  unfold tailWord_2062557
  simp only [CollatzResearch.WordTrace]
  refine ⟨75227633988715720536121925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50151755992477147024081283 75227633988715720536121925)
  ·
    refine ⟨14105181372884197600522861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75227633988715720536121925 14105181372884197600522861)
    ·
      refine ⟨5289443014831574100196073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14105181372884197600522861 5289443014831574100196073)
      ·
        refine ⟨3967082261123680575147055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5289443014831574100196073 3967082261123680575147055)
        ·
          refine ⟨5950623391685520862720583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967082261123680575147055 5950623391685520862720583)
          ·
            refine ⟨8925935087528281294080875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950623391685520862720583 8925935087528281294080875)
            ·
              refine ⟨13388902631292421941121313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925935087528281294080875 13388902631292421941121313)
              ·
                refine ⟨10041676973469316455840985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388902631292421941121313 10041676973469316455840985)
                ·
                  refine ⟨7531257730101987341880739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041676973469316455840985 7531257730101987341880739)
                  ·
                    refine ⟨11296886595152981012821109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531257730101987341880739 11296886595152981012821109)
                    ·
                      refine ⟨1059083118295591969951979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11296886595152981012821109 1059083118295591969951979)
                      ·
                        rfl

theorem cell23_2062557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2062557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062557 prefixEnd_2062557 := by exact prefixLift 2062557
  have htrace : WordTrace (prefixWord ++ tailWord_2062557) baseStart_2062557 baseEnd_2062557 := by
    simpa [prefixWord, tailWord_2062557, baseEnd_2062557] using wordTrace_append hprefix tailTrace_2062557
  have hstable : (prefixWord ++ tailWord_2062557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062557).length < 2 ^ (prefixWord ++ tailWord_2062557).sum := by decide
  have hdescent : baseEnd_2062557 < baseStart_2062557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062624 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_2062624 : Nat := 118140960795 + 2062624 * 2 ^ 59
def prefixEnd_2062624 : Nat := 4983230072969 + 3 ^ 40 * 2062624 * 2
def baseEnd_2062624 : Nat := 353039173833147735938057

theorem tailTrace_2062624 : CollatzResearch.WordTrace tailWord_2062624 prefixEnd_2062624 353039173833147735938057 := by
  unfold tailWord_2062624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37615038839736495489405463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50153385119648660652540617 37615038839736495489405463)
  ·
    refine ⟨56422558259604743234108195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37615038839736495489405463 56422558259604743234108195)
    ·
      refine ⟨84633837389407114851162293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56422558259604743234108195 84633837389407114851162293)
      ·
        refine ⟨7934422255256917017296465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84633837389407114851162293 7934422255256917017296465)
        ·
          refine ⟨5950816691442687762972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7934422255256917017296465 5950816691442687762972349)
          ·
            refine ⟨2231556259291007911114631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5950816691442687762972349 2231556259291007911114631)
            ·
              refine ⟨3347334388936511866671947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231556259291007911114631 3347334388936511866671947)
              ·
                refine ⟨5021001583404767800007921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347334388936511866671947 5021001583404767800007921)
                ·
                  refine ⟨3765751187553575850005941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021001583404767800007921 3765751187553575850005941)
                  ·
                    refine ⟨353039173833147735938057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3765751187553575850005941 353039173833147735938057)
                    ·
                      rfl

theorem cell23_2062624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_2062624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062624 prefixEnd_2062624 := by exact prefixLift 2062624
  have htrace : WordTrace (prefixWord ++ tailWord_2062624) baseStart_2062624 baseEnd_2062624 := by
    simpa [prefixWord, tailWord_2062624, baseEnd_2062624] using wordTrace_append hprefix tailTrace_2062624
  have hstable : (prefixWord ++ tailWord_2062624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062624).length < 2 ^ (prefixWord ++ tailWord_2062624).sum := by decide
  have hdescent : baseEnd_2062624 < baseStart_2062624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062627 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 6, 2]
def baseStart_2062627 : Nat := 118140960795 + 2062627 * 2 ^ 59
def prefixEnd_2062627 : Nat := 4983230072969 + 3 ^ 40 * 2062627 * 2
def baseEnd_2062627 : Nat := 1059119061941406696076657

theorem tailTrace_2062627 : CollatzResearch.WordTrace tailWord_2062627 prefixEnd_2062627 1059119061941406696076657 := by
  unfold tailWord_2062627
  simp only [CollatzResearch.WordTrace]
  refine ⟨75230187098462122491170135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50153458065641414994113423 75230187098462122491170135)
  ·
    refine ⟨112845280647693183736755203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75230187098462122491170135 112845280647693183736755203)
    ·
      refine ⟨169267920971539775605132805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112845280647693183736755203 169267920971539775605132805)
      ·
        refine ⟨31737735182163707925962401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169267920971539775605132805 31737735182163707925962401)
        ·
          refine ⟨23803301386622780944471801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31737735182163707925962401 23803301386622780944471801)
          ·
            refine ⟨17852476039967085708353851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23803301386622780944471801 17852476039967085708353851)
            ·
              refine ⟨26778714059950628562530777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852476039967085708353851 26778714059950628562530777)
              ·
                refine ⟨20084035544962971421898083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26778714059950628562530777 20084035544962971421898083)
                ·
                  refine ⟨30126053317444457132847125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20084035544962971421898083 30126053317444457132847125)
                  ·
                    refine ⟨1412158749255208928102209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30126053317444457132847125 1412158749255208928102209)
                    ·
                      refine ⟨1059119061941406696076657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412158749255208928102209 1059119061941406696076657)
                      ·
                        rfl

theorem cell23_2062627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_2062627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062627 prefixEnd_2062627 := by exact prefixLift 2062627
  have htrace : WordTrace (prefixWord ++ tailWord_2062627) baseStart_2062627 baseEnd_2062627 := by
    simpa [prefixWord, tailWord_2062627, baseEnd_2062627] using wordTrace_append hprefix tailTrace_2062627
  have hstable : (prefixWord ++ tailWord_2062627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062627).length < 2 ^ (prefixWord ++ tailWord_2062627).sum := by decide
  have hdescent : baseEnd_2062627 < baseStart_2062627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062647 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_2062647 : Nat := 118140960795 + 2062647 * 2 ^ 59
def prefixEnd_2062647 : Nat := 4983230072969 + 3 ^ 40 * 2062647 * 2
def baseEnd_2062647 : Nat := 1059129331554496617826565

theorem tailTrace_2062647 : CollatzResearch.WordTrace tailWord_2062647 prefixEnd_2062647 1059129331554496617826565 := by
  unfold tailWord_2062647
  simp only [CollatzResearch.WordTrace]
  refine ⟨75230916558389665906898195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50153944372259777271265463 75230916558389665906898195)
  ·
    refine ⟨112846374837584498860347293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75230916558389665906898195 112846374837584498860347293)
    ·
      refine ⟨42317390564094187072630235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112846374837584498860347293 42317390564094187072630235)
      ·
        refine ⟨63476085846141280608945353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42317390564094187072630235 63476085846141280608945353)
        ·
          refine ⟨47607064384605960456709015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63476085846141280608945353 47607064384605960456709015)
          ·
            refine ⟨71410596576908940685063523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47607064384605960456709015 71410596576908940685063523)
            ·
              refine ⟨107115894865363411027595285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71410596576908940685063523 107115894865363411027595285)
              ·
                refine ⟨5021057571813909891918529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107115894865363411027595285 5021057571813909891918529)
                ·
                  refine ⟨3765793178860432418938897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021057571813909891918529 3765793178860432418938897)
                  ·
                    refine ⟨2824344884145324314204173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765793178860432418938897 2824344884145324314204173)
                    ·
                      refine ⟨1059129331554496617826565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824344884145324314204173 1059129331554496617826565)
                      ·
                        rfl

theorem cell23_2062647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_2062647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062647 prefixEnd_2062647 := by exact prefixLift 2062647
  have htrace : WordTrace (prefixWord ++ tailWord_2062647) baseStart_2062647 baseEnd_2062647 := by
    simpa [prefixWord, tailWord_2062647, baseEnd_2062647] using wordTrace_append hprefix tailTrace_2062647
  have hstable : (prefixWord ++ tailWord_2062647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062647).length < 2 ^ (prefixWord ++ tailWord_2062647).sum := by decide
  have hdescent : baseEnd_2062647 < baseStart_2062647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062654 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2062654 : Nat := 118140960795 + 2062654 * 2 ^ 59
def prefixEnd_2062654 : Nat := 4983230072969 + 3 ^ 40 * 2062654 * 2
def baseEnd_2062654 : Nat := 353044308639692696813011

theorem tailTrace_2062654 : CollatzResearch.WordTrace tailWord_2062654 prefixEnd_2062654 353044308639692696813011 := by
  unfold tailWord_2062654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403896483670538262800377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50154114579576204068268677 9403896483670538262800377)
  ·
    refine ⟨7052922362752903697100283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9403896483670538262800377 7052922362752903697100283)
    ·
      refine ⟨10579383544129355545650425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052922362752903697100283 10579383544129355545650425)
      ·
        refine ⟨7934537658097016659237819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10579383544129355545650425 7934537658097016659237819)
        ·
          refine ⟨11901806487145524988856729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934537658097016659237819 11901806487145524988856729)
          ·
            refine ⟨8926354865359143741642547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11901806487145524988856729 8926354865359143741642547)
            ·
              refine ⟨13389532298038715612463821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926354865359143741642547 13389532298038715612463821)
              ·
                refine ⟨5021074611764518354673933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13389532298038715612463821 5021074611764518354673933)
                ·
                  refine ⟨1882902979411694383002725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5021074611764518354673933 1882902979411694383002725)
                  ·
                    refine ⟨353044308639692696813011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882902979411694383002725 353044308639692696813011)
                    ·
                      rfl

theorem cell23_2062654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2062654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062654 prefixEnd_2062654 := by exact prefixLift 2062654
  have htrace : WordTrace (prefixWord ++ tailWord_2062654) baseStart_2062654 baseEnd_2062654 := by
    simpa [prefixWord, tailWord_2062654, baseEnd_2062654] using wordTrace_append hprefix tailTrace_2062654
  have hstable : (prefixWord ++ tailWord_2062654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062654).length < 2 ^ (prefixWord ++ tailWord_2062654).sum := by decide
  have hdescent : baseEnd_2062654 < baseStart_2062654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062688 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 1, 4]
def baseStart_2062688 : Nat := 118140960795 + 2062688 * 2 ^ 59
def prefixEnd_2062688 : Nat := 4983230072969 + 3 ^ 40 * 2062688 * 2
def baseEnd_2062688 : Nat := 353050128087110319137959

theorem tailTrace_2062688 : CollatzResearch.WordTrace tailWord_2062688 prefixEnd_2062688 353050128087110319137959 := by
  unfold tailWord_2062688
  simp only [CollatzResearch.WordTrace]
  refine ⟨37616205975620564954570359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50154941300827419939427145 37616205975620564954570359)
  ·
    refine ⟨56424308963430847431855539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37616205975620564954570359 56424308963430847431855539)
    ·
      refine ⟨84636463445146271147783309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56424308963430847431855539 84636463445146271147783309)
      ·
        refine ⟨31738673791929851680418741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84636463445146271147783309 31738673791929851680418741)
        ·
          refine ⟨2975500667993423595039257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31738673791929851680418741 2975500667993423595039257)
          ·
            refine ⟨2231625500995067696279443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975500667993423595039257 2231625500995067696279443)
            ·
              refine ⟨3347438251492601544419165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231625500995067696279443 3347438251492601544419165)
              ·
                refine ⟨1255289344309725579157187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3347438251492601544419165 1255289344309725579157187)
                ·
                  refine ⟨1882934016464588368735781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255289344309725579157187 1882934016464588368735781)
                  ·
                    refine ⟨353050128087110319137959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882934016464588368735781 353050128087110319137959)
                    ·
                      rfl

theorem cell23_2062688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_2062688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062688 prefixEnd_2062688 := by exact prefixLift 2062688
  have htrace : WordTrace (prefixWord ++ tailWord_2062688) baseStart_2062688 baseEnd_2062688 := by
    simpa [prefixWord, tailWord_2062688, baseEnd_2062688] using wordTrace_append hprefix tailTrace_2062688
  have hstable : (prefixWord ++ tailWord_2062688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062688).length < 2 ^ (prefixWord ++ tailWord_2062688).sum := by decide
  have hdescent : baseEnd_2062688 < baseStart_2062688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062697 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_2062697 : Nat := 118140960795 + 2062697 * 2 ^ 59
def prefixEnd_2062697 : Nat := 4983230072969 + 3 ^ 40 * 2062697 * 2
def baseEnd_2062697 : Nat := 353051668529073807400445

theorem tailTrace_2062697 : CollatzResearch.WordTrace tailWord_2062697 prefixEnd_2062697 353051668529073807400445 := by
  unfold tailWord_2062697
  simp only [CollatzResearch.WordTrace]
  refine ⟨75232740208208524446218345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50155160138805682964145563 75232740208208524446218345)
  ·
    refine ⟨56424555156156393334663759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75232740208208524446218345 56424555156156393334663759)
    ·
      refine ⟨84636832734234590001995639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56424555156156393334663759 84636832734234590001995639)
      ·
        refine ⟨126955249101351885002993459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84636832734234590001995639 126955249101351885002993459)
        ·
          refine ⟨190432873652027827504490189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126955249101351885002993459 190432873652027827504490189)
          ·
            refine ⟨71412327619510435314183821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190432873652027827504490189 71412327619510435314183821)
            ·
              refine ⟨26779622857316413242818933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71412327619510435314183821 26779622857316413242818933)
              ·
                refine ⟨2510589642873413741514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26779622857316413242818933 2510589642873413741514275)
                ·
                  refine ⟨3765884464310120612271413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510589642873413741514275 3765884464310120612271413)
                  ·
                    refine ⟨353051668529073807400445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3765884464310120612271413 353051668529073807400445)
                    ·
                      rfl

theorem cell23_2062697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_2062697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062697 prefixEnd_2062697 := by exact prefixLift 2062697
  have htrace : WordTrace (prefixWord ++ tailWord_2062697) baseStart_2062697 baseEnd_2062697 := by
    simpa [prefixWord, tailWord_2062697, baseEnd_2062697] using wordTrace_append hprefix tailTrace_2062697
  have hstable : (prefixWord ++ tailWord_2062697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062697).length < 2 ^ (prefixWord ++ tailWord_2062697).sum := by decide
  have hdescent : baseEnd_2062697 < baseStart_2062697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062704 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2]
def baseStart_2062704 : Nat := 118140960795 + 2062704 * 2 ^ 59
def prefixEnd_2062704 : Nat := 4983230072969 + 3 ^ 40 * 2062704 * 2
def baseEnd_2062704 : Nat := 1059158599951802894813803

theorem tailTrace_2062704 : CollatzResearch.WordTrace tailWord_2062704 prefixEnd_2062704 1059158599951802894813803 := by
  unfold tailWord_2062704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37616497759591582320861583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50155330346122109761148777 37616497759591582320861583)
  ·
    refine ⟨56424746639387373481292375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37616497759591582320861583 56424746639387373481292375)
    ·
      refine ⟨84637119959081060221938563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56424746639387373481292375 84637119959081060221938563)
      ·
        refine ⟨126955679938621590332907845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84637119959081060221938563 126955679938621590332907845)
        ·
          refine ⟨23804189988491548187420221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126955679938621590332907845 23804189988491548187420221)
          ·
            refine ⟨8926571245684330570282583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23804189988491548187420221 8926571245684330570282583)
            ·
              refine ⟨13389856868526495855423875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926571245684330570282583 13389856868526495855423875)
              ·
                refine ⟨20084785302789743783135813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389856868526495855423875 20084785302789743783135813)
                ·
                  refine ⟨3765897244273076959337965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20084785302789743783135813 3765897244273076959337965)
                  ·
                    refine ⟨1412211466602403859751737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3765897244273076959337965 1412211466602403859751737)
                    ·
                      refine ⟨1059158599951802894813803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412211466602403859751737 1059158599951802894813803)
                      ·
                        rfl

theorem cell23_2062704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 3, 2].length) (baseStart_2062704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062704 prefixEnd_2062704 := by exact prefixLift 2062704
  have htrace : WordTrace (prefixWord ++ tailWord_2062704) baseStart_2062704 baseEnd_2062704 := by
    simpa [prefixWord, tailWord_2062704, baseEnd_2062704] using wordTrace_append hprefix tailTrace_2062704
  have hstable : (prefixWord ++ tailWord_2062704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062704).length < 2 ^ (prefixWord ++ tailWord_2062704).sum := by decide
  have hdescent : baseEnd_2062704 < baseStart_2062704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062727 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 6]
def baseStart_2062727 : Nat := 118140960795 + 2062727 * 2 ^ 59
def prefixEnd_2062727 : Nat := 4983230072969 + 3 ^ 40 * 2062727 * 2
def baseEnd_2062727 : Nat := 353056803335618768275399

theorem tailTrace_2062727 : CollatzResearch.WordTrace tailWord_2062727 prefixEnd_2062727 353056803335618768275399 := by
  unfold tailWord_2062727
  simp only [CollatzResearch.WordTrace]
  refine ⟨75233834398099839569810435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50155889598733226379873623 75233834398099839569810435)
  ·
    refine ⟨112850751597149759354715653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75233834398099839569810435 112850751597149759354715653)
    ·
      refine ⟨21159515924465579879009185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112850751597149759354715653 21159515924465579879009185)
      ·
        refine ⟨15869636943349184909256889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21159515924465579879009185 15869636943349184909256889)
        ·
          refine ⟨11902227707511888681942667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15869636943349184909256889 11902227707511888681942667)
          ·
            refine ⟨17853341561267833022914001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902227707511888681942667 17853341561267833022914001)
            ·
              refine ⟨13390006170950874767185501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17853341561267833022914001 13390006170950874767185501)
              ·
                refine ⟨5021252314106578037694563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13390006170950874767185501 5021252314106578037694563)
                ·
                  refine ⟨7531878471159867056541845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021252314106578037694563 7531878471159867056541845)
                  ·
                    refine ⟨353056803335618768275399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7531878471159867056541845 353056803335618768275399)
                    ·
                      rfl

theorem cell23_2062727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_2062727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062727 prefixEnd_2062727 := by exact prefixLift 2062727
  have htrace : WordTrace (prefixWord ++ tailWord_2062727) baseStart_2062727 baseEnd_2062727 := by
    simpa [prefixWord, tailWord_2062727, baseEnd_2062727] using wordTrace_append hprefix tailTrace_2062727
  have hstable : (prefixWord ++ tailWord_2062727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062727).length < 2 ^ (prefixWord ++ tailWord_2062727).sum := by decide
  have hdescent : baseEnd_2062727 < baseStart_2062727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062744 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_2062744 : Nat := 118140960795 + 2062744 * 2 ^ 59
def prefixEnd_2062744 : Nat := 4983230072969 + 3 ^ 40 * 2062744 * 2
def baseEnd_2062744 : Nat := 353059713059327579437873

theorem tailTrace_2062744 : CollatzResearch.WordTrace tailWord_2062744 prefixEnd_2062744 353059713059327579437873 := by
  unfold tailWord_2062744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617227219519125736589643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50156302959358834315452857 37617227219519125736589643)
  ·
    refine ⟨56425840829278688604884465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617227219519125736589643 56425840829278688604884465)
    ·
      refine ⟨42319380621959016453663349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56425840829278688604884465 42319380621959016453663349)
      ·
        refine ⟨3967441933308657792530939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42319380621959016453663349 3967441933308657792530939)
        ·
          refine ⟨5951162899962986688796409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967441933308657792530939 5951162899962986688796409)
          ·
            refine ⟨4463372174972240016597307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5951162899962986688796409 4463372174972240016597307)
            ·
              refine ⟨6695058262458360024895961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463372174972240016597307 6695058262458360024895961)
              ·
                refine ⟨5021293696843770018671971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6695058262458360024895961 5021293696843770018671971)
                ·
                  refine ⟨7531940545265655028007957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021293696843770018671971 7531940545265655028007957)
                  ·
                    refine ⟨353059713059327579437873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7531940545265655028007957 353059713059327579437873)
                    ·
                      rfl

theorem cell23_2062744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_2062744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062744 prefixEnd_2062744 := by exact prefixLift 2062744
  have htrace : WordTrace (prefixWord ++ tailWord_2062744) baseStart_2062744 baseEnd_2062744 := by
    simpa [prefixWord, tailWord_2062744, baseEnd_2062744] using wordTrace_append hprefix tailTrace_2062744
  have hstable : (prefixWord ++ tailWord_2062744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062744).length < 2 ^ (prefixWord ++ tailWord_2062744).sum := by decide
  have hdescent : baseEnd_2062744 < baseStart_2062744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062751 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2062751 : Nat := 118140960795 + 2062751 * 2 ^ 59
def prefixEnd_2062751 : Nat := 4983230072969 + 3 ^ 40 * 2062751 * 2
def baseEnd_2062751 : Nat := 1059182733542564210926087

theorem tailTrace_2062751 : CollatzResearch.WordTrace tailWord_2062751 prefixEnd_2062751 1059182733542564210926087 := by
  unfold tailWord_2062751
  simp only [CollatzResearch.WordTrace]
  refine ⟨75234709750012891668684107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50156473166675261112456071 75234709750012891668684107)
  ·
    refine ⟨112852064625019337503026161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75234709750012891668684107 112852064625019337503026161)
    ·
      refine ⟨84639048468764503127269621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112852064625019337503026161 84639048468764503127269621)
      ·
        refine ⟨7934910793946672168181527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84639048468764503127269621 7934910793946672168181527)
        ·
          refine ⟨11902366190920008252272291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934910793946672168181527 11902366190920008252272291)
          ·
            refine ⟨17853549286380012378408437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902366190920008252272291 17853549286380012378408437)
            ·
              refine ⟨1673770245598126160475791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17853549286380012378408437 1673770245598126160475791)
              ·
                refine ⟨2510655368397189240713687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673770245598126160475791 2510655368397189240713687)
                ·
                  refine ⟨3765983052595783861070531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510655368397189240713687 3765983052595783861070531)
                  ·
                    refine ⟨5648974578893675791605797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3765983052595783861070531 5648974578893675791605797)
                    ·
                      refine ⟨1059182733542564210926087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5648974578893675791605797 1059182733542564210926087)
                      ·
                        rfl

theorem cell23_2062751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2062751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062751 prefixEnd_2062751 := by exact prefixLift 2062751
  have htrace : WordTrace (prefixWord ++ tailWord_2062751) baseStart_2062751 baseEnd_2062751 := by
    simpa [prefixWord, tailWord_2062751, baseEnd_2062751] using wordTrace_append hprefix tailTrace_2062751
  have hstable : (prefixWord ++ tailWord_2062751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062751).length < 2 ^ (prefixWord ++ tailWord_2062751).sum := by decide
  have hdescent : baseEnd_2062751 < baseStart_2062751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062784 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_2062784 : Nat := 118140960795 + 2062784 * 2 ^ 59
def prefixEnd_2062784 : Nat := 4983230072969 + 3 ^ 40 * 2062784 * 2
def baseEnd_2062784 : Nat := 1059199678404162581813435

theorem tailTrace_2062784 : CollatzResearch.WordTrace tailWord_2062784 prefixEnd_2062784 1059199678404162581813435 := by
  unfold tailWord_2062784
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617956679446669152317703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50157275572595558869756937 37617956679446669152317703)
  ·
    refine ⟨56426935019170003728476555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617956679446669152317703 56426935019170003728476555)
    ·
      refine ⟨84640402528755005592714833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56426935019170003728476555 84640402528755005592714833)
      ·
        refine ⟨63480301896566254194536125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84640402528755005592714833 63480301896566254194536125)
        ·
          refine ⟨23805113211212345322951047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63480301896566254194536125 23805113211212345322951047)
          ·
            refine ⟨35707669816818517984426571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23805113211212345322951047 35707669816818517984426571)
            ·
              refine ⟨53561504725227776976639857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35707669816818517984426571 53561504725227776976639857)
              ·
                refine ⟨40171128543920832732479893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53561504725227776976639857 40171128543920832732479893)
                ·
                  refine ⟨1883021650496289034334995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40171128543920832732479893 1883021650496289034334995)
                  ·
                    refine ⟨2824532475744433551502493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1883021650496289034334995 2824532475744433551502493)
                    ·
                      refine ⟨1059199678404162581813435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824532475744433551502493 1059199678404162581813435)
                      ·
                        rfl

theorem cell23_2062784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_2062784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062784 prefixEnd_2062784 := by exact prefixLift 2062784
  have htrace : WordTrace (prefixWord ++ tailWord_2062784) baseStart_2062784 baseEnd_2062784 := by
    simpa [prefixWord, tailWord_2062784, baseEnd_2062784] using wordTrace_append hprefix tailTrace_2062784
  have hstable : (prefixWord ++ tailWord_2062784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062784).length < 2 ^ (prefixWord ++ tailWord_2062784).sum := by decide
  have hdescent : baseEnd_2062784 < baseStart_2062784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062802 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2062802 : Nat := 118140960795 + 2062802 * 2 ^ 59
def prefixEnd_2062802 : Nat := 4983230072969 + 3 ^ 40 * 2062802 * 2
def baseEnd_2062802 : Nat := 1059208921055943511388353

theorem tailTrace_2062802 : CollatzResearch.WordTrace tailWord_2062802 prefixEnd_2062802 1059208921055943511388353 := by
  unfold tailWord_2062802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809142468207031844697665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50157713248552084919193773 18809142468207031844697665)
  ·
    refine ⟨14106856851155273883523249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18809142468207031844697665 14106856851155273883523249)
    ·
      refine ⟨10580142638366455412642437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14106856851155273883523249 10580142638366455412642437)
      ·
        refine ⟨1983776744693710389870457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10580142638366455412642437 1983776744693710389870457)
        ·
          refine ⟨1487832558520282792402843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983776744693710389870457 1487832558520282792402843)
          ·
            refine ⟨2231748837780424188604265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487832558520282792402843 2231748837780424188604265)
            ·
              refine ⟨1673811628335318141453199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231748837780424188604265 1673811628335318141453199)
              ·
                refine ⟨2510717442502977212179799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673811628335318141453199 2510717442502977212179799)
                ·
                  refine ⟨3766076163754465818269699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510717442502977212179799 3766076163754465818269699)
                  ·
                    refine ⟨5649114245631698727404549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766076163754465818269699 5649114245631698727404549)
                    ·
                      refine ⟨1059208921055943511388353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5649114245631698727404549 1059208921055943511388353)
                      ·
                        rfl

theorem cell23_2062802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2062802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062802 prefixEnd_2062802 := by exact prefixLift 2062802
  have htrace : WordTrace (prefixWord ++ tailWord_2062802) baseStart_2062802 baseEnd_2062802 := by
    simpa [prefixWord, tailWord_2062802, baseEnd_2062802] using wordTrace_append hprefix tailTrace_2062802
  have hstable : (prefixWord ++ tailWord_2062802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062802).length < 2 ^ (prefixWord ++ tailWord_2062802).sum := by decide
  have hdescent : baseEnd_2062802 < baseStart_2062802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062817 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2062817 : Nat := 118140960795 + 2062817 * 2 ^ 59
def prefixEnd_2062817 : Nat := 4983230072969 + 3 ^ 40 * 2062817 * 2
def baseEnd_2062817 : Nat := 353072207755253650900261

theorem tailTrace_2062817 : CollatzResearch.WordTrace tailWord_2062817 prefixEnd_2062817 353072207755253650900261 := by
  unfold tailWord_2062817
  simp only [CollatzResearch.WordTrace]
  refine ⟨75237116967773784940586705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50158077978515856627057803 75237116967773784940586705)
  ·
    refine ⟨56427837725830338705440029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75237116967773784940586705 56427837725830338705440029)
    ·
      refine ⟨21160439147186377014540011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56427837725830338705440029 21160439147186377014540011)
      ·
        refine ⟨31740658720779565521810017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21160439147186377014540011 31740658720779565521810017)
        ·
          refine ⟨23805494040584674141357513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31740658720779565521810017 23805494040584674141357513)
          ·
            refine ⟨17854120530438505606018135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23805494040584674141357513 17854120530438505606018135)
            ·
              refine ⟨26781180795657758409027203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854120530438505606018135 26781180795657758409027203)
              ·
                refine ⟨40171771193486637613540805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26781180795657758409027203 40171771193486637613540805)
                ·
                  refine ⟨7532207098778744552538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40171771193486637613540805 7532207098778744552538901)
                  ·
                    refine ⟨353072207755253650900261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7532207098778744552538901 353072207755253650900261)
                    ·
                      rfl

theorem cell23_2062817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2062817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062817 prefixEnd_2062817 := by exact prefixLift 2062817
  have htrace : WordTrace (prefixWord ++ tailWord_2062817) baseStart_2062817 baseEnd_2062817 := by
    simpa [prefixWord, tailWord_2062817, baseEnd_2062817] using wordTrace_append hprefix tailTrace_2062817
  have hstable : (prefixWord ++ tailWord_2062817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062817).length < 2 ^ (prefixWord ++ tailWord_2062817).sum := by decide
  have hdescent : baseEnd_2062817 < baseStart_2062817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062841 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 4, 2]
def baseStart_2062841 : Nat := 118140960795 + 2062841 * 2 ^ 59
def prefixEnd_2062841 : Nat := 4983230072969 + 3 ^ 40 * 2062841 * 2
def baseEnd_2062841 : Nat := 1059228946801468858800673

theorem tailTrace_2062841 : CollatzResearch.WordTrace tailWord_2062841 prefixEnd_2062841 1059228946801468858800673 := by
  unfold tailWord_2062841
  simp only [CollatzResearch.WordTrace]
  refine ⟨75237992319686837039460377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50158661546457891359640251 75237992319686837039460377)
  ·
    refine ⟨56428494239765127779595283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75237992319686837039460377 56428494239765127779595283)
    ·
      refine ⟨84642741359647691669392925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56428494239765127779595283 84642741359647691669392925)
      ·
        refine ⟨31741028009867884376022347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84642741359647691669392925 31741028009867884376022347)
        ·
          refine ⟨47611542014801826564033521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31741028009867884376022347 47611542014801826564033521)
          ·
            refine ⟨35708656511101369923025141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47611542014801826564033521 35708656511101369923025141)
            ·
              refine ⟨3347686547915753430283607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35708656511101369923025141 3347686547915753430283607)
              ·
                refine ⟨5021529821873630145425411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347686547915753430283607 5021529821873630145425411)
                ·
                  refine ⟨7532294732810445218138117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5021529821873630145425411 7532294732810445218138117)
                  ·
                    refine ⟨1412305262401958478400897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7532294732810445218138117 1412305262401958478400897)
                    ·
                      refine ⟨1059228946801468858800673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412305262401958478400897 1059228946801468858800673)
                      ·
                        rfl

theorem cell23_2062841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_2062841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062841 prefixEnd_2062841 := by exact prefixLift 2062841
  have htrace : WordTrace (prefixWord ++ tailWord_2062841) baseStart_2062841 baseEnd_2062841 := by
    simpa [prefixWord, tailWord_2062841, baseEnd_2062841] using wordTrace_append hprefix tailTrace_2062841
  have hstable : (prefixWord ++ tailWord_2062841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062841).length < 2 ^ (prefixWord ++ tailWord_2062841).sum := by decide
  have hdescent : baseEnd_2062841 < baseStart_2062841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062847 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 7]
def baseStart_2062847 : Nat := 118140960795 + 2062847 * 2 ^ 59
def prefixEnd_2062847 : Nat := 4983230072969 + 3 ^ 40 * 2062847 * 2
def baseEnd_2062847 : Nat := 117692447520599537258405

theorem tailTrace_2062847 : CollatzResearch.WordTrace tailWord_2062847 prefixEnd_2062847 117692447520599537258405 := by
  unfold tailWord_2062847
  simp only [CollatzResearch.WordTrace]
  refine ⟨75238211157665100064178795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50158807438443400042785863 75238211157665100064178795)
  ·
    refine ⟨112857316736497650096268193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75238211157665100064178795 112857316736497650096268193)
    ·
      refine ⟨84642987552373237572201145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112857316736497650096268193 84642987552373237572201145)
      ·
        refine ⟨63482240664279928179150859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84642987552373237572201145 63482240664279928179150859)
        ·
          refine ⟨95223360996419892268726289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63482240664279928179150859 95223360996419892268726289)
          ·
            refine ⟨71417520747314919201544717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95223360996419892268726289 71417520747314919201544717)
            ·
              refine ⟨26781570280243094700579269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71417520747314919201544717 26781570280243094700579269)
              ·
                refine ⟨5021544427545580256358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26781570280243094700579269 5021544427545580256358613)
                ·
                  refine ⟨117692447520599537258405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5021544427545580256358613 117692447520599537258405)
                  ·
                    rfl

theorem cell23_2062847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 7].length) (baseStart_2062847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062847 prefixEnd_2062847 := by exact prefixLift 2062847
  have htrace : WordTrace (prefixWord ++ tailWord_2062847) baseStart_2062847 baseEnd_2062847 := by
    simpa [prefixWord, tailWord_2062847, baseEnd_2062847] using wordTrace_append hprefix tailTrace_2062847
  have hstable : (prefixWord ++ tailWord_2062847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062847).length < 2 ^ (prefixWord ++ tailWord_2062847).sum := by decide
  have hdescent : baseEnd_2062847 < baseStart_2062847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062874 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2062874 : Nat := 118140960795 + 2062874 * 2 ^ 59
def prefixEnd_2062874 : Nat := 4983230072969 + 3 ^ 40 * 2062874 * 2
def baseEnd_2062874 : Nat := 1059245891663067229688021

theorem tailTrace_2062874 : CollatzResearch.WordTrace tailWord_2062874 prefixEnd_2062874 1059245891663067229688021 := by
  unfold tailWord_2062874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809798982141820918852919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50159463952378189116941117 18809798982141820918852919)
  ·
    refine ⟨28214698473212731378279379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18809798982141820918852919 28214698473212731378279379)
    ·
      refine ⟨42322047709819097067419069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28214698473212731378279379 42322047709819097067419069)
      ·
        refine ⟨15870767891182161400282151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42322047709819097067419069 15870767891182161400282151)
        ·
          refine ⟨23806151836773242100423227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870767891182161400282151 23806151836773242100423227)
          ·
            refine ⟨35709227755159863150634841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23806151836773242100423227 35709227755159863150634841)
            ·
              refine ⟨26781920816369897362976131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35709227755159863150634841 26781920816369897362976131)
              ·
                refine ⟨40172881224554846044464197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26781920816369897362976131 40172881224554846044464197)
                ·
                  refine ⟨7532415229604033633337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40172881224554846044464197 7532415229604033633337037)
                  ·
                    refine ⟨2824655711101512612501389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532415229604033633337037 2824655711101512612501389)
                    ·
                      refine ⟨1059245891663067229688021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824655711101512612501389 1059245891663067229688021)
                      ·
                        rfl

theorem cell23_2062874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2062874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062874 prefixEnd_2062874 := by exact prefixLift 2062874
  have htrace : WordTrace (prefixWord ++ tailWord_2062874) baseStart_2062874 baseEnd_2062874 := by
    simpa [prefixWord, tailWord_2062874, baseEnd_2062874] using wordTrace_append hprefix tailTrace_2062874
  have hstable : (prefixWord ++ tailWord_2062874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062874).length < 2 ^ (prefixWord ++ tailWord_2062874).sum := by decide
  have hdescent : baseEnd_2062874 < baseStart_2062874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062942 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2062942 : Nat := 118140960795 + 2062942 * 2 ^ 59
def prefixEnd_2062942 : Nat := 4983230072969 + 3 ^ 40 * 2062942 * 2
def baseEnd_2062942 : Nat := 1059280808347572963637709

theorem tailTrace_2062942 : CollatzResearch.WordTrace tailWord_2062942 prefixEnd_2062942 1059280808347572963637709 := by
  unfold tailWord_2062942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405209511540116411110885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50161117394880620859258053 9405209511540116411110885)
  ·
    refine ⟨1763476783413771827083291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9405209511540116411110885 1763476783413771827083291)
    ·
      refine ⟨2645215175120657740624937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763476783413771827083291 2645215175120657740624937)
      ·
        refine ⟨1983911381340493305468703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645215175120657740624937 1983911381340493305468703)
        ·
          refine ⟨2975867072010739958203055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983911381340493305468703 2975867072010739958203055)
          ·
            refine ⟨4463800608016109937304583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975867072010739958203055 4463800608016109937304583)
            ·
              refine ⟨6695700912024164905956875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463800608016109937304583 6695700912024164905956875)
              ·
                refine ⟨10043551368036247358935313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6695700912024164905956875 10043551368036247358935313)
                ·
                  refine ⟨7532663526027185519201485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10043551368036247358935313 7532663526027185519201485)
                  ·
                    refine ⟨2824748822260194569700557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7532663526027185519201485 2824748822260194569700557)
                    ·
                      refine ⟨1059280808347572963637709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824748822260194569700557 1059280808347572963637709)
                      ·
                        rfl

theorem cell23_2062942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2062942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062942 prefixEnd_2062942 := by exact prefixLift 2062942
  have htrace : WordTrace (prefixWord ++ tailWord_2062942) baseStart_2062942 baseEnd_2062942 := by
    simpa [prefixWord, tailWord_2062942, baseEnd_2062942] using wordTrace_append hprefix tailTrace_2062942
  have hstable : (prefixWord ++ tailWord_2062942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062942).length < 2 ^ (prefixWord ++ tailWord_2062942).sum := by decide
  have hdescent : baseEnd_2062942 < baseStart_2062942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062958 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2062958 : Nat := 118140960795 + 2062958 * 2 ^ 59
def prefixEnd_2062958 : Nat := 4983230072969 + 3 ^ 40 * 2062958 * 2
def baseEnd_2062958 : Nat := 353096341346014967012545

theorem tailTrace_2062958 : CollatzResearch.WordTrace tailWord_2062958 prefixEnd_2062958 353096341346014967012545 := by
  unfold tailWord_2062958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405282457532870752683691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50161506440175310680979685 9405282457532870752683691)
  ·
    refine ⟨14107923686299306129025537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9405282457532870752683691 14107923686299306129025537)
    ·
      refine ⟨10580942764724479596769153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14107923686299306129025537 10580942764724479596769153)
      ·
        refine ⟨7935707073543359697576865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10580942764724479596769153 7935707073543359697576865)
        ·
          refine ⟨5951780305157519773182649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7935707073543359697576865 5951780305157519773182649)
          ·
            refine ⟨4463835228868139829886987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5951780305157519773182649 4463835228868139829886987)
            ·
              refine ⟨6695752843302209744830481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4463835228868139829886987 6695752843302209744830481)
              ·
                refine ⟨5021814632476657308622861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6695752843302209744830481 5021814632476657308622861)
                ·
                  refine ⟨1883180487178746490733573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5021814632476657308622861 1883180487178746490733573)
                  ·
                    refine ⟨353096341346014967012545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883180487178746490733573 353096341346014967012545)
                    ·
                      rfl

theorem cell23_2062958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2062958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062958 prefixEnd_2062958 := by exact prefixLift 2062958
  have htrace : WordTrace (prefixWord ++ tailWord_2062958) baseStart_2062958 baseEnd_2062958 := by
    simpa [prefixWord, tailWord_2062958, baseEnd_2062958] using wordTrace_append hprefix tailTrace_2062958
  have hstable : (prefixWord ++ tailWord_2062958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062958).length < 2 ^ (prefixWord ++ tailWord_2062958).sum := by decide
  have hdescent : baseEnd_2062958 < baseStart_2062958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062965 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2062965 : Nat := 118140960795 + 2062965 * 2 ^ 59
def prefixEnd_2062965 : Nat := 4983230072969 + 3 ^ 40 * 2062965 * 2
def baseEnd_2062965 : Nat := 1059292618402626373650103

theorem tailTrace_2062965 : CollatzResearch.WordTrace tailWord_2062965 prefixEnd_2062965 1059292618402626373650103 := by
  unfold tailWord_2062965
  simp only [CollatzResearch.WordTrace]
  refine ⟨75242514971237606216974349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50161676647491737477982899 75242514971237606216974349)
  ·
    refine ⟨28215943114214102331365381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75242514971237606216974349 28215943114214102331365381)
    ·
      refine ⟨5290489333915144187131009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28215943114214102331365381 5290489333915144187131009)
      ·
        refine ⟨3967867000436358140348257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5290489333915144187131009 3967867000436358140348257)
        ·
          refine ⟨2975900250327268605261193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3967867000436358140348257 2975900250327268605261193)
          ·
            refine ⟨2231925187745451453945895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975900250327268605261193 2231925187745451453945895)
            ·
              refine ⟨3347887781618177180918843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231925187745451453945895 3347887781618177180918843)
              ·
                refine ⟨5021831672427265771378265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347887781618177180918843 5021831672427265771378265)
                ·
                  refine ⟨3766373754320449328533699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5021831672427265771378265 3766373754320449328533699)
                  ·
                    refine ⟨5649560631480673992800549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766373754320449328533699 5649560631480673992800549)
                    ·
                      refine ⟨1059292618402626373650103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5649560631480673992800549 1059292618402626373650103)
                      ·
                        rfl

theorem cell23_2062965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2062965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2062965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2062965 prefixEnd_2062965 := by exact prefixLift 2062965
  have htrace : WordTrace (prefixWord ++ tailWord_2062965) baseStart_2062965 baseEnd_2062965 := by
    simpa [prefixWord, tailWord_2062965, baseEnd_2062965] using wordTrace_append hprefix tailTrace_2062965
  have hstable : (prefixWord ++ tailWord_2062965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062965).length < 2 ^ (prefixWord ++ tailWord_2062965).sum := by decide
  have hdescent : baseEnd_2062965 < baseStart_2062965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063024 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_2063024 : Nat := 118140960795 + 2063024 * 2 ^ 59
def prefixEnd_2063024 : Nat := 4983230072969 + 3 ^ 40 * 2063024 * 2
def baseEnd_2063024 : Nat := 1059322913761241642812331

theorem tailTrace_2063024 : CollatzResearch.WordTrace tailWord_2063024 prefixEnd_2063024 1059322913761241642812331 := by
  unfold tailWord_2063024
  simp only [CollatzResearch.WordTrace]
  refine ⟨37622333439011929646686063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50163111252015906195581417 37622333439011929646686063)
  ·
    refine ⟨56433500158517894470029095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37622333439011929646686063 56433500158517894470029095)
    ·
      refine ⟨84650250237776841705043643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56433500158517894470029095 84650250237776841705043643)
      ·
        refine ⟨126975375356665262557565465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84650250237776841705043643 126975375356665262557565465)
        ·
          refine ⟨95231531517498946918174099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126975375356665262557565465 95231531517498946918174099)
          ·
            refine ⟨142847297276248420377261149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95231531517498946918174099 142847297276248420377261149)
            ·
              refine ⟨53567736478593157641472931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142847297276248420377261149 53567736478593157641472931)
              ·
                refine ⟨80351604717889736462209397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53567736478593157641472931 80351604717889736462209397)
                ·
                  refine ⟨7532962942302162793332131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80351604717889736462209397 7532962942302162793332131)
                  ·
                    refine ⟨11299444413453244189998197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7532962942302162793332131 11299444413453244189998197)
                    ·
                      refine ⟨1059322913761241642812331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11299444413453244189998197 1059322913761241642812331)
                      ·
                        rfl

theorem cell23_2063024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_2063024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063024 prefixEnd_2063024 := by exact prefixLift 2063024
  have htrace : WordTrace (prefixWord ++ tailWord_2063024) baseStart_2063024 baseEnd_2063024 := by
    simpa [prefixWord, tailWord_2063024, baseEnd_2063024] using wordTrace_append hprefix tailTrace_2063024
  have hstable : (prefixWord ++ tailWord_2063024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063024).length < 2 ^ (prefixWord ++ tailWord_2063024).sum := by decide
  have hdescent : baseEnd_2063024 < baseStart_2063024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063038 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2063038 : Nat := 118140960795 + 2063038 * 2 ^ 59
def prefixEnd_2063038 : Nat := 4983230072969 + 3 ^ 40 * 2063038 * 2
def baseEnd_2063038 : Nat := 1059330102490404588037267

theorem tailTrace_2063038 : CollatzResearch.WordTrace tailWord_2063038 prefixEnd_2063038 1059330102490404588037267 := by
  unfold tailWord_2063038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405647187496642460547721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50163451666648759789587845 9405647187496642460547721)
  ·
    refine ⟨7054235390622481845410791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9405647187496642460547721 7054235390622481845410791)
    ·
      refine ⟨10581353085933722768116187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054235390622481845410791 10581353085933722768116187)
      ·
        refine ⟨15872029628900584152174281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581353085933722768116187 15872029628900584152174281)
        ·
          refine ⟨11904022221675438114130711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15872029628900584152174281 11904022221675438114130711)
          ·
            refine ⟨17856033332513157171196067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904022221675438114130711 17856033332513157171196067)
            ·
              refine ⟨26784049998769735756794101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17856033332513157171196067 26784049998769735756794101)
              ·
                refine ⟨2511004687384662727199447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26784049998769735756794101 2511004687384662727199447)
                ·
                  refine ⟨3766507031076994090799171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511004687384662727199447 3766507031076994090799171)
                  ·
                    refine ⟨5649760546615491136198757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766507031076994090799171 5649760546615491136198757)
                    ·
                      refine ⟨1059330102490404588037267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5649760546615491136198757 1059330102490404588037267)
                      ·
                        rfl

theorem cell23_2063038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2063038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063038 prefixEnd_2063038 := by exact prefixLift 2063038
  have htrace : WordTrace (prefixWord ++ tailWord_2063038) baseStart_2063038 baseEnd_2063038 := by
    simpa [prefixWord, tailWord_2063038, baseEnd_2063038] using wordTrace_append hprefix tailTrace_2063038
  have hstable : (prefixWord ++ tailWord_2063038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063038).length < 2 ^ (prefixWord ++ tailWord_2063038).sum := by decide
  have hdescent : baseEnd_2063038 < baseStart_2063038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063068 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2063068 : Nat := 118140960795 + 2063068 * 2 ^ 59
def prefixEnd_2063068 : Nat := 4983230072969 + 3 ^ 40 * 2063068 * 2
def baseEnd_2063068 : Nat := 1059345506910039470662129

theorem tailTrace_2063068 : CollatzResearch.WordTrace tailWord_2063068 prefixEnd_2063068 1059345506910039470662129 := by
  unfold tailWord_2063068
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623135844932227403986929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50164181126576303205315905 37623135844932227403986929)
  ·
    refine ⟨28217351883699170552990197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37623135844932227403986929 28217351883699170552990197)
    ·
      refine ⟨2645376739096797239342831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28217351883699170552990197 2645376739096797239342831)
      ·
        refine ⟨3968065108645195859014247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645376739096797239342831 3968065108645195859014247)
        ·
          refine ⟨5952097662967793788521371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968065108645195859014247 5952097662967793788521371)
          ·
            refine ⟨8928146494451690682782057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952097662967793788521371 8928146494451690682782057)
            ·
              refine ⟨6696109870838768012086543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8928146494451690682782057 6696109870838768012086543)
              ·
                refine ⟨10044164806258152018129815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696109870838768012086543 10044164806258152018129815)
                ·
                  refine ⟨15066247209387228027194723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10044164806258152018129815 15066247209387228027194723)
                  ·
                    refine ⟨22599370814080842040792085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15066247209387228027194723 22599370814080842040792085)
                    ·
                      refine ⟨1059345506910039470662129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22599370814080842040792085 1059345506910039470662129)
                      ·
                        rfl

theorem cell23_2063068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2063068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063068 prefixEnd_2063068 := by exact prefixLift 2063068
  have htrace : WordTrace (prefixWord ++ tailWord_2063068) baseStart_2063068 baseEnd_2063068 := by
    simpa [prefixWord, tailWord_2063068, baseEnd_2063068] using wordTrace_append hprefix tailTrace_2063068
  have hstable : (prefixWord ++ tailWord_2063068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063068).length < 2 ^ (prefixWord ++ tailWord_2063068).sum := by decide
  have hdescent : baseEnd_2063068 < baseStart_2063068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063075 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2063075 : Nat := 118140960795 + 2063075 * 2 ^ 59
def prefixEnd_2063075 : Nat := 4983230072969 + 3 ^ 40 * 2063075 * 2
def baseEnd_2063075 : Nat := 1059349101274620943274597

theorem tailTrace_2063075 : CollatzResearch.WordTrace tailWord_2063075 prefixEnd_2063075 1059349101274620943274597 := by
  unfold tailWord_2063075
  simp only [CollatzResearch.WordTrace]
  refine ⟨75246527000839095003478679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50164351333892730002319119 75246527000839095003478679)
  ·
    refine ⟨112869790501258642505218019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75246527000839095003478679 112869790501258642505218019)
    ·
      refine ⟨169304685751887963757827029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112869790501258642505218019 169304685751887963757827029)
      ·
        refine ⟨3968078572309874150574071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 169304685751887963757827029 3968078572309874150574071)
        ·
          refine ⟨5952117858464811225861107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968078572309874150574071 5952117858464811225861107)
          ·
            refine ⟨8928176787697216838791661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952117858464811225861107 8928176787697216838791661)
            ·
              refine ⟨3348066295386456314546873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928176787697216838791661 3348066295386456314546873)
              ·
                refine ⟨2511049721539842235910155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348066295386456314546873 2511049721539842235910155)
                ·
                  refine ⟨3766574582309763353865233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511049721539842235910155 3766574582309763353865233)
                  ·
                    refine ⟨2824930936732322515398925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766574582309763353865233 2824930936732322515398925)
                    ·
                      refine ⟨1059349101274620943274597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824930936732322515398925 1059349101274620943274597)
                      ·
                        rfl

theorem cell23_2063075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2063075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063075 prefixEnd_2063075 := by exact prefixLift 2063075
  have htrace : WordTrace (prefixWord ++ tailWord_2063075) baseStart_2063075 baseEnd_2063075 := by
    simpa [prefixWord, tailWord_2063075, baseEnd_2063075] using wordTrace_append hprefix tailTrace_2063075
  have hstable : (prefixWord ++ tailWord_2063075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063075).length < 2 ^ (prefixWord ++ tailWord_2063075).sum := by decide
  have hdescent : baseEnd_2063075 < baseStart_2063075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063106 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2063106 : Nat := 118140960795 + 2063106 * 2 ^ 59
def prefixEnd_2063106 : Nat := 4983230072969 + 3 ^ 40 * 2063106 * 2
def baseEnd_2063106 : Nat := 1059365019174910321986955

theorem tailTrace_2063106 : CollatzResearch.WordTrace tailWord_2063106 prefixEnd_2063106 1059365019174910321986955 := by
  unfold tailWord_2063106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18811914415931696824464293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50165105109151191531904781 18811914415931696824464293)
  ·
    refine ⟨3527233952987193154587055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18811914415931696824464293 3527233952987193154587055)
    ·
      refine ⟨5290850929480789731880583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527233952987193154587055 5290850929480789731880583)
      ·
        refine ⟨7936276394221184597820875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290850929480789731880583 7936276394221184597820875)
        ·
          refine ⟨11904414591331776896731313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936276394221184597820875 11904414591331776896731313)
          ·
            refine ⟨8928310943498832672548485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11904414591331776896731313 8928310943498832672548485)
            ·
              refine ⟨1674058301906031126102841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8928310943498832672548485 1674058301906031126102841)
              ·
                refine ⟨1255543726429523344577131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674058301906031126102841 1255543726429523344577131)
                ·
                  refine ⟨1883315589644285016865697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255543726429523344577131 1883315589644285016865697)
                  ·
                    refine ⟨1412486692233213762649273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883315589644285016865697 1412486692233213762649273)
                    ·
                      refine ⟨1059365019174910321986955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412486692233213762649273 1059365019174910321986955)
                      ·
                        rfl

theorem cell23_2063106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2063106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063106 prefixEnd_2063106 := by exact prefixLift 2063106
  have htrace : WordTrace (prefixWord ++ tailWord_2063106) baseStart_2063106 baseEnd_2063106 := by
    simpa [prefixWord, tailWord_2063106, baseEnd_2063106] using wordTrace_append hprefix tailTrace_2063106
  have hstable : (prefixWord ++ tailWord_2063106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063106).length < 2 ^ (prefixWord ++ tailWord_2063106).sum := by decide
  have hdescent : baseEnd_2063106 < baseStart_2063106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063122 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2063122 : Nat := 118140960795 + 2063122 * 2 ^ 59
def prefixEnd_2063122 : Nat := 4983230072969 + 3 ^ 40 * 2063122 * 2
def baseEnd_2063122 : Nat := 1059373234865382259386881

theorem tailTrace_2063122 : CollatzResearch.WordTrace tailWord_2063122 prefixEnd_2063122 1059373234865382259386881 := by
  unfold tailWord_2063122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812060307917205507609905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50165494154445881353626413 18812060307917205507609905)
  ·
    refine ⟨14109045230937904130707429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812060307917205507609905 14109045230937904130707429)
    ·
      refine ⟨2645445980800857024507643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14109045230937904130707429 2645445980800857024507643)
      ·
        refine ⟨3968168971201285536761465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645445980800857024507643 3968168971201285536761465)
        ·
          refine ⟨2976126728400964152571099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3968168971201285536761465 2976126728400964152571099)
          ·
            refine ⟨4464190092601446228856649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976126728400964152571099 4464190092601446228856649)
            ·
              refine ⟨3348142569451084671642487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464190092601446228856649 3348142569451084671642487)
              ·
                refine ⟨5022213854176627007463731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348142569451084671642487 5022213854176627007463731)
                ·
                  refine ⟨7533320781264940511195597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022213854176627007463731 7533320781264940511195597)
                  ·
                    refine ⟨2824995292974352691698349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7533320781264940511195597 2824995292974352691698349)
                    ·
                      refine ⟨1059373234865382259386881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2824995292974352691698349 1059373234865382259386881)
                      ·
                        rfl

theorem cell23_2063122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2063122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063122 prefixEnd_2063122 := by exact prefixLift 2063122
  have htrace : WordTrace (prefixWord ++ tailWord_2063122) baseStart_2063122 baseEnd_2063122 := by
    simpa [prefixWord, tailWord_2063122, baseEnd_2063122] using wordTrace_append hprefix tailTrace_2063122
  have hstable : (prefixWord ++ tailWord_2063122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063122).length < 2 ^ (prefixWord ++ tailWord_2063122).sum := by decide
  have hdescent : baseEnd_2063122 < baseStart_2063122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063141 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_2063141 : Nat := 118140960795 + 2063141 * 2 ^ 59
def prefixEnd_2063141 : Nat := 4983230072969 + 3 ^ 40 * 2063141 * 2
def baseEnd_2063141 : Nat := 1059382990997817685049293

theorem tailTrace_2063141 : CollatzResearch.WordTrace tailWord_2063141 prefixEnd_2063141 1059382990997817685049293 := by
  unfold tailWord_2063141
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248934218599988275381277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50165956145733325516920851 75248934218599988275381277)
  ·
    refine ⟨28218350331974995603267979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75248934218599988275381277 28218350331974995603267979)
    ·
      refine ⟨42327525497962493404901969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28218350331974995603267979 42327525497962493404901969)
      ·
        refine ⟨31745644123471870053676477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42327525497962493404901969 31745644123471870053676477)
        ·
          refine ⟨11904616546301951270128679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31745644123471870053676477 11904616546301951270128679)
          ·
            refine ⟨17856924819452926905193019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904616546301951270128679 17856924819452926905193019)
            ·
              refine ⟨26785387229179390357789529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17856924819452926905193019 26785387229179390357789529)
              ·
                refine ⟨20089040421884542768342147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26785387229179390357789529 20089040421884542768342147)
                ·
                  refine ⟨30133560632826814152513221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20089040421884542768342147 30133560632826814152513221)
                  ·
                    refine ⟨5650042618655027653596229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30133560632826814152513221 5650042618655027653596229)
                    ·
                      refine ⟨1059382990997817685049293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5650042618655027653596229 1059382990997817685049293)
                      ·
                        rfl

theorem cell23_2063141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_2063141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063141 prefixEnd_2063141 := by exact prefixLift 2063141
  have htrace : WordTrace (prefixWord ++ tailWord_2063141) baseStart_2063141 baseEnd_2063141 := by
    simpa [prefixWord, tailWord_2063141, baseEnd_2063141] using wordTrace_append hprefix tailTrace_2063141
  have hstable : (prefixWord ++ tailWord_2063141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063141).length < 2 ^ (prefixWord ++ tailWord_2063141).sum := by decide
  have hdescent : baseEnd_2063141 < baseStart_2063141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063156 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2063156 : Nat := 118140960795 + 2063156 * 2 ^ 59
def prefixEnd_2063156 : Nat := 4983230072969 + 3 ^ 40 * 2063156 * 2
def baseEnd_2063156 : Nat := 1059390693207635126361725

theorem tailTrace_2063156 : CollatzResearch.WordTrace tailWord_2063156 prefixEnd_2063156 1059390693207635126361725 := by
  unfold tailWord_2063156
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624740656772822918588661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50166320875697097224784881 37624740656772822918588661)
  ·
    refine ⟨3527319436572452148617687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37624740656772822918588661 3527319436572452148617687)
    ·
      refine ⟨5290979154858678222926531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527319436572452148617687 5290979154858678222926531)
      ·
        refine ⟨7936468732288017334389797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290979154858678222926531 7936468732288017334389797)
        ·
          refine ⟨1488087887304003250198087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7936468732288017334389797 1488087887304003250198087)
          ·
            refine ⟨2232131830956004875297131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488087887304003250198087 2232131830956004875297131)
            ·
              refine ⟨3348197746434007312945697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232131830956004875297131 3348197746434007312945697)
              ·
                refine ⟨2511148309825505484709273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348197746434007312945697 2511148309825505484709273)
                ·
                  refine ⟨1883361232369129113531955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511148309825505484709273 1883361232369129113531955)
                  ·
                    refine ⟨2825041848553693670297933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1883361232369129113531955 2825041848553693670297933)
                    ·
                      refine ⟨1059390693207635126361725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2825041848553693670297933 1059390693207635126361725)
                      ·
                        rfl

theorem cell23_2063156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2063156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063156 prefixEnd_2063156 := by exact prefixLift 2063156
  have htrace : WordTrace (prefixWord ++ tailWord_2063156) baseStart_2063156 baseEnd_2063156 := by
    simpa [prefixWord, tailWord_2063156, baseEnd_2063156] using wordTrace_append hprefix tailTrace_2063156
  have hstable : (prefixWord ++ tailWord_2063156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063156).length < 2 ^ (prefixWord ++ tailWord_2063156).sum := by decide
  have hdescent : baseEnd_2063156 < baseStart_2063156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063162 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_2063162 : Nat := 118140960795 + 2063162 * 2 ^ 59
def prefixEnd_2063162 : Nat := 4983230072969 + 3 ^ 40 * 2063162 * 2
def baseEnd_2063162 : Nat := 1059393774091562102886697

theorem tailTrace_2063162 : CollatzResearch.WordTrace tailWord_2063162 prefixEnd_2063162 1059393774091562102886697 := by
  unfold tailWord_2063162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812425037880977215473935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50166466767682605907930493 18812425037880977215473935)
  ·
    refine ⟨28218637556821465823210903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18812425037880977215473935 28218637556821465823210903)
    ·
      refine ⟨42327956335232198734816355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28218637556821465823210903 42327956335232198734816355)
      ·
        refine ⟨63491934502848298102224533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42327956335232198734816355 63491934502848298102224533)
        ·
          refine ⟨2976184429821013973541775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63491934502848298102224533 2976184429821013973541775)
          ·
            refine ⟨4464276644731520960312663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976184429821013973541775 4464276644731520960312663)
            ·
              refine ⟨6696414967097281440468995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464276644731520960312663 6696414967097281440468995)
              ·
                refine ⟨10044622450645922160703493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696414967097281440468995 10044622450645922160703493)
                ·
                  refine ⟨1883366709496110405131905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10044622450645922160703493 1883366709496110405131905)
                  ·
                    refine ⟨1412525032122082803848929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883366709496110405131905 1412525032122082803848929)
                    ·
                      refine ⟨1059393774091562102886697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412525032122082803848929 1059393774091562102886697)
                      ·
                        rfl

theorem cell23_2063162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_2063162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063162 prefixEnd_2063162 := by exact prefixLift 2063162
  have htrace : WordTrace (prefixWord ++ tailWord_2063162) baseStart_2063162 baseEnd_2063162 := by
    simpa [prefixWord, tailWord_2063162, baseEnd_2063162] using wordTrace_append hprefix tailTrace_2063162
  have hstable : (prefixWord ++ tailWord_2063162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063162).length < 2 ^ (prefixWord ++ tailWord_2063162).sum := by decide
  have hdescent : baseEnd_2063162 < baseStart_2063162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063218 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2063218 : Nat := 118140960795 + 2063218 * 2 ^ 59
def prefixEnd_2063218 : Nat := 4983230072969 + 3 ^ 40 * 2063218 * 2
def baseEnd_2063218 : Nat := 1059422529008213883786439

theorem tailTrace_2063218 : CollatzResearch.WordTrace tailWord_2063218 prefixEnd_2063218 1059422529008213883786439 := by
  unfold tailWord_2063218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812935659830257606483577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50167828426214020283956205 18812935659830257606483577)
  ·
    refine ⟨14109701744872693204862683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812935659830257606483577 14109701744872693204862683)
    ·
      refine ⟨21164552617309039807294025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109701744872693204862683 21164552617309039807294025)
      ·
        refine ⟨15873414462981779855470519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164552617309039807294025 15873414462981779855470519)
        ·
          refine ⟨23810121694472669783205779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873414462981779855470519 23810121694472669783205779)
          ·
            refine ⟨35715182541709004674808669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23810121694472669783205779 35715182541709004674808669)
            ·
              refine ⟨13393193453140876753053251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35715182541709004674808669 13393193453140876753053251)
              ·
                refine ⟨20089790179711315129579877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13393193453140876753053251 20089790179711315129579877)
                ·
                  refine ⟨3766835658695871586796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20089790179711315129579877 3766835658695871586796227)
                  ·
                    refine ⟨5650253488043807380194341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3766835658695871586796227 5650253488043807380194341)
                    ·
                      refine ⟨1059422529008213883786439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5650253488043807380194341 1059422529008213883786439)
                      ·
                        rfl

theorem cell23_2063218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2063218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063218 prefixEnd_2063218 := by exact prefixLift 2063218
  have htrace : WordTrace (prefixWord ++ tailWord_2063218) baseStart_2063218 baseEnd_2063218 := by
    simpa [prefixWord, tailWord_2063218, baseEnd_2063218] using wordTrace_append hprefix tailTrace_2063218
  have hstable : (prefixWord ++ tailWord_2063218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063218).length < 2 ^ (prefixWord ++ tailWord_2063218).sum := by decide
  have hdescent : baseEnd_2063218 < baseStart_2063218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063230 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2063230 : Nat := 118140960795 + 2063230 * 2 ^ 59
def prefixEnd_2063230 : Nat := 4983230072969 + 3 ^ 40 * 2063230 * 2
def baseEnd_2063230 : Nat := 1059428690776067836836385

theorem tailTrace_2063230 : CollatzResearch.WordTrace tailWord_2063230 prefixEnd_2063230 1059428690776067836836385 := by
  unfold tailWord_2063230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406522539409694559421393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50168120210185037650247429 9406522539409694559421393)
  ·
    refine ⟨7054891904557270919566045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9406522539409694559421393 7054891904557270919566045)
    ·
      refine ⟨2645584464208976594837267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7054891904557270919566045 2645584464208976594837267)
      ·
        refine ⟨3968376696313464892255901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645584464208976594837267 3968376696313464892255901)
        ·
          refine ⟨1488141261117549334595963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3968376696313464892255901 1488141261117549334595963)
          ·
            refine ⟨2232211891676324001893945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488141261117549334595963 2232211891676324001893945)
            ·
              refine ⟨1674158918757243001420459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232211891676324001893945 1674158918757243001420459)
              ·
                refine ⟨2511238378135864502130689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674158918757243001420459 2511238378135864502130689)
                ·
                  refine ⟨1883428783601898376598017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511238378135864502130689 1883428783601898376598017)
                  ·
                    refine ⟨1412571587701423782448513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883428783601898376598017 1412571587701423782448513)
                    ·
                      refine ⟨1059428690776067836836385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412571587701423782448513 1059428690776067836836385)
                      ·
                        rfl

theorem cell23_2063230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2063230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063230 prefixEnd_2063230 := by exact prefixLift 2063230
  have htrace : WordTrace (prefixWord ++ tailWord_2063230) baseStart_2063230 baseEnd_2063230 := by
    simpa [prefixWord, tailWord_2063230, baseEnd_2063230] using wordTrace_append hprefix tailTrace_2063230
  have hstable : (prefixWord ++ tailWord_2063230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063230).length < 2 ^ (prefixWord ++ tailWord_2063230).sum := by decide
  have hdescent : baseEnd_2063230 < baseStart_2063230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063231 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_2063231 : Nat := 118140960795 + 2063231 * 2 ^ 59
def prefixEnd_2063231 : Nat := 4983230072969 + 3 ^ 40 * 2063231 * 2
def baseEnd_2063231 : Nat := 1059429204256722332923879

theorem tailTrace_2063231 : CollatzResearch.WordTrace tailWord_2063231 prefixEnd_2063231 1059429204256722332923879 := by
  unfold tailWord_2063231
  simp only [CollatzResearch.WordTrace]
  refine ⟨75252216788273933646157547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50168144525515955764105031 75252216788273933646157547)
  ·
    refine ⟨112878325182410900469236321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75252216788273933646157547 112878325182410900469236321)
    ·
      refine ⟨84658743886808175351927241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112878325182410900469236321 84658743886808175351927241)
      ·
        refine ⟨63494057915106131513945431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84658743886808175351927241 63494057915106131513945431)
        ·
          refine ⟨95241086872659197270918147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63494057915106131513945431 95241086872659197270918147)
          ·
            refine ⟨142861630308988795906377221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95241086872659197270918147 142861630308988795906377221)
            ·
              refine ⟨26786555682935399232445729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142861630308988795906377221 26786555682935399232445729)
              ·
                refine ⟨20089916762201549424334297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26786555682935399232445729 20089916762201549424334297)
                ·
                  refine ⟨15067437571651162068250723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20089916762201549424334297 15067437571651162068250723)
                  ·
                    refine ⟨22601156357476743102376085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15067437571651162068250723 22601156357476743102376085)
                    ·
                      refine ⟨1059429204256722332923879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22601156357476743102376085 1059429204256722332923879)
                      ·
                        rfl

theorem cell23_2063231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_2063231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063231 prefixEnd_2063231 := by exact prefixLift 2063231
  have htrace : WordTrace (prefixWord ++ tailWord_2063231) baseStart_2063231 baseEnd_2063231 := by
    simpa [prefixWord, tailWord_2063231, baseEnd_2063231] using wordTrace_append hprefix tailTrace_2063231
  have hstable : (prefixWord ++ tailWord_2063231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063231).length < 2 ^ (prefixWord ++ tailWord_2063231).sum := by decide
  have hdescent : baseEnd_2063231 < baseStart_2063231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063255 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2063255 : Nat := 118140960795 + 2063255 * 2 ^ 59
def prefixEnd_2063255 : Nat := 4983230072969 + 3 ^ 40 * 2063255 * 2
def baseEnd_2063255 : Nat := 1059441527792430239023769

theorem tailTrace_2063255 : CollatzResearch.WordTrace tailWord_2063255 prefixEnd_2063255 1059441527792430239023769 := by
  unfold tailWord_2063255
  simp only [CollatzResearch.WordTrace]
  refine ⟨75253092140186985745031219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50168728093457990496687479 75253092140186985745031219)
  ·
    refine ⟨112879638210280478617546829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75253092140186985745031219 112879638210280478617546829)
    ·
      refine ⟨42329864328855179481580061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112879638210280478617546829 42329864328855179481580061)
      ·
        refine ⟨15873699123320692305592523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42329864328855179481580061 15873699123320692305592523)
        ·
          refine ⟨23810548684981038458388785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15873699123320692305592523 23810548684981038458388785)
          ·
            refine ⟨17857911513735778843791589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23810548684981038458388785 17857911513735778843791589)
            ·
              refine ⟨3348358408825458533210923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17857911513735778843791589 3348358408825458533210923)
              ·
                refine ⟨5022537613238187799816385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348358408825458533210923 5022537613238187799816385)
                ·
                  refine ⟨3766903209928640849862289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5022537613238187799816385 3766903209928640849862289)
                  ·
                    refine ⟨2825177407446480637396717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3766903209928640849862289 2825177407446480637396717)
                    ·
                      refine ⟨1059441527792430239023769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2825177407446480637396717 1059441527792430239023769)
                      ·
                        rfl

theorem cell23_2063255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2063255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063255 prefixEnd_2063255 := by exact prefixLift 2063255
  have htrace : WordTrace (prefixWord ++ tailWord_2063255) baseStart_2063255 baseEnd_2063255 := by
    simpa [prefixWord, tailWord_2063255, baseEnd_2063255] using wordTrace_append hprefix tailTrace_2063255
  have hstable : (prefixWord ++ tailWord_2063255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063255).length < 2 ^ (prefixWord ++ tailWord_2063255).sum := by decide
  have hdescent : baseEnd_2063255 < baseStart_2063255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063288 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_2063288 : Nat := 118140960795 + 2063288 * 2 ^ 59
def prefixEnd_2063288 : Nat := 4983230072969 + 3 ^ 40 * 2063288 * 2
def baseEnd_2063288 : Nat := 353152824218009536637039

theorem tailTrace_2063288 : CollatzResearch.WordTrace tailWord_2063288 prefixEnd_2063288 353152824218009536637039 := by
  unfold tailWord_2063288
  simp only [CollatzResearch.WordTrace]
  refine ⟨37627147874533716190491259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50169530499378288253988345 37627147874533716190491259)
  ·
    refine ⟨56440721811800574285736889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37627147874533716190491259 56440721811800574285736889)
    ·
      refine ⟨42330541358850430714302667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56440721811800574285736889 42330541358850430714302667)
      ·
        refine ⟨63495812038275646071454001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42330541358850430714302667 63495812038275646071454001)
        ·
          refine ⟨47621859028706734553590501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63495812038275646071454001 47621859028706734553590501)
          ·
            refine ⟨8929098567882512728798219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47621859028706734553590501 8929098567882512728798219)
            ·
              refine ⟨13393647851823769093197329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929098567882512728798219 13393647851823769093197329)
              ·
                refine ⟨10045235888867826819897997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13393647851823769093197329 10045235888867826819897997)
                ·
                  refine ⟨3766963458325435057461749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10045235888867826819897997 3766963458325435057461749)
                  ·
                    refine ⟨353152824218009536637039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3766963458325435057461749 353152824218009536637039)
                    ·
                      rfl

theorem cell23_2063288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_2063288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063288 prefixEnd_2063288 := by exact prefixLift 2063288
  have htrace : WordTrace (prefixWord ++ tailWord_2063288) baseStart_2063288 baseEnd_2063288 := by
    simpa [prefixWord, tailWord_2063288, baseEnd_2063288] using wordTrace_append hprefix tailTrace_2063288
  have hstable : (prefixWord ++ tailWord_2063288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063288).length < 2 ^ (prefixWord ++ tailWord_2063288).sum := by decide
  have hdescent : baseEnd_2063288 < baseStart_2063288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063322 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_2063322 : Nat := 118140960795 + 2063322 * 2 ^ 59
def prefixEnd_2063322 : Nat := 4983230072969 + 3 ^ 40 * 2063322 * 2
def baseEnd_2063322 : Nat := 353158643665427158961987

theorem tailTrace_2063322 : CollatzResearch.WordTrace tailWord_2063322 prefixEnd_2063322 353158643665427158961987 := by
  unfold tailWord_2063322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813883957736064046930055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50170357220629504125146813 18813883957736064046930055)
  ·
    refine ⟨28220825936604096070395083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813883957736064046930055 28220825936604096070395083)
    ·
      refine ⟨42331238904906144105592625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28220825936604096070395083 42331238904906144105592625)
      ·
        refine ⟨31748429178679608079194469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42331238904906144105592625 31748429178679608079194469)
        ·
          refine ⟨5952830471002426514848963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31748429178679608079194469 5952830471002426514848963)
          ·
            refine ⟨8929245706503639772273445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952830471002426514848963 8929245706503639772273445)
            ·
              refine ⟨1674233569969432457301271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8929245706503639772273445 1674233569969432457301271)
              ·
                refine ⟨2511350354954148685951907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674233569969432457301271 2511350354954148685951907)
                ·
                  refine ⟨3767025532431223028927861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511350354954148685951907 3767025532431223028927861)
                  ·
                    refine ⟨353158643665427158961987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3767025532431223028927861 353158643665427158961987)
                    ·
                      rfl

theorem cell23_2063322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_2063322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063322 prefixEnd_2063322 := by exact prefixLift 2063322
  have htrace : WordTrace (prefixWord ++ tailWord_2063322) baseStart_2063322 baseEnd_2063322 := by
    simpa [prefixWord, tailWord_2063322, baseEnd_2063322] using wordTrace_append hprefix tailTrace_2063322
  have hstable : (prefixWord ++ tailWord_2063322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063322).length < 2 ^ (prefixWord ++ tailWord_2063322).sum := by decide
  have hdescent : baseEnd_2063322 < baseStart_2063322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063345 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_2063345 : Nat := 118140960795 + 2063345 * 2 ^ 59
def prefixEnd_2063345 : Nat := 4983230072969 + 3 ^ 40 * 2063345 * 2
def baseEnd_2063345 : Nat := 1059487741051334886898355

theorem tailTrace_2063345 : CollatzResearch.WordTrace tailWord_2063345 prefixEnd_2063345 1059487741051334886898355 := by
  unfold tailWord_2063345
  simp only [CollatzResearch.WordTrace]
  refine ⟨75256374709860931115807489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50170916473240620743871659 75256374709860931115807489)
  ·
    refine ⟨56442281032395698336855617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75256374709860931115807489 56442281032395698336855617)
    ·
      refine ⟨42331710774296773752641713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56442281032395698336855617 42331710774296773752641713)
      ·
        refine ⟨31748783080722580314481285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42331710774296773752641713 31748783080722580314481285)
        ·
          refine ⟨5952896827635483808965241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31748783080722580314481285 5952896827635483808965241)
          ·
            refine ⟨4464672620726612856723931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952896827635483808965241 4464672620726612856723931)
            ·
              refine ⟨6697008931089919285085897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464672620726612856723931 6697008931089919285085897)
              ·
                refine ⟨5022756698317439463814423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697008931089919285085897 5022756698317439463814423)
                ·
                  refine ⟨7534135047476159195721635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022756698317439463814423 7534135047476159195721635)
                  ·
                    refine ⟨11301202571214238793582453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7534135047476159195721635 11301202571214238793582453)
                    ·
                      refine ⟨1059487741051334886898355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11301202571214238793582453 1059487741051334886898355)
                      ·
                        rfl

theorem cell23_2063345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_2063345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063345 prefixEnd_2063345 := by exact prefixLift 2063345
  have htrace : WordTrace (prefixWord ++ tailWord_2063345) baseStart_2063345 baseEnd_2063345 := by
    simpa [prefixWord, tailWord_2063345, baseEnd_2063345] using wordTrace_append hprefix tailTrace_2063345
  have hstable : (prefixWord ++ tailWord_2063345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063345).length < 2 ^ (prefixWord ++ tailWord_2063345).sum := by decide
  have hdescent : baseEnd_2063345 < baseStart_2063345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063393 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2063393 : Nat := 118140960795 + 2063393 * 2 ^ 59
def prefixEnd_2063393 : Nat := 4983230072969 + 3 ^ 40 * 2063393 * 2
def baseEnd_2063393 : Nat := 1059512388122750699098135

theorem tailTrace_2063393 : CollatzResearch.WordTrace tailWord_2063393 prefixEnd_2063393 1059512388122750699098135 := by
  unfold tailWord_2063393
  simp only [CollatzResearch.WordTrace]
  refine ⟨75258125413687035313554833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50172083609124690209036555 75258125413687035313554833)
  ·
    refine ⟨56443594060265276485166125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75258125413687035313554833 56443594060265276485166125)
    ·
      refine ⟨21166347772599478681937297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56443594060265276485166125 21166347772599478681937297)
      ·
        refine ⟨15874760829449609011452973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21166347772599478681937297 15874760829449609011452973)
        ·
          refine ⟨5953035311043603379294865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15874760829449609011452973 5953035311043603379294865)
          ·
            refine ⟨4464776483282702534471149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953035311043603379294865 4464776483282702534471149)
            ·
              refine ⟨1674291181231013450426681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4464776483282702534471149 1674291181231013450426681)
              ·
                refine ⟨1255718385923260087820011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674291181231013450426681 1255718385923260087820011)
                ·
                  refine ⟨1883577578884890131730017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255718385923260087820011 1883577578884890131730017)
                  ·
                    refine ⟨1412683184163667598797513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883577578884890131730017 1412683184163667598797513)
                    ·
                      refine ⟨1059512388122750699098135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412683184163667598797513 1059512388122750699098135)
                      ·
                        rfl

theorem cell23_2063393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2063393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063393 prefixEnd_2063393 := by exact prefixLift 2063393
  have htrace : WordTrace (prefixWord ++ tailWord_2063393) baseStart_2063393 baseEnd_2063393 := by
    simpa [prefixWord, tailWord_2063393, baseEnd_2063393] using wordTrace_append hprefix tailTrace_2063393
  have hstable : (prefixWord ++ tailWord_2063393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063393).length < 2 ^ (prefixWord ++ tailWord_2063393).sum := by decide
  have hdescent : baseEnd_2063393 < baseStart_2063393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063408 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_2063408 : Nat := 118140960795 + 2063408 * 2 ^ 59
def prefixEnd_2063408 : Nat := 4983230072969 + 3 ^ 40 * 2063408 * 2
def baseEnd_2063408 : Nat := 353173363444189380136855

theorem tailTrace_2063408 : CollatzResearch.WordTrace tailWord_2063408 prefixEnd_2063408 353173363444189380136855 := by
  unfold tailWord_2063408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37629336254316346437675439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50172448339088461916900585 37629336254316346437675439)
  ·
    refine ⟨56444004381474519656513159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37629336254316346437675439 56444004381474519656513159)
    ·
      refine ⟨84666006572211779484769739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56444004381474519656513159 84666006572211779484769739)
      ·
        refine ⟨126999009858317669227154609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84666006572211779484769739 126999009858317669227154609)
        ·
          refine ⟨95249257393738251920365957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126999009858317669227154609 95249257393738251920365957)
          ·
            refine ⟨17859235761325922235068617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95249257393738251920365957 17859235761325922235068617)
            ·
              refine ⟨13394426820994441676301463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17859235761325922235068617 13394426820994441676301463)
              ·
                refine ⟨20091640231491662514452195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394426820994441676301463 20091640231491662514452195)
                ·
                  refine ⟨30137460347237493771678293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20091640231491662514452195 30137460347237493771678293)
                  ·
                    refine ⟨353173363444189380136855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30137460347237493771678293 353173363444189380136855)
                    ·
                      rfl

theorem cell23_2063408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_2063408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063408 prefixEnd_2063408 := by exact prefixLift 2063408
  have htrace : WordTrace (prefixWord ++ tailWord_2063408) baseStart_2063408 baseEnd_2063408 := by
    simpa [prefixWord, tailWord_2063408, baseEnd_2063408] using wordTrace_append hprefix tailTrace_2063408
  have hstable : (prefixWord ++ tailWord_2063408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063408).length < 2 ^ (prefixWord ++ tailWord_2063408).sum := by decide
  have hdescent : baseEnd_2063408 < baseStart_2063408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063432 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_2063432 : Nat := 118140960795 + 2063432 * 2 ^ 59
def prefixEnd_2063432 : Nat := 4983230072969 + 3 ^ 40 * 2063432 * 2
def baseEnd_2063432 : Nat := 1059532413868276046510455

theorem tailTrace_2063432 : CollatzResearch.WordTrace tailWord_2063432 prefixEnd_2063432 1059532413868276046510455 := by
  unfold tailWord_2063432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37629773930272872487112275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50173031907030496649483033 37629773930272872487112275)
  ·
    refine ⟨56444660895409308730668413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37629773930272872487112275 56444660895409308730668413)
    ·
      refine ⟨21166747835778490774000655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56444660895409308730668413 21166747835778490774000655)
      ·
        refine ⟨31750121753667736161000983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21166747835778490774000655 31750121753667736161000983)
        ·
          refine ⟨47625182630501604241501475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31750121753667736161000983 47625182630501604241501475)
          ·
            refine ⟨71437773945752406362252213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47625182630501604241501475 71437773945752406362252213)
            ·
              refine ⟨6697291307414288096461145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71437773945752406362252213 6697291307414288096461145)
              ·
                refine ⟨5022968480560716072345859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6697291307414288096461145 5022968480560716072345859)
                ·
                  refine ⟨7534452720841074108518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022968480560716072345859 7534452720841074108518789)
                  ·
                    refine ⟨1412709885157701395347273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7534452720841074108518789 1412709885157701395347273)
                    ·
                      refine ⟨1059532413868276046510455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412709885157701395347273 1059532413868276046510455)
                      ·
                        rfl

theorem cell23_2063432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_2063432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063432 prefixEnd_2063432 := by exact prefixLift 2063432
  have htrace : WordTrace (prefixWord ++ tailWord_2063432) baseStart_2063432 baseEnd_2063432 := by
    simpa [prefixWord, tailWord_2063432, baseEnd_2063432] using wordTrace_append hprefix tailTrace_2063432
  have hstable : (prefixWord ++ tailWord_2063432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063432).length < 2 ^ (prefixWord ++ tailWord_2063432).sum := by decide
  have hdescent : baseEnd_2063432 < baseStart_2063432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063445 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2063445 : Nat := 118140960795 + 2063445 * 2 ^ 59
def prefixEnd_2063445 : Nat := 4983230072969 + 3 ^ 40 * 2063445 * 2
def baseEnd_2063445 : Nat := 1059539089116784495647895

theorem tailTrace_2063445 : CollatzResearch.WordTrace tailWord_2063445 prefixEnd_2063445 1059539089116784495647895 := by
  unfold tailWord_2063445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75260022009498648194447789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50173348006332432129631859 75260022009498648194447789)
  ·
    refine ⟨28222508253561993072917921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75260022009498648194447789 28222508253561993072917921)
    ·
      refine ⟨21166881190171494804688441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28222508253561993072917921 21166881190171494804688441)
      ·
        refine ⟨15875160892628621103516331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21166881190171494804688441 15875160892628621103516331)
        ·
          refine ⟨23812741338942931655274497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875160892628621103516331 23812741338942931655274497)
          ·
            refine ⟨17859556004207198741455873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23812741338942931655274497 17859556004207198741455873)
            ·
              refine ⟨13394667003155399056091905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17859556004207198741455873 13394667003155399056091905)
              ·
                refine ⟨10046000252366549292068929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13394667003155399056091905 10046000252366549292068929)
                ·
                  refine ⟨7534500189274911969051697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046000252366549292068929 7534500189274911969051697)
                  ·
                    refine ⟨5650875141956183976788773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7534500189274911969051697 5650875141956183976788773)
                    ·
                      refine ⟨1059539089116784495647895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5650875141956183976788773 1059539089116784495647895)
                      ·
                        rfl

theorem cell23_2063445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2063445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063445 prefixEnd_2063445 := by exact prefixLift 2063445
  have htrace : WordTrace (prefixWord ++ tailWord_2063445) baseStart_2063445 baseEnd_2063445 := by
    simpa [prefixWord, tailWord_2063445, baseEnd_2063445] using wordTrace_append hprefix tailTrace_2063445
  have hstable : (prefixWord ++ tailWord_2063445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063445).length < 2 ^ (prefixWord ++ tailWord_2063445).sum := by decide
  have hdescent : baseEnd_2063445 < baseStart_2063445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063465 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_2063465 : Nat := 118140960795 + 2063465 * 2 ^ 59
def prefixEnd_2063465 : Nat := 4983230072969 + 3 ^ 40 * 2063465 * 2
def baseEnd_2063465 : Nat := 1059549358729874417397803

theorem tailTrace_2063465 : CollatzResearch.WordTrace tailWord_2063465 prefixEnd_2063465 1059549358729874417397803 := by
  unfold tailWord_2063465
  simp only [CollatzResearch.WordTrace]
  refine ⟨75260751469426191610175849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50173834312950794406783899 75260751469426191610175849)
  ·
    refine ⟨56445563602069643707631887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75260751469426191610175849 56445563602069643707631887)
    ·
      refine ⟨84668345403104465561447831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56445563602069643707631887 84668345403104465561447831)
      ·
        refine ⟨127002518104656698342171747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84668345403104465561447831 127002518104656698342171747)
        ·
          refine ⟨190503777156985047513257621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127002518104656698342171747 190503777156985047513257621)
          ·
            refine ⟨8929864554233674102183951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190503777156985047513257621 8929864554233674102183951)
            ·
              refine ⟨13394796831350511153275927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929864554233674102183951 13394796831350511153275927)
              ·
                refine ⟨20092195247025766729913891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13394796831350511153275927 20092195247025766729913891)
                ·
                  refine ⟨30138292870538650094870837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20092195247025766729913891 30138292870538650094870837)
                  ·
                    refine ⟨2825464956612998446394141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30138292870538650094870837 2825464956612998446394141)
                    ·
                      refine ⟨1059549358729874417397803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2825464956612998446394141 1059549358729874417397803)
                      ·
                        rfl

theorem cell23_2063465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_2063465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063465 prefixEnd_2063465 := by exact prefixLift 2063465
  have htrace : WordTrace (prefixWord ++ tailWord_2063465) baseStart_2063465 baseEnd_2063465 := by
    simpa [prefixWord, tailWord_2063465, baseEnd_2063465] using wordTrace_append hprefix tailTrace_2063465
  have hstable : (prefixWord ++ tailWord_2063465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063465).length < 2 ^ (prefixWord ++ tailWord_2063465).sum := by decide
  have hdescent : baseEnd_2063465 < baseStart_2063465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063466 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2063466 : Nat := 118140960795 + 2063466 * 2 ^ 59
def prefixEnd_2063466 : Nat := 4983230072969 + 3 ^ 40 * 2063466 * 2
def baseEnd_2063466 : Nat := 1059549872210528913485299

theorem tailTrace_2063466 : CollatzResearch.WordTrace tailWord_2063466 prefixEnd_2063466 1059549872210528913485299 := by
  unfold tailWord_2063466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815196985605642195240563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50173858628281712520641501 18815196985605642195240563)
  ·
    refine ⟨28222795478408463292860845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18815196985605642195240563 28222795478408463292860845)
    ·
      refine ⟨10583548304403173734822817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28222795478408463292860845 10583548304403173734822817)
      ·
        refine ⟨7937661228302380301117113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10583548304403173734822817 7937661228302380301117113)
        ·
          refine ⟨5953245921226785225837835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937661228302380301117113 5953245921226785225837835)
          ·
            refine ⟨8929868881840177838756753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953245921226785225837835 8929868881840177838756753)
            ·
              refine ⟨6697401661380133379067565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929868881840177838756753 6697401661380133379067565)
              ·
                refine ⟨2511525623017550017150337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6697401661380133379067565 2511525623017550017150337)
                ·
                  refine ⟨1883644217263162512862753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511525623017550017150337 1883644217263162512862753)
                  ·
                    refine ⟨1412733162947371884647065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1883644217263162512862753 1412733162947371884647065)
                    ·
                      refine ⟨1059549872210528913485299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412733162947371884647065 1059549872210528913485299)
                      ·
                        rfl

theorem cell23_2063466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2063466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063466 prefixEnd_2063466 := by exact prefixLift 2063466
  have htrace : WordTrace (prefixWord ++ tailWord_2063466) baseStart_2063466 baseEnd_2063466 := by
    simpa [prefixWord, tailWord_2063466, baseEnd_2063466] using wordTrace_append hprefix tailTrace_2063466
  have hstable : (prefixWord ++ tailWord_2063466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063466).length < 2 ^ (prefixWord ++ tailWord_2063466).sum := by decide
  have hdescent : baseEnd_2063466 < baseStart_2063466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063485 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2063485 : Nat := 118140960795 + 2063485 * 2 ^ 59
def prefixEnd_2063485 : Nat := 4983230072969 + 3 ^ 40 * 2063485 * 2
def baseEnd_2063485 : Nat := 353186542780988113049237

theorem tailTrace_2063485 : CollatzResearch.WordTrace tailWord_2063485 prefixEnd_2063485 353186542780988113049237 := by
  unfold tailWord_2063485
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261480929353735025903909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50174320619569156683935939 75261480929353735025903909)
  ·
    refine ⟨14111527674253825317356983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75261480929353735025903909 14111527674253825317356983)
    ·
      refine ⟨21167291511380737976035475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111527674253825317356983 21167291511380737976035475)
      ·
        refine ⟨31750937267071106964053213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167291511380737976035475 31750937267071106964053213)
        ·
          refine ⟨11906601475151665111519955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31750937267071106964053213 11906601475151665111519955)
          ·
            refine ⟨17859902212727497667279933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906601475151665111519955 17859902212727497667279933)
            ·
              refine ⟨6697463329772811625229975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17859902212727497667279933 6697463329772811625229975)
              ·
                refine ⟨10046194994659217437844963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697463329772811625229975 10046194994659217437844963)
                ·
                  refine ⟨15069292491988826156767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10046194994659217437844963 15069292491988826156767445)
                  ·
                    refine ⟨353186542780988113049237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15069292491988826156767445 353186542780988113049237)
                    ·
                      rfl

theorem cell23_2063485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2063485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063485 prefixEnd_2063485 := by exact prefixLift 2063485
  have htrace : WordTrace (prefixWord ++ tailWord_2063485) baseStart_2063485 baseEnd_2063485 := by
    simpa [prefixWord, tailWord_2063485, baseEnd_2063485] using wordTrace_append hprefix tailTrace_2063485
  have hstable : (prefixWord ++ tailWord_2063485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063485).length < 2 ^ (prefixWord ++ tailWord_2063485).sum := by decide
  have hdescent : baseEnd_2063485 < baseStart_2063485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063489 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 5]
def baseStart_2063489 : Nat := 118140960795 + 2063489 * 2 ^ 59
def prefixEnd_2063489 : Nat := 4983230072969 + 3 ^ 40 * 2063489 * 2
def baseEnd_2063489 : Nat := 117729075807286924833077

theorem tailTrace_2063489 : CollatzResearch.WordTrace tailWord_2063489 prefixEnd_2063489 117729075807286924833077 := by
  unfold tailWord_2063489
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261626821339243709049521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50174417880892829139366347 75261626821339243709049521)
  ·
    refine ⟨56446220116004432781787141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75261626821339243709049521 56446220116004432781787141)
    ·
      refine ⟨10583666271750831146585089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56446220116004432781787141 10583666271750831146585089)
      ·
        refine ⟨7937749703813123359938817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10583666271750831146585089 7937749703813123359938817)
        ·
          refine ⟨5953312277859842519954113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937749703813123359938817 5953312277859842519954113)
          ·
            refine ⟨4464984208394881889965585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953312277859842519954113 4464984208394881889965585)
            ·
              refine ⟨3348738156296161417474189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464984208394881889965585 3348738156296161417474189)
              ·
                refine ⟨1255776808611060531552821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3348738156296161417474189 1255776808611060531552821)
                ·
                  refine ⟨117729075807286924833077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1255776808611060531552821 117729075807286924833077)
                  ·
                    rfl

theorem cell23_2063489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 5].length) (baseStart_2063489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063489 prefixEnd_2063489 := by exact prefixLift 2063489
  have htrace : WordTrace (prefixWord ++ tailWord_2063489) baseStart_2063489 baseEnd_2063489 := by
    simpa [prefixWord, tailWord_2063489, baseEnd_2063489] using wordTrace_append hprefix tailTrace_2063489
  have hstable : (prefixWord ++ tailWord_2063489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063489).length < 2 ^ (prefixWord ++ tailWord_2063489).sum := by decide
  have hdescent : baseEnd_2063489 < baseStart_2063489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063545 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 8]
def baseStart_2063545 : Nat := 118140960795 + 2063545 * 2 ^ 59
def prefixEnd_2063545 : Nat := 4983230072969 + 3 ^ 40 * 2063545 * 2
def baseEnd_2063545 : Nat := 117732270798026011599715

theorem tailTrace_2063545 : CollatzResearch.WordTrace tailWord_2063545 prefixEnd_2063545 117732270798026011599715 := by
  unfold tailWord_2063545
  simp only [CollatzResearch.WordTrace]
  refine ⟨75263669309136365273088089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50175779539424243515392059 75263669309136365273088089)
  ·
    refine ⟨56447751981852273954816067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75263669309136365273088089 56447751981852273954816067)
    ·
      refine ⟨84671627972778410932224101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56447751981852273954816067 84671627972778410932224101)
      ·
        refine ⟨15875930244895952049792019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84671627972778410932224101 15875930244895952049792019)
        ·
          refine ⟨23813895367343928074688029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15875930244895952049792019 23813895367343928074688029)
          ·
            refine ⟨8930210762753973028008011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23813895367343928074688029 8930210762753973028008011)
            ·
              refine ⟨13395316144130959542012017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930210762753973028008011 13395316144130959542012017)
              ·
                refine ⟨10046487108098219656509013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13395316144130959542012017 10046487108098219656509013)
                ·
                  refine ⟨117732270798026011599715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10046487108098219656509013 117732270798026011599715)
                  ·
                    rfl

theorem cell23_2063545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_2063545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063545 prefixEnd_2063545 := by exact prefixLift 2063545
  have htrace : WordTrace (prefixWord ++ tailWord_2063545) baseStart_2063545 baseEnd_2063545 := by
    simpa [prefixWord, tailWord_2063545, baseEnd_2063545] using wordTrace_append hprefix tailTrace_2063545
  have hstable : (prefixWord ++ tailWord_2063545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063545).length < 2 ^ (prefixWord ++ tailWord_2063545).sum := by decide
  have hdescent : baseEnd_2063545 < baseStart_2063545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063566 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2063566 : Nat := 118140960795 + 2063566 * 2 ^ 59
def prefixEnd_2063566 : Nat := 4983230072969 + 3 ^ 40 * 2063566 * 2
def baseEnd_2063566 : Nat := 353200406758659507411613

theorem tailTrace_2063566 : CollatzResearch.WordTrace tailWord_2063566 prefixEnd_2063566 353200406758659507411613 := by
  unfold tailWord_2063566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408054405257535732450319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50176290161373523906401701 9408054405257535732450319)
  ·
    refine ⟨14112081607886303598675479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9408054405257535732450319 14112081607886303598675479)
    ·
      refine ⟨21168122411829455398013219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14112081607886303598675479 21168122411829455398013219)
      ·
        refine ⟨31752183617744183097019829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21168122411829455398013219 31752183617744183097019829)
        ·
          refine ⟨2976767214163517165345609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31752183617744183097019829 2976767214163517165345609)
          ·
            refine ⟨2232575410622637874009207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2976767214163517165345609 2232575410622637874009207)
            ·
              refine ⟨3348863115933956811013811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232575410622637874009207 3348863115933956811013811)
              ·
                refine ⟨5023294673900935216520717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348863115933956811013811 5023294673900935216520717)
                ·
                  refine ⟨1883735502712850706195269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5023294673900935216520717 1883735502712850706195269)
                  ·
                    refine ⟨353200406758659507411613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883735502712850706195269 353200406758659507411613)
                    ·
                      rfl

theorem cell23_2063566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2063566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063566 prefixEnd_2063566 := by exact prefixLift 2063566
  have htrace : WordTrace (prefixWord ++ tailWord_2063566) baseStart_2063566 baseEnd_2063566 := by
    simpa [prefixWord, tailWord_2063566, baseEnd_2063566] using wordTrace_append hprefix tailTrace_2063566
  have hstable : (prefixWord ++ tailWord_2063566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063566).length < 2 ^ (prefixWord ++ tailWord_2063566).sum := by decide
  have hdescent : baseEnd_2063566 < baseStart_2063566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063592 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2063592 : Nat := 118140960795 + 2063592 * 2 ^ 59
def prefixEnd_2063592 : Nat := 4983230072969 + 3 ^ 40 * 2063592 * 2
def baseEnd_2063592 : Nat := 353204856924331806836573

theorem tailTrace_2063592 : CollatzResearch.WordTrace tailWord_2063592 prefixEnd_2063592 353204856924331806836573 := by
  unfold tailWord_2063592
  simp only [CollatzResearch.WordTrace]
  refine ⟨37632691769983046150024515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50176922359977394866699353 37632691769983046150024515)
  ·
    refine ⟨56449037654974569225036773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37632691769983046150024515 56449037654974569225036773)
    ·
      refine ⟨10584194560307731729694395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56449037654974569225036773 10584194560307731729694395)
      ·
        refine ⟨15876291840461597594541593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584194560307731729694395 15876291840461597594541593)
        ·
          refine ⟨11907218880346198195906195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15876291840461597594541593 11907218880346198195906195)
          ·
            refine ⟨17860828320519297293859293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11907218880346198195906195 17860828320519297293859293)
            ·
              refine ⟨6697810620194736485197235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17860828320519297293859293 6697810620194736485197235)
              ·
                refine ⟨10046715930292104727795853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697810620194736485197235 10046715930292104727795853)
                ·
                  refine ⟨3767518473859539272923445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10046715930292104727795853 3767518473859539272923445)
                  ·
                    refine ⟨353204856924331806836573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3767518473859539272923445 353204856924331806836573)
                    ·
                      rfl

theorem cell23_2063592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2063592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063592 prefixEnd_2063592 := by exact prefixLift 2063592
  have htrace : WordTrace (prefixWord ++ tailWord_2063592) baseStart_2063592 baseEnd_2063592 := by
    simpa [prefixWord, tailWord_2063592, baseEnd_2063592] using wordTrace_append hprefix tailTrace_2063592
  have hstable : (prefixWord ++ tailWord_2063592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063592).length < 2 ^ (prefixWord ++ tailWord_2063592).sum := by decide
  have hdescent : baseEnd_2063592 < baseStart_2063592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063609 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_2063609 : Nat := 118140960795 + 2063609 * 2 ^ 59
def prefixEnd_2063609 : Nat := 4983230072969 + 3 ^ 40 * 2063609 * 2
def baseEnd_2063609 : Nat := 353207766648040617999047

theorem tailTrace_2063609 : CollatzResearch.WordTrace tailWord_2063609 prefixEnd_2063609 353207766648040617999047 := by
  unfold tailWord_2063609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75266003580904504203417881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50177335720603002802278587 75266003580904504203417881)
  ·
    refine ⟨56449502685678378152563411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75266003580904504203417881 56449502685678378152563411)
    ·
      refine ⟨84674254028517567228845117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56449502685678378152563411 84674254028517567228845117)
      ·
        refine ⟨31752845260694087710816919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84674254028517567228845117 31752845260694087710816919)
        ·
          refine ⟨47629267891041131566225379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31752845260694087710816919 47629267891041131566225379)
          ·
            refine ⟨71443901836561697349338069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47629267891041131566225379 71443901836561697349338069)
            ·
              refine ⟨1674466449294414781625111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71443901836561697349338069 1674466449294414781625111)
              ·
                refine ⟨2511699673941622172437667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674466449294414781625111 2511699673941622172437667)
                ·
                  refine ⟨3767549510912433258656501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511699673941622172437667 3767549510912433258656501)
                  ·
                    refine ⟨353207766648040617999047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3767549510912433258656501 353207766648040617999047)
                    ·
                      rfl

theorem cell23_2063609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_2063609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063609 prefixEnd_2063609 := by exact prefixLift 2063609
  have htrace : WordTrace (prefixWord ++ tailWord_2063609) baseStart_2063609 baseEnd_2063609 := by
    simpa [prefixWord, tailWord_2063609, baseEnd_2063609] using wordTrace_append hprefix tailTrace_2063609
  have hstable : (prefixWord ++ tailWord_2063609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063609).length < 2 ^ (prefixWord ++ tailWord_2063609).sum := by decide
  have hdescent : baseEnd_2063609 < baseStart_2063609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063639 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 2, 4]
def baseStart_2063639 : Nat := 118140960795 + 2063639 * 2 ^ 59
def prefixEnd_2063639 : Nat := 4983230072969 + 3 ^ 40 * 2063639 * 2
def baseEnd_2063639 : Nat := 353212901454585578874001

theorem tailTrace_2063639 : CollatzResearch.WordTrace tailWord_2063639 prefixEnd_2063639 353212901454585578874001 := by
  unfold tailWord_2063639
  simp only [CollatzResearch.WordTrace]
  refine ⟨75267097770795819327009971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50178065180530546218006647 75267097770795819327009971)
  ·
    refine ⟨112900646656193728990514957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75267097770795819327009971 112900646656193728990514957)
    ·
      refine ⟨42337742496072648371443109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112900646656193728990514957 42337742496072648371443109)
      ·
        refine ⟨7938326718013621569645583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42337742496072648371443109 7938326718013621569645583)
        ·
          refine ⟨11907490077020432354468375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938326718013621569645583 11907490077020432354468375)
          ·
            refine ⟨17861235115530648531702563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11907490077020432354468375 17861235115530648531702563)
            ·
              refine ⟨26791852673295972797553845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17861235115530648531702563 26791852673295972797553845)
              ·
                refine ⟨2511736188121497449770673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26791852673295972797553845 2511736188121497449770673)
                ·
                  refine ⟨1883802141091123087328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511736188121497449770673 1883802141091123087328005)
                  ·
                    refine ⟨353212901454585578874001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883802141091123087328005 353212901454585578874001)
                    ·
                      rfl

theorem cell23_2063639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_2063639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063639 prefixEnd_2063639 := by exact prefixLift 2063639
  have htrace : WordTrace (prefixWord ++ tailWord_2063639) baseStart_2063639 baseEnd_2063639 := by
    simpa [prefixWord, tailWord_2063639, baseEnd_2063639] using wordTrace_append hprefix tailTrace_2063639
  have hstable : (prefixWord ++ tailWord_2063639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063639).length < 2 ^ (prefixWord ++ tailWord_2063639).sum := by decide
  have hdescent : baseEnd_2063639 < baseStart_2063639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063649 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2063649 : Nat := 118140960795 + 2063649 * 2 ^ 59
def prefixEnd_2063649 : Nat := 4983230072969 + 3 ^ 40 * 2063649 * 2
def baseEnd_2063649 : Nat := 1059643839170301697496957

theorem tailTrace_2063649 : CollatzResearch.WordTrace tailWord_2063649 prefixEnd_2063649 1059643839170301697496957 := by
  unfold tailWord_2063649
  simp only [CollatzResearch.WordTrace]
  refine ⟨75267462500759591034874001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50178308333839727356582667 75267462500759591034874001)
  ·
    refine ⟨56450596875569693276155501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75267462500759591034874001 56450596875569693276155501)
    ·
      refine ⟨21168973828338634978558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56450596875569693276155501 21168973828338634978558313)
      ·
        refine ⟨15876730371253976233918735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21168973828338634978558313 15876730371253976233918735)
        ·
          refine ⟨23815095556880964350878103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876730371253976233918735 23815095556880964350878103)
          ·
            refine ⟨35722643335321446526317155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23815095556880964350878103 35722643335321446526317155)
            ·
              refine ⟨53583965002982169789475733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35722643335321446526317155 53583965002982169789475733)
              ·
                refine ⟨2511748359514789208881675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53583965002982169789475733 2511748359514789208881675)
                ·
                  refine ⟨3767622539272183813322513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511748359514789208881675 3767622539272183813322513)
                  ·
                    refine ⟨2825716904454137859991885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3767622539272183813322513 2825716904454137859991885)
                    ·
                      refine ⟨1059643839170301697496957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2825716904454137859991885 1059643839170301697496957)
                      ·
                        rfl

theorem cell23_2063649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2063649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063649 prefixEnd_2063649 := by exact prefixLift 2063649
  have htrace : WordTrace (prefixWord ++ tailWord_2063649) baseStart_2063649 baseEnd_2063649 := by
    simpa [prefixWord, tailWord_2063649, baseEnd_2063649] using wordTrace_append hprefix tailTrace_2063649
  have hstable : (prefixWord ++ tailWord_2063649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063649).length < 2 ^ (prefixWord ++ tailWord_2063649).sum := by decide
  have hdescent : baseEnd_2063649 < baseStart_2063649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063650 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2063650 : Nat := 118140960795 + 2063650 * 2 ^ 59
def prefixEnd_2063650 : Nat := 4983230072969 + 3 ^ 40 * 2063650 * 2
def baseEnd_2063650 : Nat := 1059644352650956193584453

theorem tailTrace_2063650 : CollatzResearch.WordTrace tailWord_2063650 prefixEnd_2063650 1059644352650956193584453 := by
  unfold tailWord_2063650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816874743438992051415101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50178332649170645470440269 18816874743438992051415101)
  ·
    refine ⟨7056328028789622019280663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18816874743438992051415101 7056328028789622019280663)
    ·
      refine ⟨10584492043184433028920995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056328028789622019280663 10584492043184433028920995)
      ·
        refine ⟨15876738064776649543381493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10584492043184433028920995 15876738064776649543381493)
        ·
          refine ⟨1488444193572810894692015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15876738064776649543381493 1488444193572810894692015)
          ·
            refine ⟨2232666290359216342038023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488444193572810894692015 2232666290359216342038023)
            ·
              refine ⟨3348999435538824513057035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232666290359216342038023 3348999435538824513057035)
              ·
                refine ⟨5023499153308236769585553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348999435538824513057035 5023499153308236769585553)
                ·
                  refine ⟨3767624364981177577189165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5023499153308236769585553 3767624364981177577189165)
                  ·
                    refine ⟨1412859136867941591445937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767624364981177577189165 1412859136867941591445937)
                    ·
                      refine ⟨1059644352650956193584453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412859136867941591445937 1059644352650956193584453)
                      ·
                        rfl

theorem cell23_2063650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2063650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063650 prefixEnd_2063650 := by exact prefixLift 2063650
  have htrace : WordTrace (prefixWord ++ tailWord_2063650) baseStart_2063650 baseEnd_2063650 := by
    simpa [prefixWord, tailWord_2063650, baseEnd_2063650] using wordTrace_append hprefix tailTrace_2063650
  have hstable : (prefixWord ++ tailWord_2063650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063650).length < 2 ^ (prefixWord ++ tailWord_2063650).sum := by decide
  have hdescent : baseEnd_2063650 < baseStart_2063650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063666 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2063666 : Nat := 118140960795 + 2063666 * 2 ^ 59
def prefixEnd_2063666 : Nat := 4983230072969 + 3 ^ 40 * 2063666 * 2
def baseEnd_2063666 : Nat := 1059652568341428130984379

theorem tailTrace_2063666 : CollatzResearch.WordTrace tailWord_2063666 prefixEnd_2063666 1059652568341428130984379 := by
  unfold tailWord_2063666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817020635424500734560713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50178721694465335292161901 18817020635424500734560713)
  ·
    refine ⟨14112765476568375550920535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18817020635424500734560713 14112765476568375550920535)
    ·
      refine ⟨21169148214852563326380803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14112765476568375550920535 21169148214852563326380803)
      ·
        refine ⟨31753722322278844989571205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21169148214852563326380803 31753722322278844989571205)
        ·
          refine ⟨5953822935427283435544601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31753722322278844989571205 5953822935427283435544601)
          ·
            refine ⟨4465367201570462576658451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953822935427283435544601 4465367201570462576658451)
            ·
              refine ⟨6698050802355693864987677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465367201570462576658451 6698050802355693864987677)
              ·
                refine ⟨2511769050883385199370379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698050802355693864987677 2511769050883385199370379)
                ·
                  refine ⟨3767653576325077799055569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511769050883385199370379 3767653576325077799055569)
                  ·
                    refine ⟨2825740182243808349291677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3767653576325077799055569 2825740182243808349291677)
                    ·
                      refine ⟨1059652568341428130984379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2825740182243808349291677 1059652568341428130984379)
                      ·
                        rfl

theorem cell23_2063666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2063666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063666 prefixEnd_2063666 := by exact prefixLift 2063666
  have htrace : WordTrace (prefixWord ++ tailWord_2063666) baseStart_2063666 baseEnd_2063666 := by
    simpa [prefixWord, tailWord_2063666, baseEnd_2063666] using wordTrace_append hprefix tailTrace_2063666
  have hstable : (prefixWord ++ tailWord_2063666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063666).length < 2 ^ (prefixWord ++ tailWord_2063666).sum := by decide
  have hdescent : baseEnd_2063666 < baseStart_2063666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063673 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_2063673 : Nat := 118140960795 + 2063673 * 2 ^ 59
def prefixEnd_2063673 : Nat := 4983230072969 + 3 ^ 40 * 2063673 * 2
def baseEnd_2063673 : Nat := 353218720902003201198949

theorem tailTrace_2063673 : CollatzResearch.WordTrace tailWord_2063673 prefixEnd_2063673 353218720902003201198949 := by
  unfold tailWord_2063673
  simp only [CollatzResearch.WordTrace]
  refine ⟨75268337852672643133747673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50178891901781762089165115 75268337852672643133747673)
  ·
    refine ⟨56451253389504482350310755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75268337852672643133747673 56451253389504482350310755)
    ·
      refine ⟨84676880084256723525466133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56451253389504482350310755 84676880084256723525466133)
      ·
        refine ⟨3969228753949533915256225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84676880084256723525466133 3969228753949533915256225)
        ·
          refine ⟨2976921565462150436442169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3969228753949533915256225 2976921565462150436442169)
          ·
            refine ⟨2232691174096612827331627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2976921565462150436442169 2232691174096612827331627)
            ·
              refine ⟨3349036761144919240997441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232691174096612827331627 3349036761144919240997441)
              ·
                refine ⟨2511777570858689430748081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349036761144919240997441 2511777570858689430748081)
                ·
                  refine ⟨1883833178144017073061061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511777570858689430748081 1883833178144017073061061)
                  ·
                    refine ⟨353218720902003201198949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883833178144017073061061 353218720902003201198949)
                    ·
                      rfl

theorem cell23_2063673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_2063673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063673 prefixEnd_2063673 := by exact prefixLift 2063673
  have htrace : WordTrace (prefixWord ++ tailWord_2063673) baseStart_2063673 baseEnd_2063673 := by
    simpa [prefixWord, tailWord_2063673, baseEnd_2063673] using wordTrace_append hprefix tailTrace_2063673
  have hstable : (prefixWord ++ tailWord_2063673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063673).length < 2 ^ (prefixWord ++ tailWord_2063673).sum := by decide
  have hdescent : baseEnd_2063673 < baseStart_2063673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063689 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 5, 3, 2]
def baseStart_2063689 : Nat := 118140960795 + 2063689 * 2 ^ 59
def prefixEnd_2063689 : Nat := 4983230072969 + 3 ^ 40 * 2063689 * 2
def baseEnd_2063689 : Nat := 1059664378396481540996773

theorem tailTrace_2063689 : CollatzResearch.WordTrace tailWord_2063689 prefixEnd_2063689 1059664378396481540996773 := by
  unfold tailWord_2063689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75268921420614677866330121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50179280947076451910886747 75268921420614677866330121)
  ·
    refine ⟨56451691065461008399747591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75268921420614677866330121 56451691065461008399747591)
    ·
      refine ⟨84677536598191512599621387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56451691065461008399747591 84677536598191512599621387)
      ·
        refine ⟨127016304897287268899432081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84677536598191512599621387 127016304897287268899432081)
        ·
          refine ⟨95262228672965451674574061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127016304897287268899432081 95262228672965451674574061)
          ·
            refine ⟨35723335752362044377965273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95262228672965451674574061 35723335752362044377965273)
            ·
              refine ⟨26792501814271533283473955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35723335752362044377965273 26792501814271533283473955)
              ·
                refine ⟨40188752721407299925210933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26792501814271533283473955 40188752721407299925210933)
                ·
                  refine ⟨3767695567631934367988525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40188752721407299925210933 3767695567631934367988525)
                  ·
                    refine ⟨1412885837861975387995697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767695567631934367988525 1412885837861975387995697)
                    ·
                      refine ⟨1059664378396481540996773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412885837861975387995697 1059664378396481540996773)
                      ·
                        rfl

theorem cell23_2063689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3, 2].length) (baseStart_2063689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063689 prefixEnd_2063689 := by exact prefixLift 2063689
  have htrace : WordTrace (prefixWord ++ tailWord_2063689) baseStart_2063689 baseEnd_2063689 := by
    simpa [prefixWord, tailWord_2063689, baseEnd_2063689] using wordTrace_append hprefix tailTrace_2063689
  have hstable : (prefixWord ++ tailWord_2063689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063689).length < 2 ^ (prefixWord ++ tailWord_2063689).sum := by decide
  have hdescent : baseEnd_2063689 < baseStart_2063689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063706 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_2063706 : Nat := 118140960795 + 2063706 * 2 ^ 59
def prefixEnd_2063706 : Nat := 4983230072969 + 3 ^ 40 * 2063706 * 2
def baseEnd_2063706 : Nat := 1059673107567607974484195

theorem tailTrace_2063706 : CollatzResearch.WordTrace tailWord_2063706 prefixEnd_2063706 1059673107567607974484195 := by
  unfold tailWord_2063706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817385365388272442424743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50179694307702059846465981 18817385365388272442424743)
  ·
    refine ⟨28226078048082408663637115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18817385365388272442424743 28226078048082408663637115)
    ·
      refine ⟨42339117072123612995455673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28226078048082408663637115 42339117072123612995455673)
      ·
        refine ⟨31754337804092709746591755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42339117072123612995455673 31754337804092709746591755)
        ·
          refine ⟨47631506706139064619887633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31754337804092709746591755 47631506706139064619887633)
          ·
            refine ⟨35723630029604298464915725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47631506706139064619887633 35723630029604298464915725)
            ·
              refine ⟨13396361261101611924343397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35723630029604298464915725 13396361261101611924343397)
              ·
                refine ⟨2511817736456552235814387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13396361261101611924343397 2511817736456552235814387)
                ·
                  refine ⟨3767726604684828353721581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511817736456552235814387 3767726604684828353721581)
                  ·
                    refine ⟨1412897476756810632645593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767726604684828353721581 1412897476756810632645593)
                    ·
                      refine ⟨1059673107567607974484195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1412897476756810632645593 1059673107567607974484195)
                      ·
                        rfl

theorem cell23_2063706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_2063706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063706 prefixEnd_2063706 := by exact prefixLift 2063706
  have htrace : WordTrace (prefixWord ++ tailWord_2063706) baseStart_2063706 baseEnd_2063706 := by
    simpa [prefixWord, tailWord_2063706, baseEnd_2063706] using wordTrace_append hprefix tailTrace_2063706
  have hstable : (prefixWord ++ tailWord_2063706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063706).length < 2 ^ (prefixWord ++ tailWord_2063706).sum := by decide
  have hdescent : baseEnd_2063706 < baseStart_2063706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063802 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_2063802 : Nat := 118140960795 + 2063802 * 2 ^ 59
def prefixEnd_2063802 : Nat := 4983230072969 + 3 ^ 40 * 2063802 * 2
def baseEnd_2063802 : Nat := 353240800570146532961251

theorem tailTrace_2063802 : CollatzResearch.WordTrace tailWord_2063802 prefixEnd_2063802 353240800570146532961251 := by
  unfold tailWord_2063802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818260717301324541298415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50182028579470198776795773 18818260717301324541298415)
  ·
    refine ⟨28227391075951986811947623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18818260717301324541298415 28227391075951986811947623)
    ·
      refine ⟨42341086613927980217921435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28227391075951986811947623 42341086613927980217921435)
      ·
        refine ⟨63511629920891970326882153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42341086613927980217921435 63511629920891970326882153)
        ·
          refine ⟨47633722440668977745161615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63511629920891970326882153 47633722440668977745161615)
          ·
            refine ⟨71450583661003466617742423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47633722440668977745161615 71450583661003466617742423)
            ·
              refine ⟨107175875491505199926613635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71450583661003466617742423 107175875491505199926613635)
              ·
                refine ⟨160763813237257799889920453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107175875491505199926613635 160763813237257799889920453)
                ·
                  refine ⟨30143214981985837479360085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160763813237257799889920453 30143214981985837479360085)
                  ·
                    refine ⟨353240800570146532961251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30143214981985837479360085 353240800570146532961251)
                    ·
                      rfl

theorem cell23_2063802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_2063802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063802 prefixEnd_2063802 := by exact prefixLift 2063802
  have htrace : WordTrace (prefixWord ++ tailWord_2063802) baseStart_2063802 baseEnd_2063802 := by
    simpa [prefixWord, tailWord_2063802, baseEnd_2063802] using wordTrace_append hprefix tailTrace_2063802
  have hstable : (prefixWord ++ tailWord_2063802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063802).length < 2 ^ (prefixWord ++ tailWord_2063802).sum := by decide
  have hdescent : baseEnd_2063802 < baseStart_2063802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063819 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 5, 4]
def baseStart_2063819 : Nat := 118140960795 + 2063819 * 2 ^ 59
def prefixEnd_2063819 : Nat := 4983230072969 + 3 ^ 40 * 2063819 * 2
def baseEnd_2063819 : Nat := 353243710293855344123725

theorem tailTrace_2063819 : CollatzResearch.WordTrace tailWord_2063819 prefixEnd_2063819 353243710293855344123725 := by
  unfold tailWord_2063819
  simp only [CollatzResearch.WordTrace]
  refine ⟨75273662910143710068562511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50182441940095806712375007 75273662910143710068562511)
  ·
    refine ⟨112910494365215565102843767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75273662910143710068562511 112910494365215565102843767)
    ·
      refine ⟨169365741547823347654265651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112910494365215565102843767 169365741547823347654265651)
      ·
        refine ⟨254048612321735021481398477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169365741547823347654265651 254048612321735021481398477)
        ·
          refine ⟨95268229620650633055524429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254048612321735021481398477 95268229620650633055524429)
          ·
            refine ⟨35725586107743987395821661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95268229620650633055524429 35725586107743987395821661)
            ·
              refine ⟨13397094790403995273433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35725586107743987395821661 13397094790403995273433123)
              ·
                refine ⟨20095642185605992910149685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397094790403995273433123 20095642185605992910149685)
                ·
                  refine ⟨1883966454900561835326533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20095642185605992910149685 1883966454900561835326533)
                  ·
                    refine ⟨353243710293855344123725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883966454900561835326533 353243710293855344123725)
                    ·
                      rfl

theorem cell23_2063819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 4].length) (baseStart_2063819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063819 prefixEnd_2063819 := by exact prefixLift 2063819
  have htrace : WordTrace (prefixWord ++ tailWord_2063819) baseStart_2063819 baseEnd_2063819 := by
    simpa [prefixWord, tailWord_2063819, baseEnd_2063819] using wordTrace_append hprefix tailTrace_2063819
  have hstable : (prefixWord ++ tailWord_2063819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063819).length < 2 ^ (prefixWord ++ tailWord_2063819).sum := by decide
  have hdescent : baseEnd_2063819 < baseStart_2063819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063866 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_2063866 : Nat := 118140960795 + 2063866 * 2 ^ 59
def prefixEnd_2063866 : Nat := 4983230072969 + 3 ^ 40 * 2063866 * 2
def baseEnd_2063866 : Nat := 117750584941369705387051

theorem tailTrace_2063866 : CollatzResearch.WordTrace tailWord_2063866 prefixEnd_2063866 117750584941369705387051 := by
  unfold tailWord_2063866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818844285243359273880863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50183584760648958063682301 18818844285243359273880863)
  ·
    refine ⟨28228266427865038910821295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18818844285243359273880863 28228266427865038910821295)
    ·
      refine ⟨42342399641797558366231943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28228266427865038910821295 42342399641797558366231943)
      ·
        refine ⟨63513599462696337549347915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42342399641797558366231943 63513599462696337549347915)
        ·
          refine ⟨95270399194044506324021873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63513599462696337549347915 95270399194044506324021873)
          ·
            refine ⟨71452799395533379743016405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95270399194044506324021873 71452799395533379743016405)
            ·
              refine ⟨1674674985832813587726947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71452799395533379743016405 1674674985832813587726947)
              ·
                refine ⟨2512012478749220381590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674674985832813587726947 2512012478749220381590421)
                ·
                  refine ⟨117750584941369705387051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2512012478749220381590421 117750584941369705387051)
                  ·
                    rfl

theorem cell23_2063866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_2063866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063866 prefixEnd_2063866 := by exact prefixLift 2063866
  have htrace : WordTrace (prefixWord ++ tailWord_2063866) baseStart_2063866 baseEnd_2063866 := by
    simpa [prefixWord, tailWord_2063866, baseEnd_2063866] using wordTrace_append hprefix tailTrace_2063866
  have hstable : (prefixWord ++ tailWord_2063866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063866).length < 2 ^ (prefixWord ++ tailWord_2063866).sum := by decide
  have hdescent : baseEnd_2063866 < baseStart_2063866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063933 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2063933 : Nat := 118140960795 + 2063933 * 2 ^ 59
def prefixEnd_2063933 : Nat := 4983230072969 + 3 ^ 40 * 2063933 * 2
def baseEnd_2063933 : Nat := 1059789667676178586345651

theorem tailTrace_2063933 : CollatzResearch.WordTrace tailWord_2063933 prefixEnd_2063933 1059789667676178586345651 := by
  unfold tailWord_2063933
  simp only [CollatzResearch.WordTrace]
  refine ⟨75277820831730707538212453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50185213887820471692141635 75277820831730707538212453)
  ·
    refine ⟨14114591405949507663414835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75277820831730707538212453 14114591405949507663414835)
    ·
      refine ⟨21171887108924261495122253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114591405949507663414835 21171887108924261495122253)
      ·
        refine ⟨7939457665846598060670845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21171887108924261495122253 7939457665846598060670845)
        ·
          refine ⟨2977296624692474272751567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7939457665846598060670845 2977296624692474272751567)
          ·
            refine ⟨4465944937038711409127351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977296624692474272751567 4465944937038711409127351)
            ·
              refine ⟨6698917405558067113691027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465944937038711409127351 6698917405558067113691027)
              ·
                refine ⟨10048376108337100670536541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698917405558067113691027 10048376108337100670536541)
                ·
                  refine ⟨3768141040626412751451203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10048376108337100670536541 3768141040626412751451203)
                  ·
                    refine ⟨5652211560939619127176805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768141040626412751451203 5652211560939619127176805)
                    ·
                      refine ⟨1059789667676178586345651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5652211560939619127176805 1059789667676178586345651)
                      ·
                        rfl

theorem cell23_2063933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2063933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063933 prefixEnd_2063933 := by exact prefixLift 2063933
  have htrace : WordTrace (prefixWord ++ tailWord_2063933) baseStart_2063933 baseEnd_2063933 := by
    simpa [prefixWord, tailWord_2063933, baseEnd_2063933] using wordTrace_append hprefix tailTrace_2063933
  have hstable : (prefixWord ++ tailWord_2063933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063933).length < 2 ^ (prefixWord ++ tailWord_2063933).sum := by decide
  have hdescent : baseEnd_2063933 < baseStart_2063933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063946 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2063946 : Nat := 118140960795 + 2063946 * 2 ^ 59
def prefixEnd_2063946 : Nat := 4983230072969 + 3 ^ 40 * 2063946 * 2
def baseEnd_2063946 : Nat := 1059796342924687035483091

theorem tailTrace_2063946 : CollatzResearch.WordTrace tailWord_2063946 prefixEnd_2063946 1059796342924687035483091 := by
  unfold tailWord_2063946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819573745170902689608923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50185529987122407172290461 18819573745170902689608923)
  ·
    refine ⟨28229360617756354034413385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18819573745170902689608923 28229360617756354034413385)
    ·
      refine ⟨21172020463317265525810039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28229360617756354034413385 21172020463317265525810039)
      ·
        refine ⟨31758030694975898288715059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21172020463317265525810039 31758030694975898288715059)
        ·
          refine ⟨47637046042463847433072589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31758030694975898288715059 47637046042463847433072589)
          ·
            refine ⟨17863892265923942787402221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47637046042463847433072589 17863892265923942787402221)
            ·
              refine ⟨6698959599721478545275833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17863892265923942787402221 6698959599721478545275833)
              ·
                refine ⟨5024219699791108908956875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6698959599721478545275833 5024219699791108908956875)
                ·
                  refine ⟨7536329549686663363435313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024219699791108908956875 7536329549686663363435313)
                  ·
                    refine ⟨5652247162264997522576485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7536329549686663363435313 5652247162264997522576485)
                    ·
                      refine ⟨1059796342924687035483091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5652247162264997522576485 1059796342924687035483091)
                      ·
                        rfl

theorem cell23_2063946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2063946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063946 prefixEnd_2063946 := by exact prefixLift 2063946
  have htrace : WordTrace (prefixWord ++ tailWord_2063946) baseStart_2063946 baseEnd_2063946 := by
    simpa [prefixWord, tailWord_2063946, baseEnd_2063946] using wordTrace_append hprefix tailTrace_2063946
  have hstable : (prefixWord ++ tailWord_2063946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063946).length < 2 ^ (prefixWord ++ tailWord_2063946).sum := by decide
  have hdescent : baseEnd_2063946 < baseStart_2063946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063969 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2063969 : Nat := 118140960795 + 2063969 * 2 ^ 59
def prefixEnd_2063969 : Nat := 4983230072969 + 3 ^ 40 * 2063969 * 2
def baseEnd_2063969 : Nat := 353269384326580148498495

theorem tailTrace_2063969 : CollatzResearch.WordTrace tailWord_2063969 prefixEnd_2063969 353269384326580148498495 := by
  unfold tailWord_2063969
  simp only [CollatzResearch.WordTrace]
  refine ⟨75279133859600285686522961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50186089239733523791015307 75279133859600285686522961)
  ·
    refine ⟨56459350394700214264892221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75279133859600285686522961 56459350394700214264892221)
    ·
      refine ⟨21172256398012580349334583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56459350394700214264892221 21172256398012580349334583)
      ·
        refine ⟨31758384597018870524001875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21172256398012580349334583 31758384597018870524001875)
        ·
          refine ⟨47637576895528305786002813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31758384597018870524001875 47637576895528305786002813)
          ·
            refine ⟨17864091335823114669751055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47637576895528305786002813 17864091335823114669751055)
            ·
              refine ⟨26796137003734672004626583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17864091335823114669751055 26796137003734672004626583)
              ·
                refine ⟨40194205505602008006939875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26796137003734672004626583 40194205505602008006939875)
                ·
                  refine ⟨60291308258403012010409813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40194205505602008006939875 60291308258403012010409813)
                  ·
                    refine ⟨353269384326580148498495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60291308258403012010409813 353269384326580148498495)
                    ·
                      rfl

theorem cell23_2063969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2063969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063969 prefixEnd_2063969 := by exact prefixLift 2063969
  have htrace : WordTrace (prefixWord ++ tailWord_2063969) baseStart_2063969 baseEnd_2063969 := by
    simpa [prefixWord, tailWord_2063969, baseEnd_2063969] using wordTrace_append hprefix tailTrace_2063969
  have hstable : (prefixWord ++ tailWord_2063969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063969).length < 2 ^ (prefixWord ++ tailWord_2063969).sum := by decide
  have hdescent : baseEnd_2063969 < baseStart_2063969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063993 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 3, 3, 2]
def baseStart_2063993 : Nat := 118140960795 + 2063993 * 2 ^ 59
def prefixEnd_2063993 : Nat := 4983230072969 + 3 ^ 40 * 2063993 * 2
def baseEnd_2063993 : Nat := 1059820476515448351595375

theorem tailTrace_2063993 : CollatzResearch.WordTrace tailWord_2063993 prefixEnd_2063993 1059820476515448351595375 := by
  unfold tailWord_2063993
  simp only [CollatzResearch.WordTrace]
  refine ⟨75280009211513337785396633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50186672807675558523597755 75280009211513337785396633)
  ·
    refine ⟨56460006908635003339047475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75280009211513337785396633 56460006908635003339047475)
    ·
      refine ⟨84690010362952505008571213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56460006908635003339047475 84690010362952505008571213)
      ·
        refine ⟨31758753886107189378214205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84690010362952505008571213 31758753886107189378214205)
        ·
          refine ⟨11909532707290196016830327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31758753886107189378214205 11909532707290196016830327)
          ·
            refine ⟨17864299060935294025245491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11909532707290196016830327 17864299060935294025245491)
            ·
              refine ⟨26796448591402941037868237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17864299060935294025245491 26796448591402941037868237)
              ·
                refine ⟨10048668221776102889200589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26796448591402941037868237 10048668221776102889200589)
                ·
                  refine ⟨3768250583166038583450221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10048668221776102889200589 3768250583166038583450221)
                  ·
                    refine ⟨1413093968687264468793833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768250583166038583450221 1413093968687264468793833)
                    ·
                      refine ⟨1059820476515448351595375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413093968687264468793833 1059820476515448351595375)
                      ·
                        rfl

theorem cell23_2063993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_2063993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2063993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2063993 prefixEnd_2063993 := by exact prefixLift 2063993
  have htrace : WordTrace (prefixWord ++ tailWord_2063993) baseStart_2063993 baseEnd_2063993 := by
    simpa [prefixWord, tailWord_2063993, baseEnd_2063993] using wordTrace_append hprefix tailTrace_2063993
  have hstable : (prefixWord ++ tailWord_2063993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063993).length < 2 ^ (prefixWord ++ tailWord_2063993).sum := by decide
  have hdescent : baseEnd_2063993 < baseStart_2063993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064004 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_2064004 : Nat := 118140960795 + 2064004 * 2 ^ 59
def prefixEnd_2064004 : Nat := 4983230072969 + 3 ^ 40 * 2064004 * 2
def baseEnd_2064004 : Nat := 1059826124802647808557825

theorem tailTrace_2064004 : CollatzResearch.WordTrace tailWord_2064004 prefixEnd_2064004 1059826124802647808557825 := by
  unfold tailWord_2064004
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640205207236743332023533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50186940276315657776031377 37640205207236743332023533)
  ·
    refine ⟨14115076952713778749508825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37640205207236743332023533 14115076952713778749508825)
    ·
      refine ⟨10586307714535334062131619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14115076952713778749508825 10586307714535334062131619)
      ·
        refine ⟨15879461571803001093197429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586307714535334062131619 15879461571803001093197429)
        ·
          refine ⟨1488699522356531352487259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15879461571803001093197429 1488699522356531352487259)
          ·
            refine ⟨2233049283534797028730889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488699522356531352487259 2233049283534797028730889)
            ·
              refine ⟨1674786962651097771548167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233049283534797028730889 1674786962651097771548167)
              ·
                refine ⟨2512180443976646657322251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674786962651097771548167 2512180443976646657322251)
                ·
                  refine ⟨3768270665964969985983377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512180443976646657322251 3768270665964969985983377)
                  ·
                    refine ⟨2826202999473727489487533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768270665964969985983377 2826202999473727489487533)
                    ·
                      refine ⟨1059826124802647808557825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826202999473727489487533 1059826124802647808557825)
                      ·
                        rfl

theorem cell23_2064004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_2064004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064004 prefixEnd_2064004 := by exact prefixLift 2064004
  have htrace : WordTrace (prefixWord ++ tailWord_2064004) baseStart_2064004 baseEnd_2064004 := by
    simpa [prefixWord, tailWord_2064004, baseEnd_2064004] using wordTrace_append hprefix tailTrace_2064004
  have hstable : (prefixWord ++ tailWord_2064004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064004).length < 2 ^ (prefixWord ++ tailWord_2064004).sum := by decide
  have hdescent : baseEnd_2064004 < baseStart_2064004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064019 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_2064019 : Nat := 118140960795 + 2064019 * 2 ^ 59
def prefixEnd_2064019 : Nat := 4983230072969 + 3 ^ 40 * 2064019 * 2
def baseEnd_2064019 : Nat := 1059833827012465249870255

theorem tailTrace_2064019 : CollatzResearch.WordTrace tailWord_2064019 prefixEnd_2064019 1059833827012465249870255 := by
  unfold tailWord_2064019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75280957509419144225843111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50187305006279429483895407 75280957509419144225843111)
  ·
    refine ⟨112921436264128716338764667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75280957509419144225843111 112921436264128716338764667)
    ·
      refine ⟨169382154396193074508147001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112921436264128716338764667 169382154396193074508147001)
      ·
        refine ⟨127036615797144805881110251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169382154396193074508147001 127036615797144805881110251)
        ·
          refine ⟨190554923695717208821665377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127036615797144805881110251 190554923695717208821665377)
          ·
            refine ⟨142916192771787906616249033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190554923695717208821665377 142916192771787906616249033)
            ·
              refine ⟨107187144578840929962186775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142916192771787906616249033 107187144578840929962186775)
              ·
                refine ⟨160780716868261394943280163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107187144578840929962186775 160780716868261394943280163)
                ·
                  refine ⟨241171075302392092414920245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160780716868261394943280163 241171075302392092414920245)
                  ·
                    refine ⟨22609788309599258663898773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241171075302392092414920245 22609788309599258663898773)
                    ·
                      refine ⟨1059833827012465249870255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22609788309599258663898773 1059833827012465249870255)
                      ·
                        rfl

theorem cell23_2064019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_2064019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064019 prefixEnd_2064019 := by exact prefixLift 2064019
  have htrace : WordTrace (prefixWord ++ tailWord_2064019) baseStart_2064019 baseEnd_2064019 := by
    simpa [prefixWord, tailWord_2064019, baseEnd_2064019] using wordTrace_append hprefix tailTrace_2064019
  have hstable : (prefixWord ++ tailWord_2064019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064019).length < 2 ^ (prefixWord ++ tailWord_2064019).sum := by decide
  have hdescent : baseEnd_2064019 < baseStart_2064019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064034 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2064034 : Nat := 118140960795 + 2064034 * 2 ^ 59
def prefixEnd_2064034 : Nat := 4983230072969 + 3 ^ 40 * 2064034 * 2
def baseEnd_2064034 : Nat := 1059841529222282691182687

theorem tailTrace_2064034 : CollatzResearch.WordTrace tailWord_2064034 prefixEnd_2064034 1059841529222282691182687 := by
  unfold tailWord_2064034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820376151091200446909789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50187669736243201191759437 18820376151091200446909789)
  ·
    refine ⟨7057641056659200167591171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18820376151091200446909789 7057641056659200167591171)
    ·
      refine ⟨10586461584988800251386757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057641056659200167591171 10586461584988800251386757)
      ·
        refine ⟨1984961547185400047135017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10586461584988800251386757 1984961547185400047135017)
        ·
          refine ⟨1488721160389050035351263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984961547185400047135017 1488721160389050035351263)
          ·
            refine ⟨2233081740583575053026895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488721160389050035351263 2233081740583575053026895)
            ·
              refine ⟨3349622610875362579540343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233081740583575053026895 3349622610875362579540343)
              ·
                refine ⟨5024433916313043869310515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349622610875362579540343 5024433916313043869310515)
                ·
                  refine ⟨7536650874469565803965773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024433916313043869310515 7536650874469565803965773)
                  ·
                    refine ⟨2826244077926087176487165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7536650874469565803965773 2826244077926087176487165)
                    ·
                      refine ⟨1059841529222282691182687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826244077926087176487165 1059841529222282691182687)
                      ·
                        rfl

theorem cell23_2064034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2064034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064034 prefixEnd_2064034 := by exact prefixLift 2064034
  have htrace : WordTrace (prefixWord ++ tailWord_2064034) baseStart_2064034 baseEnd_2064034 := by
    simpa [prefixWord, tailWord_2064034, baseEnd_2064034] using wordTrace_append hprefix tailTrace_2064034
  have hstable : (prefixWord ++ tailWord_2064034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064034).length < 2 ^ (prefixWord ++ tailWord_2064034).sum := by decide
  have hdescent : baseEnd_2064034 < baseStart_2064034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064056 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_2064056 : Nat := 118140960795 + 2064056 * 2 ^ 59
def prefixEnd_2064056 : Nat := 4983230072969 + 3 ^ 40 * 2064056 * 2
def baseEnd_2064056 : Nat := 1059852825796681605107585

theorem tailTrace_2064056 : CollatzResearch.WordTrace tailWord_2064056 prefixEnd_2064056 1059852825796681605107585 := by
  unfold tailWord_2064056
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641153505142549772470011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50188204673523399696626681 37641153505142549772470011)
  ·
    refine ⟨56461730257713824658705017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37641153505142549772470011 56461730257713824658705017)
    ·
      refine ⟨42346297693285368494028763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56461730257713824658705017 42346297693285368494028763)
      ·
        refine ⟨63519446539928052741043145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42346297693285368494028763 63519446539928052741043145)
        ·
          refine ⟨47639584904946039555782359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63519446539928052741043145 47639584904946039555782359)
          ·
            refine ⟨71459377357419059333673539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47639584904946039555782359 71459377357419059333673539)
            ·
              refine ⟨107189066036128589000510309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71459377357419059333673539 107189066036128589000510309)
              ·
                refine ⟨20097949881774110437595683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107189066036128589000510309 20097949881774110437595683)
                ·
                  refine ⟨30146924822661165656393525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20097949881774110437595683 30146924822661165656393525)
                  ·
                    refine ⟨2826274202124484280286893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30146924822661165656393525 2826274202124484280286893)
                    ·
                      refine ⟨1059852825796681605107585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826274202124484280286893 1059852825796681605107585)
                      ·
                        rfl

theorem cell23_2064056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_2064056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064056 prefixEnd_2064056 := by exact prefixLift 2064056
  have htrace : WordTrace (prefixWord ++ tailWord_2064056) baseStart_2064056 baseEnd_2064056 := by
    simpa [prefixWord, tailWord_2064056, baseEnd_2064056] using wordTrace_append hprefix tailTrace_2064056
  have hstable : (prefixWord ++ tailWord_2064056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064056).length < 2 ^ (prefixWord ++ tailWord_2064056).sum := by decide
  have hdescent : baseEnd_2064056 < baseStart_2064056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064096 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2064096 : Nat := 118140960795 + 2064096 * 2 ^ 59
def prefixEnd_2064096 : Nat := 4983230072969 + 3 ^ 40 * 2064096 * 2
def baseEnd_2064096 : Nat := 1059873365022861448607401

theorem tailTrace_2064096 : CollatzResearch.WordTrace tailWord_2064096 prefixEnd_2064096 1059873365022861448607401 := by
  unfold tailWord_2064096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641882965070093188198071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50189177286760124250930761 37641882965070093188198071)
  ·
    refine ⟨56462824447605139782297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37641882965070093188198071 56462824447605139782297107)
    ·
      refine ⟨84694236671407709673445661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56462824447605139782297107 84694236671407709673445661)
      ·
        refine ⟨31760338751777891127542123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84694236671407709673445661 31760338751777891127542123)
        ·
          refine ⟨47640508127666836691313185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31760338751777891127542123 47640508127666836691313185)
          ·
            refine ⟨35730381095750127518484889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47640508127666836691313185 35730381095750127518484889)
            ·
              refine ⟨26797785821812595638863667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35730381095750127518484889 26797785821812595638863667)
              ·
                refine ⟨40196678732718893458295501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26797785821812595638863667 40196678732718893458295501)
                ·
                  refine ⟨15073754524769585046860813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40196678732718893458295501 15073754524769585046860813)
                  ·
                    refine ⟨5652657946788594392572805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15073754524769585046860813 5652657946788594392572805)
                    ·
                      refine ⟨1059873365022861448607401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5652657946788594392572805 1059873365022861448607401)
                      ·
                        rfl

theorem cell23_2064096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2064096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064096 prefixEnd_2064096 := by exact prefixLift 2064096
  have htrace : WordTrace (prefixWord ++ tailWord_2064096) baseStart_2064096 baseEnd_2064096 := by
    simpa [prefixWord, tailWord_2064096, baseEnd_2064096] using wordTrace_append hprefix tailTrace_2064096
  have hstable : (prefixWord ++ tailWord_2064096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064096).length < 2 ^ (prefixWord ++ tailWord_2064096).sum := by decide
  have hdescent : baseEnd_2064096 < baseStart_2064096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064106 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2064106 : Nat := 118140960795 + 2064106 * 2 ^ 59
def prefixEnd_2064106 : Nat := 4983230072969 + 3 ^ 40 * 2064106 * 2
def baseEnd_2064106 : Nat := 353292833276468803160785

theorem tailTrace_2064106 : CollatzResearch.WordTrace tailWord_2064106 prefixEnd_2064106 353292833276468803160785 := by
  unfold tailWord_2064106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821032665025989521065043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50189420440069305389506781 18821032665025989521065043)
  ·
    refine ⟨28231548997538984281597565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18821032665025989521065043 28231548997538984281597565)
    ·
      refine ⟨10586830874077119105599087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28231548997538984281597565 10586830874077119105599087)
      ·
        refine ⟨15880246311115678658398631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586830874077119105599087 15880246311115678658398631)
        ·
          refine ⟨23820369466673517987597947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15880246311115678658398631 23820369466673517987597947)
          ·
            refine ⟨35730554200010276981396921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23820369466673517987597947 35730554200010276981396921)
            ·
              refine ⟨26797915650007707736047691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35730554200010276981396921 26797915650007707736047691)
              ·
                refine ⟨40196873475011561604071537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26797915650007707736047691 40196873475011561604071537)
                ·
                  refine ⟨30147655106258671203053653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40196873475011561604071537 30147655106258671203053653)
                  ·
                    refine ⟨353292833276468803160785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30147655106258671203053653 353292833276468803160785)
                    ·
                      rfl

theorem cell23_2064106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2064106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064106 prefixEnd_2064106 := by exact prefixLift 2064106
  have htrace : WordTrace (prefixWord ++ tailWord_2064106) baseStart_2064106 baseEnd_2064106 := by
    simpa [prefixWord, tailWord_2064106, baseEnd_2064106] using wordTrace_append hprefix tailTrace_2064106
  have hstable : (prefixWord ++ tailWord_2064106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064106).length < 2 ^ (prefixWord ++ tailWord_2064106).sum := by decide
  have hdescent : baseEnd_2064106 < baseStart_2064106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064113 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_2064113 : Nat := 118140960795 + 2064113 * 2 ^ 59
def prefixEnd_2064113 : Nat := 4983230072969 + 3 ^ 40 * 2064113 * 2
def baseEnd_2064113 : Nat := 1059882094193987882094823

theorem tailTrace_2064113 : CollatzResearch.WordTrace tailWord_2064113 prefixEnd_2064113 1059882094193987882094823 := by
  unfold tailWord_2064113
  simp only [CollatzResearch.WordTrace]
  refine ⟨75284385971078598279764993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50189590647385732186509995 75284385971078598279764993)
  ·
    refine ⟨56463289478308948709823745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75284385971078598279764993 56463289478308948709823745)
    ·
      refine ⟨42347467108731711532367809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56463289478308948709823745 42347467108731711532367809)
      ·
        refine ⟨31760600331548783649275857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42347467108731711532367809 31760600331548783649275857)
        ·
          refine ⟨23820450248661587736956893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31760600331548783649275857 23820450248661587736956893)
          ·
            refine ⟨8932668843248095401358835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23820450248661587736956893 8932668843248095401358835)
            ·
              refine ⟨13399003264872143102038253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932668843248095401358835 13399003264872143102038253)
              ·
                refine ⟨5024626224327053663264345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13399003264872143102038253 5024626224327053663264345)
                ·
                  refine ⟨3768469668245290247448259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5024626224327053663264345 3768469668245290247448259)
                  ·
                    refine ⟨5652704502367935371172389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768469668245290247448259 5652704502367935371172389)
                    ·
                      refine ⟨1059882094193987882094823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5652704502367935371172389 1059882094193987882094823)
                      ·
                        rfl

theorem cell23_2064113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_2064113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064113 prefixEnd_2064113 := by exact prefixLift 2064113
  have htrace : WordTrace (prefixWord ++ tailWord_2064113) baseStart_2064113 baseEnd_2064113 := by
    simpa [prefixWord, tailWord_2064113, baseEnd_2064113] using wordTrace_append hprefix tailTrace_2064113
  have hstable : (prefixWord ++ tailWord_2064113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064113).length < 2 ^ (prefixWord ++ tailWord_2064113).sum := by decide
  have hdescent : baseEnd_2064113 < baseStart_2064113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064130 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2064130 : Nat := 118140960795 + 2064130 * 2 ^ 59
def prefixEnd_2064130 : Nat := 4983230072969 + 3 ^ 40 * 2064130 * 2
def baseEnd_2064130 : Nat := 1059890823365114315582245

theorem tailTrace_2064130 : CollatzResearch.WordTrace tailWord_2064130 prefixEnd_2064130 1059890823365114315582245 := by
  unfold tailWord_2064130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821251503004252545783461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50190004008011340122089229 18821251503004252545783461)
  ·
    refine ⟨3528984656813297352334399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18821251503004252545783461 3528984656813297352334399)
    ·
      refine ⟨5293476985219946028501599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528984656813297352334399 5293476985219946028501599)
      ·
        refine ⟨7940215477829919042752399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293476985219946028501599 7940215477829919042752399)
        ·
          refine ⟨11910323216744878564128599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940215477829919042752399 11910323216744878564128599)
          ·
            refine ⟨17865484825117317846192899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910323216744878564128599 17865484825117317846192899)
            ·
              refine ⟨26798227237675976769289349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17865484825117317846192899 26798227237675976769289349)
              ·
                refine ⟨5024667607064245644241753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26798227237675976769289349 5024667607064245644241753)
                ·
                  refine ⟨3768500705298184233181315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5024667607064245644241753 3768500705298184233181315)
                  ·
                    refine ⟨5652751057947276349771973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768500705298184233181315 5652751057947276349771973)
                    ·
                      refine ⟨1059890823365114315582245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5652751057947276349771973 1059890823365114315582245)
                      ·
                        rfl

theorem cell23_2064130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2064130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064130 prefixEnd_2064130 := by exact prefixLift 2064130
  have htrace : WordTrace (prefixWord ++ tailWord_2064130) baseStart_2064130 baseEnd_2064130 := by
    simpa [prefixWord, tailWord_2064130, baseEnd_2064130] using wordTrace_append hprefix tailTrace_2064130
  have hstable : (prefixWord ++ tailWord_2064130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064130).length < 2 ^ (prefixWord ++ tailWord_2064130).sum := by decide
  have hdescent : baseEnd_2064130 < baseStart_2064130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064141 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2064141 : Nat := 118140960795 + 2064141 * 2 ^ 59
def prefixEnd_2064141 : Nat := 4983230072969 + 3 ^ 40 * 2064141 * 2
def baseEnd_2064141 : Nat := 1059896471652313772544695

theorem tailTrace_2064141 : CollatzResearch.WordTrace tailWord_2064141 prefixEnd_2064141 1059896471652313772544695 := by
  unfold tailWord_2064141
  simp only [CollatzResearch.WordTrace]
  refine ⟨75285407214977159061784277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50190271476651439374522851 75285407214977159061784277)
  ·
    refine ⟨1764501731601027165510569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75285407214977159061784277 1764501731601027165510569)
    ·
      refine ⟨1323376298700770374132927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764501731601027165510569 1323376298700770374132927)
      ·
        refine ⟨1985064448051155561199391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323376298700770374132927 1985064448051155561199391)
        ·
          refine ⟨2977596672076733341799087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985064448051155561199391 2977596672076733341799087)
          ·
            refine ⟨4466395008115100012698631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977596672076733341799087 4466395008115100012698631)
            ·
              refine ⟨6699592512172650019047947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466395008115100012698631 6699592512172650019047947)
              ·
                refine ⟨10049388768258975028571921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699592512172650019047947 10049388768258975028571921)
                ·
                  refine ⟨7537041576194231271428941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10049388768258975028571921 7537041576194231271428941)
                  ·
                    refine ⟨2826390591072836726785853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7537041576194231271428941 2826390591072836726785853)
                    ·
                      refine ⟨1059896471652313772544695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826390591072836726785853 1059896471652313772544695)
                      ·
                        rfl

theorem cell23_2064141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2064141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064141 prefixEnd_2064141 := by exact prefixLift 2064141
  have htrace : WordTrace (prefixWord ++ tailWord_2064141) baseStart_2064141 baseEnd_2064141 := by
    simpa [prefixWord, tailWord_2064141, baseEnd_2064141] using wordTrace_append hprefix tailTrace_2064141
  have hstable : (prefixWord ++ tailWord_2064141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064141).length < 2 ^ (prefixWord ++ tailWord_2064141).sum := by decide
  have hdescent : baseEnd_2064141 < baseStart_2064141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064176 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_2064176 : Nat := 118140960795 + 2064176 * 2 ^ 59
def prefixEnd_2064176 : Nat := 4983230072969 + 3 ^ 40 * 2064176 * 2
def baseEnd_2064176 : Nat := 1059914443475221135607033

theorem tailTrace_2064176 : CollatzResearch.WordTrace tailWord_2064176 prefixEnd_2064176 1059914443475221135607033 := by
  unfold tailWord_2064176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37643341884925180019654191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50191122513233573359538921 37643341884925180019654191)
  ·
    refine ⟨56465012827387770029481287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37643341884925180019654191 56465012827387770029481287)
    ·
      refine ⟨84697519241081655044221931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56465012827387770029481287 84697519241081655044221931)
      ·
        refine ⟨127046278861622482566332897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84697519241081655044221931 127046278861622482566332897)
        ·
          refine ⟨95284709146216861924749673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127046278861622482566332897 95284709146216861924749673)
          ·
            refine ⟨71463531859662646443562255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95284709146216861924749673 71463531859662646443562255)
            ·
              refine ⟨107195297789493969665343383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71463531859662646443562255 107195297789493969665343383)
              ·
                refine ⟨160792946684240954498015075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107195297789493969665343383 160792946684240954498015075)
                ·
                  refine ⟨241189420026361431747022613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160792946684240954498015075 241189420026361431747022613)
                  ·
                    refine ⟨11305754063735692113141685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241189420026361431747022613 11305754063735692113141685)
                    ·
                      refine ⟨1059914443475221135607033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11305754063735692113141685 1059914443475221135607033)
                      ·
                        rfl

theorem cell23_2064176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_2064176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064176 prefixEnd_2064176 := by exact prefixLift 2064176
  have htrace : WordTrace (prefixWord ++ tailWord_2064176) baseStart_2064176 baseEnd_2064176 := by
    simpa [prefixWord, tailWord_2064176, baseEnd_2064176] using wordTrace_append hprefix tailTrace_2064176
  have hstable : (prefixWord ++ tailWord_2064176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064176).length < 2 ^ (prefixWord ++ tailWord_2064176).sum := by decide
  have hdescent : baseEnd_2064176 < baseStart_2064176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064197 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_2064197 : Nat := 118140960795 + 2064197 * 2 ^ 59
def prefixEnd_2064197 : Nat := 4983230072969 + 3 ^ 40 * 2064197 * 2
def baseEnd_2064197 : Nat := 1059925226568965553444437

theorem tailTrace_2064197 : CollatzResearch.WordTrace tailWord_2064197 prefixEnd_2064197 1059925226568965553444437 := by
  unfold tailWord_2064197
  simp only [CollatzResearch.WordTrace]
  refine ⟨75287449702774280625822845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50191633135182853750548563 75287449702774280625822845)
  ·
    refine ⟨28232793638540355234683567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75287449702774280625822845 28232793638540355234683567)
    ·
      refine ⟨42349190457810532852025351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28232793638540355234683567 42349190457810532852025351)
      ·
        refine ⟨63523785686715799278038027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42349190457810532852025351 63523785686715799278038027)
        ·
          refine ⟨95285678530073698917057041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63523785686715799278038027 95285678530073698917057041)
          ·
            refine ⟨71464258897555274187792781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95285678530073698917057041 71464258897555274187792781)
            ·
              refine ⟨26799097086583227820422293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71464258897555274187792781 26799097086583227820422293)
              ·
                refine ⟨1256207675933588804082295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26799097086583227820422293 1256207675933588804082295)
                ·
                  refine ⟨1884311513900383206123443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256207675933588804082295 1884311513900383206123443)
                  ·
                    refine ⟨2826467270850574809185165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1884311513900383206123443 2826467270850574809185165)
                    ·
                      refine ⟨1059925226568965553444437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826467270850574809185165 1059925226568965553444437)
                      ·
                        rfl

theorem cell23_2064197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_2064197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064197 prefixEnd_2064197 := by exact prefixLift 2064197
  have htrace : WordTrace (prefixWord ++ tailWord_2064197) baseStart_2064197 baseEnd_2064197 := by
    simpa [prefixWord, tailWord_2064197, baseEnd_2064197] using wordTrace_append hprefix tailTrace_2064197
  have hstable : (prefixWord ++ tailWord_2064197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064197).length < 2 ^ (prefixWord ++ tailWord_2064197).sum := by decide
  have hdescent : baseEnd_2064197 < baseStart_2064197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064233 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_2064233 : Nat := 118140960795 + 2064233 * 2 ^ 59
def prefixEnd_2064233 : Nat := 4983230072969 + 3 ^ 40 * 2064233 * 2
def baseEnd_2064233 : Nat := 1059943711872527412594271

theorem tailTrace_2064233 : CollatzResearch.WordTrace tailWord_2064233 prefixEnd_2064233 1059943711872527412594271 := by
  unfold tailWord_2064233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288762730643858774133353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50192508487095905849422235 75288762730643858774133353)
  ·
    refine ⟨56466572047982894080600015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75288762730643858774133353 56466572047982894080600015)
    ·
      refine ⟨84699858071974341120900023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56466572047982894080600015 84699858071974341120900023)
      ·
        refine ⟨127049787107961511681350035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84699858071974341120900023 127049787107961511681350035)
        ·
          refine ⟨190574680661942267522025053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127049787107961511681350035 190574680661942267522025053)
          ·
            refine ⟨71465505248228350320759395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190574680661942267522025053 71465505248228350320759395)
            ·
              refine ⟨107198257872342525481139093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71465505248228350320759395 107198257872342525481139093)
              ·
                refine ⟨5024918337766055881928395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107198257872342525481139093 5024918337766055881928395)
                ·
                  refine ⟨7537377506649083822892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024918337766055881928395 7537377506649083822892593)
                  ·
                    refine ⟨5653033129986812867169445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537377506649083822892593 5653033129986812867169445)
                    ·
                      refine ⟨1059943711872527412594271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5653033129986812867169445 1059943711872527412594271)
                      ·
                        rfl

theorem cell23_2064233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_2064233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064233 prefixEnd_2064233 := by exact prefixLift 2064233
  have htrace : WordTrace (prefixWord ++ tailWord_2064233) baseStart_2064233 baseEnd_2064233 := by
    simpa [prefixWord, tailWord_2064233, baseEnd_2064233] using wordTrace_append hprefix tailTrace_2064233
  have hstable : (prefixWord ++ tailWord_2064233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064233).length < 2 ^ (prefixWord ++ tailWord_2064233).sum := by decide
  have hdescent : baseEnd_2064233 < baseStart_2064233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064237 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2064237 : Nat := 118140960795 + 2064237 * 2 ^ 59
def prefixEnd_2064237 : Nat := 4983230072969 + 3 ^ 40 * 2064237 * 2
def baseEnd_2064237 : Nat := 1059945765795145396944253

theorem tailTrace_2064237 : CollatzResearch.WordTrace tailWord_2064237 prefixEnd_2064237 1059945765795145396944253 := by
  unfold tailWord_2064237
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288908622629367457278965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50192605748419578304852643 75288908622629367457278965)
  ·
    refine ⟨7058335183371503199119903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75288908622629367457278965 7058335183371503199119903)
    ·
      refine ⟨10587502775057254798679855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058335183371503199119903 10587502775057254798679855)
      ·
        refine ⟨15881254162585882198019783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10587502775057254798679855 15881254162585882198019783)
        ·
          refine ⟨23821881243878823297029675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15881254162585882198019783 23821881243878823297029675)
          ·
            refine ⟨35732821865818234945544513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821881243878823297029675 35732821865818234945544513)
            ·
              refine ⟨26799616399363676209158385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35732821865818234945544513 26799616399363676209158385)
              ·
                refine ⟨20099712299522757156868789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26799616399363676209158385 20099712299522757156868789)
                ·
                  refine ⟨1884348028080258483456449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20099712299522757156868789 1884348028080258483456449)
                  ·
                    refine ⟨1413261021060193862592337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1884348028080258483456449 1413261021060193862592337)
                    ·
                      refine ⟨1059945765795145396944253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413261021060193862592337 1059945765795145396944253)
                      ·
                        rfl

theorem cell23_2064237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2064237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064237 prefixEnd_2064237 := by exact prefixLift 2064237
  have htrace : WordTrace (prefixWord ++ tailWord_2064237) baseStart_2064237 baseEnd_2064237 := by
    simpa [prefixWord, tailWord_2064237, baseEnd_2064237] using wordTrace_append hprefix tailTrace_2064237
  have hstable : (prefixWord ++ tailWord_2064237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064237).length < 2 ^ (prefixWord ++ tailWord_2064237).sum := by decide
  have hdescent : baseEnd_2064237 < baseStart_2064237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064274 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2064274 : Nat := 118140960795 + 2064274 * 2 ^ 59
def prefixEnd_2064274 : Nat := 4983230072969 + 3 ^ 40 * 2064274 * 2
def baseEnd_2064274 : Nat := 1059964764579361752181583

theorem tailTrace_2064274 : CollatzResearch.WordTrace tailWord_2064274 prefixEnd_2064274 1059964764579361752181583 := by
  unfold tailWord_2064274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18822564530873830694093969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50193505415663548517583917 18822564530873830694093969)
  ·
    refine ⟨14116923398155373020570477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18822564530873830694093969 14116923398155373020570477)
    ·
      refine ⟨5293846274308264882713929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14116923398155373020570477 5293846274308264882713929)
      ·
        refine ⟨3970384705731198662035447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5293846274308264882713929 3970384705731198662035447)
        ·
          refine ⟨5955577058596797993053171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970384705731198662035447 5955577058596797993053171)
          ·
            refine ⟨8933365587895196989579757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5955577058596797993053171 8933365587895196989579757)
            ·
              refine ⟨3350012095460698871092409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8933365587895196989579757 3350012095460698871092409)
              ·
                refine ⟨2512509071595524153319307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350012095460698871092409 2512509071595524153319307)
                ·
                  refine ⟨3768763607393286229978961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512509071595524153319307 3768763607393286229978961)
                  ·
                    refine ⟨2826572705544964672484221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3768763607393286229978961 2826572705544964672484221)
                    ·
                      refine ⟨1059964764579361752181583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826572705544964672484221 1059964764579361752181583)
                      ·
                        rfl

theorem cell23_2064274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2064274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064274 prefixEnd_2064274 := by exact prefixLift 2064274
  have htrace : WordTrace (prefixWord ++ tailWord_2064274) baseStart_2064274 baseEnd_2064274 := by
    simpa [prefixWord, tailWord_2064274, baseEnd_2064274] using wordTrace_append hprefix tailTrace_2064274
  have hstable : (prefixWord ++ tailWord_2064274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064274).length < 2 ^ (prefixWord ++ tailWord_2064274).sum := by decide
  have hdescent : baseEnd_2064274 < baseStart_2064274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064287 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2064287 : Nat := 118140960795 + 2064287 * 2 ^ 59
def prefixEnd_2064287 : Nat := 4983230072969 + 3 ^ 40 * 2064287 * 2
def baseEnd_2064287 : Nat := 1059971439827870201319023

theorem tailTrace_2064287 : CollatzResearch.WordTrace tailWord_2064287 prefixEnd_2064287 1059971439827870201319023 := by
  unfold tailWord_2064287
  simp only [CollatzResearch.WordTrace]
  refine ⟨75290732272448225996599115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50193821514965483997732743 75290732272448225996599115)
  ·
    refine ⟨112936098408672338994898673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75290732272448225996599115 112936098408672338994898673)
    ·
      refine ⟨84702073806504254246174005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112936098408672338994898673 84702073806504254246174005)
      ·
        refine ⟨7940819419359773835578813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84702073806504254246174005 7940819419359773835578813)
        ·
          refine ⟨2977807282259915188342055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7940819419359773835578813 2977807282259915188342055)
          ·
            refine ⟨4466710923389872782513083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977807282259915188342055 4466710923389872782513083)
            ·
              refine ⟨6700066385084809173769625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466710923389872782513083 6700066385084809173769625)
              ·
                refine ⟨5025049788813606880327219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700066385084809173769625 5025049788813606880327219)
                ·
                  refine ⟨7537574683220410320490829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025049788813606880327219 7537574683220410320490829)
                  ·
                    refine ⟨2826590506207653870184061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7537574683220410320490829 2826590506207653870184061)
                    ·
                      refine ⟨1059971439827870201319023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2826590506207653870184061 1059971439827870201319023)
                      ·
                        rfl

theorem cell23_2064287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2064287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064287 prefixEnd_2064287 := by exact prefixLift 2064287
  have htrace : WordTrace (prefixWord ++ tailWord_2064287) baseStart_2064287 baseEnd_2064287 := by
    simpa [prefixWord, tailWord_2064287, baseEnd_2064287] using wordTrace_append hprefix tailTrace_2064287
  have hstable : (prefixWord ++ tailWord_2064287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064287).length < 2 ^ (prefixWord ++ tailWord_2064287).sum := by decide
  have hdescent : baseEnd_2064287 < baseStart_2064287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064293 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_2064293 : Nat := 118140960795 + 2064293 * 2 ^ 59
def prefixEnd_2064293 : Nat := 4983230072969 + 3 ^ 40 * 2064293 * 2
def baseEnd_2064293 : Nat := 1059974520711797177843995

theorem tailTrace_2064293 : CollatzResearch.WordTrace tailWord_2064293 prefixEnd_2064293 1059974520711797177843995 := by
  unfold tailWord_2064293
  simp only [CollatzResearch.WordTrace]
  refine ⟨75290951110426489021317533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50193967406950992680878355 75290951110426489021317533)
  ·
    refine ⟨28234106666409933382994075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75290951110426489021317533 28234106666409933382994075)
    ·
      refine ⟨42351159999614900074491113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28234106666409933382994075 42351159999614900074491113)
      ·
        refine ⟨31763369999711175055868335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42351159999614900074491113 31763369999711175055868335)
        ·
          refine ⟨47645054999566762583802503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763369999711175055868335 47645054999566762583802503)
          ·
            refine ⟨71467582499350143875703755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47645054999566762583802503 71467582499350143875703755)
            ·
              refine ⟨107201373749025215813555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71467582499350143875703755 107201373749025215813555633)
              ·
                refine ⟨80401030311768911860166725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107201373749025215813555633 80401030311768911860166725)
                ·
                  refine ⟨15075193183456670973781261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80401030311768911860166725 15075193183456670973781261)
                  ·
                    refine ⟨5653197443796251615167973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15075193183456670973781261 5653197443796251615167973)
                    ·
                      refine ⟨1059974520711797177843995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5653197443796251615167973 1059974520711797177843995)
                      ·
                        rfl

theorem cell23_2064293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_2064293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064293 prefixEnd_2064293 := by exact prefixLift 2064293
  have htrace : WordTrace (prefixWord ++ tailWord_2064293) baseStart_2064293 baseEnd_2064293 := by
    simpa [prefixWord, tailWord_2064293, baseEnd_2064293] using wordTrace_append hprefix tailTrace_2064293
  have hstable : (prefixWord ++ tailWord_2064293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064293).length < 2 ^ (prefixWord ++ tailWord_2064293).sum := by decide
  have hdescent : baseEnd_2064293 < baseStart_2064293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064303 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 6]
def baseStart_2064303 : Nat := 118140960795 + 2064303 * 2 ^ 59
def prefixEnd_2064303 : Nat := 4983230072969 + 3 ^ 40 * 2064303 * 2
def baseEnd_2064303 : Nat := 353326551839447379572983

theorem tailTrace_2064303 : CollatzResearch.WordTrace tailWord_2064303 prefixEnd_2064303 353326551839447379572983 := by
  unfold tailWord_2064303
  simp only [CollatzResearch.WordTrace]
  refine ⟨75291315840390260729181563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50194210560260173819454375 75291315840390260729181563)
  ·
    refine ⟨112936973760585391093772345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75291315840390260729181563 112936973760585391093772345)
    ·
      refine ⟨84702730320439043320329259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112936973760585391093772345 84702730320439043320329259)
      ·
        refine ⟨127054095480658564980493889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84702730320439043320329259 127054095480658564980493889)
        ·
          refine ⟨95290571610493923735370417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127054095480658564980493889 95290571610493923735370417)
          ·
            refine ⟨71467928707870442801527813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95290571610493923735370417 71467928707870442801527813)
            ·
              refine ⟨13400236632725708025286465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71467928707870442801527813 13400236632725708025286465)
              ·
                refine ⟨10050177474544281018964849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13400236632725708025286465 10050177474544281018964849)
                ·
                  refine ⟨7537633105908210764223637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050177474544281018964849 7537633105908210764223637)
                  ·
                    refine ⟨353326551839447379572983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7537633105908210764223637 353326551839447379572983)
                    ·
                      rfl

theorem cell23_2064303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_2064303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064303 prefixEnd_2064303 := by exact prefixLift 2064303
  have htrace : WordTrace (prefixWord ++ tailWord_2064303) baseStart_2064303 baseEnd_2064303 := by
    simpa [prefixWord, tailWord_2064303, baseEnd_2064303] using wordTrace_append hprefix tailTrace_2064303
  have hstable : (prefixWord ++ tailWord_2064303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064303).length < 2 ^ (prefixWord ++ tailWord_2064303).sum := by decide
  have hdescent : baseEnd_2064303 < baseStart_2064303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064327 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_2064327 : Nat := 118140960795 + 2064327 * 2 ^ 59
def prefixEnd_2064327 : Nat := 4983230072969 + 3 ^ 40 * 2064327 * 2
def baseEnd_2064327 : Nat := 1059991979054050044818839

theorem tailTrace_2064327 : CollatzResearch.WordTrace tailWord_2064327 prefixEnd_2064327 1059991979054050044818839 := by
  unfold tailWord_2064327
  simp only [CollatzResearch.WordTrace]
  refine ⟨75292191192303312828055235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50194794128202208552036823 75292191192303312828055235)
  ·
    refine ⟨112938286788454969242082853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75292191192303312828055235 112938286788454969242082853)
    ·
      refine ⟨21175928772835306732890535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112938286788454969242082853 21175928772835306732890535)
      ·
        refine ⟨31763893159252960099335803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175928772835306732890535 31763893159252960099335803)
        ·
          refine ⟨47645839738879440149003705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763893159252960099335803 47645839738879440149003705)
          ·
            refine ⟨35734379804159580111752779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47645839738879440149003705 35734379804159580111752779)
            ·
              refine ⟨53601569706239370167629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35734379804159580111752779 53601569706239370167629169)
              ·
                refine ⟨40201177279679527625721877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53601569706239370167629169 40201177279679527625721877)
                ·
                  refine ⟨1884430184984977857455713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40201177279679527625721877 1884430184984977857455713)
                  ·
                    refine ⟨1413322638738733393091785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1884430184984977857455713 1413322638738733393091785)
                    ·
                      refine ⟨1059991979054050044818839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413322638738733393091785 1059991979054050044818839)
                      ·
                        rfl

theorem cell23_2064327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_2064327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064327 prefixEnd_2064327 := by exact prefixLift 2064327
  have htrace : WordTrace (prefixWord ++ tailWord_2064327) baseStart_2064327 baseEnd_2064327 := by
    simpa [prefixWord, tailWord_2064327, baseEnd_2064327] using wordTrace_append hprefix tailTrace_2064327
  have hstable : (prefixWord ++ tailWord_2064327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064327).length < 2 ^ (prefixWord ++ tailWord_2064327).sum := by decide
  have hdescent : baseEnd_2064327 < baseStart_2064327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064340 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2064340 : Nat := 118140960795 + 2064340 * 2 ^ 59
def prefixEnd_2064340 : Nat := 4983230072969 + 3 ^ 40 * 2064340 * 2
def baseEnd_2064340 : Nat := 1059998654302558493956279

theorem tailTrace_2064340 : CollatzResearch.WordTrace tailWord_2064340 prefixEnd_2064340 1059998654302558493956279 := by
  unfold tailWord_2064340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646332670628108024139237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50195110227504144032185649 37646332670628108024139237)
  ·
    refine ⟨7058687375742770254526107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37646332670628108024139237 7058687375742770254526107)
    ·
      refine ⟨10588031063614155381789161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058687375742770254526107 10588031063614155381789161)
      ·
        refine ⟨7941023297710616536341871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10588031063614155381789161 7941023297710616536341871)
        ·
          refine ⟨11911534946565924804512807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941023297710616536341871 11911534946565924804512807)
          ·
            refine ⟨17867302419848887206769211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11911534946565924804512807 17867302419848887206769211)
            ·
              refine ⟨26800953629773330810153817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867302419848887206769211 26800953629773330810153817)
              ·
                refine ⟨20100715222329998107615363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26800953629773330810153817 20100715222329998107615363)
                ·
                  refine ⟨30151072833494997161423045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20100715222329998107615363 30151072833494997161423045)
                  ·
                    refine ⟨5653326156280311967766821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30151072833494997161423045 5653326156280311967766821)
                    ·
                      refine ⟨1059998654302558493956279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5653326156280311967766821 1059998654302558493956279)
                      ·
                        rfl

theorem cell23_2064340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2064340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064340 prefixEnd_2064340 := by exact prefixLift 2064340
  have htrace : WordTrace (prefixWord ++ tailWord_2064340) baseStart_2064340 baseEnd_2064340 := by
    simpa [prefixWord, tailWord_2064340, baseEnd_2064340] using wordTrace_append hprefix tailTrace_2064340
  have hstable : (prefixWord ++ tailWord_2064340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064340).length < 2 ^ (prefixWord ++ tailWord_2064340).sum := by decide
  have hdescent : baseEnd_2064340 < baseStart_2064340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064424 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2064424 : Nat := 118140960795 + 2064424 * 2 ^ 59
def prefixEnd_2064424 : Nat := 4983230072969 + 3 ^ 40 * 2064424 * 2
def baseEnd_2064424 : Nat := 1060041786677536165305893

theorem tailTrace_2064424 : CollatzResearch.WordTrace tailWord_2064424 prefixEnd_2064424 1060041786677536165305893 := by
  unfold tailWord_2064424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647864536475949197168163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50197152715301265596224217 37647864536475949197168163)
  ·
    refine ⟨56471796804713923795752245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37647864536475949197168163 56471796804713923795752245)
    ·
      refine ⟨5294230950441930355851773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56471796804713923795752245 5294230950441930355851773)
      ·
        refine ⟨1985336606415723883444415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5294230950441930355851773 1985336606415723883444415)
        ·
          refine ⟨2978004909623585825166623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985336606415723883444415 2978004909623585825166623)
          ·
            refine ⟨4467007364435378737749935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978004909623585825166623 4467007364435378737749935)
            ·
              refine ⟨6700511046653068106624903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467007364435378737749935 6700511046653068106624903)
              ·
                refine ⟨10050766569979602159937355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700511046653068106624903 10050766569979602159937355)
                ·
                  refine ⟨15076149854969403239906033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050766569979602159937355 15076149854969403239906033)
                  ·
                    refine ⟨11307112391227052429929525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076149854969403239906033 11307112391227052429929525)
                    ·
                      refine ⟨1060041786677536165305893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11307112391227052429929525 1060041786677536165305893)
                      ·
                        rfl

theorem cell23_2064424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2064424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064424 prefixEnd_2064424 := by exact prefixLift 2064424
  have htrace : WordTrace (prefixWord ++ tailWord_2064424) baseStart_2064424 baseEnd_2064424 := by
    simpa [prefixWord, tailWord_2064424, baseEnd_2064424] using wordTrace_append hprefix tailTrace_2064424
  have hstable : (prefixWord ++ tailWord_2064424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064424).length < 2 ^ (prefixWord ++ tailWord_2064424).sum := by decide
  have hdescent : baseEnd_2064424 < baseStart_2064424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064461 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2064461 : Nat := 118140960795 + 2064461 * 2 ^ 59
def prefixEnd_2064461 : Nat := 4983230072969 + 3 ^ 40 * 2064461 * 2
def baseEnd_2064461 : Nat := 353353595153917506847741

theorem tailTrace_2064461 : CollatzResearch.WordTrace tailWord_2064461 prefixEnd_2064461 353353595153917506847741 := by
  unfold tailWord_2064461
  simp only [CollatzResearch.WordTrace]
  refine ⟨75297078573817853713433237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50198052382545235808955491 75297078573817853713433237)
  ·
    refine ⟨3529550558147711892817183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75297078573817853713433237 3529550558147711892817183)
    ·
      refine ⟨5294325837221567839225775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529550558147711892817183 5294325837221567839225775)
      ·
        refine ⟨7941488755832351758838663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294325837221567839225775 7941488755832351758838663)
        ·
          refine ⟨11912233133748527638257995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941488755832351758838663 11912233133748527638257995)
          ·
            refine ⟨17868349700622791457386993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912233133748527638257995 17868349700622791457386993)
            ·
              refine ⟨13401262275467093593040245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17868349700622791457386993 13401262275467093593040245)
              ·
                refine ⟨1256368338325040024347523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13401262275467093593040245 1256368338325040024347523)
                ·
                  refine ⟨1884552507487560036521285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256368338325040024347523 1884552507487560036521285)
                  ·
                    refine ⟨353353595153917506847741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1884552507487560036521285 353353595153917506847741)
                    ·
                      rfl

theorem cell23_2064461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2064461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064461 prefixEnd_2064461 := by exact prefixLift 2064461
  have htrace : WordTrace (prefixWord ++ tailWord_2064461) baseStart_2064461 baseEnd_2064461 := by
    simpa [prefixWord, tailWord_2064461, baseEnd_2064461] using wordTrace_append hprefix tailTrace_2064461
  have hstable : (prefixWord ++ tailWord_2064461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064461).length < 2 ^ (prefixWord ++ tailWord_2064461).sum := by decide
  have hdescent : baseEnd_2064461 < baseStart_2064461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064494 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2064494 : Nat := 118140960795 + 2064494 * 2 ^ 59
def prefixEnd_2064494 : Nat := 4983230072969 + 3 ^ 40 * 2064494 * 2
def baseEnd_2064494 : Nat := 1060077730323350891430571

theorem tailTrace_2064494 : CollatzResearch.WordTrace tailWord_2064494 prefixEnd_2064494 1060077730323350891430571 := by
  unfold tailWord_2064494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412285272837287543673067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50198854788465533566256357 9412285272837287543673067)
  ·
    refine ⟨14118427909255931315509601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9412285272837287543673067 14118427909255931315509601)
    ·
      refine ⟨10588820931941948486632201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118427909255931315509601 10588820931941948486632201)
      ·
        refine ⟨7941615698956461364974151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10588820931941948486632201 7941615698956461364974151)
        ·
          refine ⟨11912423548434692047461227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941615698956461364974151 11912423548434692047461227)
          ·
            refine ⟨17868635322652038071191841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912423548434692047461227 17868635322652038071191841)
            ·
              refine ⟨13401476491989028553393881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17868635322652038071191841 13401476491989028553393881)
              ·
                refine ⟨10051107368991771415045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13401476491989028553393881 10051107368991771415045411)
                ·
                  refine ⟨15076661053487657122568117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051107368991771415045411 15076661053487657122568117)
                  ·
                    refine ⟨1413436973764467855240761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15076661053487657122568117 1413436973764467855240761)
                    ·
                      refine ⟨1060077730323350891430571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413436973764467855240761 1060077730323350891430571)
                      ·
                        rfl

theorem cell23_2064494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2064494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064494 prefixEnd_2064494 := by exact prefixLift 2064494
  have htrace : WordTrace (prefixWord ++ tailWord_2064494) baseStart_2064494 baseEnd_2064494 := by
    simpa [prefixWord, tailWord_2064494, baseEnd_2064494] using wordTrace_append hprefix tailTrace_2064494
  have hstable : (prefixWord ++ tailWord_2064494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064494).length < 2 ^ (prefixWord ++ tailWord_2064494).sum := by decide
  have hdescent : baseEnd_2064494 < baseStart_2064494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064517 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_2064517 : Nat := 118140960795 + 2064517 * 2 ^ 59
def prefixEnd_2064517 : Nat := 4983230072969 + 3 ^ 40 * 2064517 * 2
def baseEnd_2064517 : Nat := 353363180126134767147655

theorem tailTrace_2064517 : CollatzResearch.WordTrace tailWord_2064517 prefixEnd_2064517 353363180126134767147655 := by
  unfold tailWord_2064517
  simp only [CollatzResearch.WordTrace]
  refine ⟨75299121061614975277471805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50199414041076650184981203 75299121061614975277471805)
  ·
    refine ⟨28237170398105615729051927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75299121061614975277471805 28237170398105615729051927)
    ·
      refine ⟨42355755597158423593577891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28237170398105615729051927 42355755597158423593577891)
      ·
        refine ⟨63533633395737635390366837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42355755597158423593577891 63533633395737635390366837)
        ·
          refine ⟨5956278130850403317846891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63533633395737635390366837 5956278130850403317846891)
          ·
            refine ⟨8934417196275604976770337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956278130850403317846891 8934417196275604976770337)
            ·
              refine ⟨6700812897206703732577753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8934417196275604976770337 6700812897206703732577753)
              ·
                refine ⟨5025609672905027799433315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700812897206703732577753 5025609672905027799433315)
                ·
                  refine ⟨7538414509357541699149973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025609672905027799433315 7538414509357541699149973)
                  ·
                    refine ⟨353363180126134767147655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7538414509357541699149973 353363180126134767147655)
                    ·
                      rfl

theorem cell23_2064517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_2064517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064517 prefixEnd_2064517 := by exact prefixLift 2064517
  have htrace : WordTrace (prefixWord ++ tailWord_2064517) baseStart_2064517 baseEnd_2064517 := by
    simpa [prefixWord, tailWord_2064517, baseEnd_2064517] using wordTrace_append hprefix tailTrace_2064517
  have hstable : (prefixWord ++ tailWord_2064517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064517).length < 2 ^ (prefixWord ++ tailWord_2064517).sum := by decide
  have hdescent : baseEnd_2064517 < baseStart_2064517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064541 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_2064541 : Nat := 118140960795 + 2064541 * 2 ^ 59
def prefixEnd_2064541 : Nat := 4983230072969 + 3 ^ 40 * 2064541 * 2
def baseEnd_2064541 : Nat := 1060101863914112207542855

theorem tailTrace_2064541 : CollatzResearch.WordTrace tailWord_2064541 prefixEnd_2064541 1060101863914112207542855 := by
  unfold tailWord_2064541
  simp only [CollatzResearch.WordTrace]
  refine ⟨75299996413528027376345477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50199997609018684917563651 75299996413528027376345477)
  ·
    refine ⟨14118749327536505133064777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75299996413528027376345477 14118749327536505133064777)
    ·
      refine ⟨10589061995652378849798583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118749327536505133064777 10589061995652378849798583)
      ·
        refine ⟨15883592993478568274697875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589061995652378849798583 15883592993478568274697875)
        ·
          refine ⟨23825389490217852412046813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883592993478568274697875 23825389490217852412046813)
          ·
            refine ⟨8934521058831694654517555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23825389490217852412046813 8934521058831694654517555)
            ·
              refine ⟨13401781588247541981776333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934521058831694654517555 13401781588247541981776333)
              ·
                refine ⟨5025668095592828243166125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13401781588247541981776333 5025668095592828243166125)
                ·
                  refine ⟨1884625535847310591187297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5025668095592828243166125 1884625535847310591187297)
                  ·
                    refine ⟨1413469151885482943390473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1884625535847310591187297 1413469151885482943390473)
                    ·
                      refine ⟨1060101863914112207542855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413469151885482943390473 1060101863914112207542855)
                      ·
                        rfl

theorem cell23_2064541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_2064541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064541 prefixEnd_2064541 := by exact prefixLift 2064541
  have htrace : WordTrace (prefixWord ++ tailWord_2064541) baseStart_2064541 baseEnd_2064541 := by
    simpa [prefixWord, tailWord_2064541, baseEnd_2064541] using wordTrace_append hprefix tailTrace_2064541
  have hstable : (prefixWord ++ tailWord_2064541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064541).length < 2 ^ (prefixWord ++ tailWord_2064541).sum := by decide
  have hdescent : baseEnd_2064541 < baseStart_2064541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064551 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2064551 : Nat := 118140960795 + 2064551 * 2 ^ 59
def prefixEnd_2064551 : Nat := 4983230072969 + 3 ^ 40 * 2064551 * 2
def baseEnd_2064551 : Nat := 353368999573552389472603

theorem tailTrace_2064551 : CollatzResearch.WordTrace tailWord_2064551 prefixEnd_2064551 353368999573552389472603 := by
  unfold tailWord_2064551
  simp only [CollatzResearch.WordTrace]
  refine ⟨75300361143491799084209507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50200240762327866056139671 75300361143491799084209507)
  ·
    refine ⟨112950541715237698626314261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75300361143491799084209507 112950541715237698626314261)
    ·
      refine ⟨5294556642901767123108481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112950541715237698626314261 5294556642901767123108481)
      ·
        refine ⟨3970917482176325342331361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5294556642901767123108481 3970917482176325342331361)
        ·
          refine ⟨2978188111632244006748521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3970917482176325342331361 2978188111632244006748521)
          ·
            refine ⟨2233641083724183005061391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2978188111632244006748521 2233641083724183005061391)
            ·
              refine ⟨3350461625586274507592087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233641083724183005061391 3350461625586274507592087)
              ·
                refine ⟨5025692438379411761388131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350461625586274507592087 5025692438379411761388131)
                ·
                  refine ⟨7538538657569117642082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025692438379411761388131 7538538657569117642082197)
                  ·
                    refine ⟨353368999573552389472603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7538538657569117642082197 353368999573552389472603)
                    ·
                      rfl

theorem cell23_2064551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2064551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064551 prefixEnd_2064551 := by exact prefixLift 2064551
  have htrace : WordTrace (prefixWord ++ tailWord_2064551) baseStart_2064551 baseEnd_2064551 := by
    simpa [prefixWord, tailWord_2064551, baseEnd_2064551] using wordTrace_append hprefix tailTrace_2064551
  have hstable : (prefixWord ++ tailWord_2064551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064551).length < 2 ^ (prefixWord ++ tailWord_2064551).sum := by decide
  have hdescent : baseEnd_2064551 < baseStart_2064551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064578 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2064578 : Nat := 118140960795 + 2064578 * 2 ^ 59
def prefixEnd_2064578 : Nat := 4983230072969 + 3 ^ 40 * 2064578 * 2
def baseEnd_2064578 : Nat := 1060120862698328562780185

theorem tailTrace_2064578 : CollatzResearch.WordTrace tailWord_2064578 prefixEnd_2064578 1060120862698328562780185 := by
  unfold tailWord_2064578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18825336478598495673860597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50200897276262655130294925 18825336478598495673860597)
  ·
    refine ⟨1764875294868608969424431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18825336478598495673860597 1764875294868608969424431)
    ·
      refine ⟨2647312942302913454136647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764875294868608969424431 2647312942302913454136647)
      ·
        refine ⟨3970969413454370181204971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647312942302913454136647 3970969413454370181204971)
        ·
          refine ⟨5956454120181555271807457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970969413454370181204971 5956454120181555271807457)
          ·
            refine ⟨4467340590136166453855593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956454120181555271807457 4467340590136166453855593)
            ·
              refine ⟨3350505442602124840391695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467340590136166453855593 3350505442602124840391695)
              ·
                refine ⟨5025758163903187260587543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350505442602124840391695 5025758163903187260587543)
                ·
                  refine ⟨7538637245854780890881315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025758163903187260587543 7538637245854780890881315)
                  ·
                    refine ⟨11307955868782171336321973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538637245854780890881315 11307955868782171336321973)
                    ·
                      refine ⟨1060120862698328562780185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11307955868782171336321973 1060120862698328562780185)
                      ·
                        rfl

theorem cell23_2064578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2064578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064578 prefixEnd_2064578 := by exact prefixLift 2064578
  have htrace : WordTrace (prefixWord ++ tailWord_2064578) baseStart_2064578 baseEnd_2064578 := by
    simpa [prefixWord, tailWord_2064578, baseEnd_2064578] using wordTrace_append hprefix tailTrace_2064578
  have hstable : (prefixWord ++ tailWord_2064578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064578).length < 2 ^ (prefixWord ++ tailWord_2064578).sum := by decide
  have hdescent : baseEnd_2064578 < baseStart_2064578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
