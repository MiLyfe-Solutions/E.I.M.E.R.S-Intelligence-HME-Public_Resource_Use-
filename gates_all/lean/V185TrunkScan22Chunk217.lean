import V185TrunkScan22Chunk216

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1934468 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1934468 : Nat := 118140960795 + 1934468 * 2 ^ 59
def prefixEnd_1934468 : Nat := 4983230072969 + 3 ^ 40 * 1934468 * 2
def baseEnd_1934468 : Nat := 220735976609298359723011

theorem tailTrace_1934468 : CollatzResearch.WordTrace tailWord_1934468 prefixEnd_1934468 220735976609298359723011 := by
  unfold tailWord_1934468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35277922177880145838274029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47037229570506861117698705 35277922177880145838274029)
  ·
    refine ⟨13229220816705054689352761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35277922177880145838274029 13229220816705054689352761)
    ·
      refine ⟨9921915612528791017014571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13229220816705054689352761 9921915612528791017014571)
      ·
        refine ⟨14882873418793186525521857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9921915612528791017014571 14882873418793186525521857)
        ·
          refine ⟨11162155064094889894141393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14882873418793186525521857 11162155064094889894141393)
          ·
            refine ⟨8371616298071167420606045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11162155064094889894141393 8371616298071167420606045)
            ·
              refine ⟨3139356111776687782727267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8371616298071167420606045 3139356111776687782727267)
              ·
                refine ⟨4709034167665031674090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139356111776687782727267 4709034167665031674090901)
                ·
                  refine ⟨220735976609298359723011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709034167665031674090901 220735976609298359723011)
                  ·
                    rfl

theorem cell22_1934468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1934468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934468 prefixEnd_1934468 := by exact prefixLift 1934468
  have htrace : WordTrace (prefixWord ++ tailWord_1934468) baseStart_1934468 baseEnd_1934468 := by
    simpa [prefixWord, tailWord_1934468, baseEnd_1934468] using wordTrace_append hprefix tailTrace_1934468
  have hstable : (prefixWord ++ tailWord_1934468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934468).length < 2 ^ (prefixWord ++ tailWord_1934468).sum := by decide
  have hdescent : baseEnd_1934468 < baseStart_1934468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934496 : List Nat := [2, 1, 1, 4, 2, 1, 1, 10]
def baseStart_1934496 : Nat := 118140960795 + 1934496 * 2 ^ 59
def prefixEnd_1934496 : Nat := 4983230072969 + 3 ^ 40 * 1934496 * 2
def baseEnd_1934496 : Nat := 73579723866679148829883

theorem tailTrace_1934496 : CollatzResearch.WordTrace tailWord_1934496 prefixEnd_1934496 73579723866679148829883 := by
  unfold tailWord_1934496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35278432799829426229283671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47037910399772568305711561 35278432799829426229283671)
  ·
    refine ⟨52917649199744139343925507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35278432799829426229283671 52917649199744139343925507)
    ·
      refine ⟨79376473799616209015888261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52917649199744139343925507 79376473799616209015888261)
      ·
        refine ⟨14883088837428039190479049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79376473799616209015888261 14883088837428039190479049)
        ·
          refine ⟨11162316628071029392859287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14883088837428039190479049 11162316628071029392859287)
          ·
            refine ⟨16743474942106544089288931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11162316628071029392859287 16743474942106544089288931)
            ·
              refine ⟨25115212413159816133933397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16743474942106544089288931 25115212413159816133933397)
              ·
                refine ⟨73579723866679148829883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25115212413159816133933397 73579723866679148829883)
                ·
                  rfl

theorem cell22_1934496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_1934496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934496 prefixEnd_1934496 := by exact prefixLift 1934496
  have htrace : WordTrace (prefixWord ++ tailWord_1934496) baseStart_1934496 baseEnd_1934496 := by
    simpa [prefixWord, tailWord_1934496, baseEnd_1934496] using wordTrace_append hprefix tailTrace_1934496
  have hstable : (prefixWord ++ tailWord_1934496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934496).length < 2 ^ (prefixWord ++ tailWord_1934496).sum := by decide
  have hdescent : baseEnd_1934496 < baseStart_1934496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934590 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1934590 : Nat := 118140960795 + 1934590 * 2 ^ 59
def prefixEnd_1934590 : Nat := 4983230072969 + 3 ^ 40 * 1934590 * 2
def baseEnd_1934590 : Nat := 662249692921127427618659

theorem tailTrace_1934590 : CollatzResearch.WordTrace tailWord_1934590 prefixEnd_1934590 662249692921127427618659 := by
  unfold tailWord_1934590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820036757664788314061153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47040196040878871008326149 8820036757664788314061153)
  ·
    refine ⟨6615027568248591235545865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8820036757664788314061153 6615027568248591235545865)
    ·
      refine ⟨4961270676186443426659399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6615027568248591235545865 4961270676186443426659399)
      ·
        refine ⟨7441906014279665139989099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961270676186443426659399 7441906014279665139989099)
        ·
          refine ⟨11162859021419497709983649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441906014279665139989099 11162859021419497709983649)
          ·
            refine ⟨8372144266064623282487737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11162859021419497709983649 8372144266064623282487737)
            ·
              refine ⟨6279108199548467461865803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372144266064623282487737 6279108199548467461865803)
              ·
                refine ⟨9418662299322701192798705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279108199548467461865803 9418662299322701192798705)
                ·
                  refine ⟨7063996724492025894599029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418662299322701192798705 7063996724492025894599029)
                  ·
                    refine ⟨662249692921127427618659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7063996724492025894599029 662249692921127427618659)
                    ·
                      rfl

theorem cell22_1934590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1934590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934590 prefixEnd_1934590 := by exact prefixLift 1934590
  have htrace : WordTrace (prefixWord ++ tailWord_1934590) baseStart_1934590 baseEnd_1934590 := by
    simpa [prefixWord, tailWord_1934590, baseEnd_1934590] using wordTrace_append hprefix tailTrace_1934590
  have hstable : (prefixWord ++ tailWord_1934590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934590).length < 2 ^ (prefixWord ++ tailWord_1934590).sum := by decide
  have hdescent : baseEnd_1934590 < baseStart_1934590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934603 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 6]
def baseStart_1934603 : Nat := 118140960795 + 1934603 * 2 ^ 59
def prefixEnd_1934603 : Nat := 4983230072969 + 3 ^ 40 * 1934603 * 2
def baseEnd_1934603 : Nat := 220751381028933242347873

theorem tailTrace_1934603 : CollatzResearch.WordTrace tailWord_1934603 prefixEnd_1934603 220751381028933242347873 := by
  unfold tailWord_1934603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70560768210271209732712463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47040512140180806488474975 70560768210271209732712463)
  ·
    refine ⟨105841152315406814599068695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70560768210271209732712463 105841152315406814599068695)
    ·
      refine ⟨158761728473110221898603043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105841152315406814599068695 158761728473110221898603043)
      ·
        refine ⟨238142592709665332847904565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158761728473110221898603043 238142592709665332847904565)
        ·
          refine ⟨22325868066531124954491053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238142592709665332847904565 22325868066531124954491053)
          ·
            refine ⟨8372200524949171857934145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22325868066531124954491053 8372200524949171857934145)
            ·
              refine ⟨6279150393711878893450609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372200524949171857934145 6279150393711878893450609)
              ·
                refine ⟨4709362795283909170087957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279150393711878893450609 4709362795283909170087957)
                ·
                  refine ⟨220751381028933242347873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709362795283909170087957 220751381028933242347873)
                  ·
                    rfl

theorem cell22_1934603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_1934603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934603 prefixEnd_1934603 := by exact prefixLift 1934603
  have htrace : WordTrace (prefixWord ++ tailWord_1934603) baseStart_1934603 baseEnd_1934603 := by
    simpa [prefixWord, tailWord_1934603, baseEnd_1934603] using wordTrace_append hprefix tailTrace_1934603
  have hstable : (prefixWord ++ tailWord_1934603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934603).length < 2 ^ (prefixWord ++ tailWord_1934603).sum := by decide
  have hdescent : baseEnd_1934603 < baseStart_1934603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934637 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1934637 : Nat := 118140960795 + 1934637 * 2 ^ 59
def prefixEnd_1934637 : Nat := 4983230072969 + 3 ^ 40 * 1934637 * 2
def baseEnd_1934637 : Nat := 220755260660544990564505

theorem tailTrace_1934637 : CollatzResearch.WordTrace tailWord_1934637 prefixEnd_1934637 220755260660544990564505 := by
  unfold tailWord_1934637
  simp only [CollatzResearch.WordTrace]
  refine ⟨70562008292148033539450165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47041338861432022359633443 70562008292148033539450165)
  ·
    refine ⟨6615188277388878144323453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70562008292148033539450165 6615188277388878144323453)
    ·
      refine ⟨2480695604020829304121295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6615188277388878144323453 2480695604020829304121295)
      ·
        refine ⟨3721043406031243956181943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480695604020829304121295 3721043406031243956181943)
        ·
          refine ⟨5581565109046865934272915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721043406031243956181943 5581565109046865934272915)
          ·
            refine ⟨8372347663570298901409373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581565109046865934272915 8372347663570298901409373)
            ·
              refine ⟨3139630373838862088028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372347663570298901409373 3139630373838862088028515)
              ·
                refine ⟨4709445560758293132042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139630373838862088028515 4709445560758293132042773)
                ·
                  refine ⟨220755260660544990564505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709445560758293132042773 220755260660544990564505)
                  ·
                    rfl

theorem cell22_1934637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1934637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934637 prefixEnd_1934637 := by exact prefixLift 1934637
  have htrace : WordTrace (prefixWord ++ tailWord_1934637) baseStart_1934637 baseEnd_1934637 := by
    simpa [prefixWord, tailWord_1934637, baseEnd_1934637] using wordTrace_append hprefix tailTrace_1934637
  have hstable : (prefixWord ++ tailWord_1934637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934637).length < 2 ^ (prefixWord ++ tailWord_1934637).sum := by decide
  have hdescent : baseEnd_1934637 < baseStart_1934637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934652 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1934652 : Nat := 118140960795 + 1934652 * 2 ^ 59
def prefixEnd_1934652 : Nat := 4983230072969 + 3 ^ 40 * 1934652 * 2
def baseEnd_1934652 : Nat := 662270916788179932568469

theorem tailTrace_1934652 : CollatzResearch.WordTrace tailWord_1934652 prefixEnd_1934652 662270916788179932568469 := by
  unfold tailWord_1934652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281277693546845550623105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47041703591395794067497473 35281277693546845550623105)
  ·
    refine ⟨26460958270160134162967329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35281277693546845550623105 26460958270160134162967329)
    ·
      refine ⟨19845718702620100622225497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26460958270160134162967329 19845718702620100622225497)
      ·
        refine ⟨14884289026965075466669123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19845718702620100622225497 14884289026965075466669123)
        ·
          refine ⟨22326433540447613200003685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14884289026965075466669123 22326433540447613200003685)
          ·
            refine ⟨4186206288833927475000691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22326433540447613200003685 4186206288833927475000691)
            ·
              refine ⟨6279309433250891212501037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186206288833927475000691 6279309433250891212501037)
              ·
                refine ⟨2354741037469084204687889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279309433250891212501037 2354741037469084204687889)
                ·
                  refine ⟨1766055778101813153515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354741037469084204687889 1766055778101813153515917)
                  ·
                    refine ⟨662270916788179932568469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766055778101813153515917 662270916788179932568469)
                    ·
                      rfl

theorem cell22_1934652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1934652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934652 prefixEnd_1934652 := by exact prefixLift 1934652
  have htrace : WordTrace (prefixWord ++ tailWord_1934652) baseStart_1934652 baseEnd_1934652 := by
    simpa [prefixWord, tailWord_1934652, baseEnd_1934652] using wordTrace_append hprefix tailTrace_1934652
  have hstable : (prefixWord ++ tailWord_1934652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934652).length < 2 ^ (prefixWord ++ tailWord_1934652).sum := by decide
  have hdescent : baseEnd_1934652 < baseStart_1934652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934669 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1934669 : Nat := 118140960795 + 1934669 * 2 ^ 59
def prefixEnd_1934669 : Nat := 4983230072969 + 3 ^ 40 * 1934669 * 2
def baseEnd_1934669 : Nat := 662276736235597554893417

theorem tailTrace_1934669 : CollatzResearch.WordTrace tailWord_1934669 prefixEnd_1934669 662276736235597554893417 := by
  unfold tailWord_1934669
  simp only [CollatzResearch.WordTrace]
  refine ⟨70563175428032103004615061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47042116952021402003076707 70563175428032103004615061)
  ·
    refine ⟨3307648848189004828341331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70563175428032103004615061 3307648848189004828341331)
    ·
      refine ⟨4961473272283507242511997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3307648848189004828341331 4961473272283507242511997)
      ·
        refine ⟨1860552477106315215941999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4961473272283507242511997 1860552477106315215941999)
        ·
          refine ⟨2790828715659472823912999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860552477106315215941999 2790828715659472823912999)
          ·
            refine ⟨4186243073489209235869499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790828715659472823912999 4186243073489209235869499)
            ·
              refine ⟨6279364610233813853804249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186243073489209235869499 6279364610233813853804249)
              ·
                refine ⟨4709523457675360390353187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279364610233813853804249 4709523457675360390353187)
                ·
                  refine ⟨7064285186513040585529781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709523457675360390353187 7064285186513040585529781)
                  ·
                    refine ⟨662276736235597554893417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7064285186513040585529781 662276736235597554893417)
                    ·
                      rfl

theorem cell22_1934669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1934669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934669 prefixEnd_1934669 := by exact prefixLift 1934669
  have htrace : WordTrace (prefixWord ++ tailWord_1934669) baseStart_1934669 baseEnd_1934669 := by
    simpa [prefixWord, tailWord_1934669, baseEnd_1934669] using wordTrace_append hprefix tailTrace_1934669
  have hstable : (prefixWord ++ tailWord_1934669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934669).length < 2 ^ (prefixWord ++ tailWord_1934669).sum := by decide
  have hdescent : baseEnd_1934669 < baseStart_1934669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934718 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1934718 : Nat := 118140960795 + 1934718 * 2 ^ 59
def prefixEnd_1934718 : Nat := 4983230072969 + 3 ^ 40 * 1934718 * 2
def baseEnd_1934718 : Nat := 662293509936977760418267

theorem tailTrace_1934718 : CollatzResearch.WordTrace tailWord_1934718 prefixEnd_1934718 662293509936977760418267 := by
  unfold tailWord_1934718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820620325606823046643601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47043308403236389582099205 8820620325606823046643601)
  ·
    refine ⟨6615465244205117284982701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8820620325606823046643601 6615465244205117284982701)
    ·
      refine ⟨2480799466576918981868513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6615465244205117284982701 2480799466576918981868513)
      ·
        refine ⟨1860599599932689236401385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480799466576918981868513 1860599599932689236401385)
        ·
          refine ⟨1395449699949516927301039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860599599932689236401385 1395449699949516927301039)
          ·
            refine ⟨2093174549924275390951559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395449699949516927301039 2093174549924275390951559)
            ·
              refine ⟨3139761824886413086427339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093174549924275390951559 3139761824886413086427339)
              ·
                refine ⟨4709642737329619629641009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139761824886413086427339 4709642737329619629641009)
                ·
                  refine ⟨3532232052997214722230757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709642737329619629641009 3532232052997214722230757)
                  ·
                    refine ⟨662293509936977760418267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3532232052997214722230757 662293509936977760418267)
                    ·
                      rfl

theorem cell22_1934718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1934718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934718 prefixEnd_1934718 := by exact prefixLift 1934718
  have htrace : WordTrace (prefixWord ++ tailWord_1934718) baseStart_1934718 baseEnd_1934718 := by
    simpa [prefixWord, tailWord_1934718, baseEnd_1934718] using wordTrace_append hprefix tailTrace_1934718
  have hstable : (prefixWord ++ tailWord_1934718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934718).length < 2 ^ (prefixWord ++ tailWord_1934718).sum := by decide
  have hdescent : baseEnd_1934718 < baseStart_1934718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934744 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_1934744 : Nat := 118140960795 + 1934744 * 2 ^ 59
def prefixEnd_1934744 : Nat := 4983230072969 + 3 ^ 40 * 1934744 * 2
def baseEnd_1934744 : Nat := 220767470089440786422729

theorem tailTrace_1934744 : CollatzResearch.WordTrace tailWord_1934744 prefixEnd_1934744 220767470089440786422729 := by
  unfold tailWord_1934744
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282955451380195406797643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47043940601840260542396857 35282955451380195406797643)
  ·
    refine ⟨52924433177070293110196465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35282955451380195406797643 52924433177070293110196465)
    ·
      refine ⟨39693324882802719832647349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52924433177070293110196465 39693324882802719832647349)
      ·
        refine ⟨3721249207762754984310689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39693324882802719832647349 3721249207762754984310689)
        ·
          refine ⟨2790936905822066238233017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721249207762754984310689 2790936905822066238233017)
          ·
            refine ⟨2093202679366549678674763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790936905822066238233017 2093202679366549678674763)
            ·
              refine ⟨3139804019049824518012145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093202679366549678674763 3139804019049824518012145)
              ·
                refine ⟨2354853014287368388509109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139804019049824518012145 2354853014287368388509109)
                ·
                  refine ⟨220767470089440786422729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2354853014287368388509109 220767470089440786422729)
                  ·
                    rfl

theorem cell22_1934744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_1934744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934744 prefixEnd_1934744 := by exact prefixLift 1934744
  have htrace : WordTrace (prefixWord ++ tailWord_1934744) baseStart_1934744 baseEnd_1934744 := by
    simpa [prefixWord, tailWord_1934744, baseEnd_1934744] using wordTrace_append hprefix tailTrace_1934744
  have hstable : (prefixWord ++ tailWord_1934744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934744).length < 2 ^ (prefixWord ++ tailWord_1934744).sum := by decide
  have hdescent : baseEnd_1934744 < baseStart_1934744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934755 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 6]
def baseStart_1934755 : Nat := 118140960795 + 1934755 * 2 ^ 59
def prefixEnd_1934755 : Nat := 4983230072969 + 3 ^ 40 * 1934755 * 2
def baseEnd_1934755 : Nat := 220768725264373999081051

theorem tailTrace_1934755 : CollatzResearch.WordTrace tailWord_1934755 prefixEnd_1934755 220768725264373999081051 := by
  unfold tailWord_1934755
  simp only [CollatzResearch.WordTrace]
  refine ⟨70566312105720539692245719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47044208070480359794830479 70566312105720539692245719)
  ·
    refine ⟨105849468158580809538368579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70566312105720539692245719 105849468158580809538368579)
    ·
      refine ⟨158774202237871214307552869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105849468158580809538368579 158774202237871214307552869)
      ·
        refine ⟨29770162919600852682666163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158774202237871214307552869 29770162919600852682666163)
        ·
          refine ⟨44655244379401279023999245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29770162919600852682666163 44655244379401279023999245)
          ·
            refine ⟨16745716642275479633999717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44655244379401279023999245 16745716642275479633999717)
            ·
              refine ⟨3139821870426652431374947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16745716642275479633999717 3139821870426652431374947)
              ·
                refine ⟨4709732805639978647062421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139821870426652431374947 4709732805639978647062421)
                ·
                  refine ⟨220768725264373999081051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709732805639978647062421 220768725264373999081051)
                  ·
                    rfl

theorem cell22_1934755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_1934755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934755 prefixEnd_1934755 := by exact prefixLift 1934755
  have htrace : WordTrace (prefixWord ++ tailWord_1934755) baseStart_1934755 baseEnd_1934755 := by
    simpa [prefixWord, tailWord_1934755, baseEnd_1934755] using wordTrace_append hprefix tailTrace_1934755
  have hstable : (prefixWord ++ tailWord_1934755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934755).length < 2 ^ (prefixWord ++ tailWord_1934755).sum := by decide
  have hdescent : baseEnd_1934755 < baseStart_1934755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934770 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1934770 : Nat := 118140960795 + 1934770 * 2 ^ 59
def prefixEnd_1934770 : Nat := 4983230072969 + 3 ^ 40 * 1934770 * 2
def baseEnd_1934770 : Nat := 662311310599666958118107

theorem tailTrace_1934770 : CollatzResearch.WordTrace tailWord_1934770 prefixEnd_1934770 662311310599666958118107 := by
  unfold tailWord_1934770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641714800166549313510441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47044572800444131502694509 17641714800166549313510441)
  ·
    refine ⟨13231286100124911985132831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17641714800166549313510441 13231286100124911985132831)
    ·
      refine ⟨19846929150187367977699247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13231286100124911985132831 19846929150187367977699247)
      ·
        refine ⟨29770393725281051966548871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846929150187367977699247 29770393725281051966548871)
        ·
          refine ⟨44655590587921577949823307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29770393725281051966548871 44655590587921577949823307)
          ·
            refine ⟨66983385881882366924734961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44655590587921577949823307 66983385881882366924734961)
            ·
              refine ⟨50237539411411775193551221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66983385881882366924734961 50237539411411775193551221)
              ·
                refine ⟨4709769319819853924395427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50237539411411775193551221 4709769319819853924395427)
                ·
                  refine ⟨7064653979729780886593141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709769319819853924395427 7064653979729780886593141)
                  ·
                    refine ⟨662311310599666958118107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7064653979729780886593141 662311310599666958118107)
                    ·
                      rfl

theorem cell22_1934770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1934770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934770 prefixEnd_1934770 := by exact prefixLift 1934770
  have htrace : WordTrace (prefixWord ++ tailWord_1934770) baseStart_1934770 baseEnd_1934770 := by
    simpa [prefixWord, tailWord_1934770, baseEnd_1934770] using wordTrace_append hprefix tailTrace_1934770
  have hstable : (prefixWord ++ tailWord_1934770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934770).length < 2 ^ (prefixWord ++ tailWord_1934770).sum := by decide
  have hdescent : baseEnd_1934770 < baseStart_1934770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934821 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_1934821 : Nat := 118140960795 + 1934821 * 2 ^ 59
def prefixEnd_1934821 : Nat := 4983230072969 + 3 ^ 40 * 1934821 * 2
def baseEnd_1934821 : Nat := 662328768941919825092951

theorem tailTrace_1934821 : CollatzResearch.WordTrace tailWord_1934821 prefixEnd_1934821 662328768941919825092951 := by
  unfold tailWord_1934821
  simp only [CollatzResearch.WordTrace]
  refine ⟨70568719323481432964148317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47045812882320955309432211 70568719323481432964148317)
  ·
    refine ⟨26463269746305537361555619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70568719323481432964148317 26463269746305537361555619)
    ·
      refine ⟨39694904619458306042333429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463269746305537361555619 39694904619458306042333429)
      ·
        refine ⟨3721397308074216191468759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39694904619458306042333429 3721397308074216191468759)
        ·
          refine ⟨5582095962111324287203139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721397308074216191468759 5582095962111324287203139)
          ·
            refine ⟨8373143943166986430804709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582095962111324287203139 8373143943166986430804709)
            ·
              refine ⟨1569964489343809955775883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8373143943166986430804709 1569964489343809955775883)
              ·
                refine ⟨2354946734015714933663825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569964489343809955775883 2354946734015714933663825)
                ·
                  refine ⟨1766210050511786200247869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354946734015714933663825 1766210050511786200247869)
                  ·
                    refine ⟨662328768941919825092951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766210050511786200247869 662328768941919825092951)
                    ·
                      rfl

theorem cell22_1934821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_1934821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934821 prefixEnd_1934821 := by exact prefixLift 1934821
  have htrace : WordTrace (prefixWord ++ tailWord_1934821) baseStart_1934821 baseEnd_1934821 := by
    simpa [prefixWord, tailWord_1934821, baseEnd_1934821] using wordTrace_append hprefix tailTrace_1934821
  have hstable : (prefixWord ++ tailWord_1934821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934821).length < 2 ^ (prefixWord ++ tailWord_1934821).sum := by decide
  have hdescent : baseEnd_1934821 < baseStart_1934821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934877 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1934877 : Nat := 118140960795 + 1934877 * 2 ^ 59
def prefixEnd_1934877 : Nat := 4983230072969 + 3 ^ 40 * 1934877 * 2
def baseEnd_1934877 : Nat := 662347938886354345692779

theorem tailTrace_1934877 : CollatzResearch.WordTrace tailWord_1934877 prefixEnd_1934877 662347938886354345692779 := by
  unfold tailWord_1934877
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570761811278554528186885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47047174540852369685457923 70570761811278554528186885)
  ·
    refine ⟨13232017839614728974035041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70570761811278554528186885 13232017839614728974035041)
    ·
      refine ⟨9924013379711046730526281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13232017839614728974035041 9924013379711046730526281)
      ·
        refine ⟨7443010034783285047894711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924013379711046730526281 7443010034783285047894711)
        ·
          refine ⟨11164515052174927571842067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443010034783285047894711 11164515052174927571842067)
          ·
            refine ⟨16746772578262391357763101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164515052174927571842067 16746772578262391357763101)
            ·
              refine ⟨6280039716848396759161163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16746772578262391357763101 6280039716848396759161163)
              ·
                refine ⟨9420059575272595138741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280039716848396759161163 9420059575272595138741745)
                ·
                  refine ⟨7065044681454446354056309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420059575272595138741745 7065044681454446354056309)
                  ·
                    refine ⟨662347938886354345692779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7065044681454446354056309 662347938886354345692779)
                    ·
                      rfl

theorem cell22_1934877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1934877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934877 prefixEnd_1934877 := by exact prefixLift 1934877
  have htrace : WordTrace (prefixWord ++ tailWord_1934877) baseStart_1934877 baseEnd_1934877 := by
    simpa [prefixWord, tailWord_1934877, baseEnd_1934877] using wordTrace_append hprefix tailTrace_1934877
  have hstable : (prefixWord ++ tailWord_1934877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934877).length < 2 ^ (prefixWord ++ tailWord_1934877).sum := by decide
  have hdescent : baseEnd_1934877 < baseStart_1934877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934924 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1934924 : Nat := 118140960795 + 1934924 * 2 ^ 59
def prefixEnd_1934924 : Nat := 4983230072969 + 3 ^ 40 * 1934924 * 2
def baseEnd_1934924 : Nat := 220788009315620629922545

theorem tailTrace_1934924 : CollatzResearch.WordTrace tailWord_1934924 prefixEnd_1934924 220788009315620629922545 := by
  unfold tailWord_1934924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35286238021054140777573913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47048317361405521036765217 35286238021054140777573913)
  ·
    refine ⟨26464678515790605583180435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35286238021054140777573913 26464678515790605583180435)
    ·
      refine ⟨39697017773685908374770653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26464678515790605583180435 39697017773685908374770653)
      ·
        refine ⟨14886381665132215640538995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39697017773685908374770653 14886381665132215640538995)
        ·
          refine ⟨22329572497698323460808493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886381665132215640538995 22329572497698323460808493)
          ·
            refine ⟨8373589686636871297803185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22329572497698323460808493 8373589686636871297803185)
            ·
              refine ⟨6280192264977653473352389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373589686636871297803185 6280192264977653473352389)
              ·
                refine ⟨1177536049683310026253573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6280192264977653473352389 1177536049683310026253573)
                ·
                  refine ⟨220788009315620629922545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177536049683310026253573 220788009315620629922545)
                  ·
                    rfl

theorem cell22_1934924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1934924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934924 prefixEnd_1934924 := by exact prefixLift 1934924
  have htrace : WordTrace (prefixWord ++ tailWord_1934924) baseStart_1934924 baseEnd_1934924 := by
    simpa [prefixWord, tailWord_1934924, baseEnd_1934924] using wordTrace_append hprefix tailTrace_1934924
  have hstable : (prefixWord ++ tailWord_1934924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934924).length < 2 ^ (prefixWord ++ tailWord_1934924).sum := by decide
  have hdescent : baseEnd_1934924 < baseStart_1934924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934958 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_1934958 : Nat := 118140960795 + 1934958 * 2 ^ 59
def prefixEnd_1934958 : Nat := 4983230072969 + 3 ^ 40 * 1934958 * 2
def baseEnd_1934958 : Nat := 220791888947232378139177

theorem tailTrace_1934958 : CollatzResearch.WordTrace tailWord_1934958 prefixEnd_1934958 220791888947232378139177 := by
  unfold tailWord_1934958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821714515498138170235691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47049144082656736907923685 8821714515498138170235691)
  ·
    refine ⟨13232571773247207255353537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8821714515498138170235691 13232571773247207255353537)
    ·
      refine ⟨9924428829935405441515153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13232571773247207255353537 9924428829935405441515153)
      ·
        refine ⟨7443321622451554081136365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924428829935405441515153 7443321622451554081136365)
        ·
          refine ⟨2791245608419332780426137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443321622451554081136365 2791245608419332780426137)
          ·
            refine ⟨2093434206314499585319603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2791245608419332780426137 2093434206314499585319603)
            ·
              refine ⟨3140151309471749377979405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093434206314499585319603 3140151309471749377979405)
              ·
                refine ⟨1177556741051906016742277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3140151309471749377979405 1177556741051906016742277)
                ·
                  refine ⟨220791888947232378139177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177556741051906016742277 220791888947232378139177)
                  ·
                    rfl

theorem cell22_1934958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_1934958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1934958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1934958 prefixEnd_1934958 := by exact prefixLift 1934958
  have htrace : WordTrace (prefixWord ++ tailWord_1934958) baseStart_1934958 baseEnd_1934958 := by
    simpa [prefixWord, tailWord_1934958, baseEnd_1934958] using wordTrace_append hprefix tailTrace_1934958
  have hstable : (prefixWord ++ tailWord_1934958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934958).length < 2 ^ (prefixWord ++ tailWord_1934958).sum := by decide
  have hdescent : baseEnd_1934958 < baseStart_1934958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935044 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1935044 : Nat := 118140960795 + 1935044 * 2 ^ 59
def prefixEnd_1935044 : Nat := 4983230072969 + 3 ^ 40 * 1935044 * 2
def baseEnd_1935044 : Nat := 662405106399221576767267

theorem tailTrace_1935044 : CollatzResearch.WordTrace tailWord_1935044 prefixEnd_1935044 662405106399221576767267 := by
  unfold tailWord_1935044
  simp only [CollatzResearch.WordTrace]
  refine ⟨35288426400836771024758093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47051235201115694699677457 35288426400836771024758093)
  ·
    refine ⟨13233159900313789134284285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35288426400836771024758093 13233159900313789134284285)
    ·
      refine ⟨4962434962617670925356607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13233159900313789134284285 4962434962617670925356607)
      ·
        refine ⟨7443652443926506388034911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962434962617670925356607 7443652443926506388034911)
        ·
          refine ⟨11165478665889759582052367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443652443926506388034911 11165478665889759582052367)
          ·
            refine ⟨16748217998834639373078551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165478665889759582052367 16748217998834639373078551)
            ·
              refine ⟨25122326998251959059617827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16748217998834639373078551 25122326998251959059617827)
              ·
                refine ⟨37683490497377938589426741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25122326998251959059617827 37683490497377938589426741)
                ·
                  refine ⟨3532827234129181742758757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37683490497377938589426741 3532827234129181742758757)
                  ·
                    refine ⟨662405106399221576767267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3532827234129181742758757 662405106399221576767267)
                    ·
                      rfl

theorem cell22_1935044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1935044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935044 prefixEnd_1935044 := by exact prefixLift 1935044
  have htrace : WordTrace (prefixWord ++ tailWord_1935044) baseStart_1935044 baseEnd_1935044 := by
    simpa [prefixWord, tailWord_1935044, baseEnd_1935044] using wordTrace_append hprefix tailTrace_1935044
  have hstable : (prefixWord ++ tailWord_1935044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935044).length < 2 ^ (prefixWord ++ tailWord_1935044).sum := by decide
  have hdescent : baseEnd_1935044 < baseStart_1935044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935076 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1935076 : Nat := 118140960795 + 1935076 * 2 ^ 59
def prefixEnd_1935076 : Nat := 4983230072969 + 3 ^ 40 * 1935076 * 2
def baseEnd_1935076 : Nat := 220805353551061386655723

theorem tailTrace_1935076 : CollatzResearch.WordTrace tailWord_1935076 prefixEnd_1935076 220805353551061386655723 := by
  unfold tailWord_1935076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35289009968778805757340541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47052013291705074343120721 35289009968778805757340541)
  ·
    refine ⟨13233378738292052159002703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35289009968778805757340541 13233378738292052159002703)
    ·
      refine ⟨19850068107438078238504055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13233378738292052159002703 19850068107438078238504055)
      ·
        refine ⟨29775102161157117357756083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19850068107438078238504055 29775102161157117357756083)
        ·
          refine ⟨44662653241735676036634125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29775102161157117357756083 44662653241735676036634125)
          ·
            refine ⟨16748494965650878513737797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44662653241735676036634125 16748494965650878513737797)
            ·
              refine ⟨3140342806059539721325837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16748494965650878513737797 3140342806059539721325837)
              ·
                refine ⟨1177628552272327395497189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3140342806059539721325837 1177628552272327395497189)
                ·
                  refine ⟨220805353551061386655723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177628552272327395497189 220805353551061386655723)
                  ·
                    rfl

theorem cell22_1935076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1935076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935076 prefixEnd_1935076 := by exact prefixLift 1935076
  have htrace : WordTrace (prefixWord ++ tailWord_1935076) baseStart_1935076 baseEnd_1935076 := by
    simpa [prefixWord, tailWord_1935076, baseEnd_1935076] using wordTrace_append hprefix tailTrace_1935076
  have hstable : (prefixWord ++ tailWord_1935076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935076).length < 2 ^ (prefixWord ++ tailWord_1935076).sum := by decide
  have hdescent : baseEnd_1935076 < baseStart_1935076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935087 : List Nat := [1, 1, 2, 1, 5, 1, 11]
def baseStart_1935087 : Nat := 118140960795 + 1935087 * 2 ^ 59
def prefixEnd_1935087 : Nat := 4983230072969 + 3 ^ 40 * 1935087 * 2
def baseEnd_1935087 : Nat := 24534067636221622146005

theorem tailTrace_1935087 : CollatzResearch.WordTrace tailWord_1935087 prefixEnd_1935087 24534067636221622146005 := by
  unfold tailWord_1935087
  simp only [CollatzResearch.WordTrace]
  refine ⟨70578421140517760393331515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47052280760345173595554343 70578421140517760393331515)
  ·
    refine ⟨105867631710776640589997273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70578421140517760393331515 105867631710776640589997273)
    ·
      refine ⟨79400723783082480442497955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105867631710776640589997273 79400723783082480442497955)
      ·
        refine ⟨119101085674623720663746933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79400723783082480442497955 119101085674623720663746933)
        ·
          refine ⟨11165726781995973812226275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119101085674623720663746933 11165726781995973812226275)
          ·
            refine ⟨16748590172993960718339413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165726781995973812226275 16748590172993960718339413)
            ·
              refine ⟨24534067636221622146005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16748590172993960718339413 24534067636221622146005)
              ·
                rfl

theorem cell22_1935087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 11].length) (baseStart_1935087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935087 prefixEnd_1935087 := by exact prefixLift 1935087
  have htrace : WordTrace (prefixWord ++ tailWord_1935087) baseStart_1935087 baseEnd_1935087 := by
    simpa [prefixWord, tailWord_1935087, baseEnd_1935087] using wordTrace_append hprefix tailTrace_1935087
  have hstable : (prefixWord ++ tailWord_1935087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935087).length < 2 ^ (prefixWord ++ tailWord_1935087).sum := by decide
  have hdescent : baseEnd_1935087 < baseStart_1935087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935091 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 2, 3]
def baseStart_1935091 : Nat := 118140960795 + 1935091 * 2 ^ 59
def prefixEnd_1935091 : Nat := 4983230072969 + 3 ^ 40 * 1935091 * 2
def baseEnd_1935091 : Nat := 662421195459729120842123

theorem tailTrace_1935091 : CollatzResearch.WordTrace tailWord_1935091 prefixEnd_1935091 662421195459729120842123 := by
  unfold tailWord_1935091
  simp only [CollatzResearch.WordTrace]
  refine ⟨70578567032503269076477127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47052378021668846050984751 70578567032503269076477127)
  ·
    refine ⟨105867850548754903614715691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70578567032503269076477127 105867850548754903614715691)
    ·
      refine ⟨158801775823132355422073537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105867850548754903614715691 158801775823132355422073537)
      ·
        refine ⟨119101331867349266566555153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158801775823132355422073537 119101331867349266566555153)
        ·
          refine ⟨89325998900511949924916365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119101331867349266566555153 89325998900511949924916365)
          ·
            refine ⟨33497249587691981221843637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89325998900511949924916365 33497249587691981221843637)
            ·
              refine ⟨3140367148846123239547841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33497249587691981221843637 3140367148846123239547841)
              ·
                refine ⟨2355275361634592429660881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140367148846123239547841 2355275361634592429660881)
                ·
                  refine ⟨1766456521225944322245661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355275361634592429660881 1766456521225944322245661)
                  ·
                    refine ⟨662421195459729120842123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766456521225944322245661 662421195459729120842123)
                    ·
                      rfl

theorem cell22_1935091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].length) (baseStart_1935091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935091 prefixEnd_1935091 := by exact prefixLift 1935091
  have htrace : WordTrace (prefixWord ++ tailWord_1935091) baseStart_1935091 baseEnd_1935091 := by
    simpa [prefixWord, tailWord_1935091, baseEnd_1935091] using wordTrace_append hprefix tailTrace_1935091
  have hstable : (prefixWord ++ tailWord_1935091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935091).length < 2 ^ (prefixWord ++ tailWord_1935091).sum := by decide
  have hdescent : baseEnd_1935091 < baseStart_1935091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935119 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 5, 3]
def baseStart_1935119 : Nat := 118140960795 + 1935119 * 2 ^ 59
def prefixEnd_1935119 : Nat := 4983230072969 + 3 ^ 40 * 1935119 * 2
def baseEnd_1935119 : Nat := 662430780431946381142037

theorem tailTrace_1935119 : CollatzResearch.WordTrace tailWord_1935119 prefixEnd_1935119 662430780431946381142037 := by
  unfold tailWord_1935119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70579588276401829858496411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47053058850934553238997607 70579588276401829858496411)
  ·
    refine ⟨105869382414602744787744617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70579588276401829858496411 105869382414602744787744617)
    ·
      refine ⟨79402036810952058590808463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105869382414602744787744617 79402036810952058590808463)
      ·
        refine ⟨119103055216428087886212695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79402036810952058590808463 119103055216428087886212695)
        ·
          refine ⟨178654582824642131829319043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119103055216428087886212695 178654582824642131829319043)
          ·
            refine ⟨267981874236963197743978565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178654582824642131829319043 267981874236963197743978565)
            ·
              refine ⟨50246601419430599576995981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267981874236963197743978565 50246601419430599576995981)
              ·
                refine ⟨18842475532286474841373493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50246601419430599576995981 18842475532286474841373493)
                ·
                  refine ⟨1766482081151857016378765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18842475532286474841373493 1766482081151857016378765)
                  ·
                    refine ⟨662430780431946381142037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766482081151857016378765 662430780431946381142037)
                    ·
                      rfl

theorem cell22_1935119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_1935119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935119 prefixEnd_1935119 := by exact prefixLift 1935119
  have htrace : WordTrace (prefixWord ++ tailWord_1935119) baseStart_1935119 baseEnd_1935119 := by
    simpa [prefixWord, tailWord_1935119, baseEnd_1935119] using wordTrace_append hprefix tailTrace_1935119
  have hstable : (prefixWord ++ tailWord_1935119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935119).length < 2 ^ (prefixWord ++ tailWord_1935119).sum := by decide
  have hdescent : baseEnd_1935119 < baseStart_1935119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935153 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1935153 : Nat := 118140960795 + 1935153 * 2 ^ 59
def prefixEnd_1935153 : Nat := 4983230072969 + 3 ^ 40 * 1935153 * 2
def baseEnd_1935153 : Nat := 662442419326781625791933

theorem tailTrace_1935153 : CollatzResearch.WordTrace tailWord_1935153 prefixEnd_1935153 662442419326781625791933 := by
  unfold tailWord_1935153
  simp only [CollatzResearch.WordTrace]
  refine ⟨70580828358278653665234113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47053885572185769110156075 70580828358278653665234113)
  ·
    refine ⟨52935621268708990248925585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70580828358278653665234113 52935621268708990248925585)
    ·
      refine ⟨39701715951531742686694189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52935621268708990248925585 39701715951531742686694189)
      ·
        refine ⟨14888143481824403507510321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39701715951531742686694189 14888143481824403507510321)
        ·
          refine ⟨11166107611368302630632741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14888143481824403507510321 11166107611368302630632741)
          ·
            refine ⟨2093645177131556743243639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11166107611368302630632741 2093645177131556743243639)
            ·
              refine ⟨3140467765697335114865459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093645177131556743243639 3140467765697335114865459)
              ·
                refine ⟨4710701648546002672298189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140467765697335114865459 4710701648546002672298189)
                ·
                  refine ⟨1766513118204751002111821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4710701648546002672298189 1766513118204751002111821)
                  ·
                    refine ⟨662442419326781625791933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766513118204751002111821 662442419326781625791933)
                    ·
                      rfl

theorem cell22_1935153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1935153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935153 prefixEnd_1935153 := by exact prefixLift 1935153
  have htrace : WordTrace (prefixWord ++ tailWord_1935153) baseStart_1935153 baseEnd_1935153 := by
    simpa [prefixWord, tailWord_1935153, baseEnd_1935153] using wordTrace_append hprefix tailTrace_1935153
  have hstable : (prefixWord ++ tailWord_1935153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935153).length < 2 ^ (prefixWord ++ tailWord_1935153).sum := by decide
  have hdescent : baseEnd_1935153 < baseStart_1935153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935164 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1935164 : Nat := 118140960795 + 1935164 * 2 ^ 59
def prefixEnd_1935164 : Nat := 4983230072969 + 3 ^ 40 * 1935164 * 2
def baseEnd_1935164 : Nat := 662446184851581263766899

theorem tailTrace_1935164 : CollatzResearch.WordTrace tailWord_1935164 prefixEnd_1935164 662446184851581263766899 := by
  unfold tailWord_1935164
  simp only [CollatzResearch.WordTrace]
  refine ⟨35290614780619401271942273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47054153040825868362589697 35290614780619401271942273)
  ·
    refine ⟨26467961085464550953956705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35290614780619401271942273 26467961085464550953956705)
    ·
      refine ⟨19850970814098413215467529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26467961085464550953956705 19850970814098413215467529)
      ·
        refine ⟨14888228110573809911600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19850970814098413215467529 14888228110573809911600647)
        ·
          refine ⟨22332342165860714867400971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888228110573809911600647 22332342165860714867400971)
          ·
            refine ⟨33498513248791072301101457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22332342165860714867400971 33498513248791072301101457)
            ·
              refine ⟨25123884936593304225826093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33498513248791072301101457 25123884936593304225826093)
              ·
                refine ⟨9421456851222489084684785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25123884936593304225826093 9421456851222489084684785)
                ·
                  refine ⟨7066092638416866813513589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421456851222489084684785 7066092638416866813513589)
                  ·
                    refine ⟨662446184851581263766899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7066092638416866813513589 662446184851581263766899)
                    ·
                      rfl

theorem cell22_1935164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1935164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935164 prefixEnd_1935164 := by exact prefixLift 1935164
  have htrace : WordTrace (prefixWord ++ tailWord_1935164) baseStart_1935164 baseEnd_1935164 := by
    simpa [prefixWord, tailWord_1935164, baseEnd_1935164] using wordTrace_append hprefix tailTrace_1935164
  have hstable : (prefixWord ++ tailWord_1935164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935164).length < 2 ^ (prefixWord ++ tailWord_1935164).sum := by decide
  have hdescent : baseEnd_1935164 < baseStart_1935164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935204 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1935204 : Nat := 118140960795 + 1935204 * 2 ^ 59
def prefixEnd_1935204 : Nat := 4983230072969 + 3 ^ 40 * 1935204 * 2
def baseEnd_1935204 : Nat := 662459877669034492766777

theorem tailTrace_1935204 : CollatzResearch.WordTrace tailWord_1935204 prefixEnd_1935204 662459877669034492766777 := by
  unfold tailWord_1935204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291344240546944687670333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47055125654062592916893777 35291344240546944687670333)
  ·
    refine ⟨13234254090205104257876375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35291344240546944687670333 13234254090205104257876375)
    ·
      refine ⟨19851381135307656386814563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13234254090205104257876375 19851381135307656386814563)
      ·
        refine ⟨29777071702961484580221845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19851381135307656386814563 29777071702961484580221845)
        ·
          refine ⟨1395800236076319589697899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29777071702961484580221845 1395800236076319589697899)
          ·
            refine ⟨2093700354114479384546849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395800236076319589697899 2093700354114479384546849)
            ·
              refine ⟨1570275265585859538410137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093700354114479384546849 1570275265585859538410137)
              ·
                refine ⟨1177706449189394653807603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570275265585859538410137 1177706449189394653807603)
                ·
                  refine ⟨1766559673784091980711405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177706449189394653807603 1766559673784091980711405)
                  ·
                    refine ⟨662459877669034492766777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766559673784091980711405 662459877669034492766777)
                    ·
                      rfl

theorem cell22_1935204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1935204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935204 prefixEnd_1935204 := by exact prefixLift 1935204
  have htrace : WordTrace (prefixWord ++ tailWord_1935204) baseStart_1935204 baseEnd_1935204 := by
    simpa [prefixWord, tailWord_1935204, baseEnd_1935204] using wordTrace_append hprefix tailTrace_1935204
  have hstable : (prefixWord ++ tailWord_1935204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935204).length < 2 ^ (prefixWord ++ tailWord_1935204).sum := by decide
  have hdescent : baseEnd_1935204 < baseStart_1935204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935260 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1935260 : Nat := 118140960795 + 1935260 * 2 ^ 59
def prefixEnd_1935260 : Nat := 4983230072969 + 3 ^ 40 * 1935260 * 2
def baseEnd_1935260 : Nat := 662479047613469013366605

theorem tailTrace_1935260 : CollatzResearch.WordTrace tailWord_1935260 prefixEnd_1935260 662479047613469013366605 := by
  unfold tailWord_1935260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35292365484445505469689617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47056487312594007292919489 35292365484445505469689617)
  ·
    refine ⟨26469274113334129102267213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35292365484445505469689617 26469274113334129102267213)
    ·
      refine ⟨9925977792500298413350205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26469274113334129102267213 9925977792500298413350205)
      ·
        refine ⟨3722241672187611905006327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9925977792500298413350205 3722241672187611905006327)
        ·
          refine ⟨5583362508281417857509491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722241672187611905006327 5583362508281417857509491)
          ·
            refine ⟨8375043762422126786264237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583362508281417857509491 8375043762422126786264237)
            ·
              refine ⟨3140641410908297544849089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8375043762422126786264237 3140641410908297544849089)
              ·
                refine ⟨2355481058181223158636817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140641410908297544849089 2355481058181223158636817)
                ·
                  refine ⟨1766610793635917368977613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355481058181223158636817 1766610793635917368977613)
                  ·
                    refine ⟨662479047613469013366605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766610793635917368977613 662479047613469013366605)
                    ·
                      rfl

theorem cell22_1935260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1935260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935260 prefixEnd_1935260 := by exact prefixLift 1935260
  have htrace : WordTrace (prefixWord ++ tailWord_1935260) baseStart_1935260 baseEnd_1935260 := by
    simpa [prefixWord, tailWord_1935260, baseEnd_1935260] using wordTrace_append hprefix tailTrace_1935260
  have hstable : (prefixWord ++ tailWord_1935260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935260).length < 2 ^ (prefixWord ++ tailWord_1935260).sum := by decide
  have hdescent : baseEnd_1935260 < baseStart_1935260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935269 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1935269 : Nat := 118140960795 + 1935269 * 2 ^ 59
def prefixEnd_1935269 : Nat := 4983230072969 + 3 ^ 40 * 1935269 * 2
def baseEnd_1935269 : Nat := 662482128497395989891577

theorem tailTrace_1935269 : CollatzResearch.WordTrace tailWord_1935269 prefixEnd_1935269 662482128497395989891577 := by
  unfold tailWord_1935269
  simp only [CollatzResearch.WordTrace]
  refine ⟨70585059225858405476456861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47056706150572270317637907 70585059225858405476456861)
  ·
    refine ⟨26469397209696902053671323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70585059225858405476456861 26469397209696902053671323)
    ·
      refine ⟨39704095814545353080506985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26469397209696902053671323 39704095814545353080506985)
      ·
        refine ⟨29778071860909014810380239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39704095814545353080506985 29778071860909014810380239)
        ·
          refine ⟨44667107791363522215570359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778071860909014810380239 44667107791363522215570359)
          ·
            refine ⟨67000661687045283323355539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667107791363522215570359 67000661687045283323355539)
            ·
              refine ⟨100500992530567924985033309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67000661687045283323355539 100500992530567924985033309)
              ·
                refine ⟨37687872198962971869387491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100500992530567924985033309 37687872198962971869387491)
                ·
                  refine ⟨56531808298444457804081237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37687872198962971869387491 56531808298444457804081237)
                  ·
                    refine ⟨662482128497395989891577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56531808298444457804081237 662482128497395989891577)
                    ·
                      rfl

theorem cell22_1935269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1935269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935269 prefixEnd_1935269 := by exact prefixLift 1935269
  have htrace : WordTrace (prefixWord ++ tailWord_1935269) baseStart_1935269 baseEnd_1935269 := by
    simpa [prefixWord, tailWord_1935269, baseEnd_1935269] using wordTrace_append hprefix tailTrace_1935269
  have hstable : (prefixWord ++ tailWord_1935269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935269).length < 2 ^ (prefixWord ++ tailWord_1935269).sum := by decide
  have hdescent : baseEnd_1935269 < baseStart_1935269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935322 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_1935322 : Nat := 118140960795 + 1935322 * 2 ^ 59
def prefixEnd_1935322 : Nat := 4983230072969 + 3 ^ 40 * 1935322 * 2
def baseEnd_1935322 : Nat := 662500271480521518316415

theorem tailTrace_1935322 : CollatzResearch.WordTrace tailWord_1935322 prefixEnd_1935322 662500271480521518316415 := by
  unfold tailWord_1935322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646748073666598882034055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47057994863110930352090813 17646748073666598882034055)
  ·
    refine ⟨26470122110499898323051083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17646748073666598882034055 26470122110499898323051083)
    ·
      refine ⟨39705183165749847484576625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26470122110499898323051083 39705183165749847484576625)
      ·
        refine ⟨29778887374312385613432469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39705183165749847484576625 29778887374312385613432469)
        ·
          refine ⟨1395885345670893075629647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29778887374312385613432469 1395885345670893075629647)
          ·
            refine ⟨2093828018506339613444471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395885345670893075629647 2093828018506339613444471)
            ·
              refine ⟨3140742027759509420166707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093828018506339613444471 3140742027759509420166707)
              ·
                refine ⟨4711113041639264130250061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140742027759509420166707 4711113041639264130250061)
                ·
                  refine ⟨1766667390614724048843773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4711113041639264130250061 1766667390614724048843773)
                  ·
                    refine ⟨662500271480521518316415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766667390614724048843773 662500271480521518316415)
                    ·
                      rfl

theorem cell22_1935322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_1935322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935322 prefixEnd_1935322 := by exact prefixLift 1935322
  have htrace : WordTrace (prefixWord ++ tailWord_1935322) baseStart_1935322 baseEnd_1935322 := by
    simpa [prefixWord, tailWord_1935322, baseEnd_1935322] using wordTrace_append hprefix tailTrace_1935322
  have hstable : (prefixWord ++ tailWord_1935322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935322).length < 2 ^ (prefixWord ++ tailWord_1935322).sum := by decide
  have hdescent : baseEnd_1935322 < baseStart_1935322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935365 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_1935365 : Nat := 118140960795 + 1935365 * 2 ^ 59
def prefixEnd_1935365 : Nat := 4983230072969 + 3 ^ 40 * 1935365 * 2
def baseEnd_1935365 : Nat := 662514991259283739491283

theorem tailTrace_1935365 : CollatzResearch.WordTrace tailWord_1935365 prefixEnd_1935365 662514991259283739491283 := by
  unfold tailWord_1935365
  simp only [CollatzResearch.WordTrace]
  refine ⟨70588560633510613871951549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47059040422340409247967699 70588560633510613871951549)
  ·
    refine ⟨26470710237566480201981831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70588560633510613871951549 26470710237566480201981831)
    ·
      refine ⟨39706065356349720302972747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26470710237566480201981831 39706065356349720302972747)
      ·
        refine ⟨59559098034524580454459121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39706065356349720302972747 59559098034524580454459121)
        ·
          refine ⟨44669323525893435340844341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59559098034524580454459121 44669323525893435340844341)
          ·
            refine ⟨4187749080552509563204157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44669323525893435340844341 4187749080552509563204157)
            ·
              refine ⟨1570405905207191086201559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187749080552509563204157 1570405905207191086201559)
              ·
                refine ⟨2355608857810786629302339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570405905207191086201559 2355608857810786629302339)
                ·
                  refine ⟨3533413286716179943953509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355608857810786629302339 3533413286716179943953509)
                  ·
                    refine ⟨662514991259283739491283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533413286716179943953509 662514991259283739491283)
                    ·
                      rfl

theorem cell22_1935365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_1935365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935365 prefixEnd_1935365 := by exact prefixLift 1935365
  have htrace : WordTrace (prefixWord ++ tailWord_1935365) baseStart_1935365 baseEnd_1935365 := by
    simpa [prefixWord, tailWord_1935365, baseEnd_1935365] using wordTrace_append hprefix tailTrace_1935365
  have hstable : (prefixWord ++ tailWord_1935365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935365).length < 2 ^ (prefixWord ++ tailWord_1935365).sum := by decide
  have hdescent : baseEnd_1935365 < baseStart_1935365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935408 : List Nat := [2, 1, 1, 1, 2, 6, 3, 6]
def baseStart_1935408 : Nat := 118140960795 + 1935408 * 2 ^ 59
def prefixEnd_1935408 : Nat := 4983230072969 + 3 ^ 40 * 1935408 * 2
def baseEnd_1935408 : Nat := 73614412337560662296239

theorem tailTrace_1935408 : CollatzResearch.WordTrace tailWord_1935408 prefixEnd_1935408 73614412337560662296239 := by
  unfold tailWord_1935408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35295064486177416107883439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47060085981569888143844585 35295064486177416107883439)
  ·
    refine ⟨52942596729266124161825159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35295064486177416107883439 52942596729266124161825159)
    ·
      refine ⟨79413895093899186242737739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52942596729266124161825159 79413895093899186242737739)
      ·
        refine ⟨119120842640848779364106609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79413895093899186242737739 119120842640848779364106609)
        ·
          refine ⟨89340631980636584523079957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119120842640848779364106609 89340631980636584523079957)
          ·
            refine ⟨4187842124092339899519373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89340631980636584523079957 4187842124092339899519373)
            ·
              refine ⟨1570440796534627462319765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187842124092339899519373 1570440796534627462319765)
              ·
                refine ⟨73614412337560662296239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1570440796534627462319765 73614412337560662296239)
                ·
                  rfl

theorem cell22_1935408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_1935408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935408 prefixEnd_1935408 := by exact prefixLift 1935408
  have htrace : WordTrace (prefixWord ++ tailWord_1935408) baseStart_1935408 baseEnd_1935408 := by
    simpa [prefixWord, tailWord_1935408, baseEnd_1935408] using wordTrace_append hprefix tailTrace_1935408
  have hstable : (prefixWord ++ tailWord_1935408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935408).length < 2 ^ (prefixWord ++ tailWord_1935408).sum := by decide
  have hdescent : baseEnd_1935408 < baseStart_1935408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935410 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1935410 : Nat := 118140960795 + 1935410 * 2 ^ 59
def prefixEnd_1935410 : Nat := 4983230072969 + 3 ^ 40 * 1935410 * 2
def baseEnd_1935410 : Nat := 662530395678918622116145

theorem tailTrace_1935410 : CollatzResearch.WordTrace tailWord_1935410 prefixEnd_1935410 662530395678918622116145 := by
  unfold tailWord_1935410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647550479586896639334921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47060134612231724371559789 17647550479586896639334921)
  ·
    refine ⟨13235662859690172479501191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17647550479586896639334921 13235662859690172479501191)
    ·
      refine ⟨19853494289535258719251787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13235662859690172479501191 19853494289535258719251787)
      ·
        refine ⟨29780241434302888078877681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19853494289535258719251787 29780241434302888078877681)
        ·
          refine ⟨22335181075727166059158261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29780241434302888078877681 22335181075727166059158261)
          ·
            refine ⟨2093923225849421818046087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22335181075727166059158261 2093923225849421818046087)
            ·
              refine ⟨3140884838774132727069131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093923225849421818046087 3140884838774132727069131)
              ·
                refine ⟨4711327258161199090603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140884838774132727069131 4711327258161199090603697)
                ·
                  refine ⟨3533495443620899317952773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711327258161199090603697 3533495443620899317952773)
                  ·
                    refine ⟨662530395678918622116145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533495443620899317952773 662530395678918622116145)
                    ·
                      rfl

theorem cell22_1935410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1935410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935410 prefixEnd_1935410 := by exact prefixLift 1935410
  have htrace : WordTrace (prefixWord ++ tailWord_1935410) baseStart_1935410 baseEnd_1935410 := by
    simpa [prefixWord, tailWord_1935410, baseEnd_1935410] using wordTrace_append hprefix tailTrace_1935410
  have hstable : (prefixWord ++ tailWord_1935410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935410).length < 2 ^ (prefixWord ++ tailWord_1935410).sum := by decide
  have hdescent : baseEnd_1935410 < baseStart_1935410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935446 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1935446 : Nat := 118140960795 + 1935446 * 2 ^ 59
def prefixEnd_1935446 : Nat := 4983230072969 + 3 ^ 40 * 1935446 * 2
def baseEnd_1935446 : Nat := 662542719214626528216035

theorem tailTrace_1935446 : CollatzResearch.WordTrace tailWord_1935446 prefixEnd_1935446 662542719214626528216035 := by
  unfold tailWord_1935446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411969684138572794103137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47061009964144776470433461 4411969684138572794103137)
  ·
    refine ⟨3308977263103929595577353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4411969684138572794103137 3308977263103929595577353)
    ·
      refine ⟨2481732947327947196683015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3308977263103929595577353 2481732947327947196683015)
      ·
        refine ⟨3722599420991920795024523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481732947327947196683015 3722599420991920795024523)
        ·
          refine ⟨5583899131487881192536785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722599420991920795024523 5583899131487881192536785)
          ·
            refine ⟨4187924348615910894402589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5583899131487881192536785 4187924348615910894402589)
            ·
              refine ⟨1570471630730966585400971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187924348615910894402589 1570471630730966585400971)
              ·
                refine ⟨2355707446096449878101457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570471630730966585400971 2355707446096449878101457)
                ·
                  refine ⟨1766780584572337408576093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355707446096449878101457 1766780584572337408576093)
                  ·
                    refine ⟨662542719214626528216035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766780584572337408576093 662542719214626528216035)
                    ·
                      rfl

theorem cell22_1935446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1935446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935446 prefixEnd_1935446 := by exact prefixLift 1935446
  have htrace : WordTrace (prefixWord ++ tailWord_1935446) baseStart_1935446 baseEnd_1935446 := by
    simpa [prefixWord, tailWord_1935446, baseEnd_1935446] using wordTrace_append hprefix tailTrace_1935446
  have hstable : (prefixWord ++ tailWord_1935446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935446).length < 2 ^ (prefixWord ++ tailWord_1935446).sum := by decide
  have hdescent : baseEnd_1935446 < baseStart_1935446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935474 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1935474 : Nat := 118140960795 + 1935474 * 2 ^ 59
def prefixEnd_1935474 : Nat := 4983230072969 + 3 ^ 40 * 1935474 * 2
def baseEnd_1935474 : Nat := 662552304186843788515949

theorem tailTrace_1935474 : CollatzResearch.WordTrace tailWord_1935474 prefixEnd_1935474 662552304186843788515949 := by
  unfold tailWord_1935474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648134047528931371917369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47061690793410483658446317 17648134047528931371917369)
  ·
    refine ⟨13236100535646698528938027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17648134047528931371917369 13236100535646698528938027)
    ·
      refine ⟨19854150803470047793407041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236100535646698528938027 19854150803470047793407041)
      ·
        refine ⟨14890613102602535845055281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19854150803470047793407041 14890613102602535845055281)
        ·
          refine ⟨11167959826951901883791461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14890613102602535845055281 11167959826951901883791461)
          ·
            refine ⟨2093992467553481603210899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11167959826951901883791461 2093992467553481603210899)
            ·
              refine ⟨3140988701330222404816349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093992467553481603210899 3140988701330222404816349)
              ·
                refine ⟨1177870762998833401806131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3140988701330222404816349 1177870762998833401806131)
                ·
                  refine ⟨1766806144498250102709197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177870762998833401806131 1766806144498250102709197)
                  ·
                    refine ⟨662552304186843788515949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766806144498250102709197 662552304186843788515949)
                    ·
                      rfl

theorem cell22_1935474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1935474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935474 prefixEnd_1935474 := by exact prefixLift 1935474
  have htrace : WordTrace (prefixWord ++ tailWord_1935474) baseStart_1935474 baseEnd_1935474 := by
    simpa [prefixWord, tailWord_1935474, baseEnd_1935474] using wordTrace_append hprefix tailTrace_1935474
  have hstable : (prefixWord ++ tailWord_1935474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935474).length < 2 ^ (prefixWord ++ tailWord_1935474).sum := by decide
  have hdescent : baseEnd_1935474 < baseStart_1935474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935517 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1935517 : Nat := 118140960795 + 1935517 * 2 ^ 59
def prefixEnd_1935517 : Nat := 4983230072969 + 3 ^ 40 * 1935517 * 2
def baseEnd_1935517 : Nat := 662567023965606009690817

theorem tailTrace_1935517 : CollatzResearch.WordTrace tailWord_1935517 prefixEnd_1935517 662567023965606009690817 := by
  unfold tailWord_1935517
  simp only [CollatzResearch.WordTrace]
  refine ⟨70594104528959943831484805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47062736352639962554323203 70594104528959943831484805)
  ·
    refine ⟨13236394599179989468403401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70594104528959943831484805 13236394599179989468403401)
    ·
      refine ⟨9927295949384992101302551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13236394599179989468403401 9927295949384992101302551)
      ·
        refine ⟨14890943924077488151953827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927295949384992101302551 14890943924077488151953827)
        ·
          refine ⟨22336415886116232227930741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890943924077488151953827 22336415886116232227930741)
          ·
            refine ⟨2094038989323396771368507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22336415886116232227930741 2094038989323396771368507)
            ·
              refine ⟨3141058483985095157052761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094038989323396771368507 3141058483985095157052761)
              ·
                refine ⟨2355793862988821367789571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141058483985095157052761 2355793862988821367789571)
                ·
                  refine ⟨3533690794483232051684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355793862988821367789571 3533690794483232051684357)
                  ·
                    refine ⟨662567023965606009690817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533690794483232051684357 662567023965606009690817)
                    ·
                      rfl

theorem cell22_1935517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1935517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935517 prefixEnd_1935517 := by exact prefixLift 1935517
  have htrace : WordTrace (prefixWord ++ tailWord_1935517) baseStart_1935517 baseEnd_1935517 := by
    simpa [prefixWord, tailWord_1935517, baseEnd_1935517] using wordTrace_append hprefix tailTrace_1935517
  have hstable : (prefixWord ++ tailWord_1935517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935517).length < 2 ^ (prefixWord ++ tailWord_1935517).sum := by decide
  have hdescent : baseEnd_1935517 < baseStart_1935517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935588 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_1935588 : Nat := 118140960795 + 1935588 * 2 ^ 59
def prefixEnd_1935588 : Nat := 4983230072969 + 3 ^ 40 * 1935588 * 2
def baseEnd_1935588 : Nat := 220863776238861830388533

theorem tailTrace_1935588 : CollatzResearch.WordTrace tailWord_1935588 prefixEnd_1935588 220863776238861830388533 := by
  unfold tailWord_1935588
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298347055851361478659709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47064462741135148638212945 35298347055851361478659709)
  ·
    refine ⟨13236880145944260554497391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35298347055851361478659709 13236880145944260554497391)
    ·
      refine ⟨19855320218916390831746087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236880145944260554497391 19855320218916390831746087)
      ·
        refine ⟨29782980328374586247619131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855320218916390831746087 29782980328374586247619131)
        ·
          refine ⟨44674470492561879371428697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782980328374586247619131 44674470492561879371428697)
          ·
            refine ⟨33505852869421409528571523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44674470492561879371428697 33505852869421409528571523)
            ·
              refine ⟨50258779304132114292857285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33505852869421409528571523 50258779304132114292857285)
              ·
                refine ⟨9423521119524771429910741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50258779304132114292857285 9423521119524771429910741)
                ·
                  refine ⟨220863776238861830388533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9423521119524771429910741 220863776238861830388533)
                  ·
                    rfl

theorem cell22_1935588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_1935588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935588 prefixEnd_1935588 := by exact prefixLift 1935588
  have htrace : WordTrace (prefixWord ++ tailWord_1935588) baseStart_1935588 baseEnd_1935588 := by
    simpa [prefixWord, tailWord_1935588, baseEnd_1935588] using wordTrace_append hprefix tailTrace_1935588
  have hstable : (prefixWord ++ tailWord_1935588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935588).length < 2 ^ (prefixWord ++ tailWord_1935588).sum := by decide
  have hdescent : baseEnd_1935588 < baseStart_1935588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935603 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_1935603 : Nat := 118140960795 + 1935603 * 2 ^ 59
def prefixEnd_1935603 : Nat := 4983230072969 + 3 ^ 40 * 1935603 * 2
def baseEnd_1935603 : Nat := 662596463523130452040553

theorem tailTrace_1935603 : CollatzResearch.WordTrace tailWord_1935603 prefixEnd_1935603 662596463523130452040553 := by
  unfold tailWord_1935603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70597241206648380519115463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47064827471098920346076975 70597241206648380519115463)
  ·
    refine ⟨105895861809972570778673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70597241206648380519115463 105895861809972570778673195)
    ·
      refine ⟨158843792714958856168009793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105895861809972570778673195 158843792714958856168009793)
      ·
        refine ⟨119132844536219142126007345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158843792714958856168009793 119132844536219142126007345)
        ·
          refine ⟨89349633402164356594505509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119132844536219142126007345 89349633402164356594505509)
          ·
            refine ⟨16753056262905816861469783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89349633402164356594505509 16753056262905816861469783)
            ·
              refine ⟨25129584394358725292204675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753056262905816861469783 25129584394358725292204675)
              ·
                refine ⟨37694376591538087938307013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25129584394358725292204675 37694376591538087938307013)
                ·
                  refine ⟨7067695610913391488432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37694376591538087938307013 7067695610913391488432565)
                  ·
                    refine ⟨662596463523130452040553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7067695610913391488432565 662596463523130452040553)
                    ·
                      rfl

theorem cell22_1935603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_1935603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935603 prefixEnd_1935603 := by exact prefixLift 1935603
  have htrace : WordTrace (prefixWord ++ tailWord_1935603) baseStart_1935603 baseEnd_1935603 := by
    simpa [prefixWord, tailWord_1935603, baseEnd_1935603] using wordTrace_append hprefix tailTrace_1935603
  have hstable : (prefixWord ++ tailWord_1935603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935603).length < 2 ^ (prefixWord ++ tailWord_1935603).sum := by decide
  have hdescent : baseEnd_1935603 < baseStart_1935603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935652 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1935652 : Nat := 118140960795 + 1935652 * 2 ^ 59
def prefixEnd_1935652 : Nat := 4983230072969 + 3 ^ 40 * 1935652 * 2
def baseEnd_1935652 : Nat := 662613237224510657565403

theorem tailTrace_1935652 : CollatzResearch.WordTrace tailWord_1935652 prefixEnd_1935652 662613237224510657565403 := by
  unfold tailWord_1935652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299514191735430943824605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47066018922313907925099473 35299514191735430943824605)
  ·
    refine ⟨13237317821900786603934227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35299514191735430943824605 13237317821900786603934227)
    ·
      refine ⟨19855976732851179905901341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237317821900786603934227 19855976732851179905901341)
      ·
        refine ⟨7445991274819192464713003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19855976732851179905901341 7445991274819192464713003)
        ·
          refine ⟨11168986912228788697069505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445991274819192464713003 11168986912228788697069505)
          ·
            refine ⟨8376740184171591522802129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11168986912228788697069505 8376740184171591522802129)
            ·
              refine ⟨6282555138128693642101597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376740184171591522802129 6282555138128693642101597)
              ·
                refine ⟨2355958176798260115788099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6282555138128693642101597 2355958176798260115788099)
                ·
                  refine ⟨3533937265197390173682149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355958176798260115788099 3533937265197390173682149)
                  ·
                    refine ⟨662613237224510657565403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533937265197390173682149 662613237224510657565403)
                    ·
                      rfl

theorem cell22_1935652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1935652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935652 prefixEnd_1935652 := by exact prefixLift 1935652
  have htrace : WordTrace (prefixWord ++ tailWord_1935652) baseStart_1935652 baseEnd_1935652 := by
    simpa [prefixWord, tailWord_1935652, baseEnd_1935652] using wordTrace_append hprefix tailTrace_1935652
  have hstable : (prefixWord ++ tailWord_1935652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935652).length < 2 ^ (prefixWord ++ tailWord_1935652).sum := by decide
  have hdescent : baseEnd_1935652 < baseStart_1935652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935697 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1935697 : Nat := 118140960795 + 1935697 * 2 ^ 59
def prefixEnd_1935697 : Nat := 4983230072969 + 3 ^ 40 * 1935697 * 2
def baseEnd_1935697 : Nat := 662628641644145540190265

theorem tailTrace_1935697 : CollatzResearch.WordTrace tailWord_1935697 prefixEnd_1935697 662628641644145540190265 := by
  unfold tailWord_1935697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70600669668307834573037345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47067113112205223048691563 70600669668307834573037345)
  ·
    refine ⟨52950502251230875929778009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70600669668307834573037345 52950502251230875929778009)
    ·
      refine ⟨39712876688423156947333507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52950502251230875929778009 39712876688423156947333507)
      ·
        refine ⟨59569315032634735421000261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39712876688423156947333507 59569315032634735421000261)
        ·
          refine ⟨11169246568619012891437549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59569315032634735421000261 11169246568619012891437549)
          ·
            refine ⟨4188467463232129834289081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11169246568619012891437549 4188467463232129834289081)
            ·
              refine ⟨3141350597424097375716811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188467463232129834289081 3141350597424097375716811)
              ·
                refine ⟨4712025896136146063575217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141350597424097375716811 4712025896136146063575217)
                ·
                  refine ⟨3534019422102109547681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712025896136146063575217 3534019422102109547681413)
                  ·
                    refine ⟨662628641644145540190265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534019422102109547681413 662628641644145540190265)
                    ·
                      rfl

theorem cell22_1935697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1935697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935697 prefixEnd_1935697 := by exact prefixLift 1935697
  have htrace : WordTrace (prefixWord ++ tailWord_1935697) baseStart_1935697 baseEnd_1935697 := by
    simpa [prefixWord, tailWord_1935697, baseEnd_1935697] using wordTrace_append hprefix tailTrace_1935697
  have hstable : (prefixWord ++ tailWord_1935697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935697).length < 2 ^ (prefixWord ++ tailWord_1935697).sum := by decide
  have hdescent : baseEnd_1935697 < baseStart_1935697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935725 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1935725 : Nat := 118140960795 + 1935725 * 2 ^ 59
def prefixEnd_1935725 : Nat := 4983230072969 + 3 ^ 40 * 1935725 * 2
def baseEnd_1935725 : Nat := 662638226616362800490179

theorem tailTrace_1935725 : CollatzResearch.WordTrace tailWord_1935725 prefixEnd_1935725 662638226616362800490179 := by
  unfold tailWord_1935725
  simp only [CollatzResearch.WordTrace]
  refine ⟨70601690912206395355056629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47067793941470930236704419 70601690912206395355056629)
  ·
    refine ⟨6618908523019349564536559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70601690912206395355056629 6618908523019349564536559)
    ·
      refine ⟨9928362784529024346804839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618908523019349564536559 9928362784529024346804839)
      ·
        refine ⟨14892544176793536520207259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928362784529024346804839 14892544176793536520207259)
        ·
          refine ⟨22338816265190304780310889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14892544176793536520207259 22338816265190304780310889)
          ·
            refine ⟨16754112198892728585233167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22338816265190304780310889 16754112198892728585233167)
            ·
              refine ⟨25131168298339092877849751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16754112198892728585233167 25131168298339092877849751)
              ·
                refine ⟨37696752447508639316774627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25131168298339092877849751 37696752447508639316774627)
                ·
                  refine ⟨56545128671262958975161941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37696752447508639316774627 56545128671262958975161941)
                  ·
                    refine ⟨662638226616362800490179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56545128671262958975161941 662638226616362800490179)
                    ·
                      rfl

theorem cell22_1935725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1935725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935725 prefixEnd_1935725 := by exact prefixLift 1935725
  have htrace : WordTrace (prefixWord ++ tailWord_1935725) baseStart_1935725 baseEnd_1935725 := by
    simpa [prefixWord, tailWord_1935725, baseEnd_1935725] using wordTrace_append hprefix tailTrace_1935725
  have hstable : (prefixWord ++ tailWord_1935725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935725).length < 2 ^ (prefixWord ++ tailWord_1935725).sum := by decide
  have hdescent : baseEnd_1935725 < baseStart_1935725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935746 : List Nat := [3, 4, 2, 1, 2, 1, 3, 6]
def baseStart_1935746 : Nat := 118140960795 + 1935746 * 2 ^ 59
def prefixEnd_1935746 : Nat := 4983230072969 + 3 ^ 40 * 1935746 * 2
def baseEnd_1935746 : Nat := 73627268371725082857235

theorem tailTrace_1935746 : CollatzResearch.WordTrace tailWord_1935746 prefixEnd_1935746 73627268371725082857235 := by
  unfold tailWord_1935746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17650614211282578985392773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47068304563420210627714061 17650614211282578985392773)
  ·
    refine ⟨3309490164615483559761145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17650614211282578985392773 3309490164615483559761145)
    ·
      refine ⟨2482117623461612669820859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3309490164615483559761145 2482117623461612669820859)
      ·
        refine ⟨3723176435192419004731289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482117623461612669820859 3723176435192419004731289)
        ·
          refine ⟨2792382326394314253548467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723176435192419004731289 2792382326394314253548467)
          ·
            refine ⟨4188573489591471380322701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792382326394314253548467 4188573489591471380322701)
            ·
              refine ⟨1570715058596801767621013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4188573489591471380322701 1570715058596801767621013)
              ·
                refine ⟨73627268371725082857235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1570715058596801767621013 73627268371725082857235)
                ·
                  rfl

theorem cell22_1935746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_1935746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935746 prefixEnd_1935746 := by exact prefixLift 1935746
  have htrace : WordTrace (prefixWord ++ tailWord_1935746) baseStart_1935746 baseEnd_1935746 := by
    simpa [prefixWord, tailWord_1935746, baseEnd_1935746] using wordTrace_append hprefix tailTrace_1935746
  have hstable : (prefixWord ++ tailWord_1935746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935746).length < 2 ^ (prefixWord ++ tailWord_1935746).sum := by decide
  have hdescent : baseEnd_1935746 < baseStart_1935746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935774 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1935774 : Nat := 118140960795 + 1935774 * 2 ^ 59
def prefixEnd_1935774 : Nat := 4983230072969 + 3 ^ 40 * 1935774 * 2
def baseEnd_1935774 : Nat := 220885000105914335338343

theorem tailTrace_1935774 : CollatzResearch.WordTrace tailWord_1935774 prefixEnd_1935774 220885000105914335338343 := by
  unfold tailWord_1935774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825434761128609590448797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47068985392685917815726917 8825434761128609590448797)
  ·
    refine ⟨3309538035423228596418299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8825434761128609590448797 3309538035423228596418299)
    ·
      refine ⟨4964307053134842894627449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309538035423228596418299 4964307053134842894627449)
      ·
        refine ⟨3723230289851132170970587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4964307053134842894627449 3723230289851132170970587)
        ·
          refine ⟨5584845434776698256455881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723230289851132170970587 5584845434776698256455881)
          ·
            refine ⟨4188634076082523692341911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584845434776698256455881 4188634076082523692341911)
            ·
              refine ⟨6282951114123785538512867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188634076082523692341911 6282951114123785538512867)
              ·
                refine ⟨9424426671185678307769301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282951114123785538512867 9424426671185678307769301)
                ·
                  refine ⟨220885000105914335338343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9424426671185678307769301 220885000105914335338343)
                  ·
                    rfl

theorem cell22_1935774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1935774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935774 prefixEnd_1935774 := by exact prefixLift 1935774
  have htrace : WordTrace (prefixWord ++ tailWord_1935774) baseStart_1935774 baseEnd_1935774 := by
    simpa [prefixWord, tailWord_1935774, baseEnd_1935774] using wordTrace_append hprefix tailTrace_1935774
  have hstable : (prefixWord ++ tailWord_1935774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935774).length < 2 ^ (prefixWord ++ tailWord_1935774).sum := by decide
  have hdescent : baseEnd_1935774 < baseStart_1935774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935804 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1935804 : Nat := 118140960795 + 1935804 * 2 ^ 59
def prefixEnd_1935804 : Nat := 4983230072969 + 3 ^ 40 * 1935804 * 2
def baseEnd_1935804 : Nat := 662665269930832927764937

theorem tailTrace_1935804 : CollatzResearch.WordTrace tailWord_1935804 prefixEnd_1935804 662665269930832927764937 := by
  unfold tailWord_1935804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35302286139460095923591233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47069714852613461231454977 35302286139460095923591233)
  ·
    refine ⟨26476714604595071942693425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35302286139460095923591233 26476714604595071942693425)
    ·
      refine ⟨19857535953446303957020069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26476714604595071942693425 19857535953446303957020069)
      ·
        refine ⟨3723287991271181991941263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19857535953446303957020069 3723287991271181991941263)
        ·
          refine ⟨5584931986906772987911895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723287991271181991941263 5584931986906772987911895)
          ·
            refine ⟨8377397980360159481867843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584931986906772987911895 8377397980360159481867843)
            ·
              refine ⟨12566096970540239222801765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377397980360159481867843 12566096970540239222801765)
              ·
                refine ⟨2356143181976294854275331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12566096970540239222801765 2356143181976294854275331)
                ·
                  refine ⟨3534214772964442281412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356143181976294854275331 3534214772964442281412997)
                  ·
                    refine ⟨662665269930832927764937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534214772964442281412997 662665269930832927764937)
                    ·
                      rfl

theorem cell22_1935804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1935804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935804 prefixEnd_1935804 := by exact prefixLift 1935804
  have htrace : WordTrace (prefixWord ++ tailWord_1935804) baseStart_1935804 baseEnd_1935804 := by
    simpa [prefixWord, tailWord_1935804, baseEnd_1935804] using wordTrace_append hprefix tailTrace_1935804
  have hstable : (prefixWord ++ tailWord_1935804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935804).length < 2 ^ (prefixWord ++ tailWord_1935804).sum := by decide
  have hdescent : baseEnd_1935804 < baseStart_1935804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935817 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1935817 : Nat := 118140960795 + 1935817 * 2 ^ 59
def prefixEnd_1935817 : Nat := 4983230072969 + 3 ^ 40 * 1935817 * 2
def baseEnd_1935817 : Nat := 662669720096505227189897

theorem tailTrace_1935817 : CollatzResearch.WordTrace tailWord_1935817 prefixEnd_1935817 662669720096505227189897 := by
  unfold tailWord_1935817
  simp only [CollatzResearch.WordTrace]
  refine ⟨70605046427873095067405705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47070030951915396711603803 70605046427873095067405705)
  ·
    refine ⟨52953784820904821300554279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70605046427873095067405705 52953784820904821300554279)
    ·
      refine ⟨79430677231357231950831419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52953784820904821300554279 79430677231357231950831419)
      ·
        refine ⟨119146015847035847926247129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79430677231357231950831419 119146015847035847926247129)
        ·
          refine ⟨89359511885276885944685347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119146015847035847926247129 89359511885276885944685347)
          ·
            refine ⟨134039267827915328917028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89359511885276885944685347 134039267827915328917028021)
            ·
              refine ⟨12566181358867062085971377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134039267827915328917028021 12566181358867062085971377)
              ·
                refine ⟨9424636019150296564478533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12566181358867062085971377 9424636019150296564478533)
                ·
                  refine ⟨1767119253590680605839725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9424636019150296564478533 1767119253590680605839725)
                  ·
                    refine ⟨662669720096505227189897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767119253590680605839725 662669720096505227189897)
                    ·
                      rfl

theorem cell22_1935817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1935817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935817 prefixEnd_1935817 := by exact prefixLift 1935817
  have htrace : WordTrace (prefixWord ++ tailWord_1935817) baseStart_1935817 baseEnd_1935817 := by
    simpa [prefixWord, tailWord_1935817, baseEnd_1935817] using wordTrace_append hprefix tailTrace_1935817
  have hstable : (prefixWord ++ tailWord_1935817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935817).length < 2 ^ (prefixWord ++ tailWord_1935817).sum := by decide
  have hdescent : baseEnd_1935817 < baseStart_1935817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935834 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1935834 : Nat := 118140960795 + 1935834 * 2 ^ 59
def prefixEnd_1935834 : Nat := 4983230072969 + 3 ^ 40 * 1935834 * 2
def baseEnd_1935834 : Nat := 662675539543922849514845

theorem tailTrace_1935834 : CollatzResearch.WordTrace tailWord_1935834 prefixEnd_1935834 662675539543922849514845 := by
  unfold tailWord_1935834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651416617202876742693639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47070444312541004647183037 17651416617202876742693639)
  ·
    refine ⟨26477124925804315114040459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17651416617202876742693639 26477124925804315114040459)
    ·
      refine ⟨39715687388706472671060689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26477124925804315114040459 39715687388706472671060689)
      ·
        refine ⟨29786765541529854503295517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39715687388706472671060689 29786765541529854503295517)
        ·
          refine ⟨11170037078073695438735819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29786765541529854503295517 11170037078073695438735819)
          ·
            refine ⟨16755055617110543158103729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170037078073695438735819 16755055617110543158103729)
            ·
              refine ⟨12566291712832907368577797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16755055617110543158103729 12566291712832907368577797)
              ·
                refine ⟨2356179696156170131608337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12566291712832907368577797 2356179696156170131608337)
                ·
                  refine ⟨1767134772117127598706253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356179696156170131608337 1767134772117127598706253)
                  ·
                    refine ⟨662675539543922849514845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767134772117127598706253 662675539543922849514845)
                    ·
                      rfl

theorem cell22_1935834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1935834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935834 prefixEnd_1935834 := by exact prefixLift 1935834
  have htrace : WordTrace (prefixWord ++ tailWord_1935834) baseStart_1935834 baseEnd_1935834 := by
    simpa [prefixWord, tailWord_1935834, baseEnd_1935834] using wordTrace_append hprefix tailTrace_1935834
  have hstable : (prefixWord ++ tailWord_1935834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935834).length < 2 ^ (prefixWord ++ tailWord_1935834).sum := by decide
  have hdescent : baseEnd_1935834 < baseStart_1935834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935847 : List Nat := [1, 1, 5, 2, 1, 1, 4, 7]
def baseStart_1935847 : Nat := 118140960795 + 1935847 * 2 ^ 59
def prefixEnd_1935847 : Nat := 4983230072969 + 3 ^ 40 * 1935847 * 2
def baseEnd_1935847 : Nat := 73631109967732794326645

theorem tailTrace_1935847 : CollatzResearch.WordTrace tailWord_1935847 prefixEnd_1935847 73631109967732794326645 := by
  unfold tailWord_1935847
  simp only [CollatzResearch.WordTrace]
  refine ⟨70606140617764410190997795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47070760411842940127331863 70606140617764410190997795)
  ·
    refine ⟨105909210926646615286496693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70606140617764410190997795 105909210926646615286496693)
    ·
      refine ⟨9928988524373120183109065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105909210926646615286496693 9928988524373120183109065)
      ·
        refine ⟨7446741393279840137331799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9928988524373120183109065 7446741393279840137331799)
        ·
          refine ⟨11170112089919760205997699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446741393279840137331799 11170112089919760205997699)
          ·
            refine ⟨16755168134879640308996549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170112089919760205997699 16755168134879640308996549)
            ·
              refine ⟨3141594025289932557936853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16755168134879640308996549 3141594025289932557936853)
              ·
                refine ⟨73631109967732794326645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3141594025289932557936853 73631109967732794326645)
                ·
                  rfl

theorem cell22_1935847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 7].length) (baseStart_1935847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935847 prefixEnd_1935847 := by exact prefixLift 1935847
  have htrace : WordTrace (prefixWord ++ tailWord_1935847) baseStart_1935847 baseEnd_1935847 := by
    simpa [prefixWord, tailWord_1935847, baseEnd_1935847] using wordTrace_append hprefix tailTrace_1935847
  have hstable : (prefixWord ++ tailWord_1935847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935847).length < 2 ^ (prefixWord ++ tailWord_1935847).sum := by decide
  have hdescent : baseEnd_1935847 < baseStart_1935847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935885 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1935885 : Nat := 118140960795 + 1935885 * 2 ^ 59
def prefixEnd_1935885 : Nat := 4983230072969 + 3 ^ 40 * 1935885 * 2
def baseEnd_1935885 : Nat := 662692997886175716489689

theorem tailTrace_1935885 : CollatzResearch.WordTrace tailWord_1935885 prefixEnd_1935885 662692997886175716489689 := by
  unfold tailWord_1935885
  simp only [CollatzResearch.WordTrace]
  refine ⟨70607526591626742680881109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47071684394417828453920739 70607526591626742680881109)
  ·
    refine ⟨1654863904491251781583151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70607526591626742680881109 1654863904491251781583151)
    ·
      refine ⟨2482295856736877672374727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654863904491251781583151 2482295856736877672374727)
      ·
        refine ⟨3723443785105316508562091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482295856736877672374727 3723443785105316508562091)
        ·
          refine ⟨5585165677657974762843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723443785105316508562091 5585165677657974762843137)
          ·
            refine ⟨4188874258243481072132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5585165677657974762843137 4188874258243481072132353)
            ·
              refine ⟨3141655693682610804099265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188874258243481072132353 3141655693682610804099265)
              ·
                refine ⟨2356241770261958103074449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141655693682610804099265 2356241770261958103074449)
                ·
                  refine ⟨1767181327696468577305837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356241770261958103074449 1767181327696468577305837)
                  ·
                    refine ⟨662692997886175716489689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767181327696468577305837 662692997886175716489689)
                    ·
                      rfl

theorem cell22_1935885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1935885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935885 prefixEnd_1935885 := by exact prefixLift 1935885
  have htrace : WordTrace (prefixWord ++ tailWord_1935885) baseStart_1935885 baseEnd_1935885 := by
    simpa [prefixWord, tailWord_1935885, baseEnd_1935885] using wordTrace_append hprefix tailTrace_1935885
  have hstable : (prefixWord ++ tailWord_1935885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935885).length < 2 ^ (prefixWord ++ tailWord_1935885).sum := by decide
  have hdescent : baseEnd_1935885 < baseStart_1935885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935907 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_1935907 : Nat := 118140960795 + 1935907 * 2 ^ 59
def prefixEnd_1935907 : Nat := 4983230072969 + 3 ^ 40 * 1935907 * 2
def baseEnd_1935907 : Nat := 662700528935774992439621

theorem tailTrace_1935907 : CollatzResearch.WordTrace tailWord_1935907 prefixEnd_1935907 662700528935774992439621 := by
  unfold tailWord_1935907
  simp only [CollatzResearch.WordTrace]
  refine ⟨70608328997547040438181975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47072219331698026958787983 70608328997547040438181975)
  ·
    refine ⟨105912493496320560657272963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70608328997547040438181975 105912493496320560657272963)
    ·
      refine ⟨158868740244480840985909445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105912493496320560657272963 158868740244480840985909445)
      ·
        refine ⟨29787888795840157684858021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158868740244480840985909445 29787888795840157684858021)
        ·
          refine ⟨5585229149220029565910879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29787888795840157684858021 5585229149220029565910879)
          ·
            refine ⟨8377843723830044348866319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585229149220029565910879 8377843723830044348866319)
            ·
              refine ⟨12566765585745066523299479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377843723830044348866319 12566765585745066523299479)
              ·
                refine ⟨18850148378617599784949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12566765585745066523299479 18850148378617599784949219)
                ·
                  refine ⟨28275222567926399677423829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18850148378617599784949219 28275222567926399677423829)
                  ·
                    refine ⟨662700528935774992439621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28275222567926399677423829 662700528935774992439621)
                    ·
                      rfl

theorem cell22_1935907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_1935907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935907 prefixEnd_1935907 := by exact prefixLift 1935907
  have htrace : WordTrace (prefixWord ++ tailWord_1935907) baseStart_1935907 baseEnd_1935907 := by
    simpa [prefixWord, tailWord_1935907, baseEnd_1935907] using wordTrace_append hprefix tailTrace_1935907
  have hstable : (prefixWord ++ tailWord_1935907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935907).length < 2 ^ (prefixWord ++ tailWord_1935907).sum := by decide
  have hdescent : baseEnd_1935907 < baseStart_1935907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935917 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1935917 : Nat := 118140960795 + 1935917 * 2 ^ 59
def prefixEnd_1935917 : Nat := 4983230072969 + 3 ^ 40 * 1935917 * 2
def baseEnd_1935917 : Nat := 662703952140138299689591

theorem tailTrace_1935917 : CollatzResearch.WordTrace tailWord_1935917 prefixEnd_1935917 662703952140138299689591 := by
  unfold tailWord_1935917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70608693727510812146046005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47072462485007208097364003 70608693727510812146046005)
  ·
    refine ⟨6619565036954138638691813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70608693727510812146046005 6619565036954138638691813)
    ·
      refine ⟨1241168444428900994754715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6619565036954138638691813 1241168444428900994754715)
      ·
        refine ⟨1861752666643351492132073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241168444428900994754715 1861752666643351492132073)
        ·
          refine ⟨1396314499982513619099055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861752666643351492132073 1396314499982513619099055)
          ·
            refine ⟨2094471749973770428648583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396314499982513619099055 2094471749973770428648583)
            ·
              refine ⟨3141707624960655642972875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094471749973770428648583 3141707624960655642972875)
              ·
                refine ⟨4712561437440983464459313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141707624960655642972875 4712561437440983464459313)
                ·
                  refine ⟨3534421078080737598344485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712561437440983464459313 3534421078080737598344485)
                  ·
                    refine ⟨662703952140138299689591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534421078080737598344485 662703952140138299689591)
                    ·
                      rfl

theorem cell22_1935917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1935917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935917 prefixEnd_1935917 := by exact prefixLift 1935917
  have htrace : WordTrace (prefixWord ++ tailWord_1935917) baseStart_1935917 baseEnd_1935917 := by
    simpa [prefixWord, tailWord_1935917, baseEnd_1935917] using wordTrace_append hprefix tailTrace_1935917
  have hstable : (prefixWord ++ tailWord_1935917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935917).length < 2 ^ (prefixWord ++ tailWord_1935917).sum := by decide
  have hdescent : baseEnd_1935917 < baseStart_1935917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935954 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1935954 : Nat := 118140960795 + 1935954 * 2 ^ 59
def prefixEnd_1935954 : Nat := 4983230072969 + 3 ^ 40 * 1935954 * 2
def baseEnd_1935954 : Nat := 220905539332094178838159

theorem tailTrace_1935954 : CollatzResearch.WordTrace tailWord_1935954 prefixEnd_1935954 220905539332094178838159 := by
  unfold tailWord_1935954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652510807094191866285729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47073362152251178310095277 17652510807094191866285729)
  ·
    refine ⟨13239383105320643899714297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17652510807094191866285729 13239383105320643899714297)
    ·
      refine ⟨9929537328990482924785723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13239383105320643899714297 9929537328990482924785723)
      ·
        refine ⟨14894305993485724387178585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9929537328990482924785723 14894305993485724387178585)
        ·
          refine ⟨11170729495114293290383939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14894305993485724387178585 11170729495114293290383939)
          ·
            refine ⟨16756094242671439935575909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170729495114293290383939 16756094242671439935575909)
            ·
              refine ⟨3141767670500894987920483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16756094242671439935575909 3141767670500894987920483)
              ·
                refine ⟨4712651505751342481880725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141767670500894987920483 4712651505751342481880725)
                ·
                  refine ⟨220905539332094178838159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4712651505751342481880725 220905539332094178838159)
                  ·
                    rfl

theorem cell22_1935954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1935954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935954 prefixEnd_1935954 := by exact prefixLift 1935954
  have htrace : WordTrace (prefixWord ++ tailWord_1935954) baseStart_1935954 baseEnd_1935954 := by
    simpa [prefixWord, tailWord_1935954, baseEnd_1935954] using wordTrace_append hprefix tailTrace_1935954
  have hstable : (prefixWord ++ tailWord_1935954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935954).length < 2 ^ (prefixWord ++ tailWord_1935954).sum := by decide
  have hdescent : baseEnd_1935954 < baseStart_1935954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935969 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1935969 : Nat := 118140960795 + 1935969 * 2 ^ 59
def prefixEnd_1935969 : Nat := 4983230072969 + 3 ^ 40 * 1935969 * 2
def baseEnd_1935969 : Nat := 662721752802827497389431

theorem tailTrace_1935969 : CollatzResearch.WordTrace tailWord_1935969 prefixEnd_1935969 662721752802827497389431 := by
  unfold tailWord_1935969
  simp only [CollatzResearch.WordTrace]
  refine ⟨70610590323322425026938961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47073726882214950017959307 70610590323322425026938961)
  ·
    refine ⟨52957942742491818770204221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70610590323322425026938961 52957942742491818770204221)
    ·
      refine ⟨19859228528434432038826583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52957942742491818770204221 19859228528434432038826583)
      ·
        refine ⟨29788842792651648058239875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19859228528434432038826583 29788842792651648058239875)
        ·
          refine ⟨44683264188977472087359813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29788842792651648058239875 44683264188977472087359813)
          ·
            refine ⟨8378112035433276016379965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44683264188977472087359813 8378112035433276016379965)
            ·
              refine ⟨3141792013287478506142487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8378112035433276016379965 3141792013287478506142487)
              ·
                refine ⟨4712688019931217759213731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141792013287478506142487 4712688019931217759213731)
                ·
                  refine ⟨7069032029896826638820597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712688019931217759213731 7069032029896826638820597)
                  ·
                    refine ⟨662721752802827497389431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7069032029896826638820597 662721752802827497389431)
                    ·
                      rfl

theorem cell22_1935969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1935969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1935969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1935969 prefixEnd_1935969 := by exact prefixLift 1935969
  have htrace : WordTrace (prefixWord ++ tailWord_1935969) baseStart_1935969 baseEnd_1935969 := by
    simpa [prefixWord, tailWord_1935969, baseEnd_1935969] using wordTrace_append hprefix tailTrace_1935969
  have hstable : (prefixWord ++ tailWord_1935969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935969).length < 2 ^ (prefixWord ++ tailWord_1935969).sum := by decide
  have hdescent : baseEnd_1935969 < baseStart_1935969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936020 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1936020 : Nat := 118140960795 + 1936020 * 2 ^ 59
def prefixEnd_1936020 : Nat := 4983230072969 + 3 ^ 40 * 1936020 * 2
def baseEnd_1936020 : Nat := 662739211145080364364275

theorem tailTrace_1936020 : CollatzResearch.WordTrace tailWord_1936020 prefixEnd_1936020 662739211145080364364275 := by
  unfold tailWord_1936020
  simp only [CollatzResearch.WordTrace]
  refine ⟨35306225223068830368522757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47074966964091773824697009 35306225223068830368522757)
  ·
    refine ⟨6619917229325405694098017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35306225223068830368522757 6619917229325405694098017)
    ·
      refine ⟨4964937921994054270573513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6619917229325405694098017 4964937921994054270573513)
      ·
        refine ⟨3723703441495540702930135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4964937921994054270573513 3723703441495540702930135)
        ·
          refine ⟨5585555162243311054395203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723703441495540702930135 5585555162243311054395203)
          ·
            refine ⟨8378332743364966581592805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585555162243311054395203 8378332743364966581592805)
            ·
              refine ⟨1570937389380931234048651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8378332743364966581592805 1570937389380931234048651)
              ·
                refine ⟨2356406084071396851072977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570937389380931234048651 2356406084071396851072977)
                ·
                  refine ⟨1767304563053547638304733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356406084071396851072977 1767304563053547638304733)
                  ·
                    refine ⟨662739211145080364364275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767304563053547638304733 662739211145080364364275)
                    ·
                      rfl

theorem cell22_1936020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1936020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936020 prefixEnd_1936020 := by exact prefixLift 1936020
  have htrace : WordTrace (prefixWord ++ tailWord_1936020) baseStart_1936020 baseEnd_1936020 := by
    simpa [prefixWord, tailWord_1936020, baseEnd_1936020] using wordTrace_append hprefix tailTrace_1936020
  have hstable : (prefixWord ++ tailWord_1936020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936020).length < 2 ^ (prefixWord ++ tailWord_1936020).sum := by decide
  have hdescent : baseEnd_1936020 < baseStart_1936020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936061 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 5]
def baseStart_1936061 : Nat := 118140960795 + 1936061 * 2 ^ 59
def prefixEnd_1936061 : Nat := 4983230072969 + 3 ^ 40 * 1936061 * 2
def baseEnd_1936061 : Nat := 220917748760989974696383

theorem tailTrace_1936061 : CollatzResearch.WordTrace tailWord_1936061 prefixEnd_1936061 220917748760989974696383 := by
  unfold tailWord_1936061
  simp only [CollatzResearch.WordTrace]
  refine ⟨70613945838989124739288037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47075963892659416492858691 70613945838989124739288037)
  ·
    refine ⟨13240114844810460888616507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70613945838989124739288037 13240114844810460888616507)
    ·
      refine ⟨19860172267215691332924761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240114844810460888616507 19860172267215691332924761)
      ·
        refine ⟨14895129200411768499693571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19860172267215691332924761 14895129200411768499693571)
        ·
          refine ⟨22342693800617652749540357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14895129200411768499693571 22342693800617652749540357)
          ·
            refine ⟨4189255087615809890538817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22342693800617652749540357 4189255087615809890538817)
            ·
              refine ⟨3141941315711857417904113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189255087615809890538817 3141941315711857417904113)
              ·
                refine ⟨2356455986783893063428085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141941315711857417904113 2356455986783893063428085)
                ·
                  refine ⟨220917748760989974696383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2356455986783893063428085 220917748760989974696383)
                  ·
                    rfl

theorem cell22_1936061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_1936061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936061 prefixEnd_1936061 := by exact prefixLift 1936061
  have htrace : WordTrace (prefixWord ++ tailWord_1936061) baseStart_1936061 baseEnd_1936061 := by
    simpa [prefixWord, tailWord_1936061, baseEnd_1936061] using wordTrace_append hprefix tailTrace_1936061
  have hstable : (prefixWord ++ tailWord_1936061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936061).length < 2 ^ (prefixWord ++ tailWord_1936061).sum := by decide
  have hdescent : baseEnd_1936061 < baseStart_1936061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936076 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_1936076 : Nat := 118140960795 + 1936076 * 2 ^ 59
def prefixEnd_1936076 : Nat := 4983230072969 + 3 ^ 40 * 1936076 * 2
def baseEnd_1936076 : Nat := 662758381089514884964103

theorem tailTrace_1936076 : CollatzResearch.WordTrace tailWord_1936076 prefixEnd_1936076 662758381089514884964103 := by
  unfold tailWord_1936076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35307246466967391150542041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47076328622623188200722721 35307246466967391150542041)
  ·
    refine ⟨26480434850225543362906531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35307246466967391150542041 26480434850225543362906531)
    ·
      refine ⟨39720652275338315044359797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26480434850225543362906531 39720652275338315044359797)
      ·
        refine ⟨3723811150812967035408731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39720652275338315044359797 3723811150812967035408731)
        ·
          refine ⟨5585716726219450553113097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723811150812967035408731 5585716726219450553113097)
          ·
            refine ⟨4189287544664587914834823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5585716726219450553113097 4189287544664587914834823)
            ·
              refine ⟨6283931316996881872252235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189287544664587914834823 6283931316996881872252235)
              ·
                refine ⟨9425896975495322808378353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283931316996881872252235 9425896975495322808378353)
                ·
                  refine ⟨7069422731621492106283765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425896975495322808378353 7069422731621492106283765)
                  ·
                    refine ⟨662758381089514884964103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7069422731621492106283765 662758381089514884964103)
                    ·
                      rfl

theorem cell22_1936076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_1936076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936076 prefixEnd_1936076 := by exact prefixLift 1936076
  have htrace : WordTrace (prefixWord ++ tailWord_1936076) baseStart_1936076 baseEnd_1936076 := by
    simpa [prefixWord, tailWord_1936076, baseEnd_1936076] using wordTrace_append hprefix tailTrace_1936076
  have hstable : (prefixWord ++ tailWord_1936076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936076).length < 2 ^ (prefixWord ++ tailWord_1936076).sum := by decide
  have hdescent : baseEnd_1936076 < baseStart_1936076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936089 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 6]
def baseStart_1936089 : Nat := 118140960795 + 1936089 * 2 ^ 59
def prefixEnd_1936089 : Nat := 4983230072969 + 3 ^ 40 * 1936089 * 2
def baseEnd_1936089 : Nat := 220920943751729061463021

theorem tailTrace_1936089 : CollatzResearch.WordTrace tailWord_1936089 prefixEnd_1936089 220920943751729061463021 := by
  unfold tailWord_1936089
  simp only [CollatzResearch.WordTrace]
  refine ⟨70614967082887685521307321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47076644721925123680871547 70614967082887685521307321)
  ·
    refine ⟨52961225312165764140980491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70614967082887685521307321 52961225312165764140980491)
    ·
      refine ⟨79441837968248646211470737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52961225312165764140980491 79441837968248646211470737)
      ·
        refine ⟨59581378476186484658603053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79441837968248646211470737 59581378476186484658603053)
        ·
          refine ⟨22343016928569931746976145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59581378476186484658603053 22343016928569931746976145)
          ·
            refine ⟨16757262696427448810232109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22343016928569931746976145 16757262696427448810232109)
            ·
              refine ⟨6283973511160293303837041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16757262696427448810232109 6283973511160293303837041)
              ·
                refine ⟨4712980133370219977877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283973511160293303837041 4712980133370219977877781)
                ·
                  refine ⟨220920943751729061463021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4712980133370219977877781 220920943751729061463021)
                  ·
                    rfl

theorem cell22_1936089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_1936089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936089 prefixEnd_1936089 := by exact prefixLift 1936089
  have htrace : WordTrace (prefixWord ++ tailWord_1936089) baseStart_1936089 baseEnd_1936089 := by
    simpa [prefixWord, tailWord_1936089, baseEnd_1936089] using wordTrace_append hprefix tailTrace_1936089
  have hstable : (prefixWord ++ tailWord_1936089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936089).length < 2 ^ (prefixWord ++ tailWord_1936089).sum := by decide
  have hdescent : baseEnd_1936089 < baseStart_1936089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936119 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1936119 : Nat := 118140960795 + 1936119 * 2 ^ 59
def prefixEnd_1936119 : Nat := 4983230072969 + 3 ^ 40 * 1936119 * 2
def baseEnd_1936119 : Nat := 662773100868277106138971

theorem tailTrace_1936119 : CollatzResearch.WordTrace tailWord_1936119 prefixEnd_1936119 662773100868277106138971 := by
  unfold tailWord_1936119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70616061272779000644899411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47077374181852667096599607 70616061272779000644899411)
  ·
    refine ⟨105924091909168500967349117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70616061272779000644899411 105924091909168500967349117)
    ·
      refine ⟨39721534465938187862755919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105924091909168500967349117 39721534465938187862755919)
      ·
        refine ⟨59582301698907281794133879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39721534465938187862755919 59582301698907281794133879)
        ·
          refine ⟨89373452548360922691200819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59582301698907281794133879 89373452548360922691200819)
          ·
            refine ⟨134060178822541384036801229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89373452548360922691200819 134060178822541384036801229)
            ·
              refine ⟨50272567058453019013800461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134060178822541384036801229 50272567058453019013800461)
              ·
                refine ⟨18852212646919882130175173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50272567058453019013800461 18852212646919882130175173)
                ·
                  refine ⟨3534789871297477899407845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18852212646919882130175173 3534789871297477899407845)
                  ·
                    refine ⟨662773100868277106138971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534789871297477899407845 662773100868277106138971)
                    ·
                      rfl

theorem cell22_1936119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1936119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936119 prefixEnd_1936119 := by exact prefixLift 1936119
  have htrace : WordTrace (prefixWord ++ tailWord_1936119) baseStart_1936119 baseEnd_1936119 := by
    simpa [prefixWord, tailWord_1936119, baseEnd_1936119] using wordTrace_append hprefix tailTrace_1936119
  have hstable : (prefixWord ++ tailWord_1936119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936119).length < 2 ^ (prefixWord ++ tailWord_1936119).sum := by decide
  have hdescent : baseEnd_1936119 < baseStart_1936119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936149 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1936149 : Nat := 118140960795 + 1936149 * 2 ^ 59
def prefixEnd_1936149 : Nat := 4983230072969 + 3 ^ 40 * 1936149 * 2
def baseEnd_1936149 : Nat := 662783370481367027888879

theorem tailTrace_1936149 : CollatzResearch.WordTrace tailWord_1936149 prefixEnd_1936149 662783370481367027888879 := by
  unfold tailWord_1936149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617155462670315768491501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47078103641780210512327667 70617155462670315768491501)
  ·
    refine ⟨26481433298501368413184313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70617155462670315768491501 26481433298501368413184313)
    ·
      refine ⟨19861074973876026309888235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26481433298501368413184313 19861074973876026309888235)
      ·
        refine ⟨29791612460814039464832353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19861074973876026309888235 29791612460814039464832353)
        ·
          refine ⟨22343709345610529598624265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29791612460814039464832353 22343709345610529598624265)
          ·
            refine ⟨16757782009207897198968199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22343709345610529598624265 16757782009207897198968199)
            ·
              refine ⟨25136673013811845798452299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757782009207897198968199 25136673013811845798452299)
              ·
                refine ⟨37705009520717768697678449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25136673013811845798452299 37705009520717768697678449)
                ·
                  refine ⟨28278757140538326523258837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37705009520717768697678449 28278757140538326523258837)
                  ·
                    refine ⟨662783370481367027888879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28278757140538326523258837 662783370481367027888879)
                    ·
                      rfl

theorem cell22_1936149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1936149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936149 prefixEnd_1936149 := by exact prefixLift 1936149
  have htrace : WordTrace (prefixWord ++ tailWord_1936149) baseStart_1936149 baseEnd_1936149 := by
    simpa [prefixWord, tailWord_1936149, baseEnd_1936149] using wordTrace_append hprefix tailTrace_1936149
  have hstable : (prefixWord ++ tailWord_1936149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936149).length < 2 ^ (prefixWord ++ tailWord_1936149).sum := by decide
  have hdescent : baseEnd_1936149 < baseStart_1936149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936151 : List Nat := [1, 1, 3, 4, 3, 1, 1, 8]
def baseStart_1936151 : Nat := 118140960795 + 1936151 * 2 ^ 59
def prefixEnd_1936151 : Nat := 4983230072969 + 3 ^ 40 * 1936151 * 2
def baseEnd_1936151 : Nat := 73642672791359965482097

theorem tailTrace_1936151 : CollatzResearch.WordTrace tailWord_1936151 prefixEnd_1936151 73642672791359965482097 := by
  unfold tailWord_1936151
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617228408663070110064307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47078152272442046740042871 70617228408663070110064307)
  ·
    refine ⟨105925842612994605165096461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70617228408663070110064307 105925842612994605165096461)
    ·
      refine ⟨39722190979872976936911173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105925842612994605165096461 39722190979872976936911173)
      ·
        refine ⟨7447910808726183175670845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39722190979872976936911173 7447910808726183175670845)
        ·
          refine ⟨2792966553272318690876567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7447910808726183175670845 2792966553272318690876567)
          ·
            refine ⟨4189449829908478036314851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792966553272318690876567 4189449829908478036314851)
            ·
              refine ⟨6284174744862717054472277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189449829908478036314851 6284174744862717054472277)
              ·
                refine ⟨73642672791359965482097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6284174744862717054472277 73642672791359965482097)
                ·
                  rfl

theorem cell22_1936151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 8].length) (baseStart_1936151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936151 prefixEnd_1936151 := by exact prefixLift 1936151
  have htrace : WordTrace (prefixWord ++ tailWord_1936151) baseStart_1936151 baseEnd_1936151 := by
    simpa [prefixWord, tailWord_1936151, baseEnd_1936151] using wordTrace_append hprefix tailTrace_1936151
  have hstable : (prefixWord ++ tailWord_1936151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936151).length < 2 ^ (prefixWord ++ tailWord_1936151).sum := by decide
  have hdescent : baseEnd_1936151 < baseStart_1936151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936157 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 4]
def baseStart_1936157 : Nat := 118140960795 + 1936157 * 2 ^ 59
def prefixEnd_1936157 : Nat := 4983230072969 + 3 ^ 40 * 1936157 * 2
def baseEnd_1936157 : Nat := 220928703014952557896285

theorem tailTrace_1936157 : CollatzResearch.WordTrace tailWord_1936157 prefixEnd_1936157 220928703014952557896285 := by
  unfold tailWord_1936157
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617447246641333134782725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47078298164427555423188483 70617447246641333134782725)
  ·
    refine ⟨13240771358745249962771761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70617447246641333134782725 13240771358745249962771761)
    ·
      refine ⟨9930578519058937472078821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13240771358745249962771761 9930578519058937472078821)
      ·
        refine ⟨1861983472323550776014779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9930578519058937472078821 1861983472323550776014779)
        ·
          refine ⟨2792975208485326164022169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861983472323550776014779 2792975208485326164022169)
          ·
            refine ⟨2094731406363994623016627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792975208485326164022169 2094731406363994623016627)
            ·
              refine ⟨3142097109545991934524941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094731406363994623016627 3142097109545991934524941)
              ·
                refine ⟨1178286416079746975446853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3142097109545991934524941 1178286416079746975446853)
                ·
                  refine ⟨220928703014952557896285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178286416079746975446853 220928703014952557896285)
                  ·
                    rfl

theorem cell22_1936157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_1936157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936157 prefixEnd_1936157 := by exact prefixLift 1936157
  have htrace : WordTrace (prefixWord ++ tailWord_1936157) baseStart_1936157 baseEnd_1936157 := by
    simpa [prefixWord, tailWord_1936157, baseEnd_1936157] using wordTrace_append hprefix tailTrace_1936157
  have hstable : (prefixWord ++ tailWord_1936157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936157).length < 2 ^ (prefixWord ++ tailWord_1936157).sum := by decide
  have hdescent : baseEnd_1936157 < baseStart_1936157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936170 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1936170 : Nat := 118140960795 + 1936170 * 2 ^ 59
def prefixEnd_1936170 : Nat := 4983230072969 + 3 ^ 40 * 1936170 * 2
def baseEnd_1936170 : Nat := 662790559210529973113815

theorem tailTrace_1936170 : CollatzResearch.WordTrace tailWord_1936170 prefixEnd_1936170 662790559210529973113815 := by
  unfold tailWord_1936170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654480348898559088751491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47078614263729490903337309 17654480348898559088751491)
  ·
    refine ⟨26481720523347838633127237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17654480348898559088751491 26481720523347838633127237)
    ·
      refine ⟨4965322598127719743711357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26481720523347838633127237 4965322598127719743711357)
      ·
        refine ⟨1861995974297894903891759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4965322598127719743711357 1861995974297894903891759)
        ·
          refine ⟨2792993961446842355837639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861995974297894903891759 2792993961446842355837639)
          ·
            refine ⟨4189490942170263533756459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792993961446842355837639 4189490942170263533756459)
            ·
              refine ⟨6284236413255395300634689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189490942170263533756459 6284236413255395300634689)
              ·
                refine ⟨4713177309941546475476017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284236413255395300634689 4713177309941546475476017)
                ·
                  refine ⟨3534882982456159856607013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713177309941546475476017 3534882982456159856607013)
                  ·
                    refine ⟨662790559210529973113815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534882982456159856607013 662790559210529973113815)
                    ·
                      rfl

theorem cell22_1936170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1936170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936170 prefixEnd_1936170 := by exact prefixLift 1936170
  have htrace : WordTrace (prefixWord ++ tailWord_1936170) baseStart_1936170 baseEnd_1936170 := by
    simpa [prefixWord, tailWord_1936170, baseEnd_1936170] using wordTrace_append hprefix tailTrace_1936170
  have hstable : (prefixWord ++ tailWord_1936170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936170).length < 2 ^ (prefixWord ++ tailWord_1936170).sum := by decide
  have hdescent : baseEnd_1936170 < baseStart_1936170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936189 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1936189 : Nat := 118140960795 + 1936189 * 2 ^ 59
def prefixEnd_1936189 : Nat := 4983230072969 + 3 ^ 40 * 1936189 * 2
def baseEnd_1936189 : Nat := 662797063298820256888757

theorem tailTrace_1936189 : CollatzResearch.WordTrace tailWord_1936189 prefixEnd_1936189 662797063298820256888757 := by
  unfold tailWord_1936189
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618614382525402599947621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47079076255016935066631747 70618614382525402599947621)
  ·
    refine ⟨13240990196723512987490179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70618614382525402599947621 13240990196723512987490179)
    ·
      refine ⟨19861485295085269481235269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240990196723512987490179 19861485295085269481235269)
      ·
        refine ⟨3724028492828488027731613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19861485295085269481235269 3724028492828488027731613)
        ·
          refine ⟨1396510684810683010399355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3724028492828488027731613 1396510684810683010399355)
          ·
            refine ⟨2094766027216024515599033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396510684810683010399355 2094766027216024515599033)
            ·
              refine ⟨1571074520412018386699275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094766027216024515599033 1571074520412018386699275)
              ·
                refine ⟨2356611780618027580048913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571074520412018386699275 2356611780618027580048913)
                ·
                  refine ⟨1767458835463520685036685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356611780618027580048913 1767458835463520685036685)
                  ·
                    refine ⟨662797063298820256888757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767458835463520685036685 662797063298820256888757)
                    ·
                      rfl

theorem cell22_1936189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1936189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936189 prefixEnd_1936189 := by exact prefixLift 1936189
  have htrace : WordTrace (prefixWord ++ tailWord_1936189) baseStart_1936189 baseEnd_1936189 := by
    simpa [prefixWord, tailWord_1936189, baseEnd_1936189] using wordTrace_append hprefix tailTrace_1936189
  have hstable : (prefixWord ++ tailWord_1936189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936189).length < 2 ^ (prefixWord ++ tailWord_1936189).sum := by decide
  have hdescent : baseEnd_1936189 < baseStart_1936189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936290 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1936290 : Nat := 118140960795 + 1936290 * 2 ^ 59
def prefixEnd_1936290 : Nat := 4983230072969 + 3 ^ 40 * 1936290 * 2
def baseEnd_1936290 : Nat := 662831637662889660113447

theorem tailTrace_1936290 : CollatzResearch.WordTrace tailWord_1936290 prefixEnd_1936290 662831637662889660113447 := by
  unfold tailWord_1936290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655574538789874212343581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47081532103439664566249549 17655574538789874212343581)
  ·
    refine ⟨6620840452046202829628843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17655574538789874212343581 6620840452046202829628843)
    ·
      refine ⟨9931260678069304244443265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620840452046202829628843 9931260678069304244443265)
      ·
        refine ⟨7448445508551978183332449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9931260678069304244443265 7448445508551978183332449)
        ·
          refine ⟨5586334131413983637499337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7448445508551978183332449 5586334131413983637499337)
          ·
            refine ⟨4189750598560487728124503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586334131413983637499337 4189750598560487728124503)
            ·
              refine ⟨6284625897840731592186755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189750598560487728124503 6284625897840731592186755)
              ·
                refine ⟨9426938846761097388280133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284625897840731592186755 9426938846761097388280133)
                ·
                  refine ⟨1767551033767705760302525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9426938846761097388280133 1767551033767705760302525)
                  ·
                    refine ⟨662831637662889660113447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767551033767705760302525 662831637662889660113447)
                    ·
                      rfl

theorem cell22_1936290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1936290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936290 prefixEnd_1936290 := by exact prefixLift 1936290
  have htrace : WordTrace (prefixWord ++ tailWord_1936290) baseStart_1936290 baseEnd_1936290 := by
    simpa [prefixWord, tailWord_1936290, baseEnd_1936290] using wordTrace_append hprefix tailTrace_1936290
  have hstable : (prefixWord ++ tailWord_1936290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936290).length < 2 ^ (prefixWord ++ tailWord_1936290).sum := by decide
  have hdescent : baseEnd_1936290 < baseStart_1936290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936331 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 7]
def baseStart_1936331 : Nat := 118140960795 + 1936331 * 2 ^ 59
def prefixEnd_1936331 : Nat := 4983230072969 + 3 ^ 40 * 1936331 * 2
def baseEnd_1936331 : Nat := 220948557600259739946107

theorem tailTrace_1936331 : CollatzResearch.WordTrace tailWord_1936331 prefixEnd_1936331 220948557600259739946107 := by
  unfold tailWord_1936331
  simp only [CollatzResearch.WordTrace]
  refine ⟨70623793548010960851616847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47082529032007307234411231 70623793548010960851616847)
  ·
    refine ⟨105935690322016441277425271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70623793548010960851616847 105935690322016441277425271)
    ·
      refine ⟨158903535483024661916137907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105935690322016441277425271 158903535483024661916137907)
      ·
        refine ⟨238355303224536992874206861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158903535483024661916137907 238355303224536992874206861)
        ·
          refine ⟨89383238709201372327827573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238355303224536992874206861 89383238709201372327827573)
          ·
            refine ⟨8379678628987628655733835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89383238709201372327827573 8379678628987628655733835)
            ·
              refine ⟨12569517943481442983600753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379678628987628655733835 12569517943481442983600753)
              ·
                refine ⟨9427138457611082237700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12569517943481442983600753 9427138457611082237700565)
                ·
                  refine ⟨220948557600259739946107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9427138457611082237700565 220948557600259739946107)
                  ·
                    rfl

theorem cell22_1936331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_1936331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936331 prefixEnd_1936331 := by exact prefixLift 1936331
  have htrace : WordTrace (prefixWord ++ tailWord_1936331) baseStart_1936331 baseEnd_1936331 := by
    simpa [prefixWord, tailWord_1936331, baseEnd_1936331] using wordTrace_append hprefix tailTrace_1936331
  have hstable : (prefixWord ++ tailWord_1936331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936331).length < 2 ^ (prefixWord ++ tailWord_1936331).sum := by decide
  have hdescent : baseEnd_1936331 < baseStart_1936331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936376 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_1936376 : Nat := 118140960795 + 1936376 * 2 ^ 59
def prefixEnd_1936376 : Nat := 4983230072969 + 3 ^ 40 * 1936376 * 2
def baseEnd_1936376 : Nat := 220953692406804700821061

theorem tailTrace_1936376 : CollatzResearch.WordTrace tailWord_1936376 prefixEnd_1936376 220953692406804700821061 := by
  unfold tailWord_1936376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35312717416423966768502491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47083623221898622358003321 35312717416423966768502491)
  ·
    refine ⟨52969076124635950152753737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35312717416423966768502491 52969076124635950152753737)
    ·
      refine ⟨39726807093476962614565303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52969076124635950152753737 39726807093476962614565303)
      ·
        refine ⟨59590210640215443921847955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39726807093476962614565303 59590210640215443921847955)
        ·
          refine ⟨89385315960323165882771933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59590210640215443921847955 89385315960323165882771933)
          ·
            refine ⟨33519493485121187206039475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89385315960323165882771933 33519493485121187206039475)
            ·
              refine ⟨50279240227681780809059213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33519493485121187206039475 50279240227681780809059213)
              ·
                refine ⟨18854715085380667803397205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50279240227681780809059213 18854715085380667803397205)
                ·
                  refine ⟨220953692406804700821061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18854715085380667803397205 220953692406804700821061)
                  ·
                    rfl

theorem cell22_1936376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_1936376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936376 prefixEnd_1936376 := by exact prefixLift 1936376
  have htrace : WordTrace (prefixWord ++ tailWord_1936376) baseStart_1936376 baseEnd_1936376 := by
    simpa [prefixWord, tailWord_1936376, baseEnd_1936376] using wordTrace_append hprefix tailTrace_1936376
  have hstable : (prefixWord ++ tailWord_1936376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936376).length < 2 ^ (prefixWord ++ tailWord_1936376).sum := by decide
  have hdescent : baseEnd_1936376 < baseStart_1936376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936410 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_1936410 : Nat := 118140960795 + 1936410 * 2 ^ 59
def prefixEnd_1936410 : Nat := 4983230072969 + 3 ^ 40 * 1936410 * 2
def baseEnd_1936410 : Nat := 220957572038416449037693

theorem tailTrace_1936410 : CollatzResearch.WordTrace tailWord_1936410 prefixEnd_1936410 220957572038416449037693 := by
  unfold tailWord_1936410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656668728681189335935671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47084449943149838229161789 17656668728681189335935671)
  ·
    refine ⟨26485003093021784003903507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656668728681189335935671 26485003093021784003903507)
    ·
      refine ⟨39727504639532676005855261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26485003093021784003903507 39727504639532676005855261)
      ·
        refine ⟨14897814239824753502195723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39727504639532676005855261 14897814239824753502195723)
        ·
          refine ⟨22346721359737130253293585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897814239824753502195723 22346721359737130253293585)
          ·
            refine ⟨16760041019802847689970189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22346721359737130253293585 16760041019802847689970189)
            ·
              refine ⟨6285015382426067883738821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16760041019802847689970189 6285015382426067883738821)
              ·
                refine ⟨1178440384204887728201029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6285015382426067883738821 1178440384204887728201029)
                ·
                  refine ⟨220957572038416449037693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178440384204887728201029 220957572038416449037693)
                  ·
                    rfl

theorem cell22_1936410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_1936410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936410 prefixEnd_1936410 := by exact prefixLift 1936410
  have htrace : WordTrace (prefixWord ++ tailWord_1936410) baseStart_1936410 baseEnd_1936410 := by
    simpa [prefixWord, tailWord_1936410, baseEnd_1936410] using wordTrace_append hprefix tailTrace_1936410
  have hstable : (prefixWord ++ tailWord_1936410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936410).length < 2 ^ (prefixWord ++ tailWord_1936410).sum := by decide
  have hdescent : baseEnd_1936410 < baseStart_1936410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936440 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_1936440 : Nat := 118140960795 + 1936440 * 2 ^ 59
def prefixEnd_1936440 : Nat := 4983230072969 + 3 ^ 40 * 1936440 * 2
def baseEnd_1936440 : Nat := 662882985728339268862987

theorem tailTrace_1936440 : CollatzResearch.WordTrace tailWord_1936440 prefixEnd_1936440 662882985728339268862987 := by
  unfold tailWord_1936440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35313884552308036233667387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47085179403077381644889849 35313884552308036233667387)
  ·
    refine ⟨52970826828462054350501081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35313884552308036233667387 52970826828462054350501081)
    ·
      refine ⟨39728120121346540762875811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52970826828462054350501081 39728120121346540762875811)
      ·
        refine ⟨59592180182019811144313717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39728120121346540762875811 59592180182019811144313717)
        ·
          refine ⟨5586766892064357294779411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59592180182019811144313717 5586766892064357294779411)
          ·
            refine ⟨8380150338096535942169117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586766892064357294779411 8380150338096535942169117)
            ·
              refine ⟨3142556376786200978313419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8380150338096535942169117 3142556376786200978313419)
              ·
                refine ⟨4713834565179301467470129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142556376786200978313419 4713834565179301467470129)
                ·
                  refine ⟨3535375923884476100602597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713834565179301467470129 3535375923884476100602597)
                  ·
                    refine ⟨662882985728339268862987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535375923884476100602597 662882985728339268862987)
                    ·
                      rfl

theorem cell22_1936440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_1936440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936440 prefixEnd_1936440 := by exact prefixLift 1936440
  have htrace : WordTrace (prefixWord ++ tailWord_1936440) baseStart_1936440 baseEnd_1936440 := by
    simpa [prefixWord, tailWord_1936440, baseEnd_1936440] using wordTrace_append hprefix tailTrace_1936440
  have hstable : (prefixWord ++ tailWord_1936440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936440).length < 2 ^ (prefixWord ++ tailWord_1936440).sum := by decide
  have hdescent : baseEnd_1936440 < baseStart_1936440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936468 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1936468 : Nat := 118140960795 + 1936468 * 2 ^ 59
def prefixEnd_1936468 : Nat := 4983230072969 + 3 ^ 40 * 1936468 * 2
def baseEnd_1936468 : Nat := 662892570700556529162901

theorem tailTrace_1936468 : CollatzResearch.WordTrace tailWord_1936468 prefixEnd_1936468 662892570700556529162901 := by
  unfold tailWord_1936468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314395174257316624677029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47085860232343088832902705 35314395174257316624677029)
  ·
    refine ⟨6621449095173246867126943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35314395174257316624677029 6621449095173246867126943)
    ·
      refine ⟨9932173642759870300690415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621449095173246867126943 9932173642759870300690415)
      ·
        refine ⟨14898260464139805451035623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932173642759870300690415 14898260464139805451035623)
        ·
          refine ⟨22347390696209708176553435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898260464139805451035623 22347390696209708176553435)
          ·
            refine ⟨33521086044314562264830153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22347390696209708176553435 33521086044314562264830153)
            ·
              refine ⟨25140814533235921698622615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33521086044314562264830153 25140814533235921698622615)
              ·
                refine ⟨37711221799853882547933923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25140814533235921698622615 37711221799853882547933923)
                ·
                  refine ⟨56566832699780823821900885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37711221799853882547933923 56566832699780823821900885)
                  ·
                    refine ⟨662892570700556529162901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56566832699780823821900885 662892570700556529162901)
                    ·
                      rfl

theorem cell22_1936468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1936468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936468 prefixEnd_1936468 := by exact prefixLift 1936468
  have htrace : WordTrace (prefixWord ++ tailWord_1936468) baseStart_1936468 baseEnd_1936468 := by
    simpa [prefixWord, tailWord_1936468, baseEnd_1936468] using wordTrace_append hprefix tailTrace_1936468
  have hstable : (prefixWord ++ tailWord_1936468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936468).length < 2 ^ (prefixWord ++ tailWord_1936468).sum := by decide
  have hdescent : baseEnd_1936468 < baseStart_1936468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936528 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_1936528 : Nat := 118140960795 + 1936528 * 2 ^ 59
def prefixEnd_1936528 : Nat := 4983230072969 + 3 ^ 40 * 1936528 * 2
def baseEnd_1936528 : Nat := 220971036642245457554239

theorem tailTrace_1936528 : CollatzResearch.WordTrace tailWord_1936528 prefixEnd_1936528 220971036642245457554239 := by
  unfold tailWord_1936528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35315489364148631748269119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47087319152198175664358825 35315489364148631748269119)
  ·
    refine ⟨52973234046222947622403679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35315489364148631748269119 52973234046222947622403679)
    ·
      refine ⟨79459851069334421433605519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52973234046222947622403679 79459851069334421433605519)
      ·
        refine ⟨119189776604001632150408279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79459851069334421433605519 119189776604001632150408279)
        ·
          refine ⟨178784664906002448225612419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119189776604001632150408279 178784664906002448225612419)
          ·
            refine ⟨268176997359003672338418629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178784664906002448225612419 268176997359003672338418629)
            ·
              refine ⟨50283187004813188563453493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268176997359003672338418629 50283187004813188563453493)
              ·
                refine ⟨4714048781701236427823765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50283187004813188563453493 4714048781701236427823765)
                ·
                  refine ⟨220971036642245457554239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4714048781701236427823765 220971036642245457554239)
                  ·
                    rfl

theorem cell22_1936528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_1936528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936528 prefixEnd_1936528 := by exact prefixLift 1936528
  have htrace : WordTrace (prefixWord ++ tailWord_1936528) baseStart_1936528 baseEnd_1936528 := by
    simpa [prefixWord, tailWord_1936528, baseEnd_1936528] using wordTrace_append hprefix tailTrace_1936528
  have hstable : (prefixWord ++ tailWord_1936528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936528).length < 2 ^ (prefixWord ++ tailWord_1936528).sum := by decide
  have hdescent : baseEnd_1936528 < baseStart_1936528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936575 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_1936575 : Nat := 118140960795 + 1936575 * 2 ^ 59
def prefixEnd_1936575 : Nat := 4983230072969 + 3 ^ 40 * 1936575 * 2
def baseEnd_1936575 : Nat := 662929198987243916737573

theorem tailTrace_1936575 : CollatzResearch.WordTrace tailWord_1936575 prefixEnd_1936575 662929198987243916737573 := by
  unfold tailWord_1936575
  simp only [CollatzResearch.WordTrace]
  refine ⟨70632692959126990523499179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47088461972751327015666119 70632692959126990523499179)
  ·
    refine ⟨105949039438690485785248769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70632692959126990523499179 105949039438690485785248769)
    ·
      refine ⟨79461779579017864338936577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105949039438690485785248769 79461779579017864338936577)
      ·
        refine ⟨59596334684263398254202433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79461779579017864338936577 59596334684263398254202433)
        ·
          refine ⟨44697251013197548690651825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59596334684263398254202433 44697251013197548690651825)
          ·
            refine ⟨33522938259898161517988869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44697251013197548690651825 33522938259898161517988869)
            ·
              refine ⟨6285550923730905284622913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33522938259898161517988869 6285550923730905284622913)
              ·
                refine ⟨4714163192798178963467185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285550923730905284622913 4714163192798178963467185)
                ·
                  refine ⟨3535622394598634222600389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714163192798178963467185 3535622394598634222600389)
                  ·
                    refine ⟨662929198987243916737573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535622394598634222600389 662929198987243916737573)
                    ·
                      rfl

theorem cell22_1936575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_1936575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936575 prefixEnd_1936575 := by exact prefixLift 1936575
  have htrace : WordTrace (prefixWord ++ tailWord_1936575) baseStart_1936575 baseEnd_1936575 := by
    simpa [prefixWord, tailWord_1936575, baseEnd_1936575] using wordTrace_append hprefix tailTrace_1936575
  have hstable : (prefixWord ++ tailWord_1936575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936575).length < 2 ^ (prefixWord ++ tailWord_1936575).sum := by decide
  have hdescent : baseEnd_1936575 < baseStart_1936575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_1936603 : Nat := 118140960795 + 1936603 * 2 ^ 59
def prefixEnd_1936603 : Nat := 4983230072969 + 3 ^ 40 * 1936603 * 2
def baseEnd_1936603 : Nat := 662938783959461177037487

theorem tailTrace_1936603 : CollatzResearch.WordTrace tailWord_1936603 prefixEnd_1936603 662938783959461177037487 := by
  unfold tailWord_1936603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70633714203025551305518463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47089142802017034203678975 70633714203025551305518463)
  ·
    refine ⟨105950571304538326958277695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70633714203025551305518463 105950571304538326958277695)
    ·
      refine ⟨158925856956807490437416543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105950571304538326958277695 158925856956807490437416543)
      ·
        refine ⟨238388785435211235656124815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158925856956807490437416543 238388785435211235656124815)
        ·
          refine ⟨357583178152816853484187223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238388785435211235656124815 357583178152816853484187223)
          ·
            refine ⟨536374767229225280226280835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357583178152816853484187223 536374767229225280226280835)
            ·
              refine ⟨804562150843837920339421253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536374767229225280226280835 804562150843837920339421253)
              ·
                refine ⟨150855403283219610063641485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804562150843837920339421253 150855403283219610063641485)
                ·
                  refine ⟨56570776231207353773865557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150855403283219610063641485 56570776231207353773865557)
                  ·
                    refine ⟨662938783959461177037487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56570776231207353773865557 662938783959461177037487)
                    ·
                      rfl

theorem cell22_1936603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_1936603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936603 prefixEnd_1936603 := by exact prefixLift 1936603
  have htrace : WordTrace (prefixWord ++ tailWord_1936603) baseStart_1936603 baseEnd_1936603 := by
    simpa [prefixWord, tailWord_1936603, baseEnd_1936603] using wordTrace_append hprefix tailTrace_1936603
  have hstable : (prefixWord ++ tailWord_1936603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936603).length < 2 ^ (prefixWord ++ tailWord_1936603).sum := by decide
  have hdescent : baseEnd_1936603 < baseStart_1936603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936628 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1936628 : Nat := 118140960795 + 1936628 * 2 ^ 59
def prefixEnd_1936628 : Nat := 4983230072969 + 3 ^ 40 * 1936628 * 2
def baseEnd_1936628 : Nat := 662947341970369445162411

theorem tailTrace_1936628 : CollatzResearch.WordTrace tailWord_1936628 prefixEnd_1936628 662947341970369445162411 := by
  unfold tailWord_1936628
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317313013967490287589269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47089750685289987050119025 35317313013967490287589269)
  ·
    refine ⟨1655499047529726107230747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35317313013967490287589269 1655499047529726107230747)
    ·
      refine ⟨2483248571294589160846121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655499047529726107230747 2483248571294589160846121)
      ·
        refine ⟨1862436428470941870634591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483248571294589160846121 1862436428470941870634591)
        ·
          refine ⟨2793654642706412805951887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862436428470941870634591 2793654642706412805951887)
          ·
            refine ⟨4190481964059619208927831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793654642706412805951887 4190481964059619208927831)
            ·
              refine ⟨6285722946089428813391747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190481964059619208927831 6285722946089428813391747)
              ·
                refine ⟨9428584419134143220087621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285722946089428813391747 9428584419134143220087621)
                ·
                  refine ⟨1767859578587651853766429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9428584419134143220087621 1767859578587651853766429)
                  ·
                    refine ⟨662947341970369445162411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767859578587651853766429 662947341970369445162411)
                    ·
                      rfl

theorem cell22_1936628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1936628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936628 prefixEnd_1936628 := by exact prefixLift 1936628
  have htrace : WordTrace (prefixWord ++ tailWord_1936628) baseStart_1936628 baseEnd_1936628 := by
    simpa [prefixWord, tailWord_1936628, baseEnd_1936628] using wordTrace_append hprefix tailTrace_1936628
  have hstable : (prefixWord ++ tailWord_1936628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936628).length < 2 ^ (prefixWord ++ tailWord_1936628).sum := by decide
  have hdescent : baseEnd_1936628 < baseStart_1936628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936639 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 1, 3]
def baseStart_1936639 : Nat := 118140960795 + 1936639 * 2 ^ 59
def prefixEnd_1936639 : Nat := 4983230072969 + 3 ^ 40 * 1936639 * 2
def baseEnd_1936639 : Nat := 662951107495169083137377

theorem tailTrace_1936639 : CollatzResearch.WordTrace tailWord_1936639 prefixEnd_1936639 662951107495169083137377 := by
  unfold tailWord_1936639
  simp only [CollatzResearch.WordTrace]
  refine ⟨70635027230895129453828971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47090018153930086302552647 70635027230895129453828971)
  ·
    refine ⟨105952540846342694180743457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70635027230895129453828971 105952540846342694180743457)
    ·
      refine ⟨79464405634757020635557593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105952540846342694180743457 79464405634757020635557593)
      ·
        refine ⟨59598304226067765476668195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79464405634757020635557593 59598304226067765476668195)
        ·
          refine ⟨89397456339101648215002293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59598304226067765476668195 89397456339101648215002293)
          ·
            refine ⟨8381011531790779520156465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89397456339101648215002293 8381011531790779520156465)
            ·
              refine ⟨6285758648843084640117349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381011531790779520156465 6285758648843084640117349)
              ·
                refine ⟨1178579746658078370022003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6285758648843084640117349 1178579746658078370022003)
                ·
                  refine ⟨1767869619987117555033005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178579746658078370022003 1767869619987117555033005)
                  ·
                    refine ⟨662951107495169083137377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767869619987117555033005 662951107495169083137377)
                    ·
                      rfl

theorem cell22_1936639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_1936639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936639 prefixEnd_1936639 := by exact prefixLift 1936639
  have htrace : WordTrace (prefixWord ++ tailWord_1936639) baseStart_1936639 baseEnd_1936639 := by
    simpa [prefixWord, tailWord_1936639, baseEnd_1936639] using wordTrace_append hprefix tailTrace_1936639
  have hstable : (prefixWord ++ tailWord_1936639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936639).length < 2 ^ (prefixWord ++ tailWord_1936639).sum := by decide
  have hdescent : baseEnd_1936639 < baseStart_1936639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936658 : List Nat := [3, 2, 4, 2, 2, 1, 2, 6]
def baseStart_1936658 : Nat := 118140960795 + 1936658 * 2 ^ 59
def prefixEnd_1936658 : Nat := 4983230072969 + 3 ^ 40 * 1936658 * 2
def baseEnd_1936658 : Nat := 73661956842606596323591

theorem tailTrace_1936658 : CollatzResearch.WordTrace tailWord_1936658 prefixEnd_1936658 73661956842606596323591 := by
  unfold tailWord_1936658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658930054456573924692657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47090480145217530465847085 17658930054456573924692657)
  ·
    refine ⟨13244197540842430443519493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17658930054456573924692657 13244197540842430443519493)
    ·
      refine ⟨2483287038907955708159905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13244197540842430443519493 2483287038907955708159905)
      ·
        refine ⟨1862465279180966781119929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483287038907955708159905 1862465279180966781119929)
        ·
          refine ⟨1396848959385725085839947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862465279180966781119929 1396848959385725085839947)
          ·
            refine ⟨2095273439078587628759921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396848959385725085839947 2095273439078587628759921)
            ·
              refine ⟨1571455079308940721569941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095273439078587628759921 1571455079308940721569941)
              ·
                refine ⟨73661956842606596323591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1571455079308940721569941 73661956842606596323591)
                ·
                  rfl

theorem cell22_1936658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_1936658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936658 prefixEnd_1936658 := by exact prefixLift 1936658
  have htrace : WordTrace (prefixWord ++ tailWord_1936658) baseStart_1936658 baseEnd_1936658 := by
    simpa [prefixWord, tailWord_1936658, baseEnd_1936658] using wordTrace_append hprefix tailTrace_1936658
  have hstable : (prefixWord ++ tailWord_1936658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936658).length < 2 ^ (prefixWord ++ tailWord_1936658).sum := by decide
  have hdescent : baseEnd_1936658 < baseStart_1936658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936727 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1936727 : Nat := 118140960795 + 1936727 * 2 ^ 59
def prefixEnd_1936727 : Nat := 4983230072969 + 3 ^ 40 * 1936727 * 2
def baseEnd_1936727 : Nat := 662981231693566186937107

theorem tailTrace_1936727 : CollatzResearch.WordTrace tailWord_1936727 prefixEnd_1936727 662981231693566186937107 := by
  unfold tailWord_1936727
  simp only [CollatzResearch.WordTrace]
  refine ⟨70638236854576320483032435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47092157903050880322021623 70638236854576320483032435)
  ·
    refine ⟨105957355281864480724548653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70638236854576320483032435 105957355281864480724548653)
    ·
      refine ⟨39734008230699180271705745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105957355281864480724548653 39734008230699180271705745)
      ·
        refine ⟨29800506173024385203779309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39734008230699180271705745 29800506173024385203779309)
        ·
          refine ⟨11175189814884144451417241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29800506173024385203779309 11175189814884144451417241)
          ·
            refine ⟨8381392361163108338562931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11175189814884144451417241 8381392361163108338562931)
            ·
              refine ⟨12572088541744662507844397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381392361163108338562931 12572088541744662507844397)
              ·
                refine ⟨4714533203154248440441649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12572088541744662507844397 4714533203154248440441649)
                ·
                  refine ⟨3535899902365686330331237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714533203154248440441649 3535899902365686330331237)
                  ·
                    refine ⟨662981231693566186937107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535899902365686330331237 662981231693566186937107)
                    ·
                      rfl

theorem cell22_1936727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1936727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936727 prefixEnd_1936727 := by exact prefixLift 1936727
  have htrace : WordTrace (prefixWord ++ tailWord_1936727) baseStart_1936727 baseEnd_1936727 := by
    simpa [prefixWord, tailWord_1936727, baseEnd_1936727] using wordTrace_append hprefix tailTrace_1936727
  have hstable : (prefixWord ++ tailWord_1936727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936727).length < 2 ^ (prefixWord ++ tailWord_1936727).sum := by decide
  have hdescent : baseEnd_1936727 < baseStart_1936727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936808 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1936808 : Nat := 118140960795 + 1936808 * 2 ^ 59
def prefixEnd_1936808 : Nat := 4983230072969 + 3 ^ 40 * 1936808 * 2
def baseEnd_1936808 : Nat := 663008959648908975661859

theorem tailTrace_1936808 : CollatzResearch.WordTrace tailWord_1936808 prefixEnd_1936808 663008959648908975661859 := by
  unfold tailWord_1936808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320595583641435658365539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47094127444855247544487385 35320595583641435658365539)
  ·
    refine ⟨52980893375462153487548309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35320595583641435658365539 52980893375462153487548309)
    ·
      refine ⟨2483479376974788444728827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52980893375462153487548309 2483479376974788444728827)
      ·
        refine ⟨3725219065462182667093241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483479376974788444728827 3725219065462182667093241)
        ·
          refine ⟨2793914299096637000319931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725219065462182667093241 2793914299096637000319931)
          ·
            refine ⟨4190871448644955500479897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793914299096637000319931 4190871448644955500479897)
            ·
              refine ⟨3143153586483716625359923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4190871448644955500479897 3143153586483716625359923)
              ·
                refine ⟨4714730379725574938039885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143153586483716625359923 4714730379725574938039885)
                ·
                  refine ⟨1768023892397090601764957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4714730379725574938039885 1768023892397090601764957)
                  ·
                    refine ⟨663008959648908975661859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768023892397090601764957 663008959648908975661859)
                    ·
                      rfl

theorem cell22_1936808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1936808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936808 prefixEnd_1936808 := by exact prefixLift 1936808
  have htrace : WordTrace (prefixWord ++ tailWord_1936808) baseStart_1936808 baseEnd_1936808 := by
    simpa [prefixWord, tailWord_1936808, baseEnd_1936808] using wordTrace_append hprefix tailTrace_1936808
  have hstable : (prefixWord ++ tailWord_1936808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936808).length < 2 ^ (prefixWord ++ tailWord_1936808).sum := by decide
  have hdescent : baseEnd_1936808 < baseStart_1936808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936821 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 5]
def baseStart_1936821 : Nat := 118140960795 + 1936821 * 2 ^ 59
def prefixEnd_1936821 : Nat := 4983230072969 + 3 ^ 40 * 1936821 * 2
def baseEnd_1936821 : Nat := 221004469938193758362273

theorem tailTrace_1936821 : CollatzResearch.WordTrace tailWord_1936821 prefixEnd_1936821 221004469938193758362273 := by
  unfold tailWord_1936821
  simp only [CollatzResearch.WordTrace]
  refine ⟨70641665316235774536954317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47094443544157183024636211 70641665316235774536954317)
  ·
    refine ⟨26490624493588415451357869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70641665316235774536954317 26490624493588415451357869)
    ·
      refine ⟨9933984185095655794259201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26490624493588415451357869 9933984185095655794259201)
      ·
        refine ⟨7450488138821741845694401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9933984185095655794259201 7450488138821741845694401)
        ·
          refine ⟨5587866104116306384270801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450488138821741845694401 5587866104116306384270801)
          ·
            refine ⟨4190899578087229788203101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587866104116306384270801 4190899578087229788203101)
            ·
              refine ⟨1571587341782711170576163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4190899578087229788203101 1571587341782711170576163)
              ·
                refine ⟨2357381012674066755864245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571587341782711170576163 2357381012674066755864245)
                ·
                  refine ⟨221004469938193758362273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357381012674066755864245 221004469938193758362273)
                  ·
                    rfl

theorem cell22_1936821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_1936821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936821 prefixEnd_1936821 := by exact prefixLift 1936821
  have htrace : WordTrace (prefixWord ++ tailWord_1936821) baseStart_1936821 baseEnd_1936821 := by
    simpa [prefixWord, tailWord_1936821, baseEnd_1936821] using wordTrace_append hprefix tailTrace_1936821
  have hstable : (prefixWord ++ tailWord_1936821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936821).length < 2 ^ (prefixWord ++ tailWord_1936821).sum := by decide
  have hdescent : baseEnd_1936821 < baseStart_1936821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936832 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_1936832 : Nat := 118140960795 + 1936832 * 2 ^ 59
def prefixEnd_1936832 : Nat := 4983230072969 + 3 ^ 40 * 1936832 * 2
def baseEnd_1936832 : Nat := 221005725113126971020595

theorem tailTrace_1936832 : CollatzResearch.WordTrace tailWord_1936832 prefixEnd_1936832 221005725113126971020595 := by
  unfold tailWord_1936832
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321033259597961707802375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47094711012797282277069833 35321033259597961707802375)
  ·
    refine ⟨52981549889396942561703563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35321033259597961707802375 52981549889396942561703563)
    ·
      refine ⟨79472324834095413842555345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52981549889396942561703563 79472324834095413842555345)
      ·
        refine ⟨59604243625571560381916509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79472324834095413842555345 59604243625571560381916509)
        ·
          refine ⟨22351591359589335143218691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59604243625571560381916509 22351591359589335143218691)
          ·
            refine ⟨33527387039384002714828037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22351591359589335143218691 33527387039384002714828037)
            ·
              refine ⟨6286385069884500509030257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33527387039384002714828037 6286385069884500509030257)
              ·
                refine ⟨4714788802413375381772693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286385069884500509030257 4714788802413375381772693)
                ·
                  refine ⟨221005725113126971020595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4714788802413375381772693 221005725113126971020595)
                  ·
                    rfl

theorem cell22_1936832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_1936832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936832 prefixEnd_1936832 := by exact prefixLift 1936832
  have htrace : WordTrace (prefixWord ++ tailWord_1936832) baseStart_1936832 baseEnd_1936832 := by
    simpa [prefixWord, tailWord_1936832, baseEnd_1936832] using wordTrace_append hprefix tailTrace_1936832
  have hstable : (prefixWord ++ tailWord_1936832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936832).length < 2 ^ (prefixWord ++ tailWord_1936832).sum := by decide
  have hdescent : baseEnd_1936832 < baseStart_1936832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936847 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1936847 : Nat := 118140960795 + 1936847 * 2 ^ 59
def prefixEnd_1936847 : Nat := 4983230072969 + 3 ^ 40 * 1936847 * 2
def baseEnd_1936847 : Nat := 663022310145925873936739

theorem tailTrace_1936847 : CollatzResearch.WordTrace tailWord_1936847 prefixEnd_1936847 663022310145925873936739 := by
  unfold tailWord_1936847
  simp only [CollatzResearch.WordTrace]
  refine ⟨70642613614141580977400795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47095075742761053984933863 70642613614141580977400795)
  ·
    refine ⟨105963920421212371466101193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70642613614141580977400795 105963920421212371466101193)
    ·
      refine ⟨79472940315909278599575895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105963920421212371466101193 79472940315909278599575895)
      ·
        refine ⟨119209410473863917899363843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79472940315909278599575895 119209410473863917899363843)
        ·
          refine ⟨178814115710795876849045765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119209410473863917899363843 178814115710795876849045765)
          ·
            refine ⟨33527646695774226909196081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178814115710795876849045765 33527646695774226909196081)
            ·
              refine ⟨25145735021830670181897061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33527646695774226909196081 25145735021830670181897061)
              ·
                refine ⟨4714825316593250659105699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25145735021830670181897061 4714825316593250659105699)
                ·
                  refine ⟨7072237974889875988658549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714825316593250659105699 7072237974889875988658549)
                  ·
                    refine ⟨663022310145925873936739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7072237974889875988658549 663022310145925873936739)
                    ·
                      rfl

theorem cell22_1936847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1936847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936847 prefixEnd_1936847 := by exact prefixLift 1936847
  have htrace : WordTrace (prefixWord ++ tailWord_1936847) baseStart_1936847 baseEnd_1936847 := by
    simpa [prefixWord, tailWord_1936847, baseEnd_1936847] using wordTrace_append hprefix tailTrace_1936847
  have hstable : (prefixWord ++ tailWord_1936847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936847).length < 2 ^ (prefixWord ++ tailWord_1936847).sum := by decide
  have hdescent : baseEnd_1936847 < baseStart_1936847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936881 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1936881 : Nat := 118140960795 + 1936881 * 2 ^ 59
def prefixEnd_1936881 : Nat := 4983230072969 + 3 ^ 40 * 1936881 * 2
def baseEnd_1936881 : Nat := 663033949040761118586635

theorem tailTrace_1936881 : CollatzResearch.WordTrace tailWord_1936881 prefixEnd_1936881 663033949040761118586635 := by
  unfold tailWord_1936881
  simp only [CollatzResearch.WordTrace]
  refine ⟨70643853696018404784138497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47095902464012269856092331 70643853696018404784138497)
  ·
    refine ⟨52982890272013803588103873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70643853696018404784138497 52982890272013803588103873)
    ·
      refine ⟨39737167704010352691077905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52982890272013803588103873 39737167704010352691077905)
      ·
        refine ⟨29802875778007764518308429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39737167704010352691077905 29802875778007764518308429)
        ·
          refine ⟨11176078416752911694365661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29802875778007764518308429 11176078416752911694365661)
          ·
            refine ⟨4191029406282341885387123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11176078416752911694365661 4191029406282341885387123)
            ·
              refine ⟨6286544109423512828080685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191029406282341885387123 6286544109423512828080685)
              ·
                refine ⟨2357454041033817310530257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6286544109423512828080685 2357454041033817310530257)
                ·
                  refine ⟨1768090530775362982897693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357454041033817310530257 1768090530775362982897693)
                  ·
                    refine ⟨663033949040761118586635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768090530775362982897693 663033949040761118586635)
                    ·
                      rfl

theorem cell22_1936881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1936881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936881 prefixEnd_1936881 := by exact prefixLift 1936881
  have htrace : WordTrace (prefixWord ++ tailWord_1936881) baseStart_1936881 baseEnd_1936881 := by
    simpa [prefixWord, tailWord_1936881, baseEnd_1936881] using wordTrace_append hprefix tailTrace_1936881
  have hstable : (prefixWord ++ tailWord_1936881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936881).length < 2 ^ (prefixWord ++ tailWord_1936881).sum := by decide
  have hdescent : baseEnd_1936881 < baseStart_1936881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936892 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1936892 : Nat := 118140960795 + 1936892 * 2 ^ 59
def prefixEnd_1936892 : Nat := 4983230072969 + 3 ^ 40 * 1936892 * 2
def baseEnd_1936892 : Nat := 663037714565560756561601

theorem tailTrace_1936892 : CollatzResearch.WordTrace tailWord_1936892 prefixEnd_1936892 663037714565560756561601 := by
  unfold tailWord_1936892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35322127449489276831394465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47096169932652369108525953 35322127449489276831394465)
  ·
    refine ⟨26491595587116957623545849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35322127449489276831394465 26491595587116957623545849)
    ·
      refine ⟨19868696690337718217659387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26491595587116957623545849 19868696690337718217659387)
      ·
        refine ⟨29803045035506577326489081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868696690337718217659387 29803045035506577326489081)
        ·
          refine ⟨22352283776629932994866811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29803045035506577326489081 22352283776629932994866811)
          ·
            refine ⟨33528425664944899492300217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22352283776629932994866811 33528425664944899492300217)
            ·
              refine ⟨25146319248708674619225163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33528425664944899492300217 25146319248708674619225163)
              ·
                refine ⟨37719478873063011928837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25146319248708674619225163 37719478873063011928837745)
                ·
                  refine ⟨28289609154797258946628309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37719478873063011928837745 28289609154797258946628309)
                  ·
                    refine ⟨663037714565560756561601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28289609154797258946628309 663037714565560756561601)
                    ·
                      rfl

theorem cell22_1936892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1936892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1936892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1936892 prefixEnd_1936892 := by exact prefixLift 1936892
  have htrace : WordTrace (prefixWord ++ tailWord_1936892) baseStart_1936892 baseEnd_1936892 := by
    simpa [prefixWord, tailWord_1936892, baseEnd_1936892] using wordTrace_append hprefix tailTrace_1936892
  have hstable : (prefixWord ++ tailWord_1936892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936892).length < 2 ^ (prefixWord ++ tailWord_1936892).sum := by decide
  have hdescent : baseEnd_1936892 < baseStart_1936892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937031 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1937031 : Nat := 118140960795 + 1937031 * 2 ^ 59
def prefixEnd_1937031 : Nat := 4983230072969 + 3 ^ 40 * 1937031 * 2
def baseEnd_1937031 : Nat := 663085297106210727336175

theorem tailTrace_1937031 : CollatzResearch.WordTrace tailWord_1937031 prefixEnd_1937031 663085297106210727336175 := by
  unfold tailWord_1937031
  simp only [CollatzResearch.WordTrace]
  refine ⟨70649324645474980402098947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47099549763649986934732631 70649324645474980402098947)
  ·
    refine ⟨105973986968212470603148421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70649324645474980402098947 105973986968212470603148421)
    ·
      refine ⟨19870122556539838238090329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105973986968212470603148421 19870122556539838238090329)
      ·
        refine ⟨14902591917404878678567747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19870122556539838238090329 14902591917404878678567747)
        ·
          refine ⟨22353887876107318017851621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14902591917404878678567747 22353887876107318017851621)
          ·
            refine ⟨4191353976770122128347179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22353887876107318017851621 4191353976770122128347179)
            ·
              refine ⟨6287030965155183192520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191353976770122128347179 6287030965155183192520769)
              ·
                refine ⟨4715273223866387394390577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287030965155183192520769 4715273223866387394390577)
                ·
                  refine ⟨3536454917899790545792933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4715273223866387394390577 3536454917899790545792933)
                  ·
                    refine ⟨663085297106210727336175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3536454917899790545792933 663085297106210727336175)
                    ·
                      rfl

theorem cell22_1937031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1937031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937031 prefixEnd_1937031 := by exact prefixLift 1937031
  have htrace : WordTrace (prefixWord ++ tailWord_1937031) baseStart_1937031 baseEnd_1937031 := by
    simpa [prefixWord, tailWord_1937031, baseEnd_1937031] using wordTrace_append hprefix tailTrace_1937031
  have hstable : (prefixWord ++ tailWord_1937031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937031).length < 2 ^ (prefixWord ++ tailWord_1937031).sum := by decide
  have hdescent : baseEnd_1937031 < baseStart_1937031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937061 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_1937061 : Nat := 118140960795 + 1937061 * 2 ^ 59
def prefixEnd_1937061 : Nat := 4983230072969 + 3 ^ 40 * 1937061 * 2
def baseEnd_1937061 : Nat := 663095566719300649086083

theorem tailTrace_1937061 : CollatzResearch.WordTrace tailWord_1937061 prefixEnd_1937061 663095566719300649086083 := by
  unfold tailWord_1937061
  simp only [CollatzResearch.WordTrace]
  refine ⟨70650418835366295525691037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47100279223577530350460691 70650418835366295525691037)
  ·
    refine ⟨26493907063262360822134139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70650418835366295525691037 26493907063262360822134139)
    ·
      refine ⟨39740860594893541233201209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26493907063262360822134139 39740860594893541233201209)
      ·
        refine ⟨29805645446170155924900907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39740860594893541233201209 29805645446170155924900907)
        ·
          refine ⟨44708468169255233887351361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805645446170155924900907 44708468169255233887351361)
          ·
            refine ⟨33531351126941425415513521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44708468169255233887351361 33531351126941425415513521)
            ·
              refine ⟨25148513345206069061635141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33531351126941425415513521 25148513345206069061635141)
              ·
                refine ⟨4715346252226137949056589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25148513345206069061635141 4715346252226137949056589)
                ·
                  refine ⟨1768254844584801730896221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4715346252226137949056589 1768254844584801730896221)
                  ·
                    refine ⟨663095566719300649086083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768254844584801730896221 663095566719300649086083)
                    ·
                      rfl

theorem cell22_1937061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_1937061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937061 prefixEnd_1937061 := by exact prefixLift 1937061
  have htrace : WordTrace (prefixWord ++ tailWord_1937061) baseStart_1937061 baseEnd_1937061 := by
    simpa [prefixWord, tailWord_1937061, baseEnd_1937061] using wordTrace_append hprefix tailTrace_1937061
  have hstable : (prefixWord ++ tailWord_1937061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937061).length < 2 ^ (prefixWord ++ tailWord_1937061).sum := by decide
  have hdescent : baseEnd_1937061 < baseStart_1937061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937074 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1937074 : Nat := 118140960795 + 1937074 * 2 ^ 59
def prefixEnd_1937074 : Nat := 4983230072969 + 3 ^ 40 * 1937074 * 2
def baseEnd_1937074 : Nat := 221033338961657649503681

theorem tailTrace_1937074 : CollatzResearch.WordTrace tailWord_1937074 prefixEnd_1937074 221033338961657649503681 := by
  unfold tailWord_1937074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17662723246079799686478569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47100595322879465830609517 17662723246079799686478569)
  ·
    refine ⟨13247042434559849764858927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17662723246079799686478569 13247042434559849764858927)
    ·
      refine ⟨19870563651839774647288391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247042434559849764858927 19870563651839774647288391)
      ·
        refine ⟨29805845477759661970932587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19870563651839774647288391 29805845477759661970932587)
        ·
          refine ⟨44708768216639492956398881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805845477759661970932587 44708768216639492956398881)
          ·
            refine ⟨33531576162479619717299161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44708768216639492956398881 33531576162479619717299161)
            ·
              refine ⟨25148682121859714787974371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33531576162479619717299161 25148682121859714787974371)
              ·
                refine ⟨37723023182789572181961557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25148682121859714787974371 37723023182789572181961557)
                ·
                  refine ⟨221033338961657649503681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37723023182789572181961557 221033338961657649503681)
                  ·
                    rfl

theorem cell22_1937074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1937074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937074 prefixEnd_1937074 := by exact prefixLift 1937074
  have htrace : WordTrace (prefixWord ++ tailWord_1937074) baseStart_1937074 baseEnd_1937074 := by
    simpa [prefixWord, tailWord_1937074, baseEnd_1937074] using wordTrace_append hprefix tailTrace_1937074
  have hstable : (prefixWord ++ tailWord_1937074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937074).length < 2 ^ (prefixWord ++ tailWord_1937074).sum := by decide
  have hdescent : baseEnd_1937074 < baseStart_1937074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937106 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1937106 : Nat := 118140960795 + 1937106 * 2 ^ 59
def prefixEnd_1937106 : Nat := 4983230072969 + 3 ^ 40 * 1937106 * 2
def baseEnd_1937106 : Nat := 663110971138935531710945

theorem tailTrace_1937106 : CollatzResearch.WordTrace tailWord_1937106 prefixEnd_1937106 663110971138935531710945 := by
  unfold tailWord_1937106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17663015030050817052769793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47101373413468845474052781 17663015030050817052769793)
  ·
    refine ⟨13247261272538112789577345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17663015030050817052769793 13247261272538112789577345)
    ·
      refine ⟨9935445954403584592183009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13247261272538112789577345 9935445954403584592183009)
      ·
        refine ⟨7451584465802688444137257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9935445954403584592183009 7451584465802688444137257)
        ·
          refine ⟨5588688349352016333102943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451584465802688444137257 5588688349352016333102943)
          ·
            refine ⟨8383032524028024499654415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588688349352016333102943 8383032524028024499654415)
            ·
              refine ⟨12574548786042036749481623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383032524028024499654415 12574548786042036749481623)
              ·
                refine ⟨18861823179063055124222435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12574548786042036749481623 18861823179063055124222435)
                ·
                  refine ⟨28292734768594582686333653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18861823179063055124222435 28292734768594582686333653)
                  ·
                    refine ⟨663110971138935531710945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28292734768594582686333653 663110971138935531710945)
                    ·
                      rfl

theorem cell22_1937106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1937106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937106 prefixEnd_1937106 := by exact prefixLift 1937106
  have htrace : WordTrace (prefixWord ++ tailWord_1937106) baseStart_1937106 baseEnd_1937106 := by
    simpa [prefixWord, tailWord_1937106, baseEnd_1937106] using wordTrace_append hprefix tailTrace_1937106
  have hstable : (prefixWord ++ tailWord_1937106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937106).length < 2 ^ (prefixWord ++ tailWord_1937106).sum := by decide
  have hdescent : baseEnd_1937106 < baseStart_1937106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937108 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1937108 : Nat := 118140960795 + 1937108 * 2 ^ 59
def prefixEnd_1937108 : Nat := 4983230072969 + 3 ^ 40 * 1937108 * 2
def baseEnd_1937108 : Nat := 221037218593269397720313

theorem tailTrace_1937108 : CollatzResearch.WordTrace tailWord_1937108 prefixEnd_1937108 221037218593269397720313 := by
  unfold tailWord_1937108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35326066533098011276325989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47101422044130681701767985 35326066533098011276325989)
  ·
    refine ⟨6623637474955877114311123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35326066533098011276325989 6623637474955877114311123)
    ·
      refine ⟨9935456212433815671466685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623637474955877114311123 9935456212433815671466685)
      ·
        refine ⟨3725796079662680876800007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9935456212433815671466685 3725796079662680876800007)
        ·
          refine ⟨5588694119494021315200011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725796079662680876800007 5588694119494021315200011)
          ·
            refine ⟨8383041179241031972800017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588694119494021315200011 8383041179241031972800017)
            ·
              refine ⟨6287280884430773979600013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383041179241031972800017 6287280884430773979600013)
              ·
                refine ⟨2357730331661540242350005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287280884430773979600013 2357730331661540242350005)
                ·
                  refine ⟨221037218593269397720313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357730331661540242350005 221037218593269397720313)
                  ·
                    rfl

theorem cell22_1937108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1937108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937108 prefixEnd_1937108 := by exact prefixLift 1937108
  have htrace : WordTrace (prefixWord ++ tailWord_1937108) baseStart_1937108 baseEnd_1937108 := by
    simpa [prefixWord, tailWord_1937108, baseEnd_1937108] using wordTrace_append hprefix tailTrace_1937108
  have hstable : (prefixWord ++ tailWord_1937108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937108).length < 2 ^ (prefixWord ++ tailWord_1937108).sum := by decide
  have hdescent : baseEnd_1937108 < baseStart_1937108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937138 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1937138 : Nat := 118140960795 + 1937138 * 2 ^ 59
def prefixEnd_1937138 : Nat := 4983230072969 + 3 ^ 40 * 1937138 * 2
def baseEnd_1937138 : Nat := 663121925392898114910847

theorem tailTrace_1937138 : CollatzResearch.WordTrace tailWord_1937138 prefixEnd_1937138 663121925392898114910847 := by
  unfold tailWord_1937138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17663306814021834419061017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47102151504058225117496045 17663306814021834419061017)
  ·
    refine ⟨13247480110516375814295763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17663306814021834419061017 13247480110516375814295763)
    ·
      refine ⟨19871220165774563721443645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247480110516375814295763 19871220165774563721443645)
      ·
        refine ⟨7451707562165461395541367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19871220165774563721443645 7451707562165461395541367)
        ·
          refine ⟨11177561343248192093312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451707562165461395541367 11177561343248192093312051)
          ·
            refine ⟨16766342014872288139968077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177561343248192093312051 16766342014872288139968077)
            ·
              refine ⟨6287378255577108052488029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16766342014872288139968077 6287378255577108052488029)
              ·
                refine ⟨2357766845841415519683011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287378255577108052488029 2357766845841415519683011)
                ·
                  refine ⟨3536650268762123279524517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357766845841415519683011 3536650268762123279524517)
                  ·
                    refine ⟨663121925392898114910847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3536650268762123279524517 663121925392898114910847)
                    ·
                      rfl

theorem cell22_1937138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1937138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937138 prefixEnd_1937138 := by exact prefixLift 1937138
  have htrace : WordTrace (prefixWord ++ tailWord_1937138) baseStart_1937138 baseEnd_1937138 := by
    simpa [prefixWord, tailWord_1937138, baseEnd_1937138] using wordTrace_append hprefix tailTrace_1937138
  have hstable : (prefixWord ++ tailWord_1937138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937138).length < 2 ^ (prefixWord ++ tailWord_1937138).sum := by decide
  have hdescent : baseEnd_1937138 < baseStart_1937138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937140 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1937140 : Nat := 118140960795 + 1937140 * 2 ^ 59
def prefixEnd_1937140 : Nat := 4983230072969 + 3 ^ 40 * 1937140 * 2
def baseEnd_1937140 : Nat := 663122610033770776360841

theorem tailTrace_1937140 : CollatzResearch.WordTrace tailWord_1937140 prefixEnd_1937140 663122610033770776360841 := by
  unfold tailWord_1937140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35326650101040046008908437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47102200134720061345211249 35326650101040046008908437)
  ·
    refine ⟨1655936723486252156667583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35326650101040046008908437 1655936723486252156667583)
    ·
      refine ⟨2483905085229378235001375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655936723486252156667583 2483905085229378235001375)
      ·
        refine ⟨3725857627844067352502063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483905085229378235001375 3725857627844067352502063)
        ·
          refine ⟨5588786441766101028753095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725857627844067352502063 5588786441766101028753095)
          ·
            refine ⟨8383179662649151543129643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588786441766101028753095 8383179662649151543129643)
            ·
              refine ⟨12574769493973727314694465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383179662649151543129643 12574769493973727314694465)
              ·
                refine ⟨9431077120480295486020849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574769493973727314694465 9431077120480295486020849)
                ·
                  refine ⟨7073307840360221614515637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9431077120480295486020849 7073307840360221614515637)
                  ·
                    refine ⟨663122610033770776360841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7073307840360221614515637 663122610033770776360841)
                    ·
                      rfl

theorem cell22_1937140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1937140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937140 prefixEnd_1937140 := by exact prefixLift 1937140
  have htrace : WordTrace (prefixWord ++ tailWord_1937140) baseStart_1937140 baseEnd_1937140 := by
    simpa [prefixWord, tailWord_1937140, baseEnd_1937140] using wordTrace_append hprefix tailTrace_1937140
  have hstable : (prefixWord ++ tailWord_1937140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937140).length < 2 ^ (prefixWord ++ tailWord_1937140).sum := by decide
  have hdescent : baseEnd_1937140 < baseStart_1937140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937153 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 4]
def baseStart_1937153 : Nat := 118140960795 + 1937153 * 2 ^ 59
def prefixEnd_1937153 : Nat := 4983230072969 + 3 ^ 40 * 1937153 * 2
def baseEnd_1937153 : Nat := 221042353399814358595267

theorem tailTrace_1937153 : CollatzResearch.WordTrace tailWord_1937153 prefixEnd_1937153 221042353399814358595267 := by
  unfold tailWord_1937153
  simp only [CollatzResearch.WordTrace]
  refine ⟨70653774351032995238040113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47102516234021996825360075 70653774351032995238040113)
  ·
    refine ⟨52990330763274746428530085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70653774351032995238040113 52990330763274746428530085)
    ·
      refine ⟨9935687018114014955349391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52990330763274746428530085 9935687018114014955349391)
      ·
        refine ⟨14903530527171022433024087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935687018114014955349391 14903530527171022433024087)
        ·
          refine ⟨22355295790756533649536131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903530527171022433024087 22355295790756533649536131)
          ·
            refine ⟨33532943686134800474304197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22355295790756533649536131 33532943686134800474304197)
            ·
              refine ⟨6287426941150275088932037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33532943686134800474304197 6287426941150275088932037)
              ·
                refine ⟨1178892551465676579174757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6287426941150275088932037 1178892551465676579174757)
                ·
                  refine ⟨221042353399814358595267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178892551465676579174757 221042353399814358595267)
                  ·
                    rfl

theorem cell22_1937153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_1937153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937153 prefixEnd_1937153 := by exact prefixLift 1937153
  have htrace : WordTrace (prefixWord ++ tailWord_1937153) baseStart_1937153 baseEnd_1937153 := by
    simpa [prefixWord, tailWord_1937153, baseEnd_1937153] using wordTrace_append hprefix tailTrace_1937153
  have hstable : (prefixWord ++ tailWord_1937153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937153).length < 2 ^ (prefixWord ++ tailWord_1937153).sum := by decide
  have hdescent : baseEnd_1937153 < baseStart_1937153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937166 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1937166 : Nat := 118140960795 + 1937166 * 2 ^ 59
def prefixEnd_1937166 : Nat := 4983230072969 + 3 ^ 40 * 1937166 * 2
def baseEnd_1937166 : Nat := 663131510365115375210761

theorem tailTrace_1937166 : CollatzResearch.WordTrace tailWord_1937166 prefixEnd_1937166 663131510365115375210761 := by
  unfold tailWord_1937166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831781062498237307282919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47102832333323932305508901 8831781062498237307282919)
  ·
    refine ⟨13247671593747355960924379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8831781062498237307282919 13247671593747355960924379)
    ·
      refine ⟨19871507390621033941386569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247671593747355960924379 19871507390621033941386569)
      ·
        refine ⟨14903630542965775456039927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19871507390621033941386569 14903630542965775456039927)
        ·
          refine ⟨22355445814448663184059891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903630542965775456039927 22355445814448663184059891)
          ·
            refine ⟨33533168721672994776089837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22355445814448663184059891 33533168721672994776089837)
            ·
              refine ⟨12574938270627373041033689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33533168721672994776089837 12574938270627373041033689)
              ·
                refine ⟨9431203702970529780775267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574938270627373041033689 9431203702970529780775267)
                ·
                  refine ⟨14146805554455794671162901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431203702970529780775267 14146805554455794671162901)
                  ·
                    refine ⟨663131510365115375210761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14146805554455794671162901 663131510365115375210761)
                    ·
                      rfl

theorem cell22_1937166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1937166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937166 prefixEnd_1937166 := by exact prefixLift 1937166
  have htrace : WordTrace (prefixWord ++ tailWord_1937166) baseStart_1937166 baseEnd_1937166 := by
    simpa [prefixWord, tailWord_1937166, baseEnd_1937166] using wordTrace_append hprefix tailTrace_1937166
  have hstable : (prefixWord ++ tailWord_1937166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937166).length < 2 ^ (prefixWord ++ tailWord_1937166).sum := by decide
  have hdescent : baseEnd_1937166 < baseStart_1937166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937303 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1937303 : Nat := 118140960795 + 1937303 * 2 ^ 59
def prefixEnd_1937303 : Nat := 4983230072969 + 3 ^ 40 * 1937303 * 2
def baseEnd_1937303 : Nat := 663178408264892684535341

theorem tailTrace_1937303 : CollatzResearch.WordTrace tailWord_1937303 prefixEnd_1937303 663178408264892684535341 := by
  unfold tailWord_1937303
  simp only [CollatzResearch.WordTrace]
  refine ⟨70659245300489570856000563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47106163533659713904000375 70659245300489570856000563)
  ·
    refine ⟨105988867950734356284000845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70659245300489570856000563 105988867950734356284000845)
    ·
      refine ⟨39745825481525383606500317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105988867950734356284000845 39745825481525383606500317)
      ·
        refine ⟨14904684555572018852437619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39745825481525383606500317 14904684555572018852437619)
        ·
          refine ⟨22357026833358028278656429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904684555572018852437619 22357026833358028278656429)
          ·
            refine ⟨8383885062509260604496161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22357026833358028278656429 8383885062509260604496161)
            ·
              refine ⟨6287913796881945453372121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383885062509260604496161 6287913796881945453372121)
              ·
                refine ⟨4715935347661459090029091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287913796881945453372121 4715935347661459090029091)
                ·
                  refine ⟨7073903021492188635043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715935347661459090029091 7073903021492188635043637)
                  ·
                    refine ⟨663178408264892684535341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7073903021492188635043637 663178408264892684535341)
                    ·
                      rfl

theorem cell22_1937303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1937303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937303 prefixEnd_1937303 := by exact prefixLift 1937303
  have htrace : WordTrace (prefixWord ++ tailWord_1937303) baseStart_1937303 baseEnd_1937303 := by
    simpa [prefixWord, tailWord_1937303, baseEnd_1937303] using wordTrace_append hprefix tailTrace_1937303
  have hstable : (prefixWord ++ tailWord_1937303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937303).length < 2 ^ (prefixWord ++ tailWord_1937303).sum := by decide
  have hdescent : baseEnd_1937303 < baseStart_1937303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937337 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_1937337 : Nat := 118140960795 + 1937337 * 2 ^ 59
def prefixEnd_1937337 : Nat := 4983230072969 + 3 ^ 40 * 1937337 * 2
def baseEnd_1937337 : Nat := 663190047159727929185237

theorem tailTrace_1937337 : CollatzResearch.WordTrace tailWord_1937337 prefixEnd_1937337 663190047159727929185237 := by
  unfold tailWord_1937337
  simp only [CollatzResearch.WordTrace]
  refine ⟨70660485382366394662738265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47106990254910929775158843 70660485382366394662738265)
  ·
    refine ⟨52995364036774795997053699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70660485382366394662738265 52995364036774795997053699)
    ·
      refine ⟨79493046055162193995580549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52995364036774795997053699 79493046055162193995580549)
      ·
        refine ⟨14904946135342911374171353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79493046055162193995580549 14904946135342911374171353)
        ·
          refine ⟨11178709601507183530628515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904946135342911374171353 11178709601507183530628515)
          ·
            refine ⟨16768064402260775295942773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178709601507183530628515 16768064402260775295942773)
            ·
              refine ⟨1572006037711947683994635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16768064402260775295942773 1572006037711947683994635)
              ·
                refine ⟨2358009056567921525991953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572006037711947683994635 2358009056567921525991953)
                ·
                  refine ⟨1768506792425941144493965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358009056567921525991953 1768506792425941144493965)
                  ·
                    refine ⟨663190047159727929185237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768506792425941144493965 663190047159727929185237)
                    ·
                      rfl

theorem cell22_1937337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_1937337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937337 prefixEnd_1937337 := by exact prefixLift 1937337
  have htrace : WordTrace (prefixWord ++ tailWord_1937337) baseStart_1937337 baseEnd_1937337 := by
    simpa [prefixWord, tailWord_1937337, baseEnd_1937337] using wordTrace_append hprefix tailTrace_1937337
  have hstable : (prefixWord ++ tailWord_1937337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937337).length < 2 ^ (prefixWord ++ tailWord_1937337).sum := by decide
  have hdescent : baseEnd_1937337 < baseStart_1937337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937485 : List Nat := [1, 6, 1, 1, 1, 1, 11]
def baseStart_1937485 : Nat := 118140960795 + 1937485 * 2 ^ 59
def prefixEnd_1937485 : Nat := 4983230072969 + 3 ^ 40 * 1937485 * 2
def baseEnd_1937485 : Nat := 24564470762381662092029

theorem tailTrace_1937485 : CollatzResearch.WordTrace tailWord_1937485 prefixEnd_1937485 24564470762381662092029 := by
  unfold tailWord_1937485
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665883385830215939125909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47110588923886810626083939 70665883385830215939125909)
  ·
    refine ⟨3312463283710791372146527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70665883385830215939125909 3312463283710791372146527)
    ·
      refine ⟨4968694925566187058219791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312463283710791372146527 4968694925566187058219791)
      ·
        refine ⟨7453042388349280587329687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968694925566187058219791 7453042388349280587329687)
        ·
          refine ⟨11179563582523920880994531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453042388349280587329687 11179563582523920880994531)
          ·
            refine ⟨16769345373785881321491797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179563582523920880994531 16769345373785881321491797)
            ·
              refine ⟨24564470762381662092029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16769345373785881321491797 24564470762381662092029)
              ·
                rfl

theorem cell22_1937485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 11].length) (baseStart_1937485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937485 prefixEnd_1937485 := by exact prefixLift 1937485
  have htrace : WordTrace (prefixWord ++ tailWord_1937485) baseStart_1937485 baseEnd_1937485 := by
    simpa [prefixWord, tailWord_1937485, baseEnd_1937485] using wordTrace_append hprefix tailTrace_1937485
  have hstable : (prefixWord ++ tailWord_1937485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937485).length < 2 ^ (prefixWord ++ tailWord_1937485).sum := by decide
  have hdescent : baseEnd_1937485 < baseStart_1937485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937506 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1937506 : Nat := 118140960795 + 1937506 * 2 ^ 59
def prefixEnd_1937506 : Nat := 4983230072969 + 3 ^ 40 * 1937506 * 2
def baseEnd_1937506 : Nat := 663247899313467821709719

theorem tailTrace_1937506 : CollatzResearch.WordTrace tailWord_1937506 prefixEnd_1937506 663247899313467821709719 := by
  unfold tailWord_1937506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666662329688534131410093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47111099545836091017093581 17666662329688534131410093)
  ·
    refine ⟨6624998373633200299278785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17666662329688534131410093 6624998373633200299278785)
    ·
      refine ⟨4968748780224900224459089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6624998373633200299278785 4968748780224900224459089)
      ·
        refine ⟨3726561585168675168344317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4968748780224900224459089 3726561585168675168344317)
        ·
          refine ⟨1397460594438253188129119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3726561585168675168344317 1397460594438253188129119)
          ·
            refine ⟨2096190891657379782193679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397460594438253188129119 2096190891657379782193679)
            ·
              refine ⟨3144286337486069673290519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096190891657379782193679 3144286337486069673290519)
              ·
                refine ⟨4716429506229104509935779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144286337486069673290519 4716429506229104509935779)
                ·
                  refine ⟨7074644259343656764903669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716429506229104509935779 7074644259343656764903669)
                  ·
                    refine ⟨663247899313467821709719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7074644259343656764903669 663247899313467821709719)
                    ·
                      rfl

theorem cell22_1937506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1937506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937506 prefixEnd_1937506 := by exact prefixLift 1937506
  have htrace : WordTrace (prefixWord ++ tailWord_1937506) baseStart_1937506 baseEnd_1937506 := by
    simpa [prefixWord, tailWord_1937506, baseEnd_1937506] using wordTrace_append hprefix tailTrace_1937506
  have hstable : (prefixWord ++ tailWord_1937506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937506).length < 2 ^ (prefixWord ++ tailWord_1937506).sum := by decide
  have hdescent : baseEnd_1937506 < baseStart_1937506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937517 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1937517 : Nat := 118140960795 + 1937517 * 2 ^ 59
def prefixEnd_1937517 : Nat := 4983230072969 + 3 ^ 40 * 1937517 * 2
def baseEnd_1937517 : Nat := 663251664838267459684685

theorem tailTrace_1937517 : CollatzResearch.WordTrace tailWord_1937517 prefixEnd_1937517 663251664838267459684685 := by
  unfold tailWord_1937517
  simp only [CollatzResearch.WordTrace]
  refine ⟨70667050521714285404290805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47111367014476190269527203 70667050521714285404290805)
  ·
    refine ⟨6625035986410714256652263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70667050521714285404290805 6625035986410714256652263)
    ·
      refine ⟨9937553979616071384978395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625035986410714256652263 9937553979616071384978395)
      ·
        refine ⟨14906330969424107077467593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937553979616071384978395 14906330969424107077467593)
        ·
          refine ⟨11179748227068080308100695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14906330969424107077467593 11179748227068080308100695)
          ·
            refine ⟨16769622340602120462151043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179748227068080308100695 16769622340602120462151043)
            ·
              refine ⟨25154433510903180693226565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16769622340602120462151043 25154433510903180693226565)
              ·
                refine ⟨4716456283294346379979981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25154433510903180693226565 4716456283294346379979981)
                ·
                  refine ⟨1768671106235379892492493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4716456283294346379979981 1768671106235379892492493)
                  ·
                    refine ⟨663251664838267459684685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768671106235379892492493 663251664838267459684685)
                    ·
                      rfl

theorem cell22_1937517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1937517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937517 prefixEnd_1937517 := by exact prefixLift 1937517
  have htrace : WordTrace (prefixWord ++ tailWord_1937517) baseStart_1937517 baseEnd_1937517 := by
    simpa [prefixWord, tailWord_1937517, baseEnd_1937517] using wordTrace_append hprefix tailTrace_1937517
  have hstable : (prefixWord ++ tailWord_1937517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937517).length < 2 ^ (prefixWord ++ tailWord_1937517).sum := by decide
  have hdescent : baseEnd_1937517 < baseStart_1937517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937592 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_1937592 : Nat := 118140960795 + 1937592 * 2 ^ 59
def prefixEnd_1937592 : Nat := 4983230072969 + 3 ^ 40 * 1937592 * 2
def baseEnd_1937592 : Nat := 221092446290330754686485

theorem tailTrace_1937592 : CollatzResearch.WordTrace tailWord_1937592 prefixEnd_1937592 221092446290330754686485 := by
  unfold tailWord_1937592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35334892998221286606635515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47113190664295048808847353 35334892998221286606635515)
  ·
    refine ⟨53002339497331929909953273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35334892998221286606635515 53002339497331929909953273)
    ·
      refine ⟨39751754622998947432464955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53002339497331929909953273 39751754622998947432464955)
      ·
        refine ⟨59627631934498421148697433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39751754622998947432464955 59627631934498421148697433)
        ·
          refine ⟨44720723950873815861523075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59627631934498421148697433 44720723950873815861523075)
          ·
            refine ⟨67081085926310723792284613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44720723950873815861523075 67081085926310723792284613)
            ·
              refine ⟨12577703611183260711053365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67081085926310723792284613 12577703611183260711053365)
              ·
                refine ⟨1179159713548430691661253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12577703611183260711053365 1179159713548430691661253)
                ·
                  refine ⟨221092446290330754686485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179159713548430691661253 221092446290330754686485)
                  ·
                    rfl

theorem cell22_1937592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_1937592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937592 prefixEnd_1937592 := by exact prefixLift 1937592
  have htrace : WordTrace (prefixWord ++ tailWord_1937592) baseStart_1937592 baseEnd_1937592 := by
    simpa [prefixWord, tailWord_1937592, baseEnd_1937592] using wordTrace_append hprefix tailTrace_1937592
  have hstable : (prefixWord ++ tailWord_1937592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937592).length < 2 ^ (prefixWord ++ tailWord_1937592).sum := by decide
  have hdescent : baseEnd_1937592 < baseStart_1937592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937602 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1937602 : Nat := 118140960795 + 1937602 * 2 ^ 59
def prefixEnd_1937602 : Nat := 4983230072969 + 3 ^ 40 * 1937602 * 2
def baseEnd_1937602 : Nat := 663280762075355571309425

theorem tailTrace_1937602 : CollatzResearch.WordTrace tailWord_1937602 prefixEnd_1937602 663280762075355571309425 := by
  unfold tailWord_1937602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667537681601586230283765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47113433817604229947423373 17667537681601586230283765)
  ·
    refine ⟨1656331657650148709089103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17667537681601586230283765 1656331657650148709089103)
    ·
      refine ⟨2484497486475223063633655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656331657650148709089103 2484497486475223063633655)
      ·
        refine ⟨3726746229712834595450483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484497486475223063633655 3726746229712834595450483)
        ·
          refine ⟨5590119344569251893175725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726746229712834595450483 5590119344569251893175725)
          ·
            refine ⟨2096294754213469459940897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5590119344569251893175725 2096294754213469459940897)
            ·
              refine ⟨1572221065660102094955673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096294754213469459940897 1572221065660102094955673)
              ·
                refine ⟨1179165799245076571216755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572221065660102094955673 1179165799245076571216755)
                ·
                  refine ⟨1768748698867614856825133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179165799245076571216755 1768748698867614856825133)
                  ·
                    refine ⟨663280762075355571309425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768748698867614856825133 663280762075355571309425)
                    ·
                      rfl

theorem cell22_1937602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1937602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937602 prefixEnd_1937602 := by exact prefixLift 1937602
  have htrace : WordTrace (prefixWord ++ tailWord_1937602) baseStart_1937602 baseEnd_1937602 := by
    simpa [prefixWord, tailWord_1937602, baseEnd_1937602] using wordTrace_append hprefix tailTrace_1937602
  have hstable : (prefixWord ++ tailWord_1937602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937602).length < 2 ^ (prefixWord ++ tailWord_1937602).sum := by decide
  have hdescent : baseEnd_1937602 < baseStart_1937602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937624 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_1937624 : Nat := 118140960795 + 1937624 * 2 ^ 59
def prefixEnd_1937624 : Nat := 4983230072969 + 3 ^ 40 * 1937624 * 2
def baseEnd_1937624 : Nat := 663288293124954847259357

theorem tailTrace_1937624 : CollatzResearch.WordTrace tailWord_1937624 prefixEnd_1937624 663288293124954847259357 := by
  unfold tailWord_1937624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35335476566163321339217963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47113968754884428452290617 35335476566163321339217963)
  ·
    refine ⟨53003214849244982008826945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35335476566163321339217963 53003214849244982008826945)
    ·
      refine ⟨39752411136933736506620209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53003214849244982008826945 39752411136933736506620209)
      ·
        refine ⟨29814308352700302379965157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39752411136933736506620209 29814308352700302379965157)
        ·
          refine ⟨5590182816131306696243467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29814308352700302379965157 5590182816131306696243467)
          ·
            refine ⟨8385274224196960044365201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590182816131306696243467 8385274224196960044365201)
            ·
              refine ⟨6288955668147720033273901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385274224196960044365201 6288955668147720033273901)
              ·
                refine ⟨2358358375555395012477713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6288955668147720033273901 2358358375555395012477713)
                ·
                  refine ⟨1768768781666546259358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358358375555395012477713 1768768781666546259358285)
                  ·
                    refine ⟨663288293124954847259357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768768781666546259358285 663288293124954847259357)
                    ·
                      rfl

theorem cell22_1937624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_1937624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937624 prefixEnd_1937624 := by exact prefixLift 1937624
  have htrace : WordTrace (prefixWord ++ tailWord_1937624) baseStart_1937624 baseEnd_1937624 := by
    simpa [prefixWord, tailWord_1937624, baseEnd_1937624] using wordTrace_append hprefix tailTrace_1937624
  have hstable : (prefixWord ++ tailWord_1937624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937624).length < 2 ^ (prefixWord ++ tailWord_1937624).sum := by decide
  have hdescent : baseEnd_1937624 < baseStart_1937624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937639 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1937639 : Nat := 118140960795 + 1937639 * 2 ^ 59
def prefixEnd_1937639 : Nat := 4983230072969 + 3 ^ 40 * 1937639 * 2
def baseEnd_1937639 : Nat := 663293427931499808134311

theorem tailTrace_1937639 : CollatzResearch.WordTrace tailWord_1937639 prefixEnd_1937639 663293427931499808134311 := by
  unfold tailWord_1937639
  simp only [CollatzResearch.WordTrace]
  refine ⟨70671500227272300240231971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47114333484848200160154647 70671500227272300240231971)
  ·
    refine ⟨106007250340908450360347957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70671500227272300240231971 106007250340908450360347957)
    ·
      refine ⟨9938179719460167221282621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106007250340908450360347957 9938179719460167221282621)
      ·
        refine ⟨3726817394797562707980983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9938179719460167221282621 3726817394797562707980983)
        ·
          refine ⟨5590226092196344061971475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726817394797562707980983 5590226092196344061971475)
          ·
            refine ⟨8385339138294516092957213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590226092196344061971475 8385339138294516092957213)
            ·
              refine ⟨3144502176860443534858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8385339138294516092957213 3144502176860443534858955)
              ·
                refine ⟨4716753265290665302288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144502176860443534858955 4716753265290665302288433)
                ·
                  refine ⟨3537564948967998976716325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716753265290665302288433 3537564948967998976716325)
                  ·
                    refine ⟨663293427931499808134311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537564948967998976716325 663293427931499808134311)
                    ·
                      rfl

theorem cell22_1937639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1937639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937639 prefixEnd_1937639 := by exact prefixLift 1937639
  have htrace : WordTrace (prefixWord ++ tailWord_1937639) baseStart_1937639 baseEnd_1937639 := by
    simpa [prefixWord, tailWord_1937639, baseEnd_1937639] using wordTrace_append hprefix tailTrace_1937639
  have hstable : (prefixWord ++ tailWord_1937639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937639).length < 2 ^ (prefixWord ++ tailWord_1937639).sum := by decide
  have hdescent : baseEnd_1937639 < baseStart_1937639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937772 : List Nat := [2, 2, 1, 1, 6, 10]
def baseStart_1937772 : Nat := 118140960795 + 1937772 * 2 ^ 59
def prefixEnd_1937772 : Nat := 4983230072969 + 3 ^ 40 * 1937772 * 2
def baseEnd_1937772 : Nat := 8189369833944836969863

theorem tailTrace_1937772 : CollatzResearch.WordTrace tailWord_1937772 prefixEnd_1937772 8189369833944836969863 := by
  unfold tailWord_1937772
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338175567895231977411785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47117567423860309303215713 35338175567895231977411785)
  ·
    refine ⟨26503631675921423983058839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35338175567895231977411785 26503631675921423983058839)
    ·
      refine ⟨39755447513882135974588259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26503631675921423983058839 39755447513882135974588259)
      ·
        refine ⟨59633171270823203961882389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39755447513882135974588259 59633171270823203961882389)
        ·
          refine ⟨2795304903319837685713237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59633171270823203961882389 2795304903319837685713237)
          ·
            refine ⟨8189369833944836969863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2795304903319837685713237 8189369833944836969863)
            ·
              rfl

theorem cell22_1937772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 10].length) (baseStart_1937772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937772 prefixEnd_1937772 := by exact prefixLift 1937772
  have htrace : WordTrace (prefixWord ++ tailWord_1937772) baseStart_1937772 baseEnd_1937772 := by
    simpa [prefixWord, tailWord_1937772, baseEnd_1937772] using wordTrace_append hprefix tailTrace_1937772
  have hstable : (prefixWord ++ tailWord_1937772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937772).length < 2 ^ (prefixWord ++ tailWord_1937772).sum := by decide
  have hdescent : baseEnd_1937772 < baseStart_1937772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937776 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_1937776 : Nat := 118140960795 + 1937776 * 2 ^ 59
def prefixEnd_1937776 : Nat := 4983230072969 + 3 ^ 40 * 1937776 * 2
def baseEnd_1937776 : Nat := 663340325831277117458891

theorem tailTrace_1937776 : CollatzResearch.WordTrace tailWord_1937776 prefixEnd_1937776 663340325831277117458891 := by
  unfold tailWord_1937776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338248513887986318984591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47117664685183981758646121 35338248513887986318984591)
  ·
    refine ⟨53007372770831979478476887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35338248513887986318984591 53007372770831979478476887)
    ·
      refine ⟨79511059156247969217715331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53007372770831979478476887 79511059156247969217715331)
      ·
        refine ⟨119266588734371953826572997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79511059156247969217715331 119266588734371953826572997)
        ·
          refine ⟨22362485387694741342482437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119266588734371953826572997 22362485387694741342482437)
          ·
            refine ⟨4192966010192764001715457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22362485387694741342482437 4192966010192764001715457)
            ·
              refine ⟨3144724507644573001286593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192966010192764001715457 3144724507644573001286593)
              ·
                refine ⟨2358543380733429750964945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144724507644573001286593 2358543380733429750964945)
                ·
                  refine ⟨1768907535550072313223709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358543380733429750964945 1768907535550072313223709)
                  ·
                    refine ⟨663340325831277117458891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768907535550072313223709 663340325831277117458891)
                    ·
                      rfl

theorem cell22_1937776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_1937776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937776 prefixEnd_1937776 := by exact prefixLift 1937776
  have htrace : WordTrace (prefixWord ++ tailWord_1937776) baseStart_1937776 baseEnd_1937776 := by
    simpa [prefixWord, tailWord_1937776, baseEnd_1937776] using wordTrace_append hprefix tailTrace_1937776
  have hstable : (prefixWord ++ tailWord_1937776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937776).length < 2 ^ (prefixWord ++ tailWord_1937776).sum := by decide
  have hdescent : baseEnd_1937776 < baseStart_1937776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937778 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1937778 : Nat := 118140960795 + 1937778 * 2 ^ 59
def prefixEnd_1937778 : Nat := 4983230072969 + 3 ^ 40 * 1937778 * 2
def baseEnd_1937778 : Nat := 221113670157383259636295

theorem tailTrace_1937778 : CollatzResearch.WordTrace tailWord_1937778 prefixEnd_1937778 221113670157383259636295 := by
  unfold tailWord_1937778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669142493442181744885497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47117713315845817986361325 17669142493442181744885497)
  ·
    refine ⟨13251856870081636308664123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17669142493442181744885497 13251856870081636308664123)
    ·
      refine ⟨19877785305122454462996185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251856870081636308664123 19877785305122454462996185)
      ·
        refine ⟨14908338978841840847247139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19877785305122454462996185 14908338978841840847247139)
        ·
          refine ⟨22362508468262761270870709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908338978841840847247139 22362508468262761270870709)
          ·
            refine ⟨2096485168899633869144129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22362508468262761270870709 2096485168899633869144129)
            ·
              refine ⟨1572363876674725401858097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096485168899633869144129 1572363876674725401858097)
              ·
                refine ⟨1179272907506044051393573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572363876674725401858097 1179272907506044051393573)
                ·
                  refine ⟨221113670157383259636295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179272907506044051393573 221113670157383259636295)
                  ·
                    rfl

theorem cell22_1937778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1937778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937778 prefixEnd_1937778 := by exact prefixLift 1937778
  have htrace : WordTrace (prefixWord ++ tailWord_1937778) baseStart_1937778 baseEnd_1937778 := by
    simpa [prefixWord, tailWord_1937778, baseEnd_1937778] using wordTrace_append hprefix tailTrace_1937778
  have hstable : (prefixWord ++ tailWord_1937778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937778).length < 2 ^ (prefixWord ++ tailWord_1937778).sum := by decide
  have hdescent : baseEnd_1937778 < baseStart_1937778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937789 : List Nat := [1, 4, 1, 1, 2, 5, 1, 7]
def baseStart_1937789 : Nat := 118140960795 + 1937789 * 2 ^ 59
def prefixEnd_1937789 : Nat := 4983230072969 + 3 ^ 40 * 1937789 * 2
def baseEnd_1937789 : Nat := 73704975110772157431539

theorem tailTrace_1937789 : CollatzResearch.WordTrace tailWord_1937789 prefixEnd_1937789 73704975110772157431539 := by
  unfold tailWord_1937789
  simp only [CollatzResearch.WordTrace]
  refine ⟨70676971176728875858192421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47117980784485917238794947 70676971176728875858192421)
  ·
    refine ⟨13251932095636664223411079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70676971176728875858192421 13251932095636664223411079)
    ·
      refine ⟨19877898143454996335116619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251932095636664223411079 19877898143454996335116619)
      ·
        refine ⟨29816847215182494502674929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877898143454996335116619 29816847215182494502674929)
        ·
          refine ⟨22362635411386870877006197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816847215182494502674929 22362635411386870877006197)
          ·
            refine ⟨2096497069817519144719331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22362635411386870877006197 2096497069817519144719331)
            ·
              refine ⟨3144745604726278717078997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096497069817519144719331 3144745604726278717078997)
              ·
                refine ⟨73704975110772157431539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3144745604726278717078997 73704975110772157431539)
                ·
                  rfl

theorem cell22_1937789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 7].length) (baseStart_1937789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937789 prefixEnd_1937789 := by exact prefixLift 1937789
  have htrace : WordTrace (prefixWord ++ tailWord_1937789) baseStart_1937789 baseEnd_1937789 := by
    simpa [prefixWord, tailWord_1937789, baseEnd_1937789] using wordTrace_append hprefix tailTrace_1937789
  have hstable : (prefixWord ++ tailWord_1937789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937789).length < 2 ^ (prefixWord ++ tailWord_1937789).sum := by decide
  have hdescent : baseEnd_1937789 < baseStart_1937789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937804 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_1937804 : Nat := 118140960795 + 1937804 * 2 ^ 59
def prefixEnd_1937804 : Nat := 4983230072969 + 3 ^ 40 * 1937804 * 2
def baseEnd_1937804 : Nat := 663349910803494377758805

theorem tailTrace_1937804 : CollatzResearch.WordTrace tailWord_1937804 prefixEnd_1937804 663349910803494377758805 := by
  unfold tailWord_1937804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338759135837266709994233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47118345514449688946658977 35338759135837266709994233)
  ·
    refine ⟨26504069351877950032495675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35338759135837266709994233 26504069351877950032495675)
    ·
      refine ⟨39756104027816925048743513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26504069351877950032495675 39756104027816925048743513)
      ·
        refine ⟨29817078020862693786557635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39756104027816925048743513 29817078020862693786557635)
        ·
          refine ⟨44725617031294040679836453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29817078020862693786557635 44725617031294040679836453)
          ·
            refine ⟨8386053193367632627469335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44725617031294040679836453 8386053193367632627469335)
            ·
              refine ⟨12579079790051448941204003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386053193367632627469335 12579079790051448941204003)
              ·
                refine ⟨18868619685077173411806005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579079790051448941204003 18868619685077173411806005)
                ·
                  refine ⟨1768933095475985007356813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18868619685077173411806005 1768933095475985007356813)
                  ·
                    refine ⟨663349910803494377758805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768933095475985007356813 663349910803494377758805)
                    ·
                      rfl

theorem cell22_1937804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_1937804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937804 prefixEnd_1937804 := by exact prefixLift 1937804
  have htrace : WordTrace (prefixWord ++ tailWord_1937804) baseStart_1937804 baseEnd_1937804 := by
    simpa [prefixWord, tailWord_1937804, baseEnd_1937804] using wordTrace_append hprefix tailTrace_1937804
  have hstable : (prefixWord ++ tailWord_1937804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937804).length < 2 ^ (prefixWord ++ tailWord_1937804).sum := by decide
  have hdescent : baseEnd_1937804 < baseStart_1937804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937806 : List Nat := [4, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1937806 : Nat := 118140960795 + 1937806 * 2 ^ 59
def prefixEnd_1937806 : Nat := 4983230072969 + 3 ^ 40 * 1937806 * 2
def baseEnd_1937806 : Nat := 73705621716040782134311

theorem tailTrace_1937806 : CollatzResearch.WordTrace tailWord_1937806 prefixEnd_1937806 73705621716040782134311 := by
  unfold tailWord_1937806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834698902208410970195159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47118394145111525174374181 8834698902208410970195159)
  ·
    refine ⟨13252048353312616455292739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834698902208410970195159 13252048353312616455292739)
    ·
      refine ⟨19878072529968924682939109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13252048353312616455292739 19878072529968924682939109)
      ·
        refine ⟨3727138599369173378051083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19878072529968924682939109 3727138599369173378051083)
        ·
          refine ⟨5590707899053760067076625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727138599369173378051083 5590707899053760067076625)
          ·
            refine ⟨4193030924290320050307469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590707899053760067076625 4193030924290320050307469)
            ·
              refine ⟨1572386596608870018865301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4193030924290320050307469 1572386596608870018865301)
              ·
                refine ⟨73705621716040782134311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1572386596608870018865301 73705621716040782134311)
                ·
                  rfl

theorem cell22_1937806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1937806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937806 prefixEnd_1937806 := by exact prefixLift 1937806
  have htrace : WordTrace (prefixWord ++ tailWord_1937806) baseStart_1937806 baseEnd_1937806 := by
    simpa [prefixWord, tailWord_1937806, baseEnd_1937806] using wordTrace_append hprefix tailTrace_1937806
  have hstable : (prefixWord ++ tailWord_1937806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937806).length < 2 ^ (prefixWord ++ tailWord_1937806).sum := by decide
  have hdescent : baseEnd_1937806 < baseStart_1937806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937814 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1937814 : Nat := 118140960795 + 1937814 * 2 ^ 59
def prefixEnd_1937814 : Nat := 4983230072969 + 3 ^ 40 * 1937814 * 2
def baseEnd_1937814 : Nat := 663353334007857685008775

theorem tailTrace_1937814 : CollatzResearch.WordTrace tailWord_1937814 prefixEnd_1937814 663353334007857685008775 := by
  unfold tailWord_1937814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417367687602394070490781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47118588667758870085234997 4417367687602394070490781)
  ·
    refine ⟨1656512882850897776434043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4417367687602394070490781 1656512882850897776434043)
    ·
      refine ⟨2484769324276346664651065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656512882850897776434043 2484769324276346664651065)
      ·
        refine ⟨1863576993207259998488299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484769324276346664651065 1863576993207259998488299)
        ·
          refine ⟨2795365489810889997732449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863576993207259998488299 2795365489810889997732449)
          ·
            refine ⟨2096524117358167498299337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795365489810889997732449 2096524117358167498299337)
            ·
              refine ⟨1572393088018625623724503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096524117358167498299337 1572393088018625623724503)
              ·
                refine ⟨2358589632027938435586755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572393088018625623724503 2358589632027938435586755)
                ·
                  refine ⟨3537884448041907653380133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358589632027938435586755 3537884448041907653380133)
                  ·
                    refine ⟨663353334007857685008775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537884448041907653380133 663353334007857685008775)
                    ·
                      rfl

theorem cell22_1937814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1937814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937814 prefixEnd_1937814 := by exact prefixLift 1937814
  have htrace : WordTrace (prefixWord ++ tailWord_1937814) baseStart_1937814 baseEnd_1937814 := by
    simpa [prefixWord, tailWord_1937814, baseEnd_1937814] using wordTrace_append hprefix tailTrace_1937814
  have hstable : (prefixWord ++ tailWord_1937814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937814).length < 2 ^ (prefixWord ++ tailWord_1937814).sum := by decide
  have hdescent : baseEnd_1937814 < baseStart_1937814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937817 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 7]
def baseStart_1937817 : Nat := 118140960795 + 1937817 * 2 ^ 59
def prefixEnd_1937817 : Nat := 4983230072969 + 3 ^ 40 * 1937817 * 2
def baseEnd_1937817 : Nat := 221118120323055559061255

theorem tailTrace_1937817 : CollatzResearch.WordTrace tailWord_1937817 prefixEnd_1937817 221118120323055559061255 := by
  unfold tailWord_1937817
  simp only [CollatzResearch.WordTrace]
  refine ⟨70677992420627436640211705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47118661613751624426807803 70677992420627436640211705)
  ·
    refine ⟨53008494315470577480158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70677992420627436640211705 53008494315470577480158779)
    ·
      refine ⟨79512741473205866220238169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53008494315470577480158779 79512741473205866220238169)
      ·
        refine ⟨59634556104904399665178627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79512741473205866220238169 59634556104904399665178627)
        ·
          refine ⟨89451834157356599497767941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59634556104904399665178627 89451834157356599497767941)
          ·
            refine ⟨16772218904504362405831489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89451834157356599497767941 16772218904504362405831489)
            ·
              refine ⟨12579164178378271804373617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16772218904504362405831489 12579164178378271804373617)
              ·
                refine ⟨9434373133783703853280213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579164178378271804373617 9434373133783703853280213)
                ·
                  refine ⟨221118120323055559061255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9434373133783703853280213 221118120323055559061255)
                  ·
                    rfl

theorem cell22_1937817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_1937817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937817 prefixEnd_1937817 := by exact prefixLift 1937817
  have htrace : WordTrace (prefixWord ++ tailWord_1937817) baseStart_1937817 baseEnd_1937817 := by
    simpa [prefixWord, tailWord_1937817, baseEnd_1937817] using wordTrace_append hprefix tailTrace_1937817
  have hstable : (prefixWord ++ tailWord_1937817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937817).length < 2 ^ (prefixWord ++ tailWord_1937817).sum := by decide
  have hdescent : baseEnd_1937817 < baseStart_1937817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937849 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1937849 : Nat := 118140960795 + 1937849 * 2 ^ 59
def prefixEnd_1937849 : Nat := 4983230072969 + 3 ^ 40 * 1937849 * 2
def baseEnd_1937849 : Nat := 663365315223129260383667

theorem tailTrace_1937849 : CollatzResearch.WordTrace tailWord_1937849 prefixEnd_1937849 663365315223129260383667 := by
  unfold tailWord_1937849
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679159556511506105376601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47119439704341004070251067 70679159556511506105376601)
  ·
    refine ⟨53009369667383629579032451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70679159556511506105376601 53009369667383629579032451)
    ·
      refine ⟨79514054501075444368548677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53009369667383629579032451 79514054501075444368548677)
      ·
        refine ⟨14908885218951645819102877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79514054501075444368548677 14908885218951645819102877)
        ·
          refine ⟨5590831957106867182163579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14908885218951645819102877 5590831957106867182163579)
          ·
            refine ⟨8386247935660300773245369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590831957106867182163579 8386247935660300773245369)
            ·
              refine ⟨6289685951745225579934027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8386247935660300773245369 6289685951745225579934027)
              ·
                refine ⟨9434528927617838369901041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289685951745225579934027 9434528927617838369901041)
                ·
                  refine ⟨7075896695713378777425781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434528927617838369901041 7075896695713378777425781)
                  ·
                    refine ⟨663365315223129260383667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7075896695713378777425781 663365315223129260383667)
                    ·
                      rfl

theorem cell22_1937849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1937849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937849 prefixEnd_1937849 := by exact prefixLift 1937849
  have htrace : WordTrace (prefixWord ++ tailWord_1937849) baseStart_1937849 baseEnd_1937849 := by
    simpa [prefixWord, tailWord_1937849, baseEnd_1937849] using wordTrace_append hprefix tailTrace_1937849
  have hstable : (prefixWord ++ tailWord_1937849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937849).length < 2 ^ (prefixWord ++ tailWord_1937849).sum := by decide
  have hdescent : baseEnd_1937849 < baseStart_1937849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937857 : List Nat := [1, 2, 7, 1, 2, 1, 2, 6]
def baseStart_1937857 : Nat := 118140960795 + 1937857 * 2 ^ 59
def prefixEnd_1937857 : Nat := 4983230072969 + 3 ^ 40 * 1937857 * 2
def baseEnd_1937857 : Nat := 73707561531846656242627

theorem tailTrace_1937857 : CollatzResearch.WordTrace tailWord_1937857 prefixEnd_1937857 73707561531846656242627 := by
  unfold tailWord_1937857
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679451340482523471667825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47119634226988348981111883 70679451340482523471667825)
  ·
    refine ⟨53009588505361892603750869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70679451340482523471667825 53009588505361892603750869)
    ·
      refine ⟨1242412230594419357900411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53009588505361892603750869 1242412230594419357900411)
      ·
        refine ⟨1863618345891629036850617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242412230594419357900411 1863618345891629036850617)
        ·
          refine ⟨1397713759418721777637963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863618345891629036850617 1397713759418721777637963)
          ·
            refine ⟨2096570639128082666456945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397713759418721777637963 2096570639128082666456945)
            ·
              refine ⟨1572427979346061999842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096570639128082666456945 1572427979346061999842709)
              ·
                refine ⟨73707561531846656242627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1572427979346061999842709 73707561531846656242627)
                ·
                  rfl

theorem cell22_1937857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 6].length) (baseStart_1937857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937857 prefixEnd_1937857 := by exact prefixLift 1937857
  have htrace : WordTrace (prefixWord ++ tailWord_1937857) baseStart_1937857 baseEnd_1937857 := by
    simpa [prefixWord, tailWord_1937857, baseEnd_1937857] using wordTrace_append hprefix tailTrace_1937857
  have hstable : (prefixWord ++ tailWord_1937857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937857).length < 2 ^ (prefixWord ++ tailWord_1937857).sum := by decide
  have hdescent : baseEnd_1937857 < baseStart_1937857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937896 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_1937896 : Nat := 118140960795 + 1937896 * 2 ^ 59
def prefixEnd_1937896 : Nat := 4983230072969 + 3 ^ 40 * 1937896 * 2
def baseEnd_1937896 : Nat := 221127134761212268152841

theorem tailTrace_1937896 : CollatzResearch.WordTrace tailWord_1937896 prefixEnd_1937896 221127134761212268152841 := by
  unfold tailWord_1937896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340436893670616566168771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47120582524894155421558361 35340436893670616566168771)
  ·
    refine ⟨53010655340505924849253157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35340436893670616566168771 53010655340505924849253157)
    ·
      refine ⟨9939497876344860909234967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53010655340505924849253157 9939497876344860909234967)
      ·
        refine ⟨14909246814517291363852451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939497876344860909234967 14909246814517291363852451)
        ·
          refine ⟨22363870221775937045778677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14909246814517291363852451 22363870221775937045778677)
          ·
            refine ⟨2096612833291494098041751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22363870221775937045778677 2096612833291494098041751)
            ·
              refine ⟨3144919249937241147062627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096612833291494098041751 3144919249937241147062627)
              ·
                refine ⟨4717378874905861720593941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144919249937241147062627 4717378874905861720593941)
                ·
                  refine ⟨221127134761212268152841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4717378874905861720593941 221127134761212268152841)
                  ·
                    rfl

theorem cell22_1937896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_1937896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1937896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1937896 prefixEnd_1937896 := by exact prefixLift 1937896
  have htrace : WordTrace (prefixWord ++ tailWord_1937896) baseStart_1937896 baseEnd_1937896 := by
    simpa [prefixWord, tailWord_1937896, baseEnd_1937896] using wordTrace_append hprefix tailTrace_1937896
  have hstable : (prefixWord ++ tailWord_1937896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937896).length < 2 ^ (prefixWord ++ tailWord_1937896).sum := by decide
  have hdescent : baseEnd_1937896 < baseStart_1937896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938048 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_1938048 : Nat := 118140960795 + 1938048 * 2 ^ 59
def prefixEnd_1938048 : Nat := 4983230072969 + 3 ^ 40 * 1938048 * 2
def baseEnd_1938048 : Nat := 221144478996653024886019

theorem tailTrace_1938048 : CollatzResearch.WordTrace tailWord_1938048 prefixEnd_1938048 221144478996653024886019 := by
  unfold tailWord_1938048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343208841395281545935399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47124278455193708727913865 35343208841395281545935399)
  ·
    refine ⟨53014813262092922318903099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35343208841395281545935399 53014813262092922318903099)
    ·
      refine ⟨79522219893139383478354649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53014813262092922318903099 79522219893139383478354649)
      ·
        refine ⟨59641664919854537608765987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79522219893139383478354649 59641664919854537608765987)
        ·
          refine ⟨89462497379781806413148981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59641664919854537608765987 89462497379781806413148981)
          ·
            refine ⟨8387109129354544351232717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89462497379781806413148981 8387109129354544351232717)
            ·
              refine ⟨3145165923507954131712269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8387109129354544351232717 3145165923507954131712269)
              ·
                refine ⟨1179437221315482799392101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3145165923507954131712269 1179437221315482799392101)
                ·
                  refine ⟨221144478996653024886019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179437221315482799392101 221144478996653024886019)
                  ·
                    rfl

theorem cell22_1938048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_1938048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938048 prefixEnd_1938048 := by exact prefixLift 1938048
  have htrace : WordTrace (prefixWord ++ tailWord_1938048) baseStart_1938048 baseEnd_1938048 := by
    simpa [prefixWord, tailWord_1938048, baseEnd_1938048] using wordTrace_append hprefix tailTrace_1938048
  have hstable : (prefixWord ++ tailWord_1938048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938048).length < 2 ^ (prefixWord ++ tailWord_1938048).sum := by decide
  have hdescent : baseEnd_1938048 < baseStart_1938048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938076 : List Nat := [2, 2, 3, 2, 2, 1, 1, 9]
def baseStart_1938076 : Nat := 118140960795 + 1938076 * 2 ^ 59
def prefixEnd_1938076 : Nat := 4983230072969 + 3 ^ 40 * 1938076 * 2
def baseEnd_1938076 : Nat := 73715891329130703884219

theorem tailTrace_1938076 : CollatzResearch.WordTrace tailWord_1938076 prefixEnd_1938076 73715891329130703884219 := by
  unfold tailWord_1938076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343719463344561936945041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47124959284459415915926721 35343719463344561936945041)
  ·
    refine ⟨26507789597508421452708781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35343719463344561936945041 26507789597508421452708781)
    ·
      refine ⟨9940421099065658044765793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26507789597508421452708781 9940421099065658044765793)
      ·
        refine ⟨7455315824299243533574345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9940421099065658044765793 7455315824299243533574345)
        ·
          refine ⟨5591486868224432650180759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7455315824299243533574345 5591486868224432650180759)
          ·
            refine ⟨8387230302336648975271139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591486868224432650180759 8387230302336648975271139)
            ·
              refine ⟨12580845453504973462906709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387230302336648975271139 12580845453504973462906709)
              ·
                refine ⟨73715891329130703884219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12580845453504973462906709 73715891329130703884219)
                ·
                  rfl

theorem cell22_1938076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_1938076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938076 prefixEnd_1938076 := by exact prefixLift 1938076
  have htrace : WordTrace (prefixWord ++ tailWord_1938076) baseStart_1938076 baseEnd_1938076 := by
    simpa [prefixWord, tailWord_1938076, baseEnd_1938076] using wordTrace_append hprefix tailTrace_1938076
  have hstable : (prefixWord ++ tailWord_1938076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938076).length < 2 ^ (prefixWord ++ tailWord_1938076).sum := by decide
  have hdescent : baseEnd_1938076 < baseStart_1938076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938078 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1938078 : Nat := 118140960795 + 1938078 * 2 ^ 59
def prefixEnd_1938078 : Nat := 4983230072969 + 3 ^ 40 * 1938078 * 2
def baseEnd_1938078 : Nat := 663443706603048996407965

theorem tailTrace_1938078 : CollatzResearch.WordTrace tailWord_1938078 prefixEnd_1938078 663443706603048996407965 := by
  unfold tailWord_1938078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835938984085234776932861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47125007915121252143641925 8835938984085234776932861)
  ·
    refine ⟨3313477119031963041349823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8835938984085234776932861 3313477119031963041349823)
    ·
      refine ⟨4970215678547944562024735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313477119031963041349823 4970215678547944562024735)
      ·
        refine ⟨7455323517821916843037103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970215678547944562024735 7455323517821916843037103)
        ·
          refine ⟨11182985276732875264555655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455323517821916843037103 11182985276732875264555655)
          ·
            refine ⟨16774477915099312896833483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182985276732875264555655 16774477915099312896833483)
            ·
              refine ⟨25161716872648969345250225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774477915099312896833483 25161716872648969345250225)
              ·
                refine ⟨18871287654486727008937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25161716872648969345250225 18871287654486727008937669)
                ·
                  refine ⟨3538366435216261314175813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18871287654486727008937669 3538366435216261314175813)
                  ·
                    refine ⟨663443706603048996407965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538366435216261314175813 663443706603048996407965)
                    ·
                      rfl

theorem cell22_1938078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1938078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938078 prefixEnd_1938078 := by exact prefixLift 1938078
  have htrace : WordTrace (prefixWord ++ tailWord_1938078) baseStart_1938078 baseEnd_1938078 := by
    simpa [prefixWord, tailWord_1938078, baseEnd_1938078] using wordTrace_append hprefix tailTrace_1938078
  have hstable : (prefixWord ++ tailWord_1938078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938078).length < 2 ^ (prefixWord ++ tailWord_1938078).sum := by decide
  have hdescent : baseEnd_1938078 < baseStart_1938078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938080 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_1938080 : Nat := 118140960795 + 1938080 * 2 ^ 59
def prefixEnd_1938080 : Nat := 4983230072969 + 3 ^ 40 * 1938080 * 2
def baseEnd_1938080 : Nat := 663444391243921657857959

theorem tailTrace_1938080 : CollatzResearch.WordTrace tailWord_1938080 prefixEnd_1938080 663444391243921657857959 := by
  unfold tailWord_1938080
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343792409337316278517847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47125056545783088371357129 35343792409337316278517847)
  ·
    refine ⟨53015688614005974417776771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35343792409337316278517847 53015688614005974417776771)
    ·
      refine ⟨79523532921008961626665157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53015688614005974417776771 79523532921008961626665157)
      ·
        refine ⟨14910662422689180304999717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79523532921008961626665157 14910662422689180304999717)
        ·
          refine ⟨2795749204254221307187447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14910662422689180304999717 2795749204254221307187447)
          ·
            refine ⟨4193623806381331960781171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795749204254221307187447 4193623806381331960781171)
            ·
              refine ⟨6290435709571997941171757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193623806381331960781171 6290435709571997941171757)
              ·
                refine ⟨2358913391089499227939409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290435709571997941171757 2358913391089499227939409)
                ·
                  refine ⟨1769185043317124420954557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358913391089499227939409 1769185043317124420954557)
                  ·
                    refine ⟨663444391243921657857959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769185043317124420954557 663444391243921657857959)
                    ·
                      rfl

theorem cell22_1938080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_1938080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938080 prefixEnd_1938080 := by exact prefixLift 1938080
  have htrace : WordTrace (prefixWord ++ tailWord_1938080) baseStart_1938080 baseEnd_1938080 := by
    simpa [prefixWord, tailWord_1938080, baseEnd_1938080] using wordTrace_append hprefix tailTrace_1938080
  have hstable : (prefixWord ++ tailWord_1938080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938080).length < 2 ^ (prefixWord ++ tailWord_1938080).sum := by decide
  have hdescent : baseEnd_1938080 < baseStart_1938080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938136 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_1938136 : Nat := 118140960795 + 1938136 * 2 ^ 59
def prefixEnd_1938136 : Nat := 4983230072969 + 3 ^ 40 * 1938136 * 2
def baseEnd_1938136 : Nat := 663463561188356178457787

theorem tailTrace_1938136 : CollatzResearch.WordTrace tailWord_1938136 prefixEnd_1938136 663463561188356178457787 := by
  unfold tailWord_1938136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35344813653235877060537131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47126418204314502747382841 35344813653235877060537131)
  ·
    refine ⟨53017220479853815590805697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35344813653235877060537131 53017220479853815590805697)
    ·
      refine ⟨39762915359890361693104273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53017220479853815590805697 39762915359890361693104273)
      ·
        refine ⟨29822186519917771269828205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39762915359890361693104273 29822186519917771269828205)
        ·
          refine ⟨11183319944969164226185577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29822186519917771269828205 11183319944969164226185577)
          ·
            refine ⟨8387489958726873169639183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183319944969164226185577 8387489958726873169639183)
            ·
              refine ⟨12581234938090309754458775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387489958726873169639183 12581234938090309754458775)
              ·
                refine ⟨18871852407135464631688163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12581234938090309754458775 18871852407135464631688163)
                ·
                  refine ⟨28307778610703196947532245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18871852407135464631688163 28307778610703196947532245)
                  ·
                    refine ⟨663463561188356178457787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28307778610703196947532245 663463561188356178457787)
                    ·
                      rfl

theorem cell22_1938136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_1938136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938136 prefixEnd_1938136 := by exact prefixLift 1938136
  have htrace : WordTrace (prefixWord ++ tailWord_1938136) baseStart_1938136 baseEnd_1938136 := by
    simpa [prefixWord, tailWord_1938136, baseEnd_1938136] using wordTrace_append hprefix tailTrace_1938136
  have hstable : (prefixWord ++ tailWord_1938136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938136).length < 2 ^ (prefixWord ++ tailWord_1938136).sum := by decide
  have hdescent : baseEnd_1938136 < baseStart_1938136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938168 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_1938168 : Nat := 118140960795 + 1938168 * 2 ^ 59
def prefixEnd_1938168 : Nat := 4983230072969 + 3 ^ 40 * 1938168 * 2
def baseEnd_1938168 : Nat := 663474515442318761657689

theorem tailTrace_1938168 : CollatzResearch.WordTrace tailWord_1938168 prefixEnd_1938168 663474515442318761657689 := by
  unfold tailWord_1938168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345397221177911793119579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47127196294903882390826105 35345397221177911793119579)
  ·
    refine ⟨53018095831766867689679369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35345397221177911793119579 53018095831766867689679369)
    ·
      refine ⟨39763571873825150767259527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53018095831766867689679369 39763571873825150767259527)
      ·
        refine ⟨59645357810737726150889291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39763571873825150767259527 59645357810737726150889291)
        ·
          refine ⟨89468036716106589226333937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59645357810737726150889291 89468036716106589226333937)
          ·
            refine ⟨67101027537079941919750453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89468036716106589226333937 67101027537079941919750453)
            ·
              refine ⟨6290721331601244554976605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67101027537079941919750453 6290721331601244554976605)
              ·
                refine ⟨2359020499350466708116227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290721331601244554976605 2359020499350466708116227)
                ·
                  refine ⟨3538530749025700062174341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359020499350466708116227 3538530749025700062174341)
                  ·
                    refine ⟨663474515442318761657689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538530749025700062174341 663474515442318761657689)
                    ·
                      rfl

theorem cell22_1938168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_1938168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938168 prefixEnd_1938168 := by exact prefixLift 1938168
  have htrace : WordTrace (prefixWord ++ tailWord_1938168) baseStart_1938168 baseEnd_1938168 := by
    simpa [prefixWord, tailWord_1938168, baseEnd_1938168] using wordTrace_append hprefix tailTrace_1938168
  have hstable : (prefixWord ++ tailWord_1938168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938168).length < 2 ^ (prefixWord ++ tailWord_1938168).sum := by decide
  have hdescent : baseEnd_1938168 < baseStart_1938168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938181 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1938181 : Nat := 118140960795 + 1938181 * 2 ^ 59
def prefixEnd_1938181 : Nat := 4983230072969 + 3 ^ 40 * 1938181 * 2
def baseEnd_1938181 : Nat := 663478965607991061082649

theorem tailTrace_1938181 : CollatzResearch.WordTrace tailWord_1938181 prefixEnd_1938181 663478965607991061082649 := by
  unfold tailWord_1938181
  simp only [CollatzResearch.WordTrace]
  refine ⟨70691268591308726806462397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47127512394205817870974931 70691268591308726806462397)
  ·
    refine ⟨26509225721740772552423399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70691268591308726806462397 26509225721740772552423399)
    ·
      refine ⟨39763838582611158828635099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26509225721740772552423399 39763838582611158828635099)
      ·
        refine ⟨59645757873916738242952649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39763838582611158828635099 59645757873916738242952649)
        ·
          refine ⟨44734318405437553682214487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59645757873916738242952649 44734318405437553682214487)
          ·
            refine ⟨67101477608156330523321731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44734318405437553682214487 67101477608156330523321731)
            ·
              refine ⟨100652216412234495784982597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67101477608156330523321731 100652216412234495784982597)
              ·
                refine ⟨18872290577293967959684237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100652216412234495784982597 18872290577293967959684237)
                ·
                  refine ⟨7077108966485237984881589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18872290577293967959684237 7077108966485237984881589)
                  ·
                    refine ⟨663478965607991061082649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7077108966485237984881589 663478965607991061082649)
                    ·
                      rfl

theorem cell22_1938181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1938181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938181 prefixEnd_1938181 := by exact prefixLift 1938181
  have htrace : WordTrace (prefixWord ++ tailWord_1938181) baseStart_1938181 baseEnd_1938181 := by
    simpa [prefixWord, tailWord_1938181, baseEnd_1938181] using wordTrace_append hprefix tailTrace_1938181
  have hstable : (prefixWord ++ tailWord_1938181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938181).length < 2 ^ (prefixWord ++ tailWord_1938181).sum := by decide
  have hdescent : baseEnd_1938181 < baseStart_1938181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938183 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 6]
def baseStart_1938183 : Nat := 118140960795 + 1938183 * 2 ^ 59
def prefixEnd_1938183 : Nat := 4983230072969 + 3 ^ 40 * 1938183 * 2
def baseEnd_1938183 : Nat := 221159883416287907510881

theorem tailTrace_1938183 : CollatzResearch.WordTrace tailWord_1938183 prefixEnd_1938183 221159883416287907510881 := by
  unfold tailWord_1938183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70691341537301481148035203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47127561024867654098690135 70691341537301481148035203)
  ·
    refine ⟨106037012305952221722052805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70691341537301481148035203 106037012305952221722052805)
    ·
      refine ⟨19881939807366041572884901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106037012305952221722052805 19881939807366041572884901)
      ·
        refine ⟨3727863713881132794915919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19881939807366041572884901 3727863713881132794915919)
        ·
          refine ⟨5591795570821699192373879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727863713881132794915919 5591795570821699192373879)
          ·
            refine ⟨8387693356232548788560819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591795570821699192373879 8387693356232548788560819)
            ·
              refine ⟨12581540034348823182841229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387693356232548788560819 12581540034348823182841229)
              ·
                refine ⟨4718077512880808693565461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581540034348823182841229 4718077512880808693565461)
                ·
                  refine ⟨221159883416287907510881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4718077512880808693565461 221159883416287907510881)
                  ·
                    rfl

theorem cell22_1938183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_1938183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938183 prefixEnd_1938183 := by exact prefixLift 1938183
  have htrace : WordTrace (prefixWord ++ tailWord_1938183) baseStart_1938183 baseEnd_1938183 := by
    simpa [prefixWord, tailWord_1938183, baseEnd_1938183] using wordTrace_append hprefix tailTrace_1938183
  have hstable : (prefixWord ++ tailWord_1938183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938183).length < 2 ^ (prefixWord ++ tailWord_1938183).sum := by decide
  have hdescent : baseEnd_1938183 < baseStart_1938183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938213 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1938213 : Nat := 118140960795 + 1938213 * 2 ^ 59
def prefixEnd_1938213 : Nat := 4983230072969 + 3 ^ 40 * 1938213 * 2
def baseEnd_1938213 : Nat := 663489919861953644282551

theorem tailTrace_1938213 : CollatzResearch.WordTrace tailWord_1938213 prefixEnd_1938213 663489919861953644282551 := by
  unfold tailWord_1938213
  simp only [CollatzResearch.WordTrace]
  refine ⟨70692435727192796271627293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47128290484795197514418195 70692435727192796271627293)
  ·
    refine ⟨26509663397697298601860235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70692435727192796271627293 26509663397697298601860235)
    ·
      refine ⟨39764495096545947902790353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26509663397697298601860235 39764495096545947902790353)
      ·
        refine ⟨29823371322409460927092765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39764495096545947902790353 29823371322409460927092765)
        ·
          refine ⟨11183764245903547847659787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29823371322409460927092765 11183764245903547847659787)
          ·
            refine ⟨16775646368855321771489681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183764245903547847659787 16775646368855321771489681)
            ·
              refine ⟨12581734776641491328617261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16775646368855321771489681 12581734776641491328617261)
              ·
                refine ⟨4718150541240559248231473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581734776641491328617261 4718150541240559248231473)
                ·
                  refine ⟨3538612905930419436173605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718150541240559248231473 3538612905930419436173605)
                  ·
                    refine ⟨663489919861953644282551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538612905930419436173605 663489919861953644282551)
                    ·
                      rfl

theorem cell22_1938213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1938213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938213 prefixEnd_1938213 := by exact prefixLift 1938213
  have htrace : WordTrace (prefixWord ++ tailWord_1938213) baseStart_1938213 baseEnd_1938213 := by
    simpa [prefixWord, tailWord_1938213, baseEnd_1938213] using wordTrace_append hprefix tailTrace_1938213
  have hstable : (prefixWord ++ tailWord_1938213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938213).length < 2 ^ (prefixWord ++ tailWord_1938213).sum := by decide
  have hdescent : baseEnd_1938213 < baseStart_1938213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938303 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_1938303 : Nat := 118140960795 + 1938303 * 2 ^ 59
def prefixEnd_1938303 : Nat := 4983230072969 + 3 ^ 40 * 1938303 * 2
def baseEnd_1938303 : Nat := 663520728701223409532275

theorem tailTrace_1938303 : CollatzResearch.WordTrace tailWord_1938303 prefixEnd_1938303 663520728701223409532275 := by
  unfold tailWord_1938303
  simp only [CollatzResearch.WordTrace]
  refine ⟨70695718296866741642403563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47130478864577827761602375 70695718296866741642403563)
  ·
    refine ⟨106043577445300112463605345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70695718296866741642403563 106043577445300112463605345)
    ·
      refine ⟨79532683083975084347704009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106043577445300112463605345 79532683083975084347704009)
      ·
        refine ⟨59649512312981313260778007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79532683083975084347704009 59649512312981313260778007)
        ·
          refine ⟨89474268469471969891167011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59649512312981313260778007 89474268469471969891167011)
          ·
            refine ⟨134211402704207954836750517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89474268469471969891167011 134211402704207954836750517)
            ·
              refine ⟨12582319003519495765945361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134211402704207954836750517 12582319003519495765945361)
              ·
                refine ⟨9436739252639621824459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12582319003519495765945361 9436739252639621824459021)
                ·
                  refine ⟨3538777219739858184172133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9436739252639621824459021 3538777219739858184172133)
                  ·
                    refine ⟨663520728701223409532275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538777219739858184172133 663520728701223409532275)
                    ·
                      rfl

theorem cell22_1938303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_1938303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938303 prefixEnd_1938303 := by exact prefixLift 1938303
  have htrace : WordTrace (prefixWord ++ tailWord_1938303) baseStart_1938303 baseEnd_1938303 := by
    simpa [prefixWord, tailWord_1938303, baseEnd_1938303] using wordTrace_append hprefix tailTrace_1938303
  have hstable : (prefixWord ++ tailWord_1938303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938303).length < 2 ^ (prefixWord ++ tailWord_1938303).sum := by decide
  have hdescent : baseEnd_1938303 < baseStart_1938303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938337 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1938337 : Nat := 118140960795 + 1938337 * 2 ^ 59
def prefixEnd_1938337 : Nat := 4983230072969 + 3 ^ 40 * 1938337 * 2
def baseEnd_1938337 : Nat := 663532367596058654182171

theorem tailTrace_1938337 : CollatzResearch.WordTrace tailWord_1938337 prefixEnd_1938337 663532367596058654182171 := by
  unfold tailWord_1938337
  simp only [CollatzResearch.WordTrace]
  refine ⟨70696958378743565449141265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47131305585829043632760843 70696958378743565449141265)
  ·
    refine ⟨53022718784057674086855949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70696958378743565449141265 53022718784057674086855949)
    ·
      refine ⟨19883519544021627782570981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53022718784057674086855949 19883519544021627782570981)
      ·
        refine ⟨3728159914504055209232059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19883519544021627782570981 3728159914504055209232059)
        ·
          refine ⟨5592239871756082813848089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728159914504055209232059 5592239871756082813848089)
          ·
            refine ⟨4194179903817062110386067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5592239871756082813848089 4194179903817062110386067)
            ·
              refine ⟨6291269855725593165579101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194179903817062110386067 6291269855725593165579101)
              ·
                refine ⟨2359226195897097437092163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6291269855725593165579101 2359226195897097437092163)
                ·
                  refine ⟨3538839293845646155638245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359226195897097437092163 3538839293845646155638245)
                  ·
                    refine ⟨663532367596058654182171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538839293845646155638245 663532367596058654182171)
                    ·
                      rfl

theorem cell22_1938337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1938337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938337 prefixEnd_1938337 := by exact prefixLift 1938337
  have htrace : WordTrace (prefixWord ++ tailWord_1938337) baseStart_1938337 baseEnd_1938337 := by
    simpa [prefixWord, tailWord_1938337, baseEnd_1938337] using wordTrace_append hprefix tailTrace_1938337
  have hstable : (prefixWord ++ tailWord_1938337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938337).length < 2 ^ (prefixWord ++ tailWord_1938337).sum := by decide
  have hdescent : baseEnd_1938337 < baseStart_1938337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938358 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1938358 : Nat := 118140960795 + 1938358 * 2 ^ 59
def prefixEnd_1938358 : Nat := 4983230072969 + 3 ^ 40 * 1938358 * 2
def baseEnd_1938358 : Nat := 221179852108407199802369

theorem tailTrace_1938358 : CollatzResearch.WordTrace tailWord_1938358 prefixEnd_1938358 221179852108407199802369 := by
  unfold tailWord_1938358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418607769479217877228483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47131816207778324023770485 4418607769479217877228483)
  ·
    refine ⟨6627911654218826815842725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418607769479217877228483 6627911654218826815842725)
    ·
      refine ⟨1242733435166030027970511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6627911654218826815842725 1242733435166030027970511)
      ·
        refine ⟨1864100152749045041955767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242733435166030027970511 1864100152749045041955767)
        ·
          refine ⟨2796150229123567562933651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864100152749045041955767 2796150229123567562933651)
          ·
            refine ⟨4194225343685351344400477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796150229123567562933651 4194225343685351344400477)
            ·
              refine ⟨1572834503882006754150179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4194225343685351344400477 1572834503882006754150179)
              ·
                refine ⟨2359251755823010131225269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572834503882006754150179 2359251755823010131225269)
                ·
                  refine ⟨221179852108407199802369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359251755823010131225269 221179852108407199802369)
                  ·
                    rfl

theorem cell22_1938358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1938358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938358 prefixEnd_1938358 := by exact prefixLift 1938358
  have htrace : WordTrace (prefixWord ++ tailWord_1938358) baseStart_1938358 baseEnd_1938358 := by
    simpa [prefixWord, tailWord_1938358, baseEnd_1938358] using wordTrace_append hprefix tailTrace_1938358
  have hstable : (prefixWord ++ tailWord_1938358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938358).length < 2 ^ (prefixWord ++ tailWord_1938358).sum := by decide
  have hdescent : baseEnd_1938358 < baseStart_1938358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938378 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1938378 : Nat := 118140960795 + 1938378 * 2 ^ 59
def prefixEnd_1938378 : Nat := 4983230072969 + 3 ^ 40 * 1938378 * 2
def baseEnd_1938378 : Nat := 663546402733948213907045

theorem tailTrace_1938378 : CollatzResearch.WordTrace tailWord_1938378 prefixEnd_1938378 663546402733948213907045 := by
  unfold tailWord_1938378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674613442898757362845947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47132302514396686300922525 17674613442898757362845947)
  ·
    refine ⟨26511920164348136044268921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17674613442898757362845947 26511920164348136044268921)
    ·
      refine ⟨19883940123261102033201691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26511920164348136044268921 19883940123261102033201691)
      ·
        refine ⟨29825910184891653049802537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883940123261102033201691 29825910184891653049802537)
        ·
          refine ⟨22369432638668739787351903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29825910184891653049802537 22369432638668739787351903)
          ·
            refine ⟨33554148958003109681027855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22369432638668739787351903 33554148958003109681027855)
            ·
              refine ⟨50331223437004664521541783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33554148958003109681027855 50331223437004664521541783)
              ·
                refine ⟨75496835155506996782312675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50331223437004664521541783 75496835155506996782312675)
                ·
                  refine ⟨113245252733260495173469013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75496835155506996782312675 113245252733260495173469013)
                  ·
                    refine ⟨663546402733948213907045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113245252733260495173469013 663546402733948213907045)
                    ·
                      rfl

theorem cell22_1938378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1938378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938378 prefixEnd_1938378 := by exact prefixLift 1938378
  have htrace : WordTrace (prefixWord ++ tailWord_1938378) baseStart_1938378 baseEnd_1938378 := by
    simpa [prefixWord, tailWord_1938378, baseEnd_1938378] using wordTrace_append hprefix tailTrace_1938378
  have hstable : (prefixWord ++ tailWord_1938378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938378).length < 2 ^ (prefixWord ++ tailWord_1938378).sum := by decide
  have hdescent : baseEnd_1938378 < baseStart_1938378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938418 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_1938418 : Nat := 118140960795 + 1938418 * 2 ^ 59
def prefixEnd_1938418 : Nat := 4983230072969 + 3 ^ 40 * 1938418 * 2
def baseEnd_1938418 : Nat := 663560095551401442906923

theorem tailTrace_1938418 : CollatzResearch.WordTrace tailWord_1938418 prefixEnd_1938418 663560095551401442906923 := by
  unfold tailWord_1938418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674978172862529070709977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47133275127633410855226605 17674978172862529070709977)
  ·
    refine ⟨13256233629646896803032483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17674978172862529070709977 13256233629646896803032483)
    ·
      refine ⟨19884350444470345204548725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256233629646896803032483 19884350444470345204548725)
      ·
        refine ⟨1864157854169094862926443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19884350444470345204548725 1864157854169094862926443)
        ·
          refine ⟨2796236781253642294389665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864157854169094862926443 2796236781253642294389665)
          ·
            refine ⟨2097177585940231720792249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796236781253642294389665 2097177585940231720792249)
            ·
              refine ⟨1572883189455173790594187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097177585940231720792249 1572883189455173790594187)
              ·
                refine ⟨2359324784182760685891281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572883189455173790594187 2359324784182760685891281)
                ·
                  refine ⟨1769493588137070514418461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359324784182760685891281 1769493588137070514418461)
                  ·
                    refine ⟨663560095551401442906923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769493588137070514418461 663560095551401442906923)
                    ·
                      rfl

theorem cell22_1938418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_1938418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938418 prefixEnd_1938418 := by exact prefixLift 1938418
  have htrace : WordTrace (prefixWord ++ tailWord_1938418) baseStart_1938418 baseEnd_1938418 := by
    simpa [prefixWord, tailWord_1938418, baseEnd_1938418] using wordTrace_append hprefix tailTrace_1938418
  have hstable : (prefixWord ++ tailWord_1938418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938418).length < 2 ^ (prefixWord ++ tailWord_1938418).sum := by decide
  have hdescent : baseEnd_1938418 < baseStart_1938418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938425 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 5]
def baseStart_1938425 : Nat := 118140960795 + 1938425 * 2 ^ 59
def prefixEnd_1938425 : Nat := 4983230072969 + 3 ^ 40 * 1938425 * 2
def baseEnd_1938425 : Nat := 221187497264818585993967

theorem tailTrace_1938425 : CollatzResearch.WordTrace tailWord_1938425 prefixEnd_1938425 221187497264818585993967 := by
  unfold tailWord_1938425
  simp only [CollatzResearch.WordTrace]
  refine ⟨70700168002424756478344729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47133445334949837652229819 70700168002424756478344729)
  ·
    refine ⟨53025126001818567358758547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70700168002424756478344729 53025126001818567358758547)
    ·
      refine ⟨79537689002727851038137821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53025126001818567358758547 79537689002727851038137821)
      ·
        refine ⟨29826633376022944139301683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79537689002727851038137821 29826633376022944139301683)
        ·
          refine ⟨44739950064034416208952525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826633376022944139301683 44739950064034416208952525)
          ·
            refine ⟨16777481274012906078357197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44739950064034416208952525 16777481274012906078357197)
            ·
              refine ⟨6291555477754839779383949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16777481274012906078357197 6291555477754839779383949)
              ·
                refine ⟨2359333304158064917268981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6291555477754839779383949 2359333304158064917268981)
                ·
                  refine ⟨221187497264818585993967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359333304158064917268981 221187497264818585993967)
                  ·
                    rfl

theorem cell22_1938425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_1938425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938425 prefixEnd_1938425 := by exact prefixLift 1938425
  have htrace : WordTrace (prefixWord ++ tailWord_1938425) baseStart_1938425 baseEnd_1938425 := by
    simpa [prefixWord, tailWord_1938425, baseEnd_1938425] using wordTrace_append hprefix tailTrace_1938425
  have hstable : (prefixWord ++ tailWord_1938425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938425).length < 2 ^ (prefixWord ++ tailWord_1938425).sum := by decide
  have hdescent : baseEnd_1938425 < baseStart_1938425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938536 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1938536 : Nat := 118140960795 + 1938536 * 2 ^ 59
def prefixEnd_1938536 : Nat := 4983230072969 + 3 ^ 40 * 1938536 * 2
def baseEnd_1938536 : Nat := 663600489362888468456561

theorem tailTrace_1938536 : CollatzResearch.WordTrace tailWord_1938536 prefixEnd_1938536 663600489362888468456561 := by
  unfold tailWord_1938536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352108252511311217817731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47136144336681748290423641 35352108252511311217817731)
  ·
    refine ⟨53028162378766966826726597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352108252511311217817731 53028162378766966826726597)
    ·
      refine ⟨9942780446018806280011237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53028162378766966826726597 9942780446018806280011237)
      ·
        refine ⟨1864271333628526177502107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9942780446018806280011237 1864271333628526177502107)
        ·
          refine ⟨2796407000442789266253161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864271333628526177502107 2796407000442789266253161)
          ·
            refine ⟨2097305250332091949689871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796407000442789266253161 2097305250332091949689871)
            ·
              refine ⟨3145957875498137924534807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097305250332091949689871 3145957875498137924534807)
              ·
                refine ⟨4718936813247206886802211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145957875498137924534807 4718936813247206886802211)
                ·
                  refine ⟨7078405219870810330203317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718936813247206886802211 7078405219870810330203317)
                  ·
                    refine ⟨663600489362888468456561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7078405219870810330203317 663600489362888468456561)
                    ·
                      rfl

theorem cell22_1938536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1938536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938536 prefixEnd_1938536 := by exact prefixLift 1938536
  have htrace : WordTrace (prefixWord ++ tailWord_1938536) baseStart_1938536 baseEnd_1938536 := by
    simpa [prefixWord, tailWord_1938536, baseEnd_1938536] using wordTrace_append hprefix tailTrace_1938536
  have hstable : (prefixWord ++ tailWord_1938536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938536).length < 2 ^ (prefixWord ++ tailWord_1938536).sum := by decide
  have hdescent : baseEnd_1938536 < baseStart_1938536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938549 : List Nat := [1, 3, 4, 3, 1, 1, 1, 8]
def baseStart_1938549 : Nat := 118140960795 + 1938549 * 2 ^ 59
def prefixEnd_1938549 : Nat := 4983230072969 + 3 ^ 40 * 1938549 * 2
def baseEnd_1938549 : Nat := 73733882169840085320169

theorem tailTrace_1938549 : CollatzResearch.WordTrace tailWord_1938549 prefixEnd_1938549 73733882169840085320169 := by
  unfold tailWord_1938549
  simp only [CollatzResearch.WordTrace]
  refine ⟨70704690653975525655858701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47136460435983683770572467 70704690653975525655858701)
  ·
    refine ⟨26514258995240822120947013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70704690653975525655858701 26514258995240822120947013)
    ·
      refine ⟨4971423561607654147677565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26514258995240822120947013 4971423561607654147677565)
      ·
        refine ⟨1864283835602870305379087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4971423561607654147677565 1864283835602870305379087)
        ·
          refine ⟨2796425753404305458068631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864283835602870305379087 2796425753404305458068631)
          ·
            refine ⟨4194638630106458187102947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796425753404305458068631 4194638630106458187102947)
            ·
              refine ⟨6291957945159687280654421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194638630106458187102947 6291957945159687280654421)
              ·
                refine ⟨73733882169840085320169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6291957945159687280654421 73733882169840085320169)
                ·
                  rfl

theorem cell22_1938549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 8].length) (baseStart_1938549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938549 prefixEnd_1938549 := by exact prefixLift 1938549
  have htrace : WordTrace (prefixWord ++ tailWord_1938549) baseStart_1938549 baseEnd_1938549 := by
    simpa [prefixWord, tailWord_1938549, baseEnd_1938549] using wordTrace_append hprefix tailTrace_1938549
  have hstable : (prefixWord ++ tailWord_1938549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938549).length < 2 ^ (prefixWord ++ tailWord_1938549).sum := by decide
  have hdescent : baseEnd_1938549 < baseStart_1938549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938560 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_1938560 : Nat := 118140960795 + 1938560 * 2 ^ 59
def prefixEnd_1938560 : Nat := 4983230072969 + 3 ^ 40 * 1938560 * 2
def baseEnd_1938560 : Nat := 221202901684453468618829

theorem tailTrace_1938560 : CollatzResearch.WordTrace tailWord_1938560 prefixEnd_1938560 221202901684453468618829 := by
  unfold tailWord_1938560
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352545928467837267254567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47136727904623783023006089 35352545928467837267254567)
  ·
    refine ⟨53028818892701755900881851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352545928467837267254567 53028818892701755900881851)
    ·
      refine ⟨79543228339052633851322777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028818892701755900881851 79543228339052633851322777)
      ·
        refine ⟨59657421254289475388492083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79543228339052633851322777 59657421254289475388492083)
        ·
          refine ⟨89486131881434213082738125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59657421254289475388492083 89486131881434213082738125)
          ·
            refine ⟨33557299455537829906026797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89486131881434213082738125 33557299455537829906026797)
            ·
              refine ⟨12583987295826686214760049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33557299455537829906026797 12583987295826686214760049)
              ·
                refine ⟨9437990471870014661070037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583987295826686214760049 9437990471870014661070037)
                ·
                  refine ⟨221202901684453468618829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9437990471870014661070037 221202901684453468618829)
                  ·
                    rfl

theorem cell22_1938560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_1938560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938560 prefixEnd_1938560 := by exact prefixLift 1938560
  have htrace : WordTrace (prefixWord ++ tailWord_1938560) baseStart_1938560 baseEnd_1938560 := by
    simpa [prefixWord, tailWord_1938560, baseEnd_1938560] using wordTrace_append hprefix tailTrace_1938560
  have hstable : (prefixWord ++ tailWord_1938560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938560).length < 2 ^ (prefixWord ++ tailWord_1938560).sum := by decide
  have hdescent : baseEnd_1938560 < baseStart_1938560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938669 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1938669 : Nat := 118140960795 + 1938669 * 2 ^ 59
def prefixEnd_1938669 : Nat := 4983230072969 + 3 ^ 40 * 1938669 * 2
def baseEnd_1938669 : Nat := 663646017980920454881153

theorem tailTrace_1938669 : CollatzResearch.WordTrace tailWord_1938669 prefixEnd_1938669 663646017980920454881153 := by
  unfold tailWord_1938669
  simp only [CollatzResearch.WordTrace]
  refine ⟨70709067413540786150227061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47139378275693857433484707 70709067413540786150227061)
  ·
    refine ⟨6628975070019448701583787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70709067413540786150227061 6628975070019448701583787)
    ·
      refine ⟨9943462605029173052375681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628975070019448701583787 9943462605029173052375681)
      ·
        refine ⟨7457596953771879789281761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943462605029173052375681 7457596953771879789281761)
        ·
          refine ⟨5593197715328909841961321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457596953771879789281761 5593197715328909841961321)
          ·
            refine ⟨4194898286496682381470991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593197715328909841961321 4194898286496682381470991)
            ·
              refine ⟨6292347429745023572206487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194898286496682381470991 6292347429745023572206487)
              ·
                refine ⟨9438521144617535358309731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292347429745023572206487 9438521144617535358309731)
                ·
                  refine ⟨14157781716926303037464597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438521144617535358309731 14157781716926303037464597)
                  ·
                    refine ⟨663646017980920454881153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14157781716926303037464597 663646017980920454881153)
                    ·
                      rfl

theorem cell22_1938669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1938669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938669 prefixEnd_1938669 := by exact prefixLift 1938669
  have htrace : WordTrace (prefixWord ++ tailWord_1938669) baseStart_1938669 baseEnd_1938669 := by
    simpa [prefixWord, tailWord_1938669, baseEnd_1938669] using wordTrace_append hprefix tailTrace_1938669
  have hstable : (prefixWord ++ tailWord_1938669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938669).length < 2 ^ (prefixWord ++ tailWord_1938669).sum := by decide
  have hdescent : baseEnd_1938669 < baseStart_1938669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938699 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 3, 3]
def baseStart_1938699 : Nat := 118140960795 + 1938699 * 2 ^ 59
def prefixEnd_1938699 : Nat := 4983230072969 + 3 ^ 40 * 1938699 * 2
def baseEnd_1938699 : Nat := 663656287594010376631061

theorem tailTrace_1938699 : CollatzResearch.WordTrace tailWord_1938699 prefixEnd_1938699 663656287594010376631061 := by
  unfold tailWord_1938699
  simp only [CollatzResearch.WordTrace]
  refine ⟨70710161603432101273819151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47140107735621400849212767 70710161603432101273819151)
  ·
    refine ⟨106065242405148151910728727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70710161603432101273819151 106065242405148151910728727)
    ·
      refine ⟨159097863607722227866093091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106065242405148151910728727 159097863607722227866093091)
      ·
        refine ⟨238646795411583341799139637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159097863607722227866093091 238646795411583341799139637)
        ·
          refine ⟨22373137069835938293669341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238646795411583341799139637 22373137069835938293669341)
          ·
            refine ⟨8389926401188476860126003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22373137069835938293669341 8389926401188476860126003)
            ·
              refine ⟨12584889601782715290189005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389926401188476860126003 12584889601782715290189005)
              ·
                refine ⟨4719333600668518233820877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12584889601782715290189005 4719333600668518233820877)
                ·
                  refine ⟨1769750100250694337682829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4719333600668518233820877 1769750100250694337682829)
                  ·
                    refine ⟨663656287594010376631061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769750100250694337682829 663656287594010376631061)
                    ·
                      rfl

theorem cell22_1938699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].length) (baseStart_1938699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938699 prefixEnd_1938699 := by exact prefixLift 1938699
  have htrace : WordTrace (prefixWord ++ tailWord_1938699) baseStart_1938699 baseEnd_1938699 := by
    simpa [prefixWord, tailWord_1938699, baseEnd_1938699] using wordTrace_append hprefix tailTrace_1938699
  have hstable : (prefixWord ++ tailWord_1938699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938699).length < 2 ^ (prefixWord ++ tailWord_1938699).sum := by decide
  have hdescent : baseEnd_1938699 < baseStart_1938699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938750 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1938750 : Nat := 118140960795 + 1938750 * 2 ^ 59
def prefixEnd_1938750 : Nat := 4983230072969 + 3 ^ 40 * 1938750 * 2
def baseEnd_1938750 : Nat := 663673745936263243605905

theorem tailTrace_1938750 : CollatzResearch.WordTrace tailWord_1938750 prefixEnd_1938750 663673745936263243605905 := by
  unfold tailWord_1938750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839002715780917122990713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47141347817498224655950469 8839002715780917122990713)
  ·
    refine ⟨6629252036835687842243035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8839002715780917122990713 6629252036835687842243035)
    ·
      refine ⟨9943878055253531763364553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629252036835687842243035 9943878055253531763364553)
      ·
        refine ⟨7457908541440148822523415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943878055253531763364553 7457908541440148822523415)
        ·
          refine ⟨11186862812160223233785123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457908541440148822523415 11186862812160223233785123)
          ·
            refine ⟨16780294218240334850677685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186862812160223233785123 16780294218240334850677685)
            ·
              refine ⟨1573152582960031392251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16780294218240334850677685 1573152582960031392251033)
              ·
                refine ⟨1179864437220023544188275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573152582960031392251033 1179864437220023544188275)
                ·
                  refine ⟨1769796655830035316282413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179864437220023544188275 1769796655830035316282413)
                  ·
                    refine ⟨663673745936263243605905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769796655830035316282413 663673745936263243605905)
                    ·
                      rfl

theorem cell22_1938750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1938750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938750 prefixEnd_1938750 := by exact prefixLift 1938750
  have htrace : WordTrace (prefixWord ++ tailWord_1938750) baseStart_1938750 baseEnd_1938750 := by
    simpa [prefixWord, tailWord_1938750, baseEnd_1938750] using wordTrace_append hprefix tailTrace_1938750
  have hstable : (prefixWord ++ tailWord_1938750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938750).length < 2 ^ (prefixWord ++ tailWord_1938750).sum := by decide
  have hdescent : baseEnd_1938750 < baseStart_1938750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938789 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1938789 : Nat := 118140960795 + 1938789 * 2 ^ 59
def prefixEnd_1938789 : Nat := 4983230072969 + 3 ^ 40 * 1938789 * 2
def baseEnd_1938789 : Nat := 663687096433280141880785

theorem tailTrace_1938789 : CollatzResearch.WordTrace tailWord_1938789 prefixEnd_1938789 663687096433280141880785 := by
  unfold tailWord_1938789
  simp only [CollatzResearch.WordTrace]
  refine ⟨70713444173106046644595421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47142296115404031096396947 70713444173106046644595421)
  ·
    refine ⟨26517541564914767491723283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70713444173106046644595421 26517541564914767491723283)
    ·
      refine ⟨39776312347372151237584925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517541564914767491723283 39776312347372151237584925)
      ·
        refine ⟨14916117130264556714094347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39776312347372151237584925 14916117130264556714094347)
        ·
          refine ⟨22374175695396835071141521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916117130264556714094347 22374175695396835071141521)
          ·
            refine ⟨16780631771547626303356141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22374175695396835071141521 16780631771547626303356141)
            ·
              refine ⟨6292736914330359863758553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16780631771547626303356141 6292736914330359863758553)
              ·
                refine ⟨4719552685747769897818915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292736914330359863758553 4719552685747769897818915)
                ·
                  refine ⟨7079329028621654846728373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719552685747769897818915 7079329028621654846728373)
                  ·
                    refine ⟨663687096433280141880785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7079329028621654846728373 663687096433280141880785)
                    ·
                      rfl

theorem cell22_1938789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1938789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938789 prefixEnd_1938789 := by exact prefixLift 1938789
  have htrace : WordTrace (prefixWord ++ tailWord_1938789) baseStart_1938789 baseEnd_1938789 := by
    simpa [prefixWord, tailWord_1938789, baseEnd_1938789] using wordTrace_append hprefix tailTrace_1938789
  have hstable : (prefixWord ++ tailWord_1938789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938789).length < 2 ^ (prefixWord ++ tailWord_1938789).sum := by decide
  have hdescent : baseEnd_1938789 < baseStart_1938789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938819 : List Nat := [1, 1, 1, 3, 5, 1, 3, 7]
def baseStart_1938819 : Nat := 118140960795 + 1938819 * 2 ^ 59
def prefixEnd_1938819 : Nat := 4983230072969 + 3 ^ 40 * 1938819 * 2
def baseEnd_1938819 : Nat := 73744151782930007070077

theorem tailTrace_1938819 : CollatzResearch.WordTrace tailWord_1938819 prefixEnd_1938819 73744151782930007070077 := by
  unfold tailWord_1938819
  simp only [CollatzResearch.WordTrace]
  refine ⟨70714538362997361768187511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47143025575331574512125007 70714538362997361768187511)
  ·
    refine ⟨106071807544496042652281267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70714538362997361768187511 106071807544496042652281267)
    ·
      refine ⟨159107711316744063978421901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106071807544496042652281267 159107711316744063978421901)
      ·
        refine ⟨59665391743779023991908213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159107711316744063978421901 59665391743779023991908213)
        ·
          refine ⟨5593630475979283499241395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59665391743779023991908213 5593630475979283499241395)
          ·
            refine ⟨8390445713968925248862093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593630475979283499241395 8390445713968925248862093)
            ·
              refine ⟨3146417142738346968323285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8390445713968925248862093 3146417142738346968323285)
              ·
                refine ⟨73744151782930007070077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3146417142738346968323285 73744151782930007070077)
                ·
                  rfl

theorem cell22_1938819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 7].length) (baseStart_1938819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938819 prefixEnd_1938819 := by exact prefixLift 1938819
  have htrace : WordTrace (prefixWord ++ tailWord_1938819) baseStart_1938819 baseEnd_1938819 := by
    simpa [prefixWord, tailWord_1938819, baseEnd_1938819] using wordTrace_append hprefix tailTrace_1938819
  have hstable : (prefixWord ++ tailWord_1938819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938819).length < 2 ^ (prefixWord ++ tailWord_1938819).sum := by decide
  have hdescent : baseEnd_1938819 < baseStart_1938819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938864 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_1938864 : Nat := 118140960795 + 1938864 * 2 ^ 59
def prefixEnd_1938864 : Nat := 4983230072969 + 3 ^ 40 * 1938864 * 2
def baseEnd_1938864 : Nat := 221237590155334982085185

theorem tailTrace_1938864 : CollatzResearch.WordTrace tailWord_1938864 prefixEnd_1938864 221237590155334982085185 := by
  unfold tailWord_1938864
  simp only [CollatzResearch.WordTrace]
  refine ⟨35358089823917167226787823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47144119765222889635717097 35358089823917167226787823)
  ·
    refine ⟨53037134735875750840181735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35358089823917167226787823 53037134735875750840181735)
    ·
      refine ⟨79555702103813626260272603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53037134735875750840181735 79555702103813626260272603)
      ·
        refine ⟨119333553155720439390408905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79555702103813626260272603 119333553155720439390408905)
        ·
          refine ⟨89500164866790329542806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119333553155720439390408905 89500164866790329542806679)
          ·
            refine ⟨134250247300185494314210019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89500164866790329542806679 134250247300185494314210019)
            ·
              refine ⟨201375370950278241471315029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134250247300185494314210019 201375370950278241471315029)
              ·
                refine ⟨2359867628323573142241973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 201375370950278241471315029 2359867628323573142241973)
                ·
                  refine ⟨221237590155334982085185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359867628323573142241973 221237590155334982085185)
                  ·
                    rfl

theorem cell22_1938864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_1938864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938864 prefixEnd_1938864 := by exact prefixLift 1938864
  have htrace : WordTrace (prefixWord ++ tailWord_1938864) baseStart_1938864 baseEnd_1938864 := by
    simpa [prefixWord, tailWord_1938864, baseEnd_1938864] using wordTrace_append hprefix tailTrace_1938864
  have hstable : (prefixWord ++ tailWord_1938864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938864).length < 2 ^ (prefixWord ++ tailWord_1938864).sum := by decide
  have hdescent : baseEnd_1938864 < baseStart_1938864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938902 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1938902 : Nat := 118140960795 + 1938902 * 2 ^ 59
def prefixEnd_1938902 : Nat := 4983230072969 + 3 ^ 40 * 1938902 * 2
def baseEnd_1938902 : Nat := 663725778642585513805439

theorem tailTrace_1938902 : CollatzResearch.WordTrace tailWord_1938902 prefixEnd_1938902 663725778642585513805439 := by
  unfold tailWord_1938902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419847851356041683966185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47145043747797777962305973 4419847851356041683966185)
  ·
    refine ⟨3314885888517031262974639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4419847851356041683966185 3314885888517031262974639)
    ·
      refine ⟨4972328832775546894461959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3314885888517031262974639 4972328832775546894461959)
      ·
        refine ⟨7458493249163320341692939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972328832775546894461959 7458493249163320341692939)
        ·
          refine ⟨11187739873744980512539409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458493249163320341692939 11187739873744980512539409)
          ·
            refine ⟨8390804905308735384404557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11187739873744980512539409 8390804905308735384404557)
            ·
              refine ⟨3146551839490775769151709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8390804905308735384404557 3146551839490775769151709)
              ·
                refine ⟨1179956939809040913431891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3146551839490775769151709 1179956939809040913431891)
                ·
                  refine ⟨1769935409713561370147837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179956939809040913431891 1769935409713561370147837)
                  ·
                    refine ⟨663725778642585513805439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769935409713561370147837 663725778642585513805439)
                    ·
                      rfl

theorem cell22_1938902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1938902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938902 prefixEnd_1938902 := by exact prefixLift 1938902
  have htrace : WordTrace (prefixWord ++ tailWord_1938902) baseStart_1938902 baseEnd_1938902 := by
    simpa [prefixWord, tailWord_1938902, baseEnd_1938902] using wordTrace_append hprefix tailTrace_1938902
  have hstable : (prefixWord ++ tailWord_1938902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938902).length < 2 ^ (prefixWord ++ tailWord_1938902).sum := by decide
  have hdescent : baseEnd_1938902 < baseStart_1938902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938911 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1938911 : Nat := 118140960795 + 1938911 * 2 ^ 59
def prefixEnd_1938911 : Nat := 4983230072969 + 3 ^ 40 * 1938911 * 2
def baseEnd_1938911 : Nat := 663728859526512490330411

theorem tailTrace_1938911 : CollatzResearch.WordTrace tailWord_1938911 prefixEnd_1938911 663728859526512490330411 := by
  unfold tailWord_1938911
  simp only [CollatzResearch.WordTrace]
  refine ⟨70717893878664061480536587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47145262585776040987024391 70717893878664061480536587)
  ·
    refine ⟨106076840817996092220804881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70717893878664061480536587 106076840817996092220804881)
    ·
      refine ⟨79557630613497069165603661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106076840817996092220804881 79557630613497069165603661)
      ·
        refine ⟨29834111480061400937101373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79557630613497069165603661 29834111480061400937101373)
        ·
          refine ⟨11187791805023025351413015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29834111480061400937101373 11187791805023025351413015)
          ·
            refine ⟨16781687707534538027119523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187791805023025351413015 16781687707534538027119523)
            ·
              refine ⟨25172531561301807040679285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781687707534538027119523 25172531561301807040679285)
              ·
                refine ⟨2359924833872044410063683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25172531561301807040679285 2359924833872044410063683)
                ·
                  refine ⟨3539887250808066615095525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359924833872044410063683 3539887250808066615095525)
                  ·
                    refine ⟨663728859526512490330411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539887250808066615095525 663728859526512490330411)
                    ·
                      rfl

theorem cell22_1938911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1938911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938911 prefixEnd_1938911 := by exact prefixLift 1938911
  have htrace : WordTrace (prefixWord ++ tailWord_1938911) baseStart_1938911 baseEnd_1938911 := by
    simpa [prefixWord, tailWord_1938911, baseEnd_1938911] using wordTrace_append hprefix tailTrace_1938911
  have hstable : (prefixWord ++ tailWord_1938911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938911).length < 2 ^ (prefixWord ++ tailWord_1938911).sum := by decide
  have hdescent : baseEnd_1938911 < baseStart_1938911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938924 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1938924 : Nat := 118140960795 + 1938924 * 2 ^ 59
def prefixEnd_1938924 : Nat := 4983230072969 + 3 ^ 40 * 1938924 * 2
def baseEnd_1938924 : Nat := 663733309692184789755371

theorem tailTrace_1938924 : CollatzResearch.WordTrace tailWord_1938924 prefixEnd_1938924 663733309692184789755371 := by
  unfold tailWord_1938924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35359184013808482350379913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47145578685077976467173217 35359184013808482350379913)
  ·
    refine ⟨26519388010356361762784935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35359184013808482350379913 26519388010356361762784935)
    ·
      refine ⟨39779082015534542644177403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26519388010356361762784935 39779082015534542644177403)
      ·
        refine ⟨59668623023301813966266105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39779082015534542644177403 59668623023301813966266105)
        ·
          refine ⟨44751467267476360474699579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59668623023301813966266105 44751467267476360474699579)
          ·
            refine ⟨67127200901214540712049369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44751467267476360474699579 67127200901214540712049369)
            ·
              refine ⟨50345400675910905534037027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67127200901214540712049369 50345400675910905534037027)
              ·
                refine ⟨75518101013866358301055541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50345400675910905534037027 75518101013866358301055541)
                ·
                  refine ⟨7079821970049971090723957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75518101013866358301055541 7079821970049971090723957)
                  ·
                    refine ⟨663733309692184789755371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7079821970049971090723957 663733309692184789755371)
                    ·
                      rfl

theorem cell22_1938924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1938924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938924 prefixEnd_1938924 := by exact prefixLift 1938924
  have htrace : WordTrace (prefixWord ++ tailWord_1938924) baseStart_1938924 baseEnd_1938924 := by
    simpa [prefixWord, tailWord_1938924, baseEnd_1938924] using wordTrace_append hprefix tailTrace_1938924
  have hstable : (prefixWord ++ tailWord_1938924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938924).length < 2 ^ (prefixWord ++ tailWord_1938924).sum := by decide
  have hdescent : baseEnd_1938924 < baseStart_1938924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938945 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1938945 : Nat := 118140960795 + 1938945 * 2 ^ 59
def prefixEnd_1938945 : Nat := 4983230072969 + 3 ^ 40 * 1938945 * 2
def baseEnd_1938945 : Nat := 663740498421347734980307

theorem tailTrace_1938945 : CollatzResearch.WordTrace tailWord_1938945 prefixEnd_1938945 663740498421347734980307 := by
  unfold tailWord_1938945
  simp only [CollatzResearch.WordTrace]
  refine ⟨70719133960540885287274289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47146089307027256858182859 70719133960540885287274289)
  ·
    refine ⟨53039350470405663965455717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70719133960540885287274289 53039350470405663965455717)
    ·
      refine ⟨9944878213201061993522947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53039350470405663965455717 9944878213201061993522947)
      ·
        refine ⟨14917317319801592990284421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944878213201061993522947 14917317319801592990284421)
        ·
          refine ⟨2796996997462798685678329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14917317319801592990284421 2796996997462798685678329)
          ·
            refine ⟨2097747748097099014258747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796996997462798685678329 2097747748097099014258747)
            ·
              refine ⟨3146621622145648521388121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097747748097099014258747 3146621622145648521388121)
              ·
                refine ⟨2359966216609236391041091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146621622145648521388121 2359966216609236391041091)
                ·
                  refine ⟨3539949324913854586561637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359966216609236391041091 3539949324913854586561637)
                  ·
                    refine ⟨663740498421347734980307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539949324913854586561637 663740498421347734980307)
                    ·
                      rfl

theorem cell22_1938945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1938945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938945 prefixEnd_1938945 := by exact prefixLift 1938945
  have htrace : WordTrace (prefixWord ++ tailWord_1938945) baseStart_1938945 baseEnd_1938945 := by
    simpa [prefixWord, tailWord_1938945, baseEnd_1938945] using wordTrace_append hprefix tailTrace_1938945
  have hstable : (prefixWord ++ tailWord_1938945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938945).length < 2 ^ (prefixWord ++ tailWord_1938945).sum := by decide
  have hdescent : baseEnd_1938945 < baseStart_1938945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938958 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1938958 : Nat := 118140960795 + 1938958 * 2 ^ 59
def prefixEnd_1938958 : Nat := 4983230072969 + 3 ^ 40 * 1938958 * 2
def baseEnd_1938958 : Nat := 663744948587020034405267

theorem tailTrace_1938958 : CollatzResearch.WordTrace tailWord_1938958 prefixEnd_1938958 663744948587020034405267 := by
  unfold tailWord_1938958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839951013686723563437191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47146405406329192338331685 8839951013686723563437191)
  ·
    refine ⟨13259926520530085345155787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839951013686723563437191 13259926520530085345155787)
    ·
      refine ⟨19889889780795128017733681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259926520530085345155787 19889889780795128017733681)
      ·
        refine ⟨14917417335596346013300261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19889889780795128017733681 14917417335596346013300261)
        ·
          refine ⟨2797015750424314877493799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14917417335596346013300261 2797015750424314877493799)
          ·
            refine ⟨4195523625636472316240699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797015750424314877493799 4195523625636472316240699)
            ·
              refine ⟨6293285438454708474361049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195523625636472316240699 6293285438454708474361049)
              ·
                refine ⟨4719964078841031355770787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293285438454708474361049 4719964078841031355770787)
                ·
                  refine ⟨7079946118261547033656181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719964078841031355770787 7079946118261547033656181)
                  ·
                    refine ⟨663744948587020034405267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7079946118261547033656181 663744948587020034405267)
                    ·
                      rfl

theorem cell22_1938958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1938958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1938958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1938958 prefixEnd_1938958 := by exact prefixLift 1938958
  have htrace : WordTrace (prefixWord ++ tailWord_1938958) baseStart_1938958 baseEnd_1938958 := by
    simpa [prefixWord, tailWord_1938958, baseEnd_1938958] using wordTrace_append hprefix tailTrace_1938958
  have hstable : (prefixWord ++ tailWord_1938958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938958).length < 2 ^ (prefixWord ++ tailWord_1938958).sum := by decide
  have hdescent : baseEnd_1938958 < baseStart_1938958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939020 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_1939020 : Nat := 118140960795 + 1939020 * 2 ^ 59
def prefixEnd_1939020 : Nat := 4983230072969 + 3 ^ 40 * 1939020 * 2
def baseEnd_1939020 : Nat := 663766172454072539355077

theorem tailTrace_1939020 : CollatzResearch.WordTrace tailWord_1939020 prefixEnd_1939020 663766172454072539355077 := by
  unfold tailWord_1939020
  simp only [CollatzResearch.WordTrace]
  refine ⟨35360934717634586548127257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47147912956846115397503009 35360934717634586548127257)
  ·
    refine ⟨26520701038225939911095443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35360934717634586548127257 26520701038225939911095443)
    ·
      refine ⟨39781051557338909866643165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26520701038225939911095443 39781051557338909866643165)
      ·
        refine ⟨14917894334002091199991187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39781051557338909866643165 14917894334002091199991187)
        ·
          refine ⟨22376841501003136799986781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917894334002091199991187 22376841501003136799986781)
          ·
            refine ⟨8391315562876176299995043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22376841501003136799986781 8391315562876176299995043)
            ·
              refine ⟨12586973344314264449992565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391315562876176299995043 12586973344314264449992565)
              ·
                refine ⟨1180028751029462292186803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12586973344314264449992565 1180028751029462292186803)
                ·
                  refine ⟨1770043126544193438280205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180028751029462292186803 1770043126544193438280205)
                  ·
                    refine ⟨663766172454072539355077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770043126544193438280205 663766172454072539355077)
                    ·
                      rfl

theorem cell22_1939020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_1939020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939020 prefixEnd_1939020 := by exact prefixLift 1939020
  have htrace : WordTrace (prefixWord ++ tailWord_1939020) baseStart_1939020 baseEnd_1939020 := by
    simpa [prefixWord, tailWord_1939020, baseEnd_1939020] using wordTrace_append hprefix tailTrace_1939020
  have hstable : (prefixWord ++ tailWord_1939020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939020).length < 2 ^ (prefixWord ++ tailWord_1939020).sum := by decide
  have hdescent : baseEnd_1939020 < baseStart_1939020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939031 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1939031 : Nat := 118140960795 + 1939031 * 2 ^ 59
def prefixEnd_1939031 : Nat := 4983230072969 + 3 ^ 40 * 1939031 * 2
def baseEnd_1939031 : Nat := 663769937978872177330043

theorem tailTrace_1939031 : CollatzResearch.WordTrace tailWord_1939031 prefixEnd_1939031 663769937978872177330043 := by
  unfold tailWord_1939031
  simp only [CollatzResearch.WordTrace]
  refine ⟨70722270638229321974904947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47148180425486214649936631 70722270638229321974904947)
  ·
    refine ⟨106083405957343982962357421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70722270638229321974904947 106083405957343982962357421)
    ·
      refine ⟨39781277234003993610884033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106083405957343982962357421 39781277234003993610884033)
      ·
        refine ⟨29835957925502995208163025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39781277234003993610884033 29835957925502995208163025)
        ·
          refine ⟨22376968444127246406122269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29835957925502995208163025 22376968444127246406122269)
          ·
            refine ⟨8391363166547717402295851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22376968444127246406122269 8391363166547717402295851)
            ·
              refine ⟨12587044749821576103443777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391363166547717402295851 12587044749821576103443777)
              ·
                refine ⟨9440283562366182077582833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12587044749821576103443777 9440283562366182077582833)
                ·
                  refine ⟨7080212671774636558187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440283562366182077582833 7080212671774636558187125)
                  ·
                    refine ⟨663769937978872177330043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7080212671774636558187125 663769937978872177330043)
                    ·
                      rfl

theorem cell22_1939031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1939031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939031 prefixEnd_1939031 := by exact prefixLift 1939031
  have htrace : WordTrace (prefixWord ++ tailWord_1939031) baseStart_1939031 baseEnd_1939031 := by
    simpa [prefixWord, tailWord_1939031, baseEnd_1939031] using wordTrace_append hprefix tailTrace_1939031
  have hstable : (prefixWord ++ tailWord_1939031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939031).length < 2 ^ (prefixWord ++ tailWord_1939031).sum := by decide
  have hdescent : baseEnd_1939031 < baseStart_1939031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939048 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1939048 : Nat := 118140960795 + 1939048 * 2 ^ 59
def prefixEnd_1939048 : Nat := 4983230072969 + 3 ^ 40 * 1939048 * 2
def baseEnd_1939048 : Nat := 663775757426289799654991

theorem tailTrace_1939048 : CollatzResearch.WordTrace tailWord_1939048 prefixEnd_1939048 663775757426289799654991 := by
  unfold tailWord_1939048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361445339583866939136899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47148593786111822585515865 35361445339583866939136899)
  ·
    refine ⟨53042168009375800408705349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35361445339583866939136899 53042168009375800408705349)
    ·
      refine ⟨9945406501757962576632253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53042168009375800408705349 9945406501757962576632253)
      ·
        refine ⟨3729527438159235966237095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9945406501757962576632253 3729527438159235966237095)
        ·
          refine ⟨5594291157238853949355643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729527438159235966237095 5594291157238853949355643)
          ·
            refine ⟨8391436735858280924033465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594291157238853949355643 8391436735858280924033465)
            ·
              refine ⟨6293577551893710693025099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391436735858280924033465 6293577551893710693025099)
              ·
                refine ⟨9440366327840566039537649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293577551893710693025099 9440366327840566039537649)
                ·
                  refine ⟨7080274745880424529653237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440366327840566039537649 7080274745880424529653237)
                  ·
                    refine ⟨663775757426289799654991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7080274745880424529653237 663775757426289799654991)
                    ·
                      rfl

theorem cell22_1939048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1939048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939048 prefixEnd_1939048 := by exact prefixLift 1939048
  have htrace : WordTrace (prefixWord ++ tailWord_1939048) baseStart_1939048 baseEnd_1939048 := by
    simpa [prefixWord, tailWord_1939048, baseEnd_1939048] using wordTrace_append hprefix tailTrace_1939048
  have hstable : (prefixWord ++ tailWord_1939048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939048).length < 2 ^ (prefixWord ++ tailWord_1939048).sum := by decide
  have hdescent : baseEnd_1939048 < baseStart_1939048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939050 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_1939050 : Nat := 118140960795 + 1939050 * 2 ^ 59
def prefixEnd_1939050 : Nat := 4983230072969 + 3 ^ 40 * 1939050 * 2
def baseEnd_1939050 : Nat := 221258814022387487034995

theorem tailTrace_1939050 : CollatzResearch.WordTrace tailWord_1939050 prefixEnd_1939050 221258814022387487034995 := by
  unfold tailWord_1939050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680740906290122054961651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47148642416773658813231069 17680740906290122054961651)
  ·
    refine ⟨26521111359435183082442477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17680740906290122054961651 26521111359435183082442477)
    ·
      refine ⟨9945416759788193655915929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26521111359435183082442477 9945416759788193655915929)
      ·
        refine ⟨7459062569841145241936947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9945416759788193655915929 7459062569841145241936947)
        ·
          refine ⟨11188593854761717862905421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459062569841145241936947 11188593854761717862905421)
          ·
            refine ⟨4195722695535644198589533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11188593854761717862905421 4195722695535644198589533)
            ·
              refine ⟨1573396010825866574471075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4195722695535644198589533 1573396010825866574471075)
              ·
                refine ⟨2360094016238799861706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573396010825866574471075 2360094016238799861706613)
                ·
                  refine ⟨221258814022387487034995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360094016238799861706613 221258814022387487034995)
                  ·
                    rfl

theorem cell22_1939050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_1939050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939050 prefixEnd_1939050 := by exact prefixLift 1939050
  have htrace : WordTrace (prefixWord ++ tailWord_1939050) baseStart_1939050 baseEnd_1939050 := by
    simpa [prefixWord, tailWord_1939050, baseEnd_1939050] using wordTrace_append hprefix tailTrace_1939050
  have hstable : (prefixWord ++ tailWord_1939050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939050).length < 2 ^ (prefixWord ++ tailWord_1939050).sum := by decide
  have hdescent : baseEnd_1939050 < baseStart_1939050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939151 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 7]
def baseStart_1939151 : Nat := 118140960795 + 1939151 * 2 ^ 59
def prefixEnd_1939151 : Nat := 4983230072969 + 3 ^ 40 * 1939151 * 2
def baseEnd_1939151 : Nat := 221270338810410621443225

theorem tailTrace_1939151 : CollatzResearch.WordTrace tailWord_1939151 prefixEnd_1939151 221270338810410621443225 := by
  unfold tailWord_1939151
  simp only [CollatzResearch.WordTrace]
  refine ⟨70726647397794582469273307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47151098265196388312848871 70726647397794582469273307)
  ·
    refine ⟨106089971096691873703909961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70726647397794582469273307 106089971096691873703909961)
    ·
      refine ⟨79567478322518905277932471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106089971096691873703909961 79567478322518905277932471)
      ·
        refine ⟨119351217483778357916898707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79567478322518905277932471 119351217483778357916898707)
        ·
          refine ⟨179026826225667536875348061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119351217483778357916898707 179026826225667536875348061)
          ·
            refine ⟨67135059834625326328255523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179026826225667536875348061 67135059834625326328255523)
            ·
              refine ⟨100702589751937989492383285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67135059834625326328255523 100702589751937989492383285)
              ·
                refine ⟨9440867789244186514910933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100702589751937989492383285 9440867789244186514910933)
                ·
                  refine ⟨221270338810410621443225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9440867789244186514910933 221270338810410621443225)
                  ·
                    rfl

theorem cell22_1939151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_1939151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939151 prefixEnd_1939151 := by exact prefixLift 1939151
  have htrace : WordTrace (prefixWord ++ tailWord_1939151) baseStart_1939151 baseEnd_1939151 := by
    simpa [prefixWord, tailWord_1939151, baseEnd_1939151] using wordTrace_append hprefix tailTrace_1939151
  have hstable : (prefixWord ++ tailWord_1939151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939151).length < 2 ^ (prefixWord ++ tailWord_1939151).sum := by decide
  have hdescent : baseEnd_1939151 < baseStart_1939151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939168 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_1939168 : Nat := 118140960795 + 1939168 * 2 ^ 59
def prefixEnd_1939168 : Nat := 4983230072969 + 3 ^ 40 * 1939168 * 2
def baseEnd_1939168 : Nat := 221272278626216495551541

theorem tailTrace_1939168 : CollatzResearch.WordTrace tailWord_1939168 prefixEnd_1939168 221272278626216495551541 := by
  unfold tailWord_1939168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35363633719366497186321079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47151511625821996248428105 35363633719366497186321079)
  ·
    refine ⟨53045450579049745779481619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35363633719366497186321079 53045450579049745779481619)
    ·
      refine ⟨79568175868574618669222429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53045450579049745779481619 79568175868574618669222429)
      ·
        refine ⟨29838065950715482000958411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79568175868574618669222429 29838065950715482000958411)
        ·
          refine ⟨44757098926073223001437617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29838065950715482000958411 44757098926073223001437617)
          ·
            refine ⟨33567824194554917251078213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44757098926073223001437617 33567824194554917251078213)
            ·
              refine ⟨6293967036479046984577165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33567824194554917251078213 6293967036479046984577165)
              ·
                refine ⟨2360237638679642619216437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293967036479046984577165 2360237638679642619216437)
                ·
                  refine ⟨221272278626216495551541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360237638679642619216437 221272278626216495551541)
                  ·
                    rfl

theorem cell22_1939168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_1939168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939168 prefixEnd_1939168 := by exact prefixLift 1939168
  have htrace : WordTrace (prefixWord ++ tailWord_1939168) baseStart_1939168 baseEnd_1939168 := by
    simpa [prefixWord, tailWord_1939168, baseEnd_1939168] using wordTrace_append hprefix tailTrace_1939168
  have hstable : (prefixWord ++ tailWord_1939168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939168).length < 2 ^ (prefixWord ++ tailWord_1939168).sum := by decide
  have hdescent : baseEnd_1939168 < baseStart_1939168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939258 : List Nat := [3, 1, 1, 1, 5, 1, 10]
def baseStart_1939258 : Nat := 118140960795 + 1939258 * 2 ^ 59
def prefixEnd_1939258 : Nat := 4983230072969 + 3 ^ 40 * 1939258 * 2
def baseEnd_1939258 : Nat := 24586949804367379700161

theorem tailTrace_1939258 : CollatzResearch.WordTrace tailWord_1939258 prefixEnd_1939258 24586949804367379700161 := by
  unfold tailWord_1939258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682637502101734935854607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47153700005604626495612285 17682637502101734935854607)
  ·
    refine ⟨26523956253152602403781911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17682637502101734935854607 26523956253152602403781911)
    ·
      refine ⟨39785934379728903605672867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26523956253152602403781911 39785934379728903605672867)
      ·
        refine ⟨59678901569593355408509301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39785934379728903605672867 59678901569593355408509301)
        ·
          refine ⟨5594897022149377069547747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59678901569593355408509301 5594897022149377069547747)
          ·
            refine ⟨8392345533224065604321621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594897022149377069547747 8392345533224065604321621)
            ·
              refine ⟨24586949804367379700161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8392345533224065604321621 24586949804367379700161)
              ·
                rfl

theorem cell22_1939258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 10].length) (baseStart_1939258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939258 prefixEnd_1939258 := by exact prefixLift 1939258
  have htrace : WordTrace (prefixWord ++ tailWord_1939258) baseStart_1939258 baseEnd_1939258 := by
    simpa [prefixWord, tailWord_1939258, baseEnd_1939258] using wordTrace_append hprefix tailTrace_1939258
  have hstable : (prefixWord ++ tailWord_1939258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939258).length < 2 ^ (prefixWord ++ tailWord_1939258).sum := by decide
  have hdescent : baseEnd_1939258 < baseStart_1939258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939262 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1939262 : Nat := 118140960795 + 1939262 * 2 ^ 59
def prefixEnd_1939262 : Nat := 4983230072969 + 3 ^ 40 * 1939262 * 2
def baseEnd_1939262 : Nat := 663849013999664574804335

theorem tailTrace_1939262 : CollatzResearch.WordTrace tailWord_1939262 prefixEnd_1939262 663849013999664574804335 := by
  unfold tailWord_1939262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841336987549056053320505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47153797266928298951042693 8841336987549056053320505)
  ·
    refine ⟨6631002740661792039990379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8841336987549056053320505 6631002740661792039990379)
    ·
      refine ⟨9946504110992688059985569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631002740661792039990379 9946504110992688059985569)
      ·
        refine ⟨7459878083244516044989177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946504110992688059985569 7459878083244516044989177)
        ·
          refine ⟨5594908562433387033741883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7459878083244516044989177 5594908562433387033741883)
          ·
            refine ⟨8392362843650080550612825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594908562433387033741883 8392362843650080550612825)
            ·
              refine ⟨6294272132737560412959619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392362843650080550612825 6294272132737560412959619)
              ·
                refine ⟨9441408199106340619439429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294272132737560412959619 9441408199106340619439429)
                ·
                  refine ⟨1770264037332438866144893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9441408199106340619439429 1770264037332438866144893)
                  ·
                    refine ⟨663849013999664574804335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770264037332438866144893 663849013999664574804335)
                    ·
                      rfl

theorem cell22_1939262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1939262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939262 prefixEnd_1939262 := by exact prefixLift 1939262
  have htrace : WordTrace (prefixWord ++ tailWord_1939262) baseStart_1939262 baseEnd_1939262 := by
    simpa [prefixWord, tailWord_1939262, baseEnd_1939262] using wordTrace_append hprefix tailTrace_1939262
  have hstable : (prefixWord ++ tailWord_1939262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939262).length < 2 ^ (prefixWord ++ tailWord_1939262).sum := by decide
  have hdescent : baseEnd_1939262 < baseStart_1939262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939290 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1939290 : Nat := 118140960795 + 1939290 * 2 ^ 59
def prefixEnd_1939290 : Nat := 4983230072969 + 3 ^ 40 * 1939290 * 2
def baseEnd_1939290 : Nat := 663858598971881835104249

theorem tailTrace_1939290 : CollatzResearch.WordTrace tailWord_1939290 prefixEnd_1939290 663858598971881835104249 := by
  unfold tailWord_1939290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682929286072752302145831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47154478096194006139055549 17682929286072752302145831)
  ·
    refine ⟨26524393929109128453218747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17682929286072752302145831 26524393929109128453218747)
    ·
      refine ⟨39786590893663692679828121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26524393929109128453218747 39786590893663692679828121)
      ·
        refine ⟨29839943170247769509871091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39786590893663692679828121 29839943170247769509871091)
        ·
          refine ⟨44759914755371654264806637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29839943170247769509871091 44759914755371654264806637)
          ·
            refine ⟨16784968033264370349302489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44759914755371654264806637 16784968033264370349302489)
            ·
              refine ⟨12588726024948277761976867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16784968033264370349302489 12588726024948277761976867)
              ·
                refine ⟨18883089037422416642965301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588726024948277761976867 18883089037422416642965301)
                ·
                  refine ⟨1770289597258351560277997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18883089037422416642965301 1770289597258351560277997)
                  ·
                    refine ⟨663858598971881835104249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770289597258351560277997 663858598971881835104249)
                    ·
                      rfl

theorem cell22_1939290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1939290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939290 prefixEnd_1939290 := by exact prefixLift 1939290
  have htrace : WordTrace (prefixWord ++ tailWord_1939290) baseStart_1939290 baseEnd_1939290 := by
    simpa [prefixWord, tailWord_1939290, baseEnd_1939290] using wordTrace_append hprefix tailTrace_1939290
  have hstable : (prefixWord ++ tailWord_1939290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939290).length < 2 ^ (prefixWord ++ tailWord_1939290).sum := by decide
  have hdescent : baseEnd_1939290 < baseStart_1939290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939307 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 1, 3]
def baseStart_1939307 : Nat := 118140960795 + 1939307 * 2 ^ 59
def prefixEnd_1939307 : Nat := 4983230072969 + 3 ^ 40 * 1939307 * 2
def baseEnd_1939307 : Nat := 663864418419299457429197

theorem tailTrace_1939307 : CollatzResearch.WordTrace tailWord_1939307 prefixEnd_1939307 663864418419299457429197 := by
  unfold tailWord_1939307
  simp only [CollatzResearch.WordTrace]
  refine ⟨70732337185229421111952175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47154891456819614074634783 70732337185229421111952175)
  ·
    refine ⟨106098505777844131667928263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70732337185229421111952175 106098505777844131667928263)
    ·
      refine ⟨159147758666766197501892395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106098505777844131667928263 159147758666766197501892395)
      ·
        refine ⟨238721638000149296252838593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159147758666766197501892395 238721638000149296252838593)
        ·
          refine ⟨179041228500111972189628945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238721638000149296252838593 179041228500111972189628945)
          ·
            refine ⟨134280921375083979142221709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179041228500111972189628945 134280921375083979142221709)
            ·
              refine ⟨50355345515656492178333141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134280921375083979142221709 50355345515656492178333141)
              ·
                refine ⟨1180203410523199035429683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50355345515656492178333141 1180203410523199035429683)
                ·
                  refine ⟨1770305115784798553144525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180203410523199035429683 1770305115784798553144525)
                  ·
                    refine ⟨663864418419299457429197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770305115784798553144525 663864418419299457429197)
                    ·
                      rfl

theorem cell22_1939307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 3].length) (baseStart_1939307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939307 prefixEnd_1939307 := by exact prefixLift 1939307
  have htrace : WordTrace (prefixWord ++ tailWord_1939307) baseStart_1939307 baseEnd_1939307 := by
    simpa [prefixWord, tailWord_1939307, baseEnd_1939307] using wordTrace_append hprefix tailTrace_1939307
  have hstable : (prefixWord ++ tailWord_1939307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939307).length < 2 ^ (prefixWord ++ tailWord_1939307).sum := by decide
  have hdescent : baseEnd_1939307 < baseStart_1939307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939412 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1939412 : Nat := 118140960795 + 1939412 * 2 ^ 59
def prefixEnd_1939412 : Nat := 4983230072969 + 3 ^ 40 * 1939412 * 2
def baseEnd_1939412 : Nat := 663900362065114183553875

theorem tailTrace_1939412 : CollatzResearch.WordTrace tailWord_1939412 prefixEnd_1939412 663900362065114183553875 := by
  unfold tailWord_1939412
  simp only [CollatzResearch.WordTrace]
  refine ⟨35368083424924512022262245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47157444566566016029682993 35368083424924512022262245)
  ·
    refine ⟨6631515642173346004174171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35368083424924512022262245 6631515642173346004174171)
    ·
      refine ⟨9947273463260019006261257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631515642173346004174171 9947273463260019006261257)
      ·
        refine ⟨7460455097445014254695943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9947273463260019006261257 7460455097445014254695943)
        ·
          refine ⟨11190682646167521382043915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460455097445014254695943 11190682646167521382043915)
          ·
            refine ⟨16786023969251282073065873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190682646167521382043915 16786023969251282073065873)
            ·
              refine ⟨12589517976938461554799405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16786023969251282073065873 12589517976938461554799405)
              ·
                refine ⟨4721069241351923083049777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12589517976938461554799405 4721069241351923083049777)
                ·
                  refine ⟨3540801931013942312287333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721069241351923083049777 3540801931013942312287333)
                  ·
                    refine ⟨663900362065114183553875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3540801931013942312287333 663900362065114183553875)
                    ·
                      rfl

theorem cell22_1939412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1939412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939412 prefixEnd_1939412 := by exact prefixLift 1939412
  have htrace : WordTrace (prefixWord ++ tailWord_1939412) baseStart_1939412 baseEnd_1939412 := by
    simpa [prefixWord, tailWord_1939412, baseEnd_1939412] using wordTrace_append hprefix tailTrace_1939412
  have hstable : (prefixWord ++ tailWord_1939412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939412).length < 2 ^ (prefixWord ++ tailWord_1939412).sum := by decide
  have hdescent : baseEnd_1939412 < baseStart_1939412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939489 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 5]
def baseStart_1939489 : Nat := 118140960795 + 1939489 * 2 ^ 59
def prefixEnd_1939489 : Nat := 4983230072969 + 3 ^ 40 * 1939489 * 2
def baseEnd_1939489 : Nat := 221308906912903883126213

theorem tailTrace_1939489 : CollatzResearch.WordTrace tailWord_1939489 prefixEnd_1939489 221308906912903883126213 := by
  unfold tailWord_1939489
  simp only [CollatzResearch.WordTrace]
  refine ⟨70738975270570066195077521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47159316847046710796718347 70738975270570066195077521)
  ·
    refine ⟨53054231452927549646308141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70738975270570066195077521 53054231452927549646308141)
    ·
      refine ⟨19895336794847831117365553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53054231452927549646308141 19895336794847831117365553)
      ·
        refine ⟨14921502596135873338024165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19895336794847831117365553 14921502596135873338024165)
        ·
          refine ⟨2797781736775476250879531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14921502596135873338024165 2797781736775476250879531)
          ·
            refine ⟨4196672605163214376319297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797781736775476250879531 4196672605163214376319297)
            ·
              refine ⟨3147504453872410782239473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196672605163214376319297 3147504453872410782239473)
              ·
                refine ⟨2360628340404308086679605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147504453872410782239473 2360628340404308086679605)
                ·
                  refine ⟨221308906912903883126213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360628340404308086679605 221308906912903883126213)
                  ·
                    rfl

theorem cell22_1939489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_1939489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939489 prefixEnd_1939489 := by exact prefixLift 1939489
  have htrace : WordTrace (prefixWord ++ tailWord_1939489) baseStart_1939489 baseEnd_1939489 := by
    simpa [prefixWord, tailWord_1939489, baseEnd_1939489] using wordTrace_append hprefix tailTrace_1939489
  have hstable : (prefixWord ++ tailWord_1939489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939489).length < 2 ^ (prefixWord ++ tailWord_1939489).sum := by decide
  have hdescent : baseEnd_1939489 < baseStart_1939489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939493 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_1939493 : Nat := 118140960795 + 1939493 * 2 ^ 59
def prefixEnd_1939493 : Nat := 4983230072969 + 3 ^ 40 * 1939493 * 2
def baseEnd_1939493 : Nat := 663928090020456972278627

theorem tailTrace_1939493 : CollatzResearch.WordTrace tailWord_1939493 prefixEnd_1939493 663928090020456972278627 := by
  unfold tailWord_1939493
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739121162555574878223133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47159414108370383252148755 70739121162555574878223133)
  ·
    refine ⟨26527170435958340579333675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70739121162555574878223133 26527170435958340579333675)
    ·
      refine ⟨39790755653937510869000513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26527170435958340579333675 39790755653937510869000513)
      ·
        refine ⟨29843066740453133151750385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39790755653937510869000513 29843066740453133151750385)
        ·
          refine ⟨22382300055339849863812789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29843066740453133151750385 22382300055339849863812789)
          ·
            refine ⟨2098340630188110924732449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22382300055339849863812789 2098340630188110924732449)
            ·
              refine ⟨1573755472641083193549337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098340630188110924732449 1573755472641083193549337)
              ·
                refine ⟨1180316604480812395162003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573755472641083193549337 1180316604480812395162003)
                ·
                  refine ⟨1770474906721218592743005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180316604480812395162003 1770474906721218592743005)
                  ·
                    refine ⟨663928090020456972278627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770474906721218592743005 663928090020456972278627)
                    ·
                      rfl

theorem cell22_1939493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_1939493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939493 prefixEnd_1939493 := by exact prefixLift 1939493
  have htrace : WordTrace (prefixWord ++ tailWord_1939493) baseStart_1939493 baseEnd_1939493 := by
    simpa [prefixWord, tailWord_1939493, baseEnd_1939493] using wordTrace_append hprefix tailTrace_1939493
  have hstable : (prefixWord ++ tailWord_1939493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939493).length < 2 ^ (prefixWord ++ tailWord_1939493).sum := by decide
  have hdescent : baseEnd_1939493 < baseStart_1939493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939515 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_1939515 : Nat := 118140960795 + 1939515 * 2 ^ 59
def prefixEnd_1939515 : Nat := 4983230072969 + 3 ^ 40 * 1939515 * 2
def baseEnd_1939515 : Nat := 663935621070056248228559

theorem tailTrace_1939515 : CollatzResearch.WordTrace tailWord_1939515 prefixEnd_1939515 663935621070056248228559 := by
  unfold tailWord_1939515
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739923568475872635523999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47159949045650581757015999 70739923568475872635523999)
  ·
    refine ⟨106109885352713808953285999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70739923568475872635523999 106109885352713808953285999)
    ·
      refine ⟨159164828029070713429928999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106109885352713808953285999 159164828029070713429928999)
      ·
        refine ⟨238747242043606070144893499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159164828029070713429928999 238747242043606070144893499)
        ·
          refine ⟨358120863065409105217340249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238747242043606070144893499 358120863065409105217340249)
          ·
            refine ⟨268590647299056828913005187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358120863065409105217340249 268590647299056828913005187)
            ·
              refine ⟨402885970948585243369507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268590647299056828913005187 402885970948585243369507781)
              ·
                refine ⟨75541119552859733131782709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402885970948585243369507781 75541119552859733131782709)
                ·
                  refine ⟨7081979958080599981104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75541119552859733131782709 7081979958080599981104629)
                  ·
                    refine ⟨663935621070056248228559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7081979958080599981104629 663935621070056248228559)
                    ·
                      rfl

theorem cell22_1939515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_1939515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939515 prefixEnd_1939515 := by exact prefixLift 1939515
  have htrace : WordTrace (prefixWord ++ tailWord_1939515) baseStart_1939515 baseEnd_1939515 := by
    simpa [prefixWord, tailWord_1939515, baseEnd_1939515] using wordTrace_append hprefix tailTrace_1939515
  have hstable : (prefixWord ++ tailWord_1939515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939515).length < 2 ^ (prefixWord ++ tailWord_1939515).sum := by decide
  have hdescent : baseEnd_1939515 < baseStart_1939515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939517 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 6]
def baseStart_1939517 : Nat := 118140960795 + 1939517 * 2 ^ 59
def prefixEnd_1939517 : Nat := 4983230072969 + 3 ^ 40 * 1939517 * 2
def baseEnd_1939517 : Nat := 221312101903642969892851

theorem tailTrace_1939517 : CollatzResearch.WordTrace tailWord_1939517 prefixEnd_1939517 221312101903642969892851 := by
  unfold tailWord_1939517
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739996514468626977096805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47159997676312417984731203 70739996514468626977096805)
  ·
    refine ⟨13263749346462867558205651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70739996514468626977096805 13263749346462867558205651)
    ·
      refine ⟨19895624019694301337308477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13263749346462867558205651 19895624019694301337308477)
      ·
        refine ⟨7460859007385363001490679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19895624019694301337308477 7460859007385363001490679)
        ·
          refine ⟨11191288511078044502236019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460859007385363001490679 11191288511078044502236019)
          ·
            refine ⟨16786932766617066753354029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191288511078044502236019 16786932766617066753354029)
            ·
              refine ⟨6295099787481400032507761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16786932766617066753354029 6295099787481400032507761)
              ·
                refine ⟨4721324840611050024380821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295099787481400032507761 4721324840611050024380821)
                ·
                  refine ⟨221312101903642969892851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4721324840611050024380821 221312101903642969892851)
                  ·
                    rfl

theorem cell22_1939517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_1939517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939517 prefixEnd_1939517 := by exact prefixLift 1939517
  have htrace : WordTrace (prefixWord ++ tailWord_1939517) baseStart_1939517 baseEnd_1939517 := by
    simpa [prefixWord, tailWord_1939517, baseEnd_1939517] using wordTrace_append hprefix tailTrace_1939517
  have hstable : (prefixWord ++ tailWord_1939517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939517).length < 2 ^ (prefixWord ++ tailWord_1939517).sum := by decide
  have hdescent : baseEnd_1939517 < baseStart_1939517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939532 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_1939532 : Nat := 118140960795 + 1939532 * 2 ^ 59
def prefixEnd_1939532 : Nat := 4983230072969 + 3 ^ 40 * 1939532 * 2
def baseEnd_1939532 : Nat := 663941440517473870553507

theorem tailTrace_1939532 : CollatzResearch.WordTrace tailWord_1939532 prefixEnd_1939532 663941440517473870553507 := by
  unfold tailWord_1939532
  simp only [CollatzResearch.WordTrace]
  refine ⟨35370271804707142269446425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47160362406276189692595233 35370271804707142269446425)
  ·
    refine ⟨26527703853530356702084819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35370271804707142269446425 26527703853530356702084819)
    ·
      refine ⟨39791555780295535053127229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26527703853530356702084819 39791555780295535053127229)
      ·
        refine ⟨14921833417610825644922711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39791555780295535053127229 14921833417610825644922711)
        ·
          refine ⟨22382750126416238467384067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14921833417610825644922711 22382750126416238467384067)
          ·
            refine ⟨33574125189624357701076101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22382750126416238467384067 33574125189624357701076101)
            ·
              refine ⟨6295148473054567068951769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33574125189624357701076101 6295148473054567068951769)
              ·
                refine ⟨4721361354790925301713827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295148473054567068951769 4721361354790925301713827)
                ·
                  refine ⟨7082042032186387952570741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721361354790925301713827 7082042032186387952570741)
                  ·
                    refine ⟨663941440517473870553507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7082042032186387952570741 663941440517473870553507)
                    ·
                      rfl

theorem cell22_1939532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_1939532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939532 prefixEnd_1939532 := by exact prefixLift 1939532
  have htrace : WordTrace (prefixWord ++ tailWord_1939532) baseStart_1939532 baseEnd_1939532 := by
    simpa [prefixWord, tailWord_1939532, baseEnd_1939532] using wordTrace_append hprefix tailTrace_1939532
  have hstable : (prefixWord ++ tailWord_1939532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939532).length < 2 ^ (prefixWord ++ tailWord_1939532).sum := by decide
  have hdescent : baseEnd_1939532 < baseStart_1939532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939534 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1939534 : Nat := 118140960795 + 1939534 * 2 ^ 59
def prefixEnd_1939534 : Nat := 4983230072969 + 3 ^ 40 * 1939534 * 2
def baseEnd_1939534 : Nat := 221314041719448844001167

theorem tailTrace_1939534 : CollatzResearch.WordTrace tailWord_1939534 prefixEnd_1939534 221314041719448844001167 := by
  unfold tailWord_1939534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842577069425879860058207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47160411036938025920310437 8842577069425879860058207)
  ·
    refine ⟨13263865604138819790087311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8842577069425879860058207 13263865604138819790087311)
    ·
      refine ⟨19895798406208229685130967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13263865604138819790087311 19895798406208229685130967)
      ·
        refine ⟨29843697609312344527696451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895798406208229685130967 29843697609312344527696451)
        ·
          refine ⟨44765546413968516791544677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843697609312344527696451 44765546413968516791544677)
          ·
            refine ⟨8393539952619096898414627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44765546413968516791544677 8393539952619096898414627)
            ·
              refine ⟨12590309928928645347621941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393539952619096898414627 12590309928928645347621941)
              ·
                refine ⟨1180341555837060501339557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12590309928928645347621941 1180341555837060501339557)
                ·
                  refine ⟨221314041719448844001167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180341555837060501339557 221314041719448844001167)
                  ·
                    rfl

theorem cell22_1939534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1939534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939534 prefixEnd_1939534 := by exact prefixLift 1939534
  have htrace : WordTrace (prefixWord ++ tailWord_1939534) baseStart_1939534 baseEnd_1939534 := by
    simpa [prefixWord, tailWord_1939534, baseEnd_1939534] using wordTrace_append hprefix tailTrace_1939534
  have hstable : (prefixWord ++ tailWord_1939534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939534).length < 2 ^ (prefixWord ++ tailWord_1939534).sum := by decide
  have hdescent : baseEnd_1939534 < baseStart_1939534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939545 : List Nat := [1, 2, 1, 2, 2, 1, 13]
def baseStart_1939545 : Nat := 118140960795 + 1939545 * 2 ^ 59
def prefixEnd_1939545 : Nat := 4983230072969 + 3 ^ 40 * 1939545 * 2
def baseEnd_1939545 : Nat := 24590588543820228517721

theorem tailTrace_1939545 : CollatzResearch.WordTrace tailWord_1939545 prefixEnd_1939545 24590588543820228517721 := by
  unfold tailWord_1939545
  simp only [CollatzResearch.WordTrace]
  refine ⟨70741017758367187759116089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47160678505578125172744059 70741017758367187759116089)
  ·
    refine ⟨53055763318775390819337067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70741017758367187759116089 53055763318775390819337067)
    ·
      refine ⟨79583644978163086229005601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53055763318775390819337067 79583644978163086229005601)
      ·
        refine ⟨59687733733622314671754201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79583644978163086229005601 59687733733622314671754201)
        ·
          refine ⟨44765800300216736003815651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59687733733622314671754201 44765800300216736003815651)
          ·
            refine ⟨67148700450325104005723477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44765800300216736003815651 67148700450325104005723477)
            ·
              refine ⟨24590588543820228517721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 67148700450325104005723477 24590588543820228517721)
              ·
                rfl

theorem cell22_1939545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 13].length) (baseStart_1939545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939545 prefixEnd_1939545 := by exact prefixLift 1939545
  have htrace : WordTrace (prefixWord ++ tailWord_1939545) baseStart_1939545 baseEnd_1939545 := by
    simpa [prefixWord, tailWord_1939545, baseEnd_1939545] using wordTrace_append hprefix tailTrace_1939545
  have hstable : (prefixWord ++ tailWord_1939545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939545).length < 2 ^ (prefixWord ++ tailWord_1939545).sum := by decide
  have hdescent : baseEnd_1939545 < baseStart_1939545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939684 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1939684 : Nat := 118140960795 + 1939684 * 2 ^ 59
def prefixEnd_1939684 : Nat := 4983230072969 + 3 ^ 40 * 1939684 * 2
def baseEnd_1939684 : Nat := 663993473223796140753041

theorem tailTrace_1939684 : CollatzResearch.WordTrace tailWord_1939684 prefixEnd_1939684 663993473223796140753041 := by
  unfold tailWord_1939684
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373043752431807249213053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47164058336575742998950737 35373043752431807249213053)
  ·
    refine ⟨13264891407161927718454895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35373043752431807249213053 13264891407161927718454895)
    ·
      refine ⟨19897337110742891577682343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264891407161927718454895 19897337110742891577682343)
      ·
        refine ⟨29846005666114337366523515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19897337110742891577682343 29846005666114337366523515)
        ·
          refine ⟨44769008499171506049785273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29846005666114337366523515 44769008499171506049785273)
          ·
            refine ⟨33576756374378629537338955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44769008499171506049785273 33576756374378629537338955)
            ·
              refine ⟨50365134561567944306008433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33576756374378629537338955 50365134561567944306008433)
              ·
                refine ⟨37773850921175958229506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50365134561567944306008433 37773850921175958229506325)
                ·
                  refine ⟨1770649261930123042008109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37773850921175958229506325 1770649261930123042008109)
                  ·
                    refine ⟨663993473223796140753041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770649261930123042008109 663993473223796140753041)
                    ·
                      rfl

theorem cell22_1939684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1939684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939684 prefixEnd_1939684 := by exact prefixLift 1939684
  have htrace : WordTrace (prefixWord ++ tailWord_1939684) baseStart_1939684 baseEnd_1939684 := by
    simpa [prefixWord, tailWord_1939684, baseEnd_1939684] using wordTrace_append hprefix tailTrace_1939684
  have hstable : (prefixWord ++ tailWord_1939684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939684).length < 2 ^ (prefixWord ++ tailWord_1939684).sum := by decide
  have hdescent : baseEnd_1939684 < baseStart_1939684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939697 : List Nat := [1, 2, 2, 2, 2, 1, 2, 10]
def baseStart_1939697 : Nat := 118140960795 + 1939697 * 2 ^ 59
def prefixEnd_1939697 : Nat := 4983230072969 + 3 ^ 40 * 1939697 * 2
def baseEnd_1939697 : Nat := 73777547043274271130889

theorem tailTrace_1939697 : CollatzResearch.WordTrace tailWord_1939697 prefixEnd_1939697 73777547043274271130889 := by
  unfold tailWord_1939697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70746561653816517718649345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47164374435877678479099563 70746561653816517718649345)
  ·
    refine ⟨53059921240362388288987009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70746561653816517718649345 53059921240362388288987009)
    ·
      refine ⟨39794940930271791216740257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53059921240362388288987009 39794940930271791216740257)
      ·
        refine ⟨29846205697703843412555193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39794940930271791216740257 29846205697703843412555193)
        ·
          refine ⟨22384654273277882559416395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29846205697703843412555193 22384654273277882559416395)
          ·
            refine ⟨33576981409916823839124593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22384654273277882559416395 33576981409916823839124593)
            ·
              refine ⟨25182736057437617879343445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33576981409916823839124593 25182736057437617879343445)
              ·
                refine ⟨73777547043274271130889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25182736057437617879343445 73777547043274271130889)
                ·
                  rfl

theorem cell22_1939697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 10].length) (baseStart_1939697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939697 prefixEnd_1939697 := by exact prefixLift 1939697
  have htrace : WordTrace (prefixWord ++ tailWord_1939697) baseStart_1939697 baseEnd_1939697 := by
    simpa [prefixWord, tailWord_1939697, baseEnd_1939697] using wordTrace_append hprefix tailTrace_1939697
  have hstable : (prefixWord ++ tailWord_1939697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939697).length < 2 ^ (prefixWord ++ tailWord_1939697).sum := by decide
  have hdescent : baseEnd_1939697 < baseStart_1939697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939727 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1939727 : Nat := 118140960795 + 1939727 * 2 ^ 59
def prefixEnd_1939727 : Nat := 4983230072969 + 3 ^ 40 * 1939727 * 2
def baseEnd_1939727 : Nat := 664008193002558361927909

theorem tailTrace_1939727 : CollatzResearch.WordTrace tailWord_1939727 prefixEnd_1939727 664008193002558361927909 := by
  unfold tailWord_1939727
  simp only [CollatzResearch.WordTrace]
  refine ⟨70747655843707832842241435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47165103895805221894827623 70747655843707832842241435)
  ·
    refine ⟨106121483765561749263362153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70747655843707832842241435 106121483765561749263362153)
    ·
      refine ⟨79591112824171311947521615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106121483765561749263362153 79591112824171311947521615)
      ·
        refine ⟨119386669236256967921282423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79591112824171311947521615 119386669236256967921282423)
        ·
          refine ⟨179080003854385451881923635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119386669236256967921282423 179080003854385451881923635)
          ·
            refine ⟨268620005781578177822885453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179080003854385451881923635 268620005781578177822885453)
            ·
              refine ⟨100732502168091816683582045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268620005781578177822885453 100732502168091816683582045)
              ·
                refine ⟨37774688313034431256343267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100732502168091816683582045 37774688313034431256343267)
                ·
                  refine ⟨56662032469551646884514901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37774688313034431256343267 56662032469551646884514901)
                  ·
                    refine ⟨664008193002558361927909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56662032469551646884514901 664008193002558361927909)
                    ·
                      rfl

theorem cell22_1939727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1939727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939727 prefixEnd_1939727 := by exact prefixLift 1939727
  have htrace : WordTrace (prefixWord ++ tailWord_1939727) baseStart_1939727 baseEnd_1939727 := by
    simpa [prefixWord, tailWord_1939727, baseEnd_1939727] using wordTrace_append hprefix tailTrace_1939727
  have hstable : (prefixWord ++ tailWord_1939727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939727).length < 2 ^ (prefixWord ++ tailWord_1939727).sum := by decide
  have hdescent : baseEnd_1939727 < baseStart_1939727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939793 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 5]
def baseStart_1939793 : Nat := 118140960795 + 1939793 * 2 ^ 59
def prefixEnd_1939793 : Nat := 4983230072969 + 3 ^ 40 * 1939793 * 2
def baseEnd_1939793 : Nat := 221343595383785396592569

theorem tailTrace_1939793 : CollatzResearch.WordTrace tailWord_1939793 prefixEnd_1939793 221343595383785396592569 := by
  unfold tailWord_1939793
  simp only [CollatzResearch.WordTrace]
  refine ⟨70750063061468726114144033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47166708707645817409429355 70750063061468726114144033)
  ·
    refine ⟨53062547296101544585608025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70750063061468726114144033 53062547296101544585608025)
    ·
      refine ⟨39796910472076158439206019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53062547296101544585608025 39796910472076158439206019)
      ·
        refine ⟨59695365708114237658809029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39796910472076158439206019 59695365708114237658809029)
        ·
          refine ⟨11192881070271419561026693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59695365708114237658809029 11192881070271419561026693)
          ·
            refine ⟨2098665200675891167692505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11192881070271419561026693 2098665200675891167692505)
            ·
              refine ⟨1573998900506918375769379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098665200675891167692505 1573998900506918375769379)
              ·
                refine ⟨2360998350760377563654069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573998900506918375769379 2360998350760377563654069)
                ·
                  refine ⟨221343595383785396592569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360998350760377563654069 221343595383785396592569)
                  ·
                    rfl

theorem cell22_1939793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_1939793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939793 prefixEnd_1939793 := by exact prefixLift 1939793
  have htrace : WordTrace (prefixWord ++ tailWord_1939793) baseStart_1939793 baseEnd_1939793 := by
    simpa [prefixWord, tailWord_1939793, baseEnd_1939793] using wordTrace_append hprefix tailTrace_1939793
  have hstable : (prefixWord ++ tailWord_1939793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939793).length < 2 ^ (prefixWord ++ tailWord_1939793).sum := by decide
  have hdescent : baseEnd_1939793 < baseStart_1939793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939819 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_1939819 : Nat := 118140960795 + 1939819 * 2 ^ 59
def prefixEnd_1939819 : Nat := 4983230072969 + 3 ^ 40 * 1939819 * 2
def baseEnd_1939819 : Nat := 664039686482700788627627

theorem tailTrace_1939819 : CollatzResearch.WordTrace tailWord_1939819 prefixEnd_1939819 664039686482700788627627 := by
  unfold tailWord_1939819
  simp only [CollatzResearch.WordTrace]
  refine ⟨70751011359374532554590511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47167340906249688369727007 70751011359374532554590511)
  ·
    refine ⟨106126517039061798831885767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70751011359374532554590511 106126517039061798831885767)
    ·
      refine ⟨159189775558592698247828651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106126517039061798831885767 159189775558592698247828651)
      ·
        refine ⟨238784663337889047371742977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159189775558592698247828651 238784663337889047371742977)
        ·
          refine ⟨179088497503416785528807233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238784663337889047371742977 179088497503416785528807233)
          ·
            refine ⟨134316373127562589146605425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179088497503416785528807233 134316373127562589146605425)
            ·
              refine ⟨100737279845671941859954069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134316373127562589146605425 100737279845671941859954069)
              ·
                refine ⟨4722059992765872274685347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100737279845671941859954069 4722059992765872274685347)
                ·
                  refine ⟨7083089989148808412028021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722059992765872274685347 7083089989148808412028021)
                  ·
                    refine ⟨664039686482700788627627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7083089989148808412028021 664039686482700788627627)
                    ·
                      rfl

theorem cell22_1939819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_1939819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939819 prefixEnd_1939819 := by exact prefixLift 1939819
  have htrace : WordTrace (prefixWord ++ tailWord_1939819) baseStart_1939819 baseEnd_1939819 := by
    simpa [prefixWord, tailWord_1939819, baseEnd_1939819] using wordTrace_append hprefix tailTrace_1939819
  have hstable : (prefixWord ++ tailWord_1939819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939819).length < 2 ^ (prefixWord ++ tailWord_1939819).sum := by decide
  have hdescent : baseEnd_1939819 < baseStart_1939819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939949 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_1939949 : Nat := 118140960795 + 1939949 * 2 ^ 59
def prefixEnd_1939949 : Nat := 4983230072969 + 3 ^ 40 * 1939949 * 2
def baseEnd_1939949 : Nat := 664084188139423782877229

theorem tailTrace_1939949 : CollatzResearch.WordTrace tailWord_1939949 prefixEnd_1939949 664084188139423782877229 := by
  unfold tailWord_1939949
  simp only [CollatzResearch.WordTrace]
  refine ⟨70755752848903564756822901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47170501899269043171215267 70755752848903564756822901)
  ·
    refine ⟨6633351829584709195952147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70755752848903564756822901 6633351829584709195952147)
    ·
      refine ⟨9950027744377063793928221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633351829584709195952147 9950027744377063793928221)
      ·
        refine ⟨3731260404141398922723083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9950027744377063793928221 3731260404141398922723083)
        ·
          refine ⟨5596890606212098384084625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731260404141398922723083 5596890606212098384084625)
          ·
            refine ⟨4197667954659073788063469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5596890606212098384084625 4197667954659073788063469)
            ·
              refine ⟨1574125482997152670523801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4197667954659073788063469 1574125482997152670523801)
              ·
                refine ⟨1180594112247864502892851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574125482997152670523801 1180594112247864502892851)
                ·
                  refine ⟨1770891168371796754339277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180594112247864502892851 1770891168371796754339277)
                  ·
                    refine ⟨664084188139423782877229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770891168371796754339277 664084188139423782877229)
                    ·
                      rfl

theorem cell22_1939949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_1939949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939949 prefixEnd_1939949 := by exact prefixLift 1939949
  have htrace : WordTrace (prefixWord ++ tailWord_1939949) baseStart_1939949 baseEnd_1939949 := by
    simpa [prefixWord, tailWord_1939949, baseEnd_1939949] using wordTrace_append hprefix tailTrace_1939949
  have hstable : (prefixWord ++ tailWord_1939949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939949).length < 2 ^ (prefixWord ++ tailWord_1939949).sum := by decide
  have hdescent : baseEnd_1939949 < baseStart_1939949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939958 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1939958 : Nat := 118140960795 + 1939958 * 2 ^ 59
def prefixEnd_1939958 : Nat := 4983230072969 + 3 ^ 40 * 1939958 * 2
def baseEnd_1939958 : Nat := 664087269023350759402201

theorem tailTrace_1939958 : CollatzResearch.WordTrace tailWord_1939958 prefixEnd_1939958 664087269023350759402201 := by
  unfold tailWord_1939958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422255069116934955868783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47170720737247306195933685 4422255069116934955868783)
  ·
    refine ⟨6633382603675402433803175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422255069116934955868783 6633382603675402433803175)
    ·
      refine ⟨9950073905513103650704763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633382603675402433803175 9950073905513103650704763)
      ·
        refine ⟨14925110858269655476057145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950073905513103650704763 14925110858269655476057145)
        ·
          refine ⟨11193833143702241607042859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14925110858269655476057145 11193833143702241607042859)
          ·
            refine ⟨16790749715553362410564289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11193833143702241607042859 16790749715553362410564289)
            ·
              refine ⟨12593062286665021807923217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16790749715553362410564289 12593062286665021807923217)
              ·
                refine ⟨9444796714998766355942413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12593062286665021807923217 9444796714998766355942413)
                ·
                  refine ⟨3541798768124537383478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9444796714998766355942413 3541798768124537383478405)
                  ·
                    refine ⟨664087269023350759402201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541798768124537383478405 664087269023350759402201)
                    ·
                      rfl

theorem cell22_1939958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1939958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939958 prefixEnd_1939958 := by exact prefixLift 1939958
  have htrace : WordTrace (prefixWord ++ tailWord_1939958) baseStart_1939958 baseEnd_1939958 := by
    simpa [prefixWord, tailWord_1939958, baseEnd_1939958] using wordTrace_append hprefix tailTrace_1939958
  have hstable : (prefixWord ++ tailWord_1939958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939958).length < 2 ^ (prefixWord ++ tailWord_1939958).sum := by decide
  have hdescent : baseEnd_1939958 < baseStart_1939958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939971 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_1939971 : Nat := 118140960795 + 1939971 * 2 ^ 59
def prefixEnd_1939971 : Nat := 4983230072969 + 3 ^ 40 * 1939971 * 2
def baseEnd_1939971 : Nat := 664091719189023058827161

theorem tailTrace_1939971 : CollatzResearch.WordTrace tailWord_1939971 prefixEnd_1939971 664091719189023058827161 := by
  unfold tailWord_1939971
  simp only [CollatzResearch.WordTrace]
  refine ⟨70756555254823862514123767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47171036836549241676082511 70756555254823862514123767)
  ·
    refine ⟨106134832882235793771185651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70756555254823862514123767 106134832882235793771185651)
    ·
      refine ⟨159202249323353690656778477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106134832882235793771185651 159202249323353690656778477)
      ·
        refine ⟨59700843496257633996291929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159202249323353690656778477 59700843496257633996291929)
        ·
          refine ⟨44775632622193225497218947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59700843496257633996291929 44775632622193225497218947)
          ·
            refine ⟨67163448933289838245828421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44775632622193225497218947 67163448933289838245828421)
            ·
              refine ⟨12593146674991844671092829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67163448933289838245828421 12593146674991844671092829)
              ·
                refine ⟨4722430003121941751659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12593146674991844671092829 4722430003121941751659811)
                ·
                  refine ⟨7083645004682912627489717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722430003121941751659811 7083645004682912627489717)
                  ·
                    refine ⟨664091719189023058827161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7083645004682912627489717 664091719189023058827161)
                    ·
                      rfl

theorem cell22_1939971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_1939971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1939971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1939971 prefixEnd_1939971 := by exact prefixLift 1939971
  have htrace : WordTrace (prefixWord ++ tailWord_1939971) baseStart_1939971 baseEnd_1939971 := by
    simpa [prefixWord, tailWord_1939971, baseEnd_1939971] using wordTrace_append hprefix tailTrace_1939971
  have hstable : (prefixWord ++ tailWord_1939971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939971).length < 2 ^ (prefixWord ++ tailWord_1939971).sum := by decide
  have hdescent : baseEnd_1939971 < baseStart_1939971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940003 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_1940003 : Nat := 118140960795 + 1940003 * 2 ^ 59
def prefixEnd_1940003 : Nat := 4983230072969 + 3 ^ 40 * 1940003 * 2
def baseEnd_1940003 : Nat := 664102673442985642027063

theorem tailTrace_1940003 : CollatzResearch.WordTrace tailWord_1940003 prefixEnd_1940003 664102673442985642027063 := by
  unfold tailWord_1940003
  simp only [CollatzResearch.WordTrace]
  refine ⟨70757722390707931979288663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47171814927138621319525775 70757722390707931979288663)
  ·
    refine ⟨106136583586061897968932995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70757722390707931979288663 106136583586061897968932995)
    ·
      refine ⟨159204875379092846953399493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106136583586061897968932995 159204875379092846953399493)
      ·
        refine ⟨29850914133579908803762405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159204875379092846953399493 29850914133579908803762405)
        ·
          refine ⟨5597046400046232900705451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29850914133579908803762405 5597046400046232900705451)
          ·
            refine ⟨8395569600069349351058177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597046400046232900705451 8395569600069349351058177)
            ·
              refine ⟨6296677200052012013293633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8395569600069349351058177 6296677200052012013293633)
              ·
                refine ⟨4722507900039009009970225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6296677200052012013293633 4722507900039009009970225)
                ·
                  refine ⟨3541880925029256757477669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722507900039009009970225 3541880925029256757477669)
                  ·
                    refine ⟨664102673442985642027063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541880925029256757477669 664102673442985642027063)
                    ·
                      rfl

theorem cell22_1940003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_1940003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940003 prefixEnd_1940003 := by exact prefixLift 1940003
  have htrace : WordTrace (prefixWord ++ tailWord_1940003) baseStart_1940003 baseEnd_1940003 := by
    simpa [prefixWord, tailWord_1940003, baseEnd_1940003] using wordTrace_append hprefix tailTrace_1940003
  have hstable : (prefixWord ++ tailWord_1940003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940003).length < 2 ^ (prefixWord ++ tailWord_1940003).sum := by decide
  have hdescent : baseEnd_1940003 < baseStart_1940003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940022 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1940022 : Nat := 118140960795 + 1940022 * 2 ^ 59
def prefixEnd_1940022 : Nat := 4983230072969 + 3 ^ 40 * 1940022 * 2
def baseEnd_1940022 : Nat := 664109177531275925802005

theorem tailTrace_1940022 : CollatzResearch.WordTrace tailWord_1940022 prefixEnd_1940022 664109177531275925802005 := by
  unfold tailWord_1940022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422400961102443639014395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47172276918426065482820213 4422400961102443639014395)
  ·
    refine ⟨6633601441653665458521593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422400961102443639014395 6633601441653665458521593)
    ·
      refine ⟨4975201081240249093891195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633601441653665458521593 4975201081240249093891195)
      ·
        refine ⟨7462801621860373640836793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975201081240249093891195 7462801621860373640836793)
        ·
          refine ⟨5597101216395280230627595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7462801621860373640836793 5597101216395280230627595)
          ·
            refine ⟨8395651824592920345941393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597101216395280230627595 8395651824592920345941393)
            ·
              refine ⟨6296738868444690259456045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8395651824592920345941393 6296738868444690259456045)
              ·
                refine ⟨2361277075666758847296017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6296738868444690259456045 2361277075666758847296017)
                ·
                  refine ⟨1770957806750069135472013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361277075666758847296017 1770957806750069135472013)
                  ·
                    refine ⟨664109177531275925802005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770957806750069135472013 664109177531275925802005)
                    ·
                      rfl

theorem cell22_1940022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1940022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940022 prefixEnd_1940022 := by exact prefixLift 1940022
  have htrace : WordTrace (prefixWord ++ tailWord_1940022) baseStart_1940022 baseEnd_1940022 := by
    simpa [prefixWord, tailWord_1940022, baseEnd_1940022] using wordTrace_append hprefix tailTrace_1940022
  have hstable : (prefixWord ++ tailWord_1940022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940022).length < 2 ^ (prefixWord ++ tailWord_1940022).sum := by decide
  have hdescent : baseEnd_1940022 < baseStart_1940022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940031 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1940031 : Nat := 118140960795 + 1940031 * 2 ^ 59
def prefixEnd_1940031 : Nat := 4983230072969 + 3 ^ 40 * 1940031 * 2
def baseEnd_1940031 : Nat := 664112258415202902326977

theorem tailTrace_1940031 : CollatzResearch.WordTrace tailWord_1940031 prefixEnd_1940031 664112258415202902326977 := by
  unfold tailWord_1940031
  simp only [CollatzResearch.WordTrace]
  refine ⟨70758743634606492761307947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47172495756404328507538631 70758743634606492761307947)
  ·
    refine ⟨106138115451909739141961921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70758743634606492761307947 106138115451909739141961921)
    ·
      refine ⟨79603586588932304356471441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106138115451909739141961921 79603586588932304356471441)
      ·
        refine ⟨59702689941699228267353581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79603586588932304356471441 59702689941699228267353581)
        ·
          refine ⟨22388508728137210600257593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59702689941699228267353581 22388508728137210600257593)
          ·
            refine ⟨16791381546102907950193195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22388508728137210600257593 16791381546102907950193195)
            ·
              refine ⟨25187072319154361925289793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791381546102907950193195 25187072319154361925289793)
              ·
                refine ⟨18890304239365771443967345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25187072319154361925289793 18890304239365771443967345)
                ·
                  refine ⟨14167728179524328582975509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18890304239365771443967345 14167728179524328582975509)
                  ·
                    refine ⟨664112258415202902326977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14167728179524328582975509 664112258415202902326977)
                    ·
                      rfl

theorem cell22_1940031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1940031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940031 prefixEnd_1940031 := by exact prefixLift 1940031
  have htrace : WordTrace (prefixWord ++ tailWord_1940031) baseStart_1940031 baseEnd_1940031 := by
    simpa [prefixWord, tailWord_1940031, baseEnd_1940031] using wordTrace_append hprefix tailTrace_1940031
  have hstable : (prefixWord ++ tailWord_1940031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940031).length < 2 ^ (prefixWord ++ tailWord_1940031).sum := by decide
  have hdescent : baseEnd_1940031 < baseStart_1940031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940091 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 8]
def baseStart_1940091 : Nat := 118140960795 + 1940091 * 2 ^ 59
def prefixEnd_1940091 : Nat := 4983230072969 + 3 ^ 40 * 1940091 * 2
def baseEnd_1940091 : Nat := 221377599213794248608931

theorem tailTrace_1940091 : CollatzResearch.WordTrace tailWord_1940091 prefixEnd_1940091 221377599213794248608931 := by
  unfold tailWord_1940091
  simp only [CollatzResearch.WordTrace]
  refine ⟨70760932014389123008492127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47173954676259415338994751 70760932014389123008492127)
  ·
    refine ⟨106141398021583684512738191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70760932014389123008492127 106141398021583684512738191)
    ·
      refine ⟨159212097032375526769107287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106141398021583684512738191 159212097032375526769107287)
      ·
        refine ⟨238818145548563290153660931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159212097032375526769107287 238818145548563290153660931)
        ·
          refine ⟨358227218322844935230491397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238818145548563290153660931 358227218322844935230491397)
          ·
            refine ⟨67167603435533425355717137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358227218322844935230491397 67167603435533425355717137)
            ·
              refine ⟨50375702576650069016787853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67167603435533425355717137 50375702576650069016787853)
              ·
                refine ⟨18890888466243775881295445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50375702576650069016787853 18890888466243775881295445)
                ·
                  refine ⟨221377599213794248608931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18890888466243775881295445 221377599213794248608931)
                  ·
                    rfl

theorem cell22_1940091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_1940091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940091 prefixEnd_1940091 := by exact prefixLift 1940091
  have htrace : WordTrace (prefixWord ++ tailWord_1940091) baseStart_1940091 baseEnd_1940091 := by
    simpa [prefixWord, tailWord_1940091, baseEnd_1940091] using wordTrace_append hprefix tailTrace_1940091
  have hstable : (prefixWord ++ tailWord_1940091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940091).length < 2 ^ (prefixWord ++ tailWord_1940091).sum := by decide
  have hdescent : baseEnd_1940091 < baseStart_1940091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940110 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1940110 : Nat := 118140960795 + 1940110 * 2 ^ 59
def prefixEnd_1940110 : Nat := 4983230072969 + 3 ^ 40 * 1940110 * 2
def baseEnd_1940110 : Nat := 664139301729673029601735

theorem tailTrace_1940110 : CollatzResearch.WordTrace tailWord_1940110 prefixEnd_1940110 664139301729673029601735 := by
  unfold tailWord_1940110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845203125165036156679223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47174416667546859502289189 8845203125165036156679223)
  ·
    refine ⟨13267804687747554235018835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8845203125165036156679223 13267804687747554235018835)
    ·
      refine ⟨19901707031621331352528253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13267804687747554235018835 19901707031621331352528253)
      ·
        refine ⟨7463140136857999257198095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19901707031621331352528253 7463140136857999257198095)
        ·
          refine ⟨11194710205286998885797143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463140136857999257198095 11194710205286998885797143)
          ·
            refine ⟨16792065307930498328695715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11194710205286998885797143 16792065307930498328695715)
            ·
              refine ⟨25188097961895747493043573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16792065307930498328695715 25188097961895747493043573)
              ·
                refine ⟨2361384183927726327472835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25188097961895747493043573 2361384183927726327472835)
                ·
                  refine ⟨3542076275891589491209253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361384183927726327472835 3542076275891589491209253)
                  ·
                    refine ⟨664139301729673029601735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3542076275891589491209253 664139301729673029601735)
                    ·
                      rfl

theorem cell22_1940110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1940110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940110 prefixEnd_1940110 := by exact prefixLift 1940110
  have htrace : WordTrace (prefixWord ++ tailWord_1940110) baseStart_1940110 baseEnd_1940110 := by
    simpa [prefixWord, tailWord_1940110, baseEnd_1940110] using wordTrace_append hprefix tailTrace_1940110
  have hstable : (prefixWord ++ tailWord_1940110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940110).length < 2 ^ (prefixWord ++ tailWord_1940110).sum := by decide
  have hdescent : baseEnd_1940110 < baseStart_1940110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940125 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 4]
def baseStart_1940125 : Nat := 118140960795 + 1940125 * 2 ^ 59
def prefixEnd_1940125 : Nat := 4983230072969 + 3 ^ 40 * 1940125 * 2
def baseEnd_1940125 : Nat := 221381478845405996825563

theorem tailTrace_1940125 : CollatzResearch.WordTrace tailWord_1940125 prefixEnd_1940125 221381478845405996825563 := by
  unfold tailWord_1940125
  simp only [CollatzResearch.WordTrace]
  refine ⟨70762172096265946815229829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47174781397510631210153219 70762172096265946815229829)
  ·
    refine ⟨13267907268049865027855593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70762172096265946815229829 13267907268049865027855593)
    ·
      refine ⟨9950930451037398770891695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13267907268049865027855593 9950930451037398770891695)
      ·
        refine ⟨14926395676556098156337543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950930451037398770891695 14926395676556098156337543)
        ·
          refine ⟨22389593514834147234506315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926395676556098156337543 22389593514834147234506315)
          ·
            refine ⟨33584390272251220851759473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22389593514834147234506315 33584390272251220851759473)
            ·
              refine ⟨25188292704188415638819605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33584390272251220851759473 25188292704188415638819605)
              ·
                refine ⟨1180701220508831983069669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25188292704188415638819605 1180701220508831983069669)
                ·
                  refine ⟨221381478845405996825563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180701220508831983069669 221381478845405996825563)
                  ·
                    rfl

theorem cell22_1940125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_1940125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940125 prefixEnd_1940125 := by exact prefixLift 1940125
  have htrace : WordTrace (prefixWord ++ tailWord_1940125) baseStart_1940125 baseEnd_1940125 := by
    simpa [prefixWord, tailWord_1940125, baseEnd_1940125] using wordTrace_append hprefix tailTrace_1940125
  have hstable : (prefixWord ++ tailWord_1940125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940125).length < 2 ^ (prefixWord ++ tailWord_1940125).sum := by decide
  have hdescent : baseEnd_1940125 < baseStart_1940125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940161 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1940161 : Nat := 118140960795 + 1940161 * 2 ^ 59
def prefixEnd_1940161 : Nat := 4983230072969 + 3 ^ 40 * 1940161 * 2
def baseEnd_1940161 : Nat := 664156760071925896576579

theorem tailTrace_1940161 : CollatzResearch.WordTrace tailWord_1940161 prefixEnd_1940161 664156760071925896576579 := by
  unfold tailWord_1940161
  simp only [CollatzResearch.WordTrace]
  refine ⟨70763485124135524963540337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47175656749423683309026891 70763485124135524963540337)
  ·
    refine ⟨53072613843101643722655253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70763485124135524963540337 53072613843101643722655253)
    ·
      refine ⟨2487778773895389549499465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53072613843101643722655253 2487778773895389549499465)
      ·
        refine ⟨1865834080421542162124599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2487778773895389549499465 1865834080421542162124599)
        ·
          refine ⟨2798751120632313243186899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865834080421542162124599 2798751120632313243186899)
          ·
            refine ⟨4198126680948469864780349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798751120632313243186899 4198126680948469864780349)
            ·
              refine ⟨1574297505355676199292631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198126680948469864780349 1574297505355676199292631)
              ·
                refine ⟨2361446258033514298938947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574297505355676199292631 2361446258033514298938947)
                ·
                  refine ⟨3542169387050271448408421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361446258033514298938947 3542169387050271448408421)
                  ·
                    refine ⟨664156760071925896576579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3542169387050271448408421 664156760071925896576579)
                    ·
                      rfl

theorem cell22_1940161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1940161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940161 prefixEnd_1940161 := by exact prefixLift 1940161
  have htrace : WordTrace (prefixWord ++ tailWord_1940161) baseStart_1940161 baseEnd_1940161 := by
    simpa [prefixWord, tailWord_1940161, baseEnd_1940161] using wordTrace_append hprefix tailTrace_1940161
  have hstable : (prefixWord ++ tailWord_1940161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940161).length < 2 ^ (prefixWord ++ tailWord_1940161).sum := by decide
  have hdescent : baseEnd_1940161 < baseStart_1940161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940183 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1940183 : Nat := 118140960795 + 1940183 * 2 ^ 59
def prefixEnd_1940183 : Nat := 4983230072969 + 3 ^ 40 * 1940183 * 2
def baseEnd_1940183 : Nat := 664164291121525172526511

theorem tailTrace_1940183 : CollatzResearch.WordTrace tailWord_1940183 prefixEnd_1940183 664164291121525172526511 := by
  unfold tailWord_1940183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70764287530055822720841203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47176191686703881813894135 70764287530055822720841203)
  ·
    refine ⟨106146431295083734081261805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70764287530055822720841203 106146431295083734081261805)
    ·
      refine ⟨39804911735656400280473177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106146431295083734081261805 39804911735656400280473177)
      ·
        refine ⟨29853683801742300210354883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39804911735656400280473177 29853683801742300210354883)
        ·
          refine ⟨44780525702613450315532325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29853683801742300210354883 44780525702613450315532325)
          ·
            refine ⟨8396348569240021934162311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44780525702613450315532325 8396348569240021934162311)
            ·
              refine ⟨12594522853860032901243467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396348569240021934162311 12594522853860032901243467)
              ·
                refine ⟨18891784280790049351865201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594522853860032901243467 18891784280790049351865201)
                ·
                  refine ⟨14168838210592537013898901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18891784280790049351865201 14168838210592537013898901)
                  ·
                    refine ⟨664164291121525172526511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14168838210592537013898901 664164291121525172526511)
                    ·
                      rfl

theorem cell22_1940183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1940183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940183 prefixEnd_1940183 := by exact prefixLift 1940183
  have htrace : WordTrace (prefixWord ++ tailWord_1940183) baseStart_1940183 baseEnd_1940183 := by
    simpa [prefixWord, tailWord_1940183, baseEnd_1940183] using wordTrace_append hprefix tailTrace_1940183
  have hstable : (prefixWord ++ tailWord_1940183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940183).length < 2 ^ (prefixWord ++ tailWord_1940183).sum := by decide
  have hdescent : baseEnd_1940183 < baseStart_1940183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940185 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_1940185 : Nat := 118140960795 + 1940185 * 2 ^ 59
def prefixEnd_1940185 : Nat := 4983230072969 + 3 ^ 40 * 1940185 * 2
def baseEnd_1940185 : Nat := 664164975762397833976505

theorem tailTrace_1940185 : CollatzResearch.WordTrace tailWord_1940185 prefixEnd_1940185 664164975762397833976505 := by
  unfold tailWord_1940185
  simp only [CollatzResearch.WordTrace]
  refine ⟨70764360476048577062414009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47176240317365718041609339 70764360476048577062414009)
  ·
    refine ⟨53073270357036432796810507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70764360476048577062414009 53073270357036432796810507)
    ·
      refine ⟨79609905535554649195215761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53073270357036432796810507 79609905535554649195215761)
      ·
        refine ⟨59707429151665986896411821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79609905535554649195215761 59707429151665986896411821)
        ·
          refine ⟨22390285931874745086154433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59707429151665986896411821 22390285931874745086154433)
          ·
            refine ⟨16792714448906058814615825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22390285931874745086154433 16792714448906058814615825)
            ·
              refine ⟨12594535836679544110961869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792714448906058814615825 12594535836679544110961869)
              ·
                refine ⟨4722950938754829041610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12594535836679544110961869 4722950938754829041610701)
                ·
                  refine ⟨1771106602033060890604013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4722950938754829041610701 1771106602033060890604013)
                  ·
                    refine ⟨664164975762397833976505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771106602033060890604013 664164975762397833976505)
                    ·
                      rfl

theorem cell22_1940185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_1940185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940185 prefixEnd_1940185 := by exact prefixLift 1940185
  have htrace : WordTrace (prefixWord ++ tailWord_1940185) baseStart_1940185 baseEnd_1940185 := by
    simpa [prefixWord, tailWord_1940185, baseEnd_1940185] using wordTrace_append hprefix tailTrace_1940185
  have hstable : (prefixWord ++ tailWord_1940185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940185).length < 2 ^ (prefixWord ++ tailWord_1940185).sum := by decide
  have hdescent : baseEnd_1940185 < baseStart_1940185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940232 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_1940232 : Nat := 118140960795 + 1940232 * 2 ^ 59
def prefixEnd_1940232 : Nat := 4983230072969 + 3 ^ 40 * 1940232 * 2
def baseEnd_1940232 : Nat := 221393688274301792683787

theorem tailTrace_1940232 : CollatzResearch.WordTrace tailWord_1940232 prefixEnd_1940232 221393688274301792683787 := by
  unfold tailWord_1940232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35383037353439152044687475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47177383137918869392916633 35383037353439152044687475)
  ·
    refine ⟨53074556030158728067031213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35383037353439152044687475 53074556030158728067031213)
    ·
      refine ⟨19902958511309523025136705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53074556030158728067031213 19902958511309523025136705)
      ·
        refine ⟨14927218883482142268852529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19902958511309523025136705 14927218883482142268852529)
        ·
          refine ⟨11195414162611606701639397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927218883482142268852529 11195414162611606701639397)
          ·
            refine ⟨2099140155489676256557387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11195414162611606701639397 2099140155489676256557387)
            ·
              refine ⟨3148710233234514384836081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099140155489676256557387 3148710233234514384836081)
              ·
                refine ⟨2361532674925885788627061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148710233234514384836081 2361532674925885788627061)
                ·
                  refine ⟨221393688274301792683787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361532674925885788627061 221393688274301792683787)
                  ·
                    rfl

theorem cell22_1940232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_1940232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940232 prefixEnd_1940232 := by exact prefixLift 1940232
  have htrace : WordTrace (prefixWord ++ tailWord_1940232) baseStart_1940232 baseEnd_1940232 := by
    simpa [prefixWord, tailWord_1940232, baseEnd_1940232] using wordTrace_append hprefix tailTrace_1940232
  have hstable : (prefixWord ++ tailWord_1940232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940232).length < 2 ^ (prefixWord ++ tailWord_1940232).sum := by decide
  have hdescent : baseEnd_1940232 < baseStart_1940232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940401 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 5]
def baseStart_1940401 : Nat := 118140960795 + 1940401 * 2 ^ 59
def prefixEnd_1940401 : Nat := 4983230072969 + 3 ^ 40 * 1940401 * 2
def baseEnd_1940401 : Nat := 221412972325548423525281

theorem tailTrace_1940401 : CollatzResearch.WordTrace tailWord_1940401 prefixEnd_1940401 221412972325548423525281 := by
  unfold tailWord_1940401
  simp only [CollatzResearch.WordTrace]
  refine ⟨70772238643266045952277057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47181492428844030634851371 70772238643266045952277057)
  ·
    refine ⟨53079178982449534464207793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70772238643266045952277057 53079178982449534464207793)
    ·
      refine ⟨39809384236837150848155845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53079178982449534464207793 39809384236837150848155845)
      ·
        refine ⟨7464259544406965784029221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39809384236837150848155845 7464259544406965784029221)
        ·
          refine ⟨1399548664576306084505479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7464259544406965784029221 1399548664576306084505479)
          ·
            refine ⟨2099322996864459126758219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399548664576306084505479 2099322996864459126758219)
            ·
              refine ⟨3148984495296688690137329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099322996864459126758219 3148984495296688690137329)
              ·
                refine ⟨2361738371472516517602997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148984495296688690137329 2361738371472516517602997)
                ·
                  refine ⟨221412972325548423525281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361738371472516517602997 221412972325548423525281)
                  ·
                    rfl

theorem cell22_1940401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_1940401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940401 prefixEnd_1940401 := by exact prefixLift 1940401
  have htrace : WordTrace (prefixWord ++ tailWord_1940401) baseStart_1940401 baseEnd_1940401 := by
    simpa [prefixWord, tailWord_1940401, baseEnd_1940401] using wordTrace_append hprefix tailTrace_1940401
  have hstable : (prefixWord ++ tailWord_1940401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940401).length < 2 ^ (prefixWord ++ tailWord_1940401).sum := by decide
  have hdescent : baseEnd_1940401 < baseStart_1940401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940427 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_1940427 : Nat := 118140960795 + 1940427 * 2 ^ 59
def prefixEnd_1940427 : Nat := 4983230072969 + 3 ^ 40 * 1940427 * 2
def baseEnd_1940427 : Nat := 664247817307989869425763

theorem tailTrace_1940427 : CollatzResearch.WordTrace tailWord_1940427 prefixEnd_1940427 664247817307989869425763 := by
  unfold tailWord_1940427
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773186941171852392723535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47182124627447901595149023 70773186941171852392723535)
  ·
    refine ⟨106159780411757778589085303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70773186941171852392723535 106159780411757778589085303)
    ·
      refine ⟨159239670617636667883627955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106159780411757778589085303 159239670617636667883627955)
      ·
        refine ⟨238859505926455001825441933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159239670617636667883627955 238859505926455001825441933)
        ·
          refine ⟨89572314722420625684540725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238859505926455001825441933 89572314722420625684540725)
          ·
            refine ⟨8397404505226933657925693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89572314722420625684540725 8397404505226933657925693)
            ·
              refine ⟨3149026689460100121722135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8397404505226933657925693 3149026689460100121722135)
              ·
                refine ⟨4723540034190150182583203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149026689460100121722135 4723540034190150182583203)
                ·
                  refine ⟨7085310051285225273874805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723540034190150182583203 7085310051285225273874805)
                  ·
                    refine ⟨664247817307989869425763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7085310051285225273874805 664247817307989869425763)
                    ·
                      rfl

theorem cell22_1940427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_1940427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940427 prefixEnd_1940427 := by exact prefixLift 1940427
  have htrace : WordTrace (prefixWord ++ tailWord_1940427) baseStart_1940427 baseEnd_1940427 := by
    simpa [prefixWord, tailWord_1940427, baseEnd_1940427] using wordTrace_append hprefix tailTrace_1940427
  have hstable : (prefixWord ++ tailWord_1940427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940427).length < 2 ^ (prefixWord ++ tailWord_1940427).sum := by decide
  have hdescent : baseEnd_1940427 < baseStart_1940427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940442 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1940442 : Nat := 118140960795 + 1940442 * 2 ^ 59
def prefixEnd_1940442 : Nat := 4983230072969 + 3 ^ 40 * 1940442 * 2
def baseEnd_1940442 : Nat := 664252952114534830300717

theorem tailTrace_1940442 : CollatzResearch.WordTrace tailWord_1940442 prefixEnd_1940442 664252952114534830300717 := by
  unfold tailWord_1940442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693433509029377488629895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47182489357411673303013053 17693433509029377488629895)
  ·
    refine ⟨26540150263544066232944843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693433509029377488629895 26540150263544066232944843)
    ·
      refine ⟨39810225395316099349417265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26540150263544066232944843 39810225395316099349417265)
      ·
        refine ⟨29857669046487074512062949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39810225395316099349417265 29857669046487074512062949)
        ·
          refine ⟨5598312946216326471011803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29857669046487074512062949 5598312946216326471011803)
          ·
            refine ⟨8397469419324489706517705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598312946216326471011803 8397469419324489706517705)
            ·
              refine ⟨6298102064493367279888279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397469419324489706517705 6298102064493367279888279)
              ·
                refine ⟨9447153096740050919832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298102064493367279888279 9447153096740050919832419)
                ·
                  refine ⟨14170729645110076379748629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9447153096740050919832419 14170729645110076379748629)
                  ·
                    refine ⟨664252952114534830300717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14170729645110076379748629 664252952114534830300717)
                    ·
                      rfl

theorem cell22_1940442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1940442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940442 prefixEnd_1940442 := by exact prefixLift 1940442
  have htrace : WordTrace (prefixWord ++ tailWord_1940442) baseStart_1940442 baseEnd_1940442 := by
    simpa [prefixWord, tailWord_1940442, baseEnd_1940442] using wordTrace_append hprefix tailTrace_1940442
  have hstable : (prefixWord ++ tailWord_1940442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940442).length < 2 ^ (prefixWord ++ tailWord_1940442).sum := by decide
  have hdescent : baseEnd_1940442 < baseStart_1940442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940478 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1940478 : Nat := 118140960795 + 1940478 * 2 ^ 59
def prefixEnd_1940478 : Nat := 4983230072969 + 3 ^ 40 * 1940478 * 2
def baseEnd_1940478 : Nat := 664265275650242736400607

theorem tailTrace_1940478 : CollatzResearch.WordTrace tailWord_1940478 prefixEnd_1940478 664265275650242736400607 := by
  unfold tailWord_1940478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846880882998386012853761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47183364709324725401886725 8846880882998386012853761)
  ·
    refine ⟨6635160662248789509640321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8846880882998386012853761 6635160662248789509640321)
    ·
      refine ⟨4976370496686592132230241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635160662248789509640321 4976370496686592132230241)
      ·
        refine ⟨3732277872514944099172681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4976370496686592132230241 3732277872514944099172681)
        ·
          refine ⟨2799208404386208074379511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732277872514944099172681 2799208404386208074379511)
          ·
            refine ⟨4198812606579312111569267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799208404386208074379511 4198812606579312111569267)
            ·
              refine ⟨6298218909868968167353901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198812606579312111569267 6298218909868968167353901)
              ·
                refine ⟨2361832091200863062757713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298218909868968167353901 2361832091200863062757713)
                ·
                  refine ⟨1771374068400647297068285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361832091200863062757713 1771374068400647297068285)
                  ·
                    refine ⟨664265275650242736400607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771374068400647297068285 664265275650242736400607)
                    ·
                      rfl

theorem cell22_1940478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1940478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940478 prefixEnd_1940478 := by exact prefixLift 1940478
  have htrace : WordTrace (prefixWord ++ tailWord_1940478) baseStart_1940478 baseEnd_1940478 := by
    simpa [prefixWord, tailWord_1940478, baseEnd_1940478] using wordTrace_append hprefix tailTrace_1940478
  have hstable : (prefixWord ++ tailWord_1940478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940478).length < 2 ^ (prefixWord ++ tailWord_1940478).sum := by decide
  have hdescent : baseEnd_1940478 < baseStart_1940478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940506 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_1940506 : Nat := 118140960795 + 1940506 * 2 ^ 59
def prefixEnd_1940506 : Nat := 4983230072969 + 3 ^ 40 * 1940506 * 2
def baseEnd_1940506 : Nat := 664274860622459996700521

theorem tailTrace_1940506 : CollatzResearch.WordTrace tailWord_1940506 prefixEnd_1940506 664274860622459996700521 := by
  unfold tailWord_1940506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694017076971412221212343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47184045538590432589899581 17694017076971412221212343)
  ·
    refine ⟨26541025615457118331818515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694017076971412221212343 26541025615457118331818515)
    ·
      refine ⟨39811538423185677497727773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26541025615457118331818515 39811538423185677497727773)
      ·
        refine ⟨14929326908694629061647915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39811538423185677497727773 14929326908694629061647915)
        ·
          refine ⟨22393990363041943592471873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14929326908694629061647915 22393990363041943592471873)
          ·
            refine ⟨16795492772281457694353905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22393990363041943592471873 16795492772281457694353905)
            ·
              refine ⟨12596619579211093270765429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16795492772281457694353905 12596619579211093270765429)
              ·
                refine ⟨1180933085551039994134259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12596619579211093270765429 1180933085551039994134259)
                ·
                  refine ⟨1771399628326559991201389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180933085551039994134259 1771399628326559991201389)
                  ·
                    refine ⟨664274860622459996700521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771399628326559991201389 664274860622459996700521)
                    ·
                      rfl

theorem cell22_1940506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_1940506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940506 prefixEnd_1940506 := by exact prefixLift 1940506
  have htrace : WordTrace (prefixWord ++ tailWord_1940506) baseStart_1940506 baseEnd_1940506 := by
    simpa [prefixWord, tailWord_1940506, baseEnd_1940506] using wordTrace_append hprefix tailTrace_1940506
  have hstable : (prefixWord ++ tailWord_1940506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940506).length < 2 ^ (prefixWord ++ tailWord_1940506).sum := by decide
  have hdescent : baseEnd_1940506 < baseStart_1940506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940517 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1940517 : Nat := 118140960795 + 1940517 * 2 ^ 59
def prefixEnd_1940517 : Nat := 4983230072969 + 3 ^ 40 * 1940517 * 2
def baseEnd_1940517 : Nat := 664278626147259634675487

theorem tailTrace_1940517 : CollatzResearch.WordTrace tailWord_1940517 prefixEnd_1940517 664278626147259634675487 := by
  unfold tailWord_1940517
  simp only [CollatzResearch.WordTrace]
  refine ⟨70776469510845797763499805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47184313007230531842333203 70776469510845797763499805)
  ·
    refine ⟨26541176066567174161312427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70776469510845797763499805 26541176066567174161312427)
    ·
      refine ⟨39811764099850761241968641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26541176066567174161312427 39811764099850761241968641)
      ·
        refine ⟨29858823074888070931476481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39811764099850761241968641 29858823074888070931476481)
        ·
          refine ⟨22394117306166053198607361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29858823074888070931476481 22394117306166053198607361)
          ·
            refine ⟨16795587979624539898955521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22394117306166053198607361 16795587979624539898955521)
            ·
              refine ⟨12596690984718404924216641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16795587979624539898955521 12596690984718404924216641)
              ·
                refine ⟨9447518238538803693162481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12596690984718404924216641 9447518238538803693162481)
                ·
                  refine ⟨7085638678904102769871861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9447518238538803693162481 7085638678904102769871861)
                  ·
                    refine ⟨664278626147259634675487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7085638678904102769871861 664278626147259634675487)
                    ·
                      rfl

theorem cell22_1940517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1940517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940517 prefixEnd_1940517 := by exact prefixLift 1940517
  have htrace : WordTrace (prefixWord ++ tailWord_1940517) baseStart_1940517 baseEnd_1940517 := by
    simpa [prefixWord, tailWord_1940517, baseEnd_1940517] using wordTrace_append hprefix tailTrace_1940517
  have hstable : (prefixWord ++ tailWord_1940517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940517).length < 2 ^ (prefixWord ++ tailWord_1940517).sum := by decide
  have hdescent : baseEnd_1940517 < baseStart_1940517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940534 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1940534 : Nat := 118140960795 + 1940534 * 2 ^ 59
def prefixEnd_1940534 : Nat := 4983230072969 + 3 ^ 40 * 1940534 * 2
def baseEnd_1940534 : Nat := 664284445594677257000435

theorem tailTrace_1940534 : CollatzResearch.WordTrace tailWord_1940534 prefixEnd_1940534 664284445594677257000435 := by
  unfold tailWord_1940534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423568096986513104179291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47184726367856139777912437 4423568096986513104179291)
  ·
    refine ⟨6635352145479769656268937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4423568096986513104179291 6635352145479769656268937)
    ·
      refine ⟨4976514109109827242201703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635352145479769656268937 4976514109109827242201703)
      ·
        refine ⟨7464771163664740863302555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976514109109827242201703 7464771163664740863302555)
        ·
          refine ⟨11197156745497111294953833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464771163664740863302555 11197156745497111294953833)
          ·
            refine ⟨8397867559122833471215375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11197156745497111294953833 8397867559122833471215375)
            ·
              refine ⟨12596801338684250206823063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397867559122833471215375 12596801338684250206823063)
              ·
                refine ⟨18895202008026375310234595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596801338684250206823063 18895202008026375310234595)
                ·
                  refine ⟨28342803012039562965351893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18895202008026375310234595 28342803012039562965351893)
                  ·
                    refine ⟨664284445594677257000435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28342803012039562965351893 664284445594677257000435)
                    ·
                      rfl

theorem cell22_1940534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1940534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940534 prefixEnd_1940534 := by exact prefixLift 1940534
  have htrace : WordTrace (prefixWord ++ tailWord_1940534) baseStart_1940534 baseEnd_1940534 := by
    simpa [prefixWord, tailWord_1940534, baseEnd_1940534] using wordTrace_append hprefix tailTrace_1940534
  have hstable : (prefixWord ++ tailWord_1940534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940534).length < 2 ^ (prefixWord ++ tailWord_1940534).sum := by decide
  have hdescent : baseEnd_1940534 < baseStart_1940534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940547 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 6]
def baseStart_1940547 : Nat := 118140960795 + 1940547 * 2 ^ 59
def prefixEnd_1940547 : Nat := 4983230072969 + 3 ^ 40 * 1940547 * 2
def baseEnd_1940547 : Nat := 221429631920116518808465

theorem tailTrace_1940547 : CollatzResearch.WordTrace tailWord_1940547 prefixEnd_1940547 221429631920116518808465 := by
  unfold tailWord_1940547
  simp only [CollatzResearch.WordTrace]
  refine ⟨70777563700737112887091895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47185042467158075258061263 70777563700737112887091895)
  ·
    refine ⟨106166345551105669330637843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70777563700737112887091895 106166345551105669330637843)
    ·
      refine ⟨159249518326658503995956765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106166345551105669330637843 159249518326658503995956765)
      ·
        refine ⟨59718569372496938998483787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159249518326658503995956765 59718569372496938998483787)
        ·
          refine ⟨89577854058745408497725681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59718569372496938998483787 89577854058745408497725681)
          ·
            refine ⟨67183390544059056373294261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89577854058745408497725681 67183390544059056373294261)
            ·
              refine ⟨6298442863505536534996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67183390544059056373294261 6298442863505536534996337)
              ·
                refine ⟨4723832147629152401247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6298442863505536534996337 4723832147629152401247253)
                ·
                  refine ⟨221429631920116518808465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4723832147629152401247253 221429631920116518808465)
                  ·
                    rfl

theorem cell22_1940547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_1940547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940547 prefixEnd_1940547 := by exact prefixLift 1940547
  have htrace : WordTrace (prefixWord ++ tailWord_1940547) baseStart_1940547 baseEnd_1940547 := by
    simpa [prefixWord, tailWord_1940547, baseEnd_1940547] using wordTrace_append hprefix tailTrace_1940547
  have hstable : (prefixWord ++ tailWord_1940547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940547).length < 2 ^ (prefixWord ++ tailWord_1940547).sum := by decide
  have hdescent : baseEnd_1940547 < baseStart_1940547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940592 : List Nat := [2, 1, 1, 1, 5, 1, 2, 9]
def baseStart_1940592 : Nat := 118140960795 + 1940592 * 2 ^ 59
def prefixEnd_1940592 : Nat := 4983230072969 + 3 ^ 40 * 1940592 * 2
def baseEnd_1940592 : Nat := 73811588908887159894473

theorem tailTrace_1940592 : CollatzResearch.WordTrace tailWord_1940592 prefixEnd_1940592 73811588908887159894473 := by
  unfold tailWord_1940592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35389602492787042786240015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47186136657049390381653353 35389602492787042786240015)
  ·
    refine ⟨53084403739180564179360023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35389602492787042786240015 53084403739180564179360023)
    ·
      refine ⟨79626605608770846269040035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53084403739180564179360023 79626605608770846269040035)
      ·
        refine ⟨119439908413156269403560053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79626605608770846269040035 119439908413156269403560053)
        ·
          refine ⟨11197491413733400256583755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119439908413156269403560053 11197491413733400256583755)
          ·
            refine ⟨16796237120600100384875633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197491413733400256583755 16796237120600100384875633)
            ·
              refine ⟨12597177840450075288656725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16796237120600100384875633 12597177840450075288656725)
              ·
                refine ⟨73811588908887159894473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12597177840450075288656725 73811588908887159894473)
                ·
                  rfl

theorem cell22_1940592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_1940592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940592 prefixEnd_1940592 := by exact prefixLift 1940592
  have htrace : WordTrace (prefixWord ++ tailWord_1940592) baseStart_1940592 baseEnd_1940592 := by
    simpa [prefixWord, tailWord_1940592, baseEnd_1940592] using wordTrace_append hprefix tailTrace_1940592
  have hstable : (prefixWord ++ tailWord_1940592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940592).length < 2 ^ (prefixWord ++ tailWord_1940592).sum := by decide
  have hdescent : baseEnd_1940592 < baseStart_1940592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940609 : List Nat := [1, 2, 4, 2, 2, 2, 1, 8]
def baseStart_1940609 : Nat := 118140960795 + 1940609 * 2 ^ 59
def prefixEnd_1940609 : Nat := 4983230072969 + 3 ^ 40 * 1940609 * 2
def baseEnd_1940609 : Nat := 73812235514155784597245

theorem tailTrace_1940609 : CollatzResearch.WordTrace tailWord_1940609 prefixEnd_1940609 73812235514155784597245 := by
  unfold tailWord_1940609
  simp only [CollatzResearch.WordTrace]
  refine ⟨70779825026512497475848881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47186550017674998317232587 70779825026512497475848881)
  ·
    refine ⟨53084868769884373106886661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70779825026512497475848881 53084868769884373106886661)
    ·
      refine ⟨9953412894353319957541249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53084868769884373106886661 9953412894353319957541249)
      ·
        refine ⟨7465059670764989968155937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9953412894353319957541249 7465059670764989968155937)
        ·
          refine ⟨5598794753073742476116953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465059670764989968155937 5598794753073742476116953)
          ·
            refine ⟨4199096064805306857087715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598794753073742476116953 4199096064805306857087715)
            ·
              refine ⟨6298644097207960285631573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199096064805306857087715 6298644097207960285631573)
              ·
                refine ⟨73812235514155784597245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6298644097207960285631573 73812235514155784597245)
                ·
                  rfl

theorem cell22_1940609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 8].length) (baseStart_1940609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940609 prefixEnd_1940609 := by exact prefixLift 1940609
  have htrace : WordTrace (prefixWord ++ tailWord_1940609) baseStart_1940609 baseEnd_1940609 := by
    simpa [prefixWord, tailWord_1940609, baseEnd_1940609] using wordTrace_append hprefix tailTrace_1940609
  have hstable : (prefixWord ++ tailWord_1940609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940609).length < 2 ^ (prefixWord ++ tailWord_1940609).sum := by decide
  have hdescent : baseEnd_1940609 < baseStart_1940609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940692 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1940692 : Nat := 118140960795 + 1940692 * 2 ^ 59
def prefixEnd_1940692 : Nat := 4983230072969 + 3 ^ 40 * 1940692 * 2
def baseEnd_1940692 : Nat := 664338532223617511549951

theorem tailTrace_1940692 : CollatzResearch.WordTrace tailWord_1940692 prefixEnd_1940692 664338532223617511549951 := by
  unfold tailWord_1940692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35391426142605901325560165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47188568190141201767413553 35391426142605901325560165)
  ·
    refine ⟨6635892401738606498542531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35391426142605901325560165 6635892401738606498542531)
    ·
      refine ⟨9953838602607909747813797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635892401738606498542531 9953838602607909747813797)
      ·
        refine ⟨1866344737988983077715087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9953838602607909747813797 1866344737988983077715087)
        ·
          refine ⟨2799517106983474616572631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866344737988983077715087 2799517106983474616572631)
          ·
            refine ⟨4199275660475211924858947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799517106983474616572631 4199275660475211924858947)
            ·
              refine ⟨6298913490712817887288421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199275660475211924858947 6298913490712817887288421)
              ·
                refine ⟨1181046279508653353866579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6298913490712817887288421 1181046279508653353866579)
                ·
                  refine ⟨1771569419262980030799869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181046279508653353866579 1771569419262980030799869)
                  ·
                    refine ⟨664338532223617511549951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771569419262980030799869 664338532223617511549951)
                    ·
                      rfl

theorem cell22_1940692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1940692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940692 prefixEnd_1940692 := by exact prefixLift 1940692
  have htrace : WordTrace (prefixWord ++ tailWord_1940692) baseStart_1940692 baseEnd_1940692 := by
    simpa [prefixWord, tailWord_1940692, baseEnd_1940692] using wordTrace_append hprefix tailTrace_1940692
  have hstable : (prefixWord ++ tailWord_1940692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940692).length < 2 ^ (prefixWord ++ tailWord_1940692).sum := by decide
  have hdescent : baseEnd_1940692 < baseStart_1940692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940729 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1940729 : Nat := 118140960795 + 1940729 * 2 ^ 59
def prefixEnd_1940729 : Nat := 4983230072969 + 3 ^ 40 * 1940729 * 2
def baseEnd_1940729 : Nat := 664351198079761748374837

theorem tailTrace_1940729 : CollatzResearch.WordTrace tailWord_1940729 prefixEnd_1940729 664351198079761748374837 := by
  unfold tailWord_1940729
  simp only [CollatzResearch.WordTrace]
  refine ⟨70784201786077757970217241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47189467857385171980144827 70784201786077757970217241)
  ·
    refine ⟨53088151339558318477662931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70784201786077757970217241 53088151339558318477662931)
    ·
      refine ⟨79632227009337477716494397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53088151339558318477662931 79632227009337477716494397)
      ·
        refine ⟨29862085128501554143685399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79632227009337477716494397 29862085128501554143685399)
        ·
          refine ⟨44793127692752331215528099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29862085128501554143685399 44793127692752331215528099)
          ·
            refine ⟨67189691539128496823292149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44793127692752331215528099 67189691539128496823292149)
            ·
              refine ⟨6299033581793296577183639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67189691539128496823292149 6299033581793296577183639)
              ·
                refine ⟨9448550372689944865775459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299033581793296577183639 9448550372689944865775459)
                ·
                  refine ⟨14172825559034917298663189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9448550372689944865775459 14172825559034917298663189)
                  ·
                    refine ⟨664351198079761748374837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14172825559034917298663189 664351198079761748374837)
                    ·
                      rfl

theorem cell22_1940729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1940729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940729 prefixEnd_1940729 := by exact prefixLift 1940729
  have htrace : WordTrace (prefixWord ++ tailWord_1940729) baseStart_1940729 baseEnd_1940729 := by
    simpa [prefixWord, tailWord_1940729, baseEnd_1940729] using wordTrace_append hprefix tailTrace_1940729
  have hstable : (prefixWord ++ tailWord_1940729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940729).length < 2 ^ (prefixWord ++ tailWord_1940729).sum := by decide
  have hdescent : baseEnd_1940729 < baseStart_1940729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940748 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_1940748 : Nat := 118140960795 + 1940748 * 2 ^ 59
def prefixEnd_1940748 : Nat := 4983230072969 + 3 ^ 40 * 1940748 * 2
def baseEnd_1940748 : Nat := 664357702168052032149779

theorem tailTrace_1940748 : CollatzResearch.WordTrace tailWord_1940748 prefixEnd_1940748 664357702168052032149779 := by
  unfold tailWord_1940748
  simp only [CollatzResearch.WordTrace]
  refine ⟨35392447386504462107579449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47189929848672616143439265 35392447386504462107579449)
  ·
    refine ⟨26544335539878346580684587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35392447386504462107579449 26544335539878346580684587)
    ·
      refine ⟨39816503309817519871026881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26544335539878346580684587 39816503309817519871026881)
      ·
        refine ⟨29862377482363139903270161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39816503309817519871026881 29862377482363139903270161)
        ·
          refine ⟨22396783111772354927452621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29862377482363139903270161 22396783111772354927452621)
          ·
            refine ⟨8398793666914633097794733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22396783111772354927452621 8398793666914633097794733)
            ·
              refine ⟨3149547625092987411673025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8398793666914633097794733 3149547625092987411673025)
              ·
                refine ⟨2362160718819740558754769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149547625092987411673025 2362160718819740558754769)
                ·
                  refine ⟨1771620539114805419066077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362160718819740558754769 1771620539114805419066077)
                  ·
                    refine ⟨664357702168052032149779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771620539114805419066077 664357702168052032149779)
                    ·
                      rfl

theorem cell22_1940748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_1940748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940748 prefixEnd_1940748 := by exact prefixLift 1940748
  have htrace : WordTrace (prefixWord ++ tailWord_1940748) baseStart_1940748 baseEnd_1940748 := by
    simpa [prefixWord, tailWord_1940748, baseEnd_1940748] using wordTrace_append hprefix tailTrace_1940748
  have hstable : (prefixWord ++ tailWord_1940748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940748).length < 2 ^ (prefixWord ++ tailWord_1940748).sum := by decide
  have hdescent : baseEnd_1940748 < baseStart_1940748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940778 : List Nat := [3, 1, 4, 2, 1, 1, 4, 6]
def baseStart_1940778 : Nat := 118140960795 + 1940778 * 2 ^ 59
def prefixEnd_1940778 : Nat := 4983230072969 + 3 ^ 40 * 1940778 * 2
def baseEnd_1940778 : Nat := 73818663531237994877743

theorem tailTrace_1940778 : CollatzResearch.WordTrace tailWord_1940778 prefixEnd_1940778 73818663531237994877743 := by
  unfold tailWord_1940778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696497240725059834687747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47190659308600159559167325 17696497240725059834687747)
  ·
    refine ⟨26544745861087589752031621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17696497240725059834687747 26544745861087589752031621)
    ·
      refine ⟨4977139848953923078505929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26544745861087589752031621 4977139848953923078505929)
      ·
        refine ⟨3732854886715442308879447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4977139848953923078505929 3732854886715442308879447)
        ·
          refine ⟨5599282330073163463319171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732854886715442308879447 5599282330073163463319171)
          ·
            refine ⟨8398923495109745194978757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599282330073163463319171 8398923495109745194978757)
            ·
              refine ⟨1574798155333077224058517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8398923495109745194978757 1574798155333077224058517)
              ·
                refine ⟨73818663531237994877743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1574798155333077224058517 73818663531237994877743)
                ·
                  rfl

theorem cell22_1940778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_1940778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940778 prefixEnd_1940778 := by exact prefixLift 1940778
  have htrace : WordTrace (prefixWord ++ tailWord_1940778) baseStart_1940778 baseEnd_1940778 := by
    simpa [prefixWord, tailWord_1940778, baseEnd_1940778] using wordTrace_append hprefix tailTrace_1940778
  have hstable : (prefixWord ++ tailWord_1940778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940778).length < 2 ^ (prefixWord ++ tailWord_1940778).sum := by decide
  have hdescent : baseEnd_1940778 < baseStart_1940778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940823 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 5]
def baseStart_1940823 : Nat := 118140960795 + 1940823 * 2 ^ 59
def prefixEnd_1940823 : Nat := 4983230072969 + 3 ^ 40 * 1940823 * 2
def baseEnd_1940823 : Nat := 221461125400258945508183

theorem tailTrace_1940823 : CollatzResearch.WordTrace tailWord_1940823 prefixEnd_1940823 221461125400258945508183 := by
  unfold tailWord_1940823
  simp only [CollatzResearch.WordTrace]
  refine ⟨70787630247737212024139123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47191753498491474682759415 70787630247737212024139123)
  ·
    refine ⟨106181445371605818036208685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70787630247737212024139123 106181445371605818036208685)
    ·
      refine ⟨39818042014352181763578257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106181445371605818036208685 39818042014352181763578257)
      ·
        refine ⟨29863531510764136322683693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39818042014352181763578257 29863531510764136322683693)
        ·
          refine ⟨11198824316536551121006385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29863531510764136322683693 11198824316536551121006385)
          ·
            refine ⟨8399118237402413340754789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11198824316536551121006385 8399118237402413340754789)
            ·
              refine ⟨1574834669512952501391523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8399118237402413340754789 1574834669512952501391523)
              ·
                refine ⟨2362252004269428752087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574834669512952501391523 2362252004269428752087285)
                ·
                  refine ⟨221461125400258945508183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362252004269428752087285 221461125400258945508183)
                  ·
                    rfl

theorem cell22_1940823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 5].length) (baseStart_1940823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940823 prefixEnd_1940823 := by exact prefixLift 1940823
  have htrace : WordTrace (prefixWord ++ tailWord_1940823) baseStart_1940823 baseEnd_1940823 := by
    simpa [prefixWord, tailWord_1940823, baseEnd_1940823] using wordTrace_append hprefix tailTrace_1940823
  have hstable : (prefixWord ++ tailWord_1940823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940823).length < 2 ^ (prefixWord ++ tailWord_1940823).sum := by decide
  have hdescent : baseEnd_1940823 < baseStart_1940823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940898 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1940898 : Nat := 118140960795 + 1940898 * 2 ^ 59
def prefixEnd_1940898 : Nat := 4983230072969 + 3 ^ 40 * 1940898 * 2
def baseEnd_1940898 : Nat := 664409050233501640899319

theorem tailTrace_1940898 : CollatzResearch.WordTrace tailWord_1940898 prefixEnd_1940898 664409050233501640899319 := by
  unfold tailWord_1940898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697591430616374958279837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47193577148310333222079565 17697591430616374958279837)
  ·
    refine ⟨6636596786481140609354939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17697591430616374958279837 6636596786481140609354939)
    ·
      refine ⟨9954895179721710914032409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636596786481140609354939 9954895179721710914032409)
      ·
        refine ⟨7466171384791283185524307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9954895179721710914032409 7466171384791283185524307)
        ·
          refine ⟨11199257077186924778286461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466171384791283185524307 11199257077186924778286461)
          ·
            refine ⟨4199721403945096791857423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11199257077186924778286461 4199721403945096791857423)
            ·
              refine ⟨6299582105917645187786135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199721403945096791857423 6299582105917645187786135)
              ·
                refine ⟨9449373158876467781679203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299582105917645187786135 9449373158876467781679203)
                ·
                  refine ⟨14174059738314701672518805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9449373158876467781679203 14174059738314701672518805)
                  ·
                    refine ⟨664409050233501640899319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14174059738314701672518805 664409050233501640899319)
                    ·
                      rfl

theorem cell22_1940898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1940898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940898 prefixEnd_1940898 := by exact prefixLift 1940898
  have htrace : WordTrace (prefixWord ++ tailWord_1940898) baseStart_1940898 baseEnd_1940898 := by
    simpa [prefixWord, tailWord_1940898, baseEnd_1940898] using wordTrace_append hprefix tailTrace_1940898
  have hstable : (prefixWord ++ tailWord_1940898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940898).length < 2 ^ (prefixWord ++ tailWord_1940898).sum := by decide
  have hdescent : baseEnd_1940898 < baseStart_1940898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940904 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1940904 : Nat := 118140960795 + 1940904 * 2 ^ 59
def prefixEnd_1940904 : Nat := 4983230072969 + 3 ^ 40 * 1940904 * 2
def baseEnd_1940904 : Nat := 664411104156119625249301

theorem tailTrace_1940904 : CollatzResearch.WordTrace tailWord_1940904 prefixEnd_1940904 664411104156119625249301 := by
  unfold tailWord_1940904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35395292280221881428918883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47193723040295841905225177 35395292280221881428918883)
  ·
    refine ⟨53092938420332822143378325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35395292280221881428918883 53092938420332822143378325)
    ·
      refine ⟨2488731488453101037970859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53092938420332822143378325 2488731488453101037970859)
      ·
        refine ⟨3733097232679651556956289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488731488453101037970859 3733097232679651556956289)
        ·
          refine ⟨2799822924509738667717217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733097232679651556956289 2799822924509738667717217)
          ·
            refine ⟨2099867193382304000787913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799822924509738667717217 2099867193382304000787913)
            ·
              refine ⟨1574900395036728000590935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099867193382304000787913 1574900395036728000590935)
              ·
                refine ⟨2362350592555092000886403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574900395036728000590935 2362350592555092000886403)
                ·
                  refine ⟨3543525888832638001329605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362350592555092000886403 3543525888832638001329605)
                  ·
                    refine ⟨664411104156119625249301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3543525888832638001329605 664411104156119625249301)
                    ·
                      rfl

theorem cell22_1940904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1940904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940904 prefixEnd_1940904 := by exact prefixLift 1940904
  have htrace : WordTrace (prefixWord ++ tailWord_1940904) baseStart_1940904 baseEnd_1940904 := by
    simpa [prefixWord, tailWord_1940904, baseEnd_1940904] using wordTrace_append hprefix tailTrace_1940904
  have hstable : (prefixWord ++ tailWord_1940904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940904).length < 2 ^ (prefixWord ++ tailWord_1940904).sum := by decide
  have hdescent : baseEnd_1940904 < baseStart_1940904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940917 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1940917 : Nat := 118140960795 + 1940917 * 2 ^ 59
def prefixEnd_1940917 : Nat := 4983230072969 + 3 ^ 40 * 1940917 * 2
def baseEnd_1940917 : Nat := 664415554321791924674261

theorem tailTrace_1940917 : CollatzResearch.WordTrace tailWord_1940917 prefixEnd_1940917 664415554321791924674261 := by
  unfold tailWord_1940917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70791058709396666078061005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47194039139597777385374003 70791058709396666078061005)
  ·
    refine ⟨26546647016023749779272877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70791058709396666078061005 26546647016023749779272877)
    ·
      refine ⟨9954992631008906167227329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26546647016023749779272877 9954992631008906167227329)
      ·
        refine ⟨7466244473256679625420497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9954992631008906167227329 7466244473256679625420497)
        ·
          refine ⟨5599683354942509719065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7466244473256679625420497 5599683354942509719065373)
          ·
            refine ⟨2099881258103441144649515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5599683354942509719065373 2099881258103441144649515)
            ·
              refine ⟨3149821887155161716974273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099881258103441144649515 3149821887155161716974273)
              ·
                refine ⟨2362366415366371287730705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149821887155161716974273 2362366415366371287730705)
                ·
                  refine ⟨1771774811524778465798029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362366415366371287730705 1771774811524778465798029)
                  ·
                    refine ⟨664415554321791924674261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771774811524778465798029 664415554321791924674261)
                    ·
                      rfl

theorem cell22_1940917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1940917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940917 prefixEnd_1940917 := by exact prefixLift 1940917
  have htrace : WordTrace (prefixWord ++ tailWord_1940917) baseStart_1940917 baseEnd_1940917 := by
    simpa [prefixWord, tailWord_1940917, baseEnd_1940917] using wordTrace_append hprefix tailTrace_1940917
  have hstable : (prefixWord ++ tailWord_1940917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940917).length < 2 ^ (prefixWord ++ tailWord_1940917).sum := by decide
  have hdescent : baseEnd_1940917 < baseStart_1940917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940928 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_1940928 : Nat := 118140960795 + 1940928 * 2 ^ 59
def prefixEnd_1940928 : Nat := 4983230072969 + 3 ^ 40 * 1940928 * 2
def baseEnd_1940928 : Nat := 664419319846591562649227

theorem tailTrace_1940928 : CollatzResearch.WordTrace tailWord_1940928 prefixEnd_1940928 664419319846591562649227 := by
  unfold tailWord_1940928
  simp only [CollatzResearch.WordTrace]
  refine ⟨35395729956178407478355719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47194306608237876637807625 35395729956178407478355719)
  ·
    refine ⟨53093594934267611217533579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35395729956178407478355719 53093594934267611217533579)
    ·
      refine ⟨79640392401401416826300369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53093594934267611217533579 79640392401401416826300369)
      ·
        refine ⟨59730294301051062619725277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79640392401401416826300369 59730294301051062619725277)
        ·
          refine ⟨22398860362894148482396979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59730294301051062619725277 22398860362894148482396979)
          ·
            refine ⟨33598290544341222723595469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22398860362894148482396979 33598290544341222723595469)
            ·
              refine ⟨12599358954127958521348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33598290544341222723595469 12599358954127958521348301)
              ·
                refine ⟨4724759607797984445505613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12599358954127958521348301 4724759607797984445505613)
                ·
                  refine ⟨1771784852924244167064605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4724759607797984445505613 1771784852924244167064605)
                  ·
                    refine ⟨664419319846591562649227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771784852924244167064605 664419319846591562649227)
                    ·
                      rfl

theorem cell22_1940928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_1940928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1940928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1940928 prefixEnd_1940928 := by exact prefixLift 1940928
  have htrace : WordTrace (prefixWord ++ tailWord_1940928) baseStart_1940928 baseEnd_1940928 := by
    simpa [prefixWord, tailWord_1940928, baseEnd_1940928] using wordTrace_append hprefix tailTrace_1940928
  have hstable : (prefixWord ++ tailWord_1940928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940928).length < 2 ^ (prefixWord ++ tailWord_1940928).sum := by decide
  have hdescent : baseEnd_1940928 < baseStart_1940928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941020 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1941020 : Nat := 118140960795 + 1941020 * 2 ^ 59
def prefixEnd_1941020 : Nat := 4983230072969 + 3 ^ 40 * 1941020 * 2
def baseEnd_1941020 : Nat := 221483604442244663116315

theorem tailTrace_1941020 : CollatzResearch.WordTrace tailWord_1941020 prefixEnd_1941020 221483604442244663116315 := by
  unfold tailWord_1941020
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397407714011757334530257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47196543618682343112707009 35397407714011757334530257)
  ·
    refine ⟨26548055785508818000897693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35397407714011757334530257 26548055785508818000897693)
    ·
      refine ⟨9955520919565806750336635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26548055785508818000897693 9955520919565806750336635)
      ·
        refine ⟨14933281379348710125504953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955520919565806750336635 14933281379348710125504953)
        ·
          refine ⟨11199961034511532594128715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14933281379348710125504953 11199961034511532594128715)
          ·
            refine ⟨16799941551767298891193073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199961034511532594128715 16799941551767298891193073)
            ·
              refine ⟨12599956163825474168394805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16799941551767298891193073 12599956163825474168394805)
              ·
                refine ⟨1181245890358638203287013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12599956163825474168394805 1181245890358638203287013)
                ·
                  refine ⟨221483604442244663116315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181245890358638203287013 221483604442244663116315)
                  ·
                    rfl

theorem cell22_1941020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1941020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941020 prefixEnd_1941020 := by exact prefixLift 1941020
  have htrace : WordTrace (prefixWord ++ tailWord_1941020) baseStart_1941020 baseEnd_1941020 := by
    simpa [prefixWord, tailWord_1941020, baseEnd_1941020] using wordTrace_append hprefix tailTrace_1941020
  have hstable : (prefixWord ++ tailWord_1941020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941020).length < 2 ^ (prefixWord ++ tailWord_1941020).sum := by decide
  have hdescent : baseEnd_1941020 < baseStart_1941020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941048 : List Nat := [2, 1, 2, 1, 4, 2, 3, 7]
def baseStart_1941048 : Nat := 118140960795 + 1941048 * 2 ^ 59
def prefixEnd_1941048 : Nat := 4983230072969 + 3 ^ 40 * 1941048 * 2
def baseEnd_1941048 : Nat := 73828933144327916627651

theorem tailTrace_1941048 : CollatzResearch.WordTrace tailWord_1941048 prefixEnd_1941048 73828933144327916627651 := by
  unfold tailWord_1941048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397918335961037725539899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47197224447948050300719865 35397918335961037725539899)
  ·
    refine ⟨53096877503941556588309849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35397918335961037725539899 53096877503941556588309849)
    ·
      refine ⟨39822658127956167441232387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53096877503941556588309849 39822658127956167441232387)
      ·
        refine ⟨59733987191934251161848581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39822658127956167441232387 59733987191934251161848581)
        ·
          refine ⟨11200122598487672092846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59733987191934251161848581 11200122598487672092846609)
          ·
            refine ⟨8400091948865754069634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11200122598487672092846609 8400091948865754069634957)
            ·
              refine ⟨3150034480824657776113109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8400091948865754069634957 3150034480824657776113109)
              ·
                refine ⟨73828933144327916627651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3150034480824657776113109 73828933144327916627651)
                ·
                  rfl

theorem cell22_1941048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_1941048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941048 prefixEnd_1941048 := by exact prefixLift 1941048
  have htrace : WordTrace (prefixWord ++ tailWord_1941048) baseStart_1941048 baseEnd_1941048 := by
    simpa [prefixWord, tailWord_1941048, baseEnd_1941048] using wordTrace_append hprefix tailTrace_1941048
  have hstable : (prefixWord ++ tailWord_1941048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941048).length < 2 ^ (prefixWord ++ tailWord_1941048).sum := by decide
  have hdescent : baseEnd_1941048 < baseStart_1941048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941097 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_1941097 : Nat := 118140960795 + 1941097 * 2 ^ 59
def prefixEnd_1941097 : Nat := 4983230072969 + 3 ^ 40 * 1941097 * 2
def baseEnd_1941097 : Nat := 664477172000331455173709

theorem tailTrace_1941097 : CollatzResearch.WordTrace tailWord_1941097 prefixEnd_1941097 664477172000331455173709 := by
  unfold tailWord_1941097
  simp only [CollatzResearch.WordTrace]
  refine ⟨70797623848744556819613545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47198415899163037879742363 70797623848744556819613545)
  ·
    refine ⟨53098217886558417614710159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70797623848744556819613545 53098217886558417614710159)
    ·
      refine ⟨79647326829837626422065239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53098217886558417614710159 79647326829837626422065239)
      ·
        refine ⟨119470990244756439633097859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79647326829837626422065239 119470990244756439633097859)
        ·
          refine ⟨179206485367134659449646789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119470990244756439633097859 179206485367134659449646789)
          ·
            refine ⟨33601216006337748646808773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179206485367134659449646789 33601216006337748646808773)
            ·
              refine ⟨6300228001188327871276645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33601216006337748646808773 6300228001188327871276645)
              ·
                refine ⟨1181292750222811475864371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6300228001188327871276645 1181292750222811475864371)
                ·
                  refine ⟨1771939125334217213796557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181292750222811475864371 1771939125334217213796557)
                  ·
                    refine ⟨664477172000331455173709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1771939125334217213796557 664477172000331455173709)
                    ·
                      rfl

theorem cell22_1941097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_1941097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941097 prefixEnd_1941097 := by exact prefixLift 1941097
  have htrace : WordTrace (prefixWord ++ tailWord_1941097) baseStart_1941097 baseEnd_1941097 := by
    simpa [prefixWord, tailWord_1941097, baseEnd_1941097] using wordTrace_append hprefix tailTrace_1941097
  have hstable : (prefixWord ++ tailWord_1941097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941097).length < 2 ^ (prefixWord ++ tailWord_1941097).sum := by decide
  have hdescent : baseEnd_1941097 < baseStart_1941097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941168 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_1941168 : Nat := 118140960795 + 1941168 * 2 ^ 59
def prefixEnd_1941168 : Nat := 4983230072969 + 3 ^ 40 * 1941168 * 2
def baseEnd_1941168 : Nat := 664501476751310936648491

theorem tailTrace_1941168 : CollatzResearch.WordTrace tailWord_1941168 prefixEnd_1941168 664501476751310936648491 := by
  unfold tailWord_1941168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400106715743667972724079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47200142287658223963632105 35400106715743667972724079)
  ·
    refine ⟨53100160073615501959086119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35400106715743667972724079 53100160073615501959086119)
    ·
      refine ⟨79650240110423252938629179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53100160073615501959086119 79650240110423252938629179)
      ·
        refine ⟨119475360165634879407943769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79650240110423252938629179 119475360165634879407943769)
        ·
          refine ⟨89606520124226159555957827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119475360165634879407943769 89606520124226159555957827)
          ·
            refine ⟨134409780186339239333936741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89606520124226159555957827 134409780186339239333936741)
            ·
              refine ⟨25201833784938607375113139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134409780186339239333936741 25201833784938607375113139)
              ·
                refine ⟨37802750677407911062669709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25201833784938607375113139 37802750677407911062669709)
                ·
                  refine ⟨14176031504027966648501141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37802750677407911062669709 14176031504027966648501141)
                  ·
                    refine ⟨664501476751310936648491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14176031504027966648501141 664501476751310936648491)
                    ·
                      rfl

theorem cell22_1941168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_1941168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941168 prefixEnd_1941168 := by exact prefixLift 1941168
  have htrace : WordTrace (prefixWord ++ tailWord_1941168) baseStart_1941168 baseEnd_1941168 := by
    simpa [prefixWord, tailWord_1941168, baseEnd_1941168] using wordTrace_append hprefix tailTrace_1941168
  have hstable : (prefixWord ++ tailWord_1941168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941168).length < 2 ^ (prefixWord ++ tailWord_1941168).sum := by decide
  have hdescent : baseEnd_1941168 < baseStart_1941168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941174 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1941174 : Nat := 118140960795 + 1941174 * 2 ^ 59
def prefixEnd_1941174 : Nat := 4983230072969 + 3 ^ 40 * 1941174 * 2
def baseEnd_1941174 : Nat := 664503530673928920998473

theorem tailTrace_1941174 : CollatzResearch.WordTrace tailWord_1941174 prefixEnd_1941174 664503530673928920998473 := by
  unfold tailWord_1941174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425027016841599935635411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47200288179643732646777717 4425027016841599935635411)
  ·
    refine ⟨6637540525262399903453117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425027016841599935635411 6637540525262399903453117)
    ·
      refine ⟨2489077696973399963794919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6637540525262399903453117 2489077696973399963794919)
      ·
        refine ⟨3733616545460099945692379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489077696973399963794919 3733616545460099945692379)
        ·
          refine ⟨5600424818190149918538569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733616545460099945692379 5600424818190149918538569)
          ·
            refine ⟨4200318613642612438903927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600424818190149918538569 4200318613642612438903927)
            ·
              refine ⟨6300477920463918658355891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200318613642612438903927 6300477920463918658355891)
              ·
                refine ⟨9450716880695877987533837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300477920463918658355891 9450716880695877987533837)
                ·
                  refine ⟨3544018830260954245325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9450716880695877987533837 3544018830260954245325189)
                  ·
                    refine ⟨664503530673928920998473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544018830260954245325189 664503530673928920998473)
                    ·
                      rfl

theorem cell22_1941174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1941174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941174 prefixEnd_1941174 := by exact prefixLift 1941174
  have htrace : WordTrace (prefixWord ++ tailWord_1941174) baseStart_1941174 baseEnd_1941174 := by
    simpa [prefixWord, tailWord_1941174, baseEnd_1941174] using wordTrace_append hprefix tailTrace_1941174
  have hstable : (prefixWord ++ tailWord_1941174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941174).length < 2 ^ (prefixWord ++ tailWord_1941174).sum := by decide
  have hdescent : baseEnd_1941174 < baseStart_1941174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941183 : List Nat := [1, 1, 2, 2, 2, 3, 1, 10]
def baseStart_1941183 : Nat := 118140960795 + 1941183 * 2 ^ 59
def prefixEnd_1941183 : Nat := 4983230072969 + 3 ^ 40 * 1941183 * 2
def baseEnd_1941183 : Nat := 73834067950872877502605

theorem tailTrace_1941183 : CollatzResearch.WordTrace tailWord_1941183 prefixEnd_1941183 73834067950872877502605 := by
  unfold tailWord_1941183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70800760526432993507244203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47200507017621995671496135 70800760526432993507244203)
  ·
    refine ⟨106201140789649490260866305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70800760526432993507244203 106201140789649490260866305)
    ·
      refine ⟨79650855592237117695649729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106201140789649490260866305 79650855592237117695649729)
      ·
        refine ⟨59738141694177838271737297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79650855592237117695649729 59738141694177838271737297)
        ·
          refine ⟨44803606270633378703802973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59738141694177838271737297 44803606270633378703802973)
          ·
            refine ⟨16801352351487517013926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44803606270633378703802973 16801352351487517013926115)
            ·
              refine ⟨25202028527231275520889173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16801352351487517013926115 25202028527231275520889173)
              ·
                refine ⟨73834067950872877502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25202028527231275520889173 73834067950872877502605)
                ·
                  rfl

theorem cell22_1941183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 10].length) (baseStart_1941183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941183 prefixEnd_1941183 := by exact prefixLift 1941183
  have htrace : WordTrace (prefixWord ++ tailWord_1941183) baseStart_1941183 baseEnd_1941183 := by
    simpa [prefixWord, tailWord_1941183, baseEnd_1941183] using wordTrace_append hprefix tailTrace_1941183
  have hstable : (prefixWord ++ tailWord_1941183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941183).length < 2 ^ (prefixWord ++ tailWord_1941183).sum := by decide
  have hdescent : baseEnd_1941183 < baseStart_1941183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941202 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1941202 : Nat := 118140960795 + 1941202 * 2 ^ 59
def prefixEnd_1941202 : Nat := 4983230072969 + 3 ^ 40 * 1941202 * 2
def baseEnd_1941202 : Nat := 664513115646146181298387

theorem tailTrace_1941202 : CollatzResearch.WordTrace tailWord_1941202 prefixEnd_1941202 664513115646146181298387 := by
  unfold tailWord_1941202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700363378341039938046465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47200969008909439834790573 17700363378341039938046465)
  ·
    refine ⟨13275272533755779953534849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17700363378341039938046465 13275272533755779953534849)
    ·
      refine ⟨9956454400316834965151137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13275272533755779953534849 9956454400316834965151137)
      ·
        refine ⟨7467340800237626223863353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9956454400316834965151137 7467340800237626223863353)
        ·
          refine ⟨5600505600178219667897515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7467340800237626223863353 5600505600178219667897515)
          ·
            refine ⟨8400758400267329501846273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600505600178219667897515 8400758400267329501846273)
            ·
              refine ⟨6300568800200497126384705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400758400267329501846273 6300568800200497126384705)
              ·
                refine ⟨4725426600150372844788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300568800200497126384705 4725426600150372844788529)
                ·
                  refine ⟨3544069950112779633591397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725426600150372844788529 3544069950112779633591397)
                  ·
                    refine ⟨664513115646146181298387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544069950112779633591397 664513115646146181298387)
                    ·
                      rfl

theorem cell22_1941202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1941202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941202 prefixEnd_1941202 := by exact prefixLift 1941202
  have htrace : WordTrace (prefixWord ++ tailWord_1941202) baseStart_1941202 baseEnd_1941202 := by
    simpa [prefixWord, tailWord_1941202, baseEnd_1941202] using wordTrace_append hprefix tailTrace_1941202
  have hstable : (prefixWord ++ tailWord_1941202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941202).length < 2 ^ (prefixWord ++ tailWord_1941202).sum := by decide
  have hdescent : baseEnd_1941202 < baseStart_1941202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941204 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1941204 : Nat := 118140960795 + 1941204 * 2 ^ 59
def prefixEnd_1941204 : Nat := 4983230072969 + 3 ^ 40 * 1941204 * 2
def baseEnd_1941204 : Nat := 664513800287018842748381

theorem tailTrace_1941204 : CollatzResearch.WordTrace tailWord_1941204 prefixEnd_1941204 664513800287018842748381 := by
  unfold tailWord_1941204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400763229678457046879333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47201017639571276062505777 35400763229678457046879333)
  ·
    refine ⟨6637643105564710696289875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35400763229678457046879333 6637643105564710696289875)
    ·
      refine ⟨9956464658347066044434813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637643105564710696289875 9956464658347066044434813)
      ·
        refine ⟨3733674246880149766663055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9956464658347066044434813 3733674246880149766663055)
        ·
          refine ⟨5600511370320224649994583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733674246880149766663055 5600511370320224649994583)
          ·
            refine ⟨8400767055480336974991875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600511370320224649994583 8400767055480336974991875)
            ·
              refine ⟨12601150583220505462487813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8400767055480336974991875 12601150583220505462487813)
              ·
                refine ⟨2362715734353844774216465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12601150583220505462487813 2362715734353844774216465)
                ·
                  refine ⟨1772036800765383580662349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362715734353844774216465 1772036800765383580662349)
                  ·
                    refine ⟨664513800287018842748381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772036800765383580662349 664513800287018842748381)
                    ·
                      rfl

theorem cell22_1941204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1941204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941204 prefixEnd_1941204 := by exact prefixLift 1941204
  have htrace : WordTrace (prefixWord ++ tailWord_1941204) baseStart_1941204 baseEnd_1941204 := by
    simpa [prefixWord, tailWord_1941204, baseEnd_1941204] using wordTrace_append hprefix tailTrace_1941204
  have hstable : (prefixWord ++ tailWord_1941204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941204).length < 2 ^ (prefixWord ++ tailWord_1941204).sum := by decide
  have hdescent : baseEnd_1941204 < baseStart_1941204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941217 : List Nat := [1, 2, 3, 1, 5, 2, 1, 7]
def baseStart_1941217 : Nat := 118140960795 + 1941217 * 2 ^ 59
def prefixEnd_1941217 : Nat := 4983230072969 + 3 ^ 40 * 1941217 * 2
def baseEnd_1941217 : Nat := 73835361161410126908149

theorem tailTrace_1941217 : CollatzResearch.WordTrace tailWord_1941217 prefixEnd_1941217 73835361161410126908149 := by
  unfold tailWord_1941217
  simp only [CollatzResearch.WordTrace]
  refine ⟨70802000608309817313981905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47201333738873211542654603 70802000608309817313981905)
  ·
    refine ⟨53101500456232362985486429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70802000608309817313981905 53101500456232362985486429)
    ·
      refine ⟨19913062671087136119557411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53101500456232362985486429 19913062671087136119557411)
      ·
        refine ⟨29869594006630704179336117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19913062671087136119557411 29869594006630704179336117)
        ·
          refine ⟨2800274438121628516812761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29869594006630704179336117 2800274438121628516812761)
          ·
            refine ⟨2100205828591221387609571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800274438121628516812761 2100205828591221387609571)
            ·
              refine ⟨3150308742886832081414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100205828591221387609571 3150308742886832081414357)
              ·
                refine ⟨73835361161410126908149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3150308742886832081414357 73835361161410126908149)
                ·
                  rfl

theorem cell22_1941217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 7].length) (baseStart_1941217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941217 prefixEnd_1941217 := by exact prefixLift 1941217
  have htrace : WordTrace (prefixWord ++ tailWord_1941217) baseStart_1941217 baseEnd_1941217 := by
    simpa [prefixWord, tailWord_1941217, baseEnd_1941217] using wordTrace_append hprefix tailTrace_1941217
  have hstable : (prefixWord ++ tailWord_1941217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941217).length < 2 ^ (prefixWord ++ tailWord_1941217).sum := by decide
  have hdescent : baseEnd_1941217 < baseStart_1941217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941230 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1941230 : Nat := 118140960795 + 1941230 * 2 ^ 59
def prefixEnd_1941230 : Nat := 4983230072969 + 3 ^ 40 * 1941230 * 2
def baseEnd_1941230 : Nat := 664522700618363441598301

theorem tailTrace_1941230 : CollatzResearch.WordTrace tailWord_1941230 prefixEnd_1941230 664522700618363441598301 := by
  unfold tailWord_1941230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850309344657840066775643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47201649838175147022803429 8850309344657840066775643)
  ·
    refine ⟨13275464016986760100163465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8850309344657840066775643 13275464016986760100163465)
    ·
      refine ⟨9956598012740070075122599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13275464016986760100163465 9956598012740070075122599)
      ·
        refine ⟨14934897019110105112683899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956598012740070075122599 14934897019110105112683899)
        ·
          refine ⟨22402345528665157669025849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934897019110105112683899 22402345528665157669025849)
          ·
            refine ⟨16801759146498868251769387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22402345528665157669025849 16801759146498868251769387)
            ·
              refine ⟨25202638719748302377654081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16801759146498868251769387 25202638719748302377654081)
              ·
                refine ⟨18901979039811226783240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25202638719748302377654081 18901979039811226783240561)
                ·
                  refine ⟨14176484279858420087430421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18901979039811226783240561 14176484279858420087430421)
                  ·
                    refine ⟨664522700618363441598301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14176484279858420087430421 664522700618363441598301)
                    ·
                      rfl

theorem cell22_1941230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1941230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941230 prefixEnd_1941230 := by exact prefixLift 1941230
  have htrace : WordTrace (prefixWord ++ tailWord_1941230) baseStart_1941230 baseEnd_1941230 := by
    simpa [prefixWord, tailWord_1941230, baseEnd_1941230] using wordTrace_append hprefix tailTrace_1941230
  have hstable : (prefixWord ++ tailWord_1941230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941230).length < 2 ^ (prefixWord ++ tailWord_1941230).sum := by decide
  have hdescent : baseEnd_1941230 < baseStart_1941230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941236 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1941236 : Nat := 118140960795 + 1941236 * 2 ^ 59
def prefixEnd_1941236 : Nat := 4983230072969 + 3 ^ 40 * 1941236 * 2
def baseEnd_1941236 : Nat := 664524754540981425948283

theorem tailTrace_1941236 : CollatzResearch.WordTrace tailWord_1941236 prefixEnd_1941236 664524754540981425948283 := by
  unfold tailWord_1941236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35401346797620491779461781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47201795730160655705949041 35401346797620491779461781)
  ·
    refine ⟨1659438131138460552162271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35401346797620491779461781 1659438131138460552162271)
    ·
      refine ⟨2489157196707690828243407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659438131138460552162271 2489157196707690828243407)
      ·
        refine ⟨3733735795061536242365111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489157196707690828243407 3733735795061536242365111)
        ·
          refine ⟨5600603692592304363547667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733735795061536242365111 5600603692592304363547667)
          ·
            refine ⟨8400905538888456545321501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600603692592304363547667 8400905538888456545321501)
            ·
              refine ⟨3150339577083171204495563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8400905538888456545321501 3150339577083171204495563)
              ·
                refine ⟨4725509365624756806743345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150339577083171204495563 4725509365624756806743345)
                ·
                  refine ⟨3544132024218567605057509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725509365624756806743345 3544132024218567605057509)
                  ·
                    refine ⟨664524754540981425948283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544132024218567605057509 664524754540981425948283)
                    ·
                      rfl

theorem cell22_1941236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1941236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941236 prefixEnd_1941236 := by exact prefixLift 1941236
  have htrace : WordTrace (prefixWord ++ tailWord_1941236) baseStart_1941236 baseEnd_1941236 := by
    simpa [prefixWord, tailWord_1941236, baseEnd_1941236] using wordTrace_append hprefix tailTrace_1941236
  have hstable : (prefixWord ++ tailWord_1941236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941236).length < 2 ^ (prefixWord ++ tailWord_1941236).sum := by decide
  have hdescent : baseEnd_1941236 < baseStart_1941236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941249 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1941249 : Nat := 118140960795 + 1941249 * 2 ^ 59
def prefixEnd_1941249 : Nat := 4983230072969 + 3 ^ 40 * 1941249 * 2
def baseEnd_1941249 : Nat := 664529204706653725373243

theorem tailTrace_1941249 : CollatzResearch.WordTrace tailWord_1941249 prefixEnd_1941249 664529204706653725373243 := by
  unfold tailWord_1941249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803167744193886779146801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47202111829462591186097867 70803167744193886779146801)
  ·
    refine ⟨53102375808145415084360101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70803167744193886779146801 53102375808145415084360101)
    ·
      refine ⟨9956695464027265328317519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53102375808145415084360101 9956695464027265328317519)
      ·
        refine ⟨14935043196040897992476279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956695464027265328317519 14935043196040897992476279)
        ·
          refine ⟨22402564794061346988714419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14935043196040897992476279 22402564794061346988714419)
          ·
            refine ⟨33603847191092020483071629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402564794061346988714419 33603847191092020483071629)
            ·
              refine ⟨12601442696659507681151861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33603847191092020483071629 12601442696659507681151861)
              ·
                refine ⟨1181385252811828845107987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12601442696659507681151861 1181385252811828845107987)
                ·
                  refine ⟨1772077879217743267661981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181385252811828845107987 1772077879217743267661981)
                  ·
                    refine ⟨664529204706653725373243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772077879217743267661981 664529204706653725373243)
                    ·
                      rfl

theorem cell22_1941249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1941249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941249 prefixEnd_1941249 := by exact prefixLift 1941249
  have htrace : WordTrace (prefixWord ++ tailWord_1941249) baseStart_1941249 baseEnd_1941249 := by
    simpa [prefixWord, tailWord_1941249, baseEnd_1941249] using wordTrace_append hprefix tailTrace_1941249
  have hstable : (prefixWord ++ tailWord_1941249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941249).length < 2 ^ (prefixWord ++ tailWord_1941249).sum := by decide
  have hdescent : baseEnd_1941249 < baseStart_1941249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941260 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1941260 : Nat := 118140960795 + 1941260 * 2 ^ 59
def prefixEnd_1941260 : Nat := 4983230072969 + 3 ^ 40 * 1941260 * 2
def baseEnd_1941260 : Nat := 664532970231453363348209

theorem tailTrace_1941260 : CollatzResearch.WordTrace tailWord_1941260 prefixEnd_1941260 664532970231453363348209 := by
  unfold tailWord_1941260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35401784473577017828898617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47202379298102690438531489 35401784473577017828898617)
  ·
    refine ⟨26551338355182763371673963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35401784473577017828898617 26551338355182763371673963)
    ·
      refine ⟨39827007532774145057510945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26551338355182763371673963 39827007532774145057510945)
      ·
        refine ⟨29870255649580608793133209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39827007532774145057510945 29870255649580608793133209)
        ·
          refine ⟨22402691737185456594849907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29870255649580608793133209 22402691737185456594849907)
          ·
            refine ⟨33604037605778184892274861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402691737185456594849907 33604037605778184892274861)
            ·
              refine ⟨12601514102166819334603073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33604037605778184892274861 12601514102166819334603073)
              ·
                refine ⟨9451135576625114500952305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12601514102166819334603073 9451135576625114500952305)
                ·
                  refine ⟨7088351682468835875714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9451135576625114500952305 7088351682468835875714229)
                  ·
                    refine ⟨664532970231453363348209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7088351682468835875714229 664532970231453363348209)
                    ·
                      rfl

theorem cell22_1941260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1941260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941260 prefixEnd_1941260 := by exact prefixLift 1941260
  have htrace : WordTrace (prefixWord ++ tailWord_1941260) baseStart_1941260 baseEnd_1941260 := by
    simpa [prefixWord, tailWord_1941260, baseEnd_1941260] using wordTrace_append hprefix tailTrace_1941260
  have hstable : (prefixWord ++ tailWord_1941260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941260).length < 2 ^ (prefixWord ++ tailWord_1941260).sum := by decide
  have hdescent : baseEnd_1941260 < baseStart_1941260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941262 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1941262 : Nat := 118140960795 + 1941262 * 2 ^ 59
def prefixEnd_1941262 : Nat := 4983230072969 + 3 ^ 40 * 1941262 * 2
def baseEnd_1941262 : Nat := 221511218290775341599401

theorem tailTrace_1941262 : CollatzResearch.WordTrace tailWord_1941262 prefixEnd_1941262 221511218290775341599401 := by
  unfold tailWord_1941262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850455236643348749921255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47202427928764526666246693 8850455236643348749921255)
  ·
    refine ⟨13275682854965023124881883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8850455236643348749921255 13275682854965023124881883)
    ·
      refine ⟨19913524282447534687322825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13275682854965023124881883 19913524282447534687322825)
      ·
        refine ⟨14935143211835651015492119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19913524282447534687322825 14935143211835651015492119)
        ·
          refine ⟨22402714817753476523238179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14935143211835651015492119 22402714817753476523238179)
          ·
            refine ⟨33604072226630214784857269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402714817753476523238179 33604072226630214784857269)
            ·
              refine ⟨3150381771246582636080369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33604072226630214784857269 3150381771246582636080369)
              ·
                refine ⟨2362786328434936977060277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150381771246582636080369 2362786328434936977060277)
                ·
                  refine ⟨221511218290775341599401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362786328434936977060277 221511218290775341599401)
                  ·
                    rfl

theorem cell22_1941262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1941262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941262 prefixEnd_1941262 := by exact prefixLift 1941262
  have htrace : WordTrace (prefixWord ++ tailWord_1941262) baseStart_1941262 baseEnd_1941262 := by
    simpa [prefixWord, tailWord_1941262, baseEnd_1941262] using wordTrace_append hprefix tailTrace_1941262
  have hstable : (prefixWord ++ tailWord_1941262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941262).length < 2 ^ (prefixWord ++ tailWord_1941262).sum := by decide
  have hdescent : baseEnd_1941262 < baseStart_1941262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941266 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1941266 : Nat := 118140960795 + 1941266 * 2 ^ 59
def prefixEnd_1941266 : Nat := 4983230072969 + 3 ^ 40 * 1941266 * 2
def baseEnd_1941266 : Nat := 664535024154071347698191

theorem tailTrace_1941266 : CollatzResearch.WordTrace tailWord_1941266 prefixEnd_1941266 664535024154071347698191 := by
  unfold tailWord_1941266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700946946283074670628913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47202525190088199121677101 17700946946283074670628913)
  ·
    refine ⟨13275710209712306002971685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17700946946283074670628913 13275710209712306002971685)
    ·
      refine ⟨2489195664321057375557191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13275710209712306002971685 2489195664321057375557191)
      ·
        refine ⟨3733793496481586063335787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489195664321057375557191 3733793496481586063335787)
        ·
          refine ⟨5600690244722379095003681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733793496481586063335787 5600690244722379095003681)
          ·
            refine ⟨4200517683541784321252761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600690244722379095003681 4200517683541784321252761)
            ·
              refine ⟨3150388262656338240939571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200517683541784321252761 3150388262656338240939571)
              ·
                refine ⟨4725582393984507361409357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150388262656338240939571 4725582393984507361409357)
                ·
                  refine ⟨1772093397744190260528509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4725582393984507361409357 1772093397744190260528509)
                  ·
                    refine ⟨664535024154071347698191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772093397744190260528509 664535024154071347698191)
                    ·
                      rfl

theorem cell22_1941266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1941266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941266 prefixEnd_1941266 := by exact prefixLift 1941266
  have htrace : WordTrace (prefixWord ++ tailWord_1941266) baseStart_1941266 baseEnd_1941266 := by
    simpa [prefixWord, tailWord_1941266, baseEnd_1941266] using wordTrace_append hprefix tailTrace_1941266
  have hstable : (prefixWord ++ tailWord_1941266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941266).length < 2 ^ (prefixWord ++ tailWord_1941266).sum := by decide
  have hdescent : baseEnd_1941266 < baseStart_1941266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941292 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_1941292 : Nat := 118140960795 + 1941292 * 2 ^ 59
def prefixEnd_1941292 : Nat := 4983230072969 + 3 ^ 40 * 1941292 * 2
def baseEnd_1941292 : Nat := 664543924485415946548111

theorem tailTrace_1941292 : CollatzResearch.WordTrace tailWord_1941292 prefixEnd_1941292 664543924485415946548111 := by
  unfold tailWord_1941292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35402368041519052561481065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47203157388692070081974753 35402368041519052561481065)
  ·
    refine ⟨26551776031139289421110799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35402368041519052561481065 26551776031139289421110799)
    ·
      refine ⟨39827664046708934131666199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26551776031139289421110799 39827664046708934131666199)
      ·
        refine ⟨59741496070063401197499299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39827664046708934131666199 59741496070063401197499299)
        ·
          refine ⟨89612244105095101796248949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59741496070063401197499299 89612244105095101796248949)
          ·
            refine ⟨8401147884852665793398339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89612244105095101796248949 8401147884852665793398339)
            ·
              refine ⟨12601721827278998690097509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401147884852665793398339 12601721827278998690097509)
              ·
                refine ⟨2362822842614812254393283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12601721827278998690097509 2362822842614812254393283)
                ·
                  refine ⟨3544234263922218381589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362822842614812254393283 3544234263922218381589925)
                  ·
                    refine ⟨664543924485415946548111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544234263922218381589925 664543924485415946548111)
                    ·
                      rfl

theorem cell22_1941292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_1941292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941292 prefixEnd_1941292 := by exact prefixLift 1941292
  have htrace : WordTrace (prefixWord ++ tailWord_1941292) baseStart_1941292 baseEnd_1941292 := by
    simpa [prefixWord, tailWord_1941292, baseEnd_1941292] using wordTrace_append hprefix tailTrace_1941292
  have hstable : (prefixWord ++ tailWord_1941292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941292).length < 2 ^ (prefixWord ++ tailWord_1941292).sum := by decide
  have hdescent : baseEnd_1941292 < baseStart_1941292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941309 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1941309 : Nat := 118140960795 + 1941309 * 2 ^ 59
def prefixEnd_1941309 : Nat := 4983230072969 + 3 ^ 40 * 1941309 * 2
def baseEnd_1941309 : Nat := 664549743932833568873059

theorem tailTrace_1941309 : CollatzResearch.WordTrace tailWord_1941309 prefixEnd_1941309 664549743932833568873059 := by
  unfold tailWord_1941309
  simp only [CollatzResearch.WordTrace]
  refine ⟨70805356123976517026330981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47203570749317678017553987 70805356123976517026330981)
  ·
    refine ⟨13276004273245596942437059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70805356123976517026330981 13276004273245596942437059)
    ·
      refine ⟨19914006409868395413655589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13276004273245596942437059 19914006409868395413655589)
      ·
        refine ⟨3733876201850324140060423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19914006409868395413655589 3733876201850324140060423)
        ·
          refine ⟨5600814302775486210090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733876201850324140060423 5600814302775486210090635)
          ·
            refine ⟨8401221454163229315135953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600814302775486210090635 8401221454163229315135953)
            ·
              refine ⟨6300916090622421986351965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401221454163229315135953 6300916090622421986351965)
              ·
                refine ⟨2362843533983408244881987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6300916090622421986351965 2362843533983408244881987)
                ·
                  refine ⟨3544265300975112367322981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362843533983408244881987 3544265300975112367322981)
                  ·
                    refine ⟨664549743932833568873059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544265300975112367322981 664549743932833568873059)
                    ·
                      rfl

theorem cell22_1941309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1941309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941309 prefixEnd_1941309 := by exact prefixLift 1941309
  have htrace : WordTrace (prefixWord ++ tailWord_1941309) baseStart_1941309 baseEnd_1941309 := by
    simpa [prefixWord, tailWord_1941309, baseEnd_1941309] using wordTrace_append hprefix tailTrace_1941309
  have hstable : (prefixWord ++ tailWord_1941309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941309).length < 2 ^ (prefixWord ++ tailWord_1941309).sum := by decide
  have hdescent : baseEnd_1941309 < baseStart_1941309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941322 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1941322 : Nat := 118140960795 + 1941322 * 2 ^ 59
def prefixEnd_1941322 : Nat := 4983230072969 + 3 ^ 40 * 1941322 * 2
def baseEnd_1941322 : Nat := 664554194098505868298019

theorem tailTrace_1941322 : CollatzResearch.WordTrace tailWord_1941322 prefixEnd_1941322 664554194098505868298019 := by
  unfold tailWord_1941322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701457568232355061638555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47203886848619613497702813 17701457568232355061638555)
  ·
    refine ⟨26552186352348532592457833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701457568232355061638555 26552186352348532592457833)
    ·
      refine ⟨19914139764261399444343375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26552186352348532592457833 19914139764261399444343375)
      ·
        refine ⟨29871209646392099166515063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19914139764261399444343375 29871209646392099166515063)
        ·
          refine ⟨44806814469588148749772595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29871209646392099166515063 44806814469588148749772595)
          ·
            refine ⟨67210221704382223124658893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44806814469588148749772595 67210221704382223124658893)
            ·
              refine ⟨25203833139143333671747085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67210221704382223124658893 25203833139143333671747085)
              ·
                refine ⟨9451437427178750126905157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25203833139143333671747085 9451437427178750126905157)
                ·
                  refine ⟨1772144517596015648794717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9451437427178750126905157 1772144517596015648794717)
                  ·
                    refine ⟨664554194098505868298019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772144517596015648794717 664554194098505868298019)
                    ·
                      rfl

theorem cell22_1941322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1941322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941322 prefixEnd_1941322 := by exact prefixLift 1941322
  have htrace : WordTrace (prefixWord ++ tailWord_1941322) baseStart_1941322 baseEnd_1941322 := by
    simpa [prefixWord, tailWord_1941322, baseEnd_1941322] using wordTrace_append hprefix tailTrace_1941322
  have hstable : (prefixWord ++ tailWord_1941322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941322).length < 2 ^ (prefixWord ++ tailWord_1941322).sum := by decide
  have hdescent : baseEnd_1941322 < baseStart_1941322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941324 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_1941324 : Nat := 118140960795 + 1941324 * 2 ^ 59
def prefixEnd_1941324 : Nat := 4983230072969 + 3 ^ 40 * 1941324 * 2
def baseEnd_1941324 : Nat := 221518292913126176582671

theorem tailTrace_1941324 : CollatzResearch.WordTrace tailWord_1941324 prefixEnd_1941324 221518292913126176582671 := by
  unfold tailWord_1941324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35402951609461087294063513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47203935479281449725418017 35402951609461087294063513)
  ·
    refine ⟨26552213707095815470547635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35402951609461087294063513 26552213707095815470547635)
    ·
      refine ⟨39828320560643723205821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26552213707095815470547635 39828320560643723205821453)
      ·
        refine ⟨14935620210241396202183045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39828320560643723205821453 14935620210241396202183045)
        ·
          refine ⟨2800428789420261787909321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14935620210241396202183045 2800428789420261787909321)
          ·
            refine ⟨2100321592065196340931991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800428789420261787909321 2100321592065196340931991)
            ·
              refine ⟨3150482388097794511397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100321592065196340931991 3150482388097794511397987)
              ·
                refine ⟨4725723582146691767096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150482388097794511397987 4725723582146691767096981)
                ·
                  refine ⟨221518292913126176582671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4725723582146691767096981 221518292913126176582671)
                  ·
                    rfl

theorem cell22_1941324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_1941324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941324 prefixEnd_1941324 := by exact prefixLift 1941324
  have htrace : WordTrace (prefixWord ++ tailWord_1941324) baseStart_1941324 baseEnd_1941324 := by
    simpa [prefixWord, tailWord_1941324, baseEnd_1941324] using wordTrace_append hprefix tailTrace_1941324
  have hstable : (prefixWord ++ tailWord_1941324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941324).length < 2 ^ (prefixWord ++ tailWord_1941324).sum := by decide
  have hdescent : baseEnd_1941324 < baseStart_1941324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941386 : List Nat := [3, 1, 2, 4, 3, 1, 1, 7]
def baseStart_1941386 : Nat := 118140960795 + 1941386 * 2 ^ 59
def prefixEnd_1941386 : Nat := 4983230072969 + 3 ^ 40 * 1941386 * 2
def baseEnd_1941386 : Nat := 73841789178492337188647

theorem tailTrace_1941386 : CollatzResearch.WordTrace tailWord_1941386 prefixEnd_1941386 73841789178492337188647 := by
  unfold tailWord_1941386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702041136174389794221003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47205443029798372784589341 17702041136174389794221003)
  ·
    refine ⟨26553061704261584691331505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702041136174389794221003 26553061704261584691331505)
    ·
      refine ⟨19914796278196188518498629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26553061704261584691331505 19914796278196188518498629)
      ·
        refine ⟨3734024302161785347218493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19914796278196188518498629 3734024302161785347218493)
        ·
          refine ⟨1400259113310669505206935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3734024302161785347218493 1400259113310669505206935)
          ·
            refine ⟨2100388669966004257810403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400259113310669505206935 2100388669966004257810403)
            ·
              refine ⟨3150583004949006386715605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100388669966004257810403 3150583004949006386715605)
              ·
                refine ⟨73841789178492337188647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3150583004949006386715605 73841789178492337188647)
                ·
                  rfl

theorem cell22_1941386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_1941386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941386 prefixEnd_1941386 := by exact prefixLift 1941386
  have htrace : WordTrace (prefixWord ++ tailWord_1941386) baseStart_1941386 baseEnd_1941386 := by
    simpa [prefixWord, tailWord_1941386, baseEnd_1941386] using wordTrace_append hprefix tailTrace_1941386
  have hstable : (prefixWord ++ tailWord_1941386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941386).length < 2 ^ (prefixWord ++ tailWord_1941386).sum := by decide
  have hdescent : baseEnd_1941386 < baseStart_1941386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941397 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1941397 : Nat := 118140960795 + 1941397 * 2 ^ 59
def prefixEnd_1941397 : Nat := 4983230072969 + 3 ^ 40 * 1941397 * 2
def baseEnd_1941397 : Nat := 221526622710410224224263

theorem tailTrace_1941397 : CollatzResearch.WordTrace tailWord_1941397 prefixEnd_1941397 221526622710410224224263 := by
  unfold tailWord_1941397
  simp only [CollatzResearch.WordTrace]
  refine ⟨70808565747657708055534445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47205710498438472037022963 70808565747657708055534445)
  ·
    refine ⟨26553212155371640520825417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70808565747657708055534445 26553212155371640520825417)
    ·
      refine ⟨19914909116528730390619063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26553212155371640520825417 19914909116528730390619063)
      ·
        refine ⟨29872363674793095585928595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19914909116528730390619063 29872363674793095585928595)
        ·
          refine ⟨44808545512189643378892893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29872363674793095585928595 44808545512189643378892893)
          ·
            refine ⟨16803204567071116267084835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44808545512189643378892893 16803204567071116267084835)
            ·
              refine ⟨25204806850606674400627253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803204567071116267084835 25204806850606674400627253)
              ·
                refine ⟨2362950642244375725058805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25204806850606674400627253 2362950642244375725058805)
                ·
                  refine ⟨221526622710410224224263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362950642244375725058805 221526622710410224224263)
                  ·
                    rfl

theorem cell22_1941397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1941397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941397 prefixEnd_1941397 := by exact prefixLift 1941397
  have htrace : WordTrace (prefixWord ++ tailWord_1941397) baseStart_1941397 baseEnd_1941397 := by
    simpa [prefixWord, tailWord_1941397, baseEnd_1941397] using wordTrace_append hprefix tailTrace_1941397
  have hstable : (prefixWord ++ tailWord_1941397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941397).length < 2 ^ (prefixWord ++ tailWord_1941397).sum := by decide
  have hdescent : baseEnd_1941397 < baseStart_1941397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941457 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1941457 : Nat := 118140960795 + 1941457 * 2 ^ 59
def prefixEnd_1941457 : Nat := 4983230072969 + 3 ^ 40 * 1941457 * 2
def baseEnd_1941457 : Nat := 664600407357410516172605

theorem tailTrace_1941457 : CollatzResearch.WordTrace tailWord_1941457 prefixEnd_1941457 664600407357410516172605 := by
  unfold tailWord_1941457
  simp only [CollatzResearch.WordTrace]
  refine ⟨70810754127440338302718625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47207169418293558868479083 70810754127440338302718625)
  ·
    refine ⟨53108065595580253727038969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70810754127440338302718625 53108065595580253727038969)
    ·
      refine ⟨39831049196685190295279227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53108065595580253727038969 39831049196685190295279227)
      ·
        refine ⟨59746573795027785442918841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39831049196685190295279227 59746573795027785442918841)
        ·
          refine ⟨44809930346270839082189131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59746573795027785442918841 44809930346270839082189131)
          ·
            refine ⟨67214895519406258623283697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44809930346270839082189131 67214895519406258623283697)
            ·
              refine ⟨50411171639554693967462773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67214895519406258623283697 50411171639554693967462773)
              ·
                refine ⟨4726047341208252559449635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50411171639554693967462773 4726047341208252559449635)
                ·
                  refine ⟨7089071011812378839174453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726047341208252559449635 7089071011812378839174453)
                  ·
                    refine ⟨664600407357410516172605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7089071011812378839174453 664600407357410516172605)
                    ·
                      rfl

theorem cell22_1941457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1941457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941457 prefixEnd_1941457 := by exact prefixLift 1941457
  have htrace : WordTrace (prefixWord ++ tailWord_1941457) baseStart_1941457 baseEnd_1941457 := by
    simpa [prefixWord, tailWord_1941457, baseEnd_1941457] using wordTrace_append hprefix tailTrace_1941457
  have hstable : (prefixWord ++ tailWord_1941457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941457).length < 2 ^ (prefixWord ++ tailWord_1941457).sum := by decide
  have hdescent : baseEnd_1941457 < baseStart_1941457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941461 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1941461 : Nat := 118140960795 + 1941461 * 2 ^ 59
def prefixEnd_1941461 : Nat := 4983230072969 + 3 ^ 40 * 1941461 * 2
def baseEnd_1941461 : Nat := 664601776639155839072593

theorem tailTrace_1941461 : CollatzResearch.WordTrace tailWord_1941461 prefixEnd_1941461 664601776639155839072593 := by
  unfold tailWord_1941461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70810900019425846985864237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47207266679617231323909491 70810900019425846985864237)
  ·
    refine ⟨26554087507284692619699089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70810900019425846985864237 26554087507284692619699089)
    ·
      refine ⟨19915565630463519464774317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26554087507284692619699089 19915565630463519464774317)
      ·
        refine ⟨7468337111423819799290369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19915565630463519464774317 7468337111423819799290369)
        ·
          refine ⟨5601252833567864849467777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7468337111423819799290369 5601252833567864849467777)
          ·
            refine ⟨4200939625175898637100833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601252833567864849467777 4200939625175898637100833)
            ·
              refine ⟨3150704718881923977825625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200939625175898637100833 3150704718881923977825625)
              ·
                refine ⟨2363028539161442983369219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150704718881923977825625 2363028539161442983369219)
                ·
                  refine ⟨3544542808742164475053829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363028539161442983369219 3544542808742164475053829)
                  ·
                    refine ⟨664601776639155839072593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544542808742164475053829 664601776639155839072593)
                    ·
                      rfl

theorem cell22_1941461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1941461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941461 prefixEnd_1941461 := by exact prefixLift 1941461
  have htrace : WordTrace (prefixWord ++ tailWord_1941461) baseStart_1941461 baseEnd_1941461 := by
    simpa [prefixWord, tailWord_1941461, baseEnd_1941461] using wordTrace_append hprefix tailTrace_1941461
  have hstable : (prefixWord ++ tailWord_1941461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941461).length < 2 ^ (prefixWord ++ tailWord_1941461).sum := by decide
  have hdescent : baseEnd_1941461 < baseStart_1941461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_1941472 : Nat := 118140960795 + 1941472 * 2 ^ 59
def prefixEnd_1941472 : Nat := 4983230072969 + 3 ^ 40 * 1941472 * 2
def baseEnd_1941472 : Nat := 664605542163955477047559

theorem tailTrace_1941472 : CollatzResearch.WordTrace tailWord_1941472 prefixEnd_1941472 664605542163955477047559 := by
  unfold tailWord_1941472
  simp only [CollatzResearch.WordTrace]
  refine ⟨35405650611192997932257335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47207534148257330576343113 35405650611192997932257335)
  ·
    refine ⟨53108475916789496898386003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35405650611192997932257335 53108475916789496898386003)
    ·
      refine ⟨79662713875184245347579005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53108475916789496898386003 79662713875184245347579005)
      ·
        refine ⟨29873517703194092005342127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79662713875184245347579005 29873517703194092005342127)
        ·
          refine ⟨44810276554791138008013191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29873517703194092005342127 44810276554791138008013191)
          ·
            refine ⟨67215414832186707012019787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44810276554791138008013191 67215414832186707012019787)
            ·
              refine ⟨100823122248280060518029681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67215414832186707012019787 100823122248280060518029681)
              ·
                refine ⟨75617341686210045388522261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100823122248280060518029681 75617341686210045388522261)
                ·
                  refine ⟨3544562891541095877586981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75617341686210045388522261 3544562891541095877586981)
                  ·
                    refine ⟨664605542163955477047559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544562891541095877586981 664605542163955477047559)
                    ·
                      rfl

theorem cell22_1941472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_1941472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941472 prefixEnd_1941472 := by exact prefixLift 1941472
  have htrace : WordTrace (prefixWord ++ tailWord_1941472) baseStart_1941472 baseEnd_1941472 := by
    simpa [prefixWord, tailWord_1941472, baseEnd_1941472] using wordTrace_append hprefix tailTrace_1941472
  have hstable : (prefixWord ++ tailWord_1941472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941472).length < 2 ^ (prefixWord ++ tailWord_1941472).sum := by decide
  have hdescent : baseEnd_1941472 < baseStart_1941472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941553 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_1941553 : Nat := 118140960795 + 1941553 * 2 ^ 59
def prefixEnd_1941553 : Nat := 4983230072969 + 3 ^ 40 * 1941553 * 2
def baseEnd_1941553 : Nat := 664633270119298265772311

theorem tailTrace_1941553 : CollatzResearch.WordTrace tailWord_1941553 prefixEnd_1941553 664633270119298265772311 := by
  unfold tailWord_1941553
  simp only [CollatzResearch.WordTrace]
  refine ⟨70814255535092546698213313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47209503690061697798808875 70814255535092546698213313)
  ·
    refine ⟨53110691651319410023659985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70814255535092546698213313 53110691651319410023659985)
    ·
      refine ⟨39833018738489557517744989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53110691651319410023659985 39833018738489557517744989)
      ·
        refine ⟨14937382026933584069154371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39833018738489557517744989 14937382026933584069154371)
        ·
          refine ⟨22406073040400376103731557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14937382026933584069154371 22406073040400376103731557)
          ·
            refine ⟨4201138695075070519449667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22406073040400376103731557 4201138695075070519449667)
            ·
              refine ⟨6301708042612605779174501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201138695075070519449667 6301708042612605779174501)
              ·
                refine ⟨1181570257989863583595219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6301708042612605779174501 1181570257989863583595219)
                ·
                  refine ⟨1772355386984795375392829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181570257989863583595219 1772355386984795375392829)
                  ·
                    refine ⟨664633270119298265772311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772355386984795375392829 664633270119298265772311)
                    ·
                      rfl

theorem cell22_1941553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_1941553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941553 prefixEnd_1941553 := by exact prefixLift 1941553
  have htrace : WordTrace (prefixWord ++ tailWord_1941553) baseStart_1941553 baseEnd_1941553 := by
    simpa [prefixWord, tailWord_1941553, baseEnd_1941553] using wordTrace_append hprefix tailTrace_1941553
  have hstable : (prefixWord ++ tailWord_1941553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941553).length < 2 ^ (prefixWord ++ tailWord_1941553).sum := by decide
  have hdescent : baseEnd_1941553 < baseStart_1941553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941564 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1941564 : Nat := 118140960795 + 1941564 * 2 ^ 59
def prefixEnd_1941564 : Nat := 4983230072969 + 3 ^ 40 * 1941564 * 2
def baseEnd_1941564 : Nat := 664637035644097903747277

theorem tailTrace_1941564 : CollatzResearch.WordTrace tailWord_1941564 prefixEnd_1941564 664637035644097903747277 := by
  unfold tailWord_1941564
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407328369026347788431873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47209771158701797051242497 35407328369026347788431873)
  ·
    refine ⟨26555496276769760841323905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35407328369026347788431873 26555496276769760841323905)
    ·
      refine ⟨19916622207577320630992929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26555496276769760841323905 19916622207577320630992929)
      ·
        refine ⟨14937466655682990473244697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19916622207577320630992929 14937466655682990473244697)
        ·
          refine ⟨11203099991762242854933523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14937466655682990473244697 11203099991762242854933523)
          ·
            refine ⟨16804649987643364282400285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203099991762242854933523 16804649987643364282400285)
            ·
              refine ⟨6301743745366261605900107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16804649987643364282400285 6301743745366261605900107)
              ·
                refine ⟨9452615618049392408850161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301743745366261605900107 9452615618049392408850161)
                ·
                  refine ⟨7089461713537044306637621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9452615618049392408850161 7089461713537044306637621)
                  ·
                    refine ⟨664637035644097903747277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7089461713537044306637621 664637035644097903747277)
                    ·
                      rfl

theorem cell22_1941564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1941564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941564 prefixEnd_1941564 := by exact prefixLift 1941564
  have htrace : WordTrace (prefixWord ++ tailWord_1941564) baseStart_1941564 baseEnd_1941564 := by
    simpa [prefixWord, tailWord_1941564, baseEnd_1941564] using wordTrace_append hprefix tailTrace_1941564
  have hstable : (prefixWord ++ tailWord_1941564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941564).length < 2 ^ (prefixWord ++ tailWord_1941564).sum := by decide
  have hdescent : baseEnd_1941564 < baseStart_1941564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941656 : List Nat := [2, 1, 2, 4, 3, 2, 8]
def baseStart_1941656 : Nat := 118140960795 + 1941656 * 2 ^ 59
def prefixEnd_1941656 : Nat := 4983230072969 + 3 ^ 40 * 1941656 * 2
def baseEnd_1941656 : Nat := 24617352930527419646185

theorem tailTrace_1941656 : CollatzResearch.WordTrace tailWord_1941656 prefixEnd_1941656 24617352930527419646185 := by
  unfold tailWord_1941656
  simp only [CollatzResearch.WordTrace]
  refine ⟨35409006126859697644606411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47212008169146263526141881 35409006126859697644606411)
  ·
    refine ⟨53113509190289546466909617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35409006126859697644606411 53113509190289546466909617)
    ·
      refine ⟨39835131892717159850182213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53113509190289546466909617 39835131892717159850182213)
      ·
        refine ⟨7469087229884467471909165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39835131892717159850182213 7469087229884467471909165)
        ·
          refine ⟨2800907711206675301965937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7469087229884467471909165 2800907711206675301965937)
          ·
            refine ⟨2100680783405006476474453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800907711206675301965937 2100680783405006476474453)
            ·
              refine ⟨24617352930527419646185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2100680783405006476474453 24617352930527419646185)
              ·
                rfl

theorem cell22_1941656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 8].length) (baseStart_1941656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941656 prefixEnd_1941656 := by exact prefixLift 1941656
  have htrace : WordTrace (prefixWord ++ tailWord_1941656) baseStart_1941656 baseEnd_1941656 := by
    simpa [prefixWord, tailWord_1941656, baseEnd_1941656] using wordTrace_append hprefix tailTrace_1941656
  have hstable : (prefixWord ++ tailWord_1941656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941656).length < 2 ^ (prefixWord ++ tailWord_1941656).sum := by decide
  have hdescent : baseEnd_1941656 < baseStart_1941656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941658 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1941658 : Nat := 118140960795 + 1941658 * 2 ^ 59
def prefixEnd_1941658 : Nat := 4983230072969 + 3 ^ 40 * 1941658 * 2
def baseEnd_1941658 : Nat := 664669213765112991896989

theorem tailTrace_1941658 : CollatzResearch.WordTrace tailWord_1941658 prefixEnd_1941658 664669213765112991896989 := by
  unfold tailWord_1941658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704521299928037407696407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47212056799808099753857085 17704521299928037407696407)
  ·
    refine ⟨26556781949892056111544611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17704521299928037407696407 26556781949892056111544611)
    ·
      refine ⟨39835172924838084167316917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26556781949892056111544611 39835172924838084167316917)
      ·
        refine ⟨3734547461703570390685961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39835172924838084167316917 3734547461703570390685961)
        ·
          refine ⟨2800910596277677793014471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3734547461703570390685961 2800910596277677793014471)
          ·
            refine ⟨4201365894416516689521707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800910596277677793014471 4201365894416516689521707)
            ·
              refine ⟨6302048841624775034282561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201365894416516689521707 6302048841624775034282561)
              ·
                refine ⟨4726536631218581275711921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302048841624775034282561 4726536631218581275711921)
                ·
                  refine ⟨3544902473413935956783941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726536631218581275711921 3544902473413935956783941)
                  ·
                    refine ⟨664669213765112991896989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3544902473413935956783941 664669213765112991896989)
                    ·
                      rfl

theorem cell22_1941658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1941658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941658 prefixEnd_1941658 := by exact prefixLift 1941658
  have htrace : WordTrace (prefixWord ++ tailWord_1941658) baseStart_1941658 baseEnd_1941658 := by
    simpa [prefixWord, tailWord_1941658, baseEnd_1941658] using wordTrace_append hprefix tailTrace_1941658
  have hstable : (prefixWord ++ tailWord_1941658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941658).length < 2 ^ (prefixWord ++ tailWord_1941658).sum := by decide
  have hdescent : baseEnd_1941658 < baseStart_1941658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941662 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1941662 : Nat := 118140960795 + 1941662 * 2 ^ 59
def prefixEnd_1941662 : Nat := 4983230072969 + 3 ^ 40 * 1941662 * 2
def baseEnd_1941662 : Nat := 221556861015619438265659

theorem tailTrace_1941662 : CollatzResearch.WordTrace tailWord_1941662 prefixEnd_1941662 221556861015619438265659 := by
  unfold tailWord_1941662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852278886462207289241405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47212154061131772209287493 8852278886462207289241405)
  ·
    refine ⟨3319604582423327733465527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8852278886462207289241405 3319604582423327733465527)
    ·
      refine ⟨4979406873634991600198291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319604582423327733465527 4979406873634991600198291)
      ·
        refine ⟨7469110310452487400297437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979406873634991600198291 7469110310452487400297437)
        ·
          refine ⟨2800916366419682775111539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7469110310452487400297437 2800916366419682775111539)
          ·
            refine ⟨4201374549629524162667309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800916366419682775111539 4201374549629524162667309)
            ·
              refine ⟨1575515456111071561000241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4201374549629524162667309 1575515456111071561000241)
              ·
                refine ⟨1181636592083303670750181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575515456111071561000241 1181636592083303670750181)
                ·
                  refine ⟨221556861015619438265659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181636592083303670750181 221556861015619438265659)
                  ·
                    rfl

theorem cell22_1941662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1941662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941662 prefixEnd_1941662 := by exact prefixLift 1941662
  have htrace : WordTrace (prefixWord ++ tailWord_1941662) baseStart_1941662 baseEnd_1941662 := by
    simpa [prefixWord, tailWord_1941662, baseEnd_1941662] using wordTrace_append hprefix tailTrace_1941662
  have hstable : (prefixWord ++ tailWord_1941662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941662).length < 2 ^ (prefixWord ++ tailWord_1941662).sum := by decide
  have hdescent : baseEnd_1941662 < baseStart_1941662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941669 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1941669 : Nat := 118140960795 + 1941669 * 2 ^ 59
def prefixEnd_1941669 : Nat := 4983230072969 + 3 ^ 40 * 1941669 * 2
def baseEnd_1941669 : Nat := 664672979289912629871955

theorem tailTrace_1941669 : CollatzResearch.WordTrace tailWord_1941669 prefixEnd_1941669 664672979289912629871955 := by
  unfold tailWord_1941669
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818486402672298509436061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47212324268448199006290707 70818486402672298509436061)
  ·
    refine ⟨26556932401002111941038523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70818486402672298509436061 26556932401002111941038523)
    ·
      refine ⟨39835398601503167911557785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26556932401002111941038523 39835398601503167911557785)
      ·
        refine ⟨29876548951127375933668339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39835398601503167911557785 29876548951127375933668339)
        ·
          refine ⟨44814823426691063900502509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29876548951127375933668339 44814823426691063900502509)
          ·
            refine ⟨16805558785009148962688441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44814823426691063900502509 16805558785009148962688441)
            ·
              refine ⟨12604169088756861722016331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16805558785009148962688441 12604169088756861722016331)
              ·
                refine ⟨18906253633135292583024497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604169088756861722016331 18906253633135292583024497)
                ·
                  refine ⟨14179690224851469437268373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18906253633135292583024497 14179690224851469437268373)
                  ·
                    refine ⟨664672979289912629871955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14179690224851469437268373 664672979289912629871955)
                    ·
                      rfl

theorem cell22_1941669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1941669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941669 prefixEnd_1941669 := by exact prefixLift 1941669
  have htrace : WordTrace (prefixWord ++ tailWord_1941669) baseStart_1941669 baseEnd_1941669 := by
    simpa [prefixWord, tailWord_1941669, baseEnd_1941669] using wordTrace_append hprefix tailTrace_1941669
  have hstable : (prefixWord ++ tailWord_1941669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941669).length < 2 ^ (prefixWord ++ tailWord_1941669).sum := by decide
  have hdescent : baseEnd_1941669 < baseStart_1941669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941677 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1941677 : Nat := 118140960795 + 1941677 * 2 ^ 59
def prefixEnd_1941677 : Nat := 4983230072969 + 3 ^ 40 * 1941677 * 2
def baseEnd_1941677 : Nat := 664675717853403275671931

theorem tailTrace_1941677 : CollatzResearch.WordTrace tailWord_1941677 prefixEnd_1941677 664675717853403275671931 := by
  unfold tailWord_1941677
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818778186643315875727285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47212518791095543917151523 70818778186643315875727285)
  ·
    refine ⟨6639260454997810863349433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70818778186643315875727285 6639260454997810863349433)
    ·
      refine ⟨4979445341248358147512075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6639260454997810863349433 4979445341248358147512075)
      ·
        refine ⟨7469168011872537221268113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979445341248358147512075 7469168011872537221268113)
        ·
          refine ⟨5601876008904402915951085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469168011872537221268113 5601876008904402915951085)
          ·
            refine ⟨2100703503339151093481657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5601876008904402915951085 2100703503339151093481657)
            ·
              refine ⟨1575527627504363320111243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100703503339151093481657 1575527627504363320111243)
              ·
                refine ⟨2363291441256544980166865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575527627504363320111243 2363291441256544980166865)
                ·
                  refine ⟨1772468580942408735125149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363291441256544980166865 1772468580942408735125149)
                  ·
                    refine ⟨664675717853403275671931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772468580942408735125149 664675717853403275671931)
                    ·
                      rfl

theorem cell22_1941677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1941677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941677 prefixEnd_1941677 := by exact prefixLift 1941677
  have htrace : WordTrace (prefixWord ++ tailWord_1941677) baseStart_1941677 baseEnd_1941677 := by
    simpa [prefixWord, tailWord_1941677, baseEnd_1941677] using wordTrace_append hprefix tailTrace_1941677
  have hstable : (prefixWord ++ tailWord_1941677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941677).length < 2 ^ (prefixWord ++ tailWord_1941677).sum := by decide
  have hdescent : baseEnd_1941677 < baseStart_1941677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941746 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1941746 : Nat := 118140960795 + 1941746 * 2 ^ 59
def prefixEnd_1941746 : Nat := 4983230072969 + 3 ^ 40 * 1941746 * 2
def baseEnd_1941746 : Nat := 221566445987836698565573

theorem tailTrace_1941746 : CollatzResearch.WordTrace tailWord_1941746 prefixEnd_1941746 221566445987836698565573 := by
  unfold tailWord_1941746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705323705848335164997273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47214196548928893773326061 17705323705848335164997273)
  ·
    refine ⟨13278992779386251373747955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17705323705848335164997273 13278992779386251373747955)
    ·
      refine ⟨19918489169079377060621933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13278992779386251373747955 19918489169079377060621933)
      ·
        refine ⟨7469433438404766397733225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19918489169079377060621933 7469433438404766397733225)
        ·
          refine ⟨5602075078803574798299919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469433438404766397733225 5602075078803574798299919)
          ·
            refine ⟨8403112618205362197449879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602075078803574798299919 8403112618205362197449879)
            ·
              refine ⟨12604668927308043296174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403112618205362197449879 12604668927308043296174819)
              ·
                refine ⟨18907003390962064944262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604668927308043296174819 18907003390962064944262229)
                ·
                  refine ⟨221566445987836698565573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18907003390962064944262229 221566445987836698565573)
                  ·
                    rfl

theorem cell22_1941746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1941746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941746 prefixEnd_1941746 := by exact prefixLift 1941746
  have htrace : WordTrace (prefixWord ++ tailWord_1941746) baseStart_1941746 baseEnd_1941746 := by
    simpa [prefixWord, tailWord_1941746, baseEnd_1941746] using wordTrace_append hprefix tailTrace_1941746
  have hstable : (prefixWord ++ tailWord_1941746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941746).length < 2 ^ (prefixWord ++ tailWord_1941746).sum := by decide
  have hdescent : baseEnd_1941746 < baseStart_1941746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941761 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1941761 : Nat := 118140960795 + 1941761 * 2 ^ 59
def prefixEnd_1941761 : Nat := 4983230072969 + 3 ^ 40 * 1941761 * 2
def baseEnd_1941761 : Nat := 664704472770055056571673

theorem tailTrace_1941761 : CollatzResearch.WordTrace tailWord_1941761 prefixEnd_1941761 664704472770055056571673 := by
  unfold tailWord_1941761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70821841918338998221785137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47214561278892665481190091 70821841918338998221785137)
  ·
    refine ⟨53116381438754248666338853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70821841918338998221785137 53116381438754248666338853)
    ·
      refine ⟨9959321519766421624938535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53116381438754248666338853 9959321519766421624938535)
      ·
        refine ⟨14938982279649632437407803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959321519766421624938535 14938982279649632437407803)
        ·
          refine ⟨22408473419474448656111705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14938982279649632437407803 22408473419474448656111705)
          ·
            refine ⟨16806355064605836492083779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408473419474448656111705 16806355064605836492083779)
            ·
              refine ⟨25209532596908754738125669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16806355064605836492083779 25209532596908754738125669)
              ·
                refine ⟨4726787361920391513398563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25209532596908754738125669 4726787361920391513398563)
                ·
                  refine ⟨7090181042880587270097845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726787361920391513398563 7090181042880587270097845)
                  ·
                    refine ⟨664704472770055056571673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7090181042880587270097845 664704472770055056571673)
                    ·
                      rfl

theorem cell22_1941761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1941761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941761 prefixEnd_1941761 := by exact prefixLift 1941761
  have htrace : WordTrace (prefixWord ++ tailWord_1941761) baseStart_1941761 baseEnd_1941761 := by
    simpa [prefixWord, tailWord_1941761, baseEnd_1941761] using wordTrace_append hprefix tailTrace_1941761
  have hstable : (prefixWord ++ tailWord_1941761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941761).length < 2 ^ (prefixWord ++ tailWord_1941761).sum := by decide
  have hdescent : baseEnd_1941761 < baseStart_1941761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941763 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 4]
def baseStart_1941763 : Nat := 118140960795 + 1941763 * 2 ^ 59
def prefixEnd_1941763 : Nat := 4983230072969 + 3 ^ 40 * 1941763 * 2
def baseEnd_1941763 : Nat := 221568385803642572673889

theorem tailTrace_1941763 : CollatzResearch.WordTrace tailWord_1941763 prefixEnd_1941763 221568385803642572673889 := by
  unfold tailWord_1941763
  simp only [CollatzResearch.WordTrace]
  refine ⟨70821914864331752563357943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47214609909554501708905295 70821914864331752563357943)
  ·
    refine ⟨106232872296497628845036915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70821914864331752563357943 106232872296497628845036915)
    ·
      refine ⟨159349308444746443267555373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106232872296497628845036915 159349308444746443267555373)
      ·
        refine ⟨59755990666779916225333265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159349308444746443267555373 59755990666779916225333265)
        ·
          refine ⟨44816993000084937168999949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59755990666779916225333265 44816993000084937168999949)
          ·
            refine ⟨16806372375031851438374981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44816993000084937168999949 16806372375031851438374981)
            ·
              refine ⟨3151194820318472144695309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16806372375031851438374981 3151194820318472144695309)
              ·
                refine ⟨1181698057619427054260741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3151194820318472144695309 1181698057619427054260741)
                ·
                  refine ⟨221568385803642572673889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181698057619427054260741 221568385803642572673889)
                  ·
                    rfl

theorem cell22_1941763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 4].length) (baseStart_1941763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941763 prefixEnd_1941763 := by exact prefixLift 1941763
  have htrace : WordTrace (prefixWord ++ tailWord_1941763) baseStart_1941763 baseEnd_1941763 := by
    simpa [prefixWord, tailWord_1941763, baseEnd_1941763] using wordTrace_append hprefix tailTrace_1941763
  have hstable : (prefixWord ++ tailWord_1941763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941763).length < 2 ^ (prefixWord ++ tailWord_1941763).sum := by decide
  have hdescent : baseEnd_1941763 < baseStart_1941763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941795 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 2, 3]
def baseStart_1941795 : Nat := 118140960795 + 1941795 * 2 ^ 59
def prefixEnd_1941795 : Nat := 4983230072969 + 3 ^ 40 * 1941795 * 2
def baseEnd_1941795 : Nat := 664716111664890301221569

theorem tailTrace_1941795 : CollatzResearch.WordTrace tailWord_1941795 prefixEnd_1941795 664716111664890301221569 := by
  unfold tailWord_1941795
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823082000215822028522839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47215388000143881352348559 70823082000215822028522839)
  ·
    refine ⟨106234623000323733042784259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70823082000215822028522839 106234623000323733042784259)
    ·
      refine ⟨159351934500485599564176389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106234623000323733042784259 159351934500485599564176389)
      ·
        refine ⟨29878487718841049918283073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159351934500485599564176389 29878487718841049918283073)
        ·
          refine ⟨22408865789130787438712305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29878487718841049918283073 22408865789130787438712305)
          ·
            refine ⟨16806649341848090579034229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408865789130787438712305 16806649341848090579034229)
            ·
              refine ⟨1575623375798258491784459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16806649341848090579034229 1575623375798258491784459)
              ·
                refine ⟨2363435063697387737676689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575623375798258491784459 2363435063697387737676689)
                ·
                  refine ⟨1772576297773040803257517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363435063697387737676689 1772576297773040803257517)
                  ·
                    refine ⟨664716111664890301221569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772576297773040803257517 664716111664890301221569)
                    ·
                      rfl

theorem cell22_1941795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 3].length) (baseStart_1941795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941795 prefixEnd_1941795 := by exact prefixLift 1941795
  have htrace : WordTrace (prefixWord ++ tailWord_1941795) baseStart_1941795 baseEnd_1941795 := by
    simpa [prefixWord, tailWord_1941795, baseEnd_1941795] using wordTrace_append hprefix tailTrace_1941795
  have hstable : (prefixWord ++ tailWord_1941795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941795).length < 2 ^ (prefixWord ++ tailWord_1941795).sum := by decide
  have hdescent : baseEnd_1941795 < baseStart_1941795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941799 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1941799 : Nat := 118140960795 + 1941799 * 2 ^ 59
def prefixEnd_1941799 : Nat := 4983230072969 + 3 ^ 40 * 1941799 * 2
def baseEnd_1941799 : Nat := 664717480946635624121557

theorem tailTrace_1941799 : CollatzResearch.WordTrace tailWord_1941799 prefixEnd_1941799 664717480946635624121557 := by
  unfold tailWord_1941799
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823227892201330711668451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47215485261467553807778967 70823227892201330711668451)
  ·
    refine ⟨106234841838301996067502677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70823227892201330711668451 106234841838301996067502677)
    ·
      refine ⟨1244939552792601516416047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 106234841838301996067502677 1244939552792601516416047)
      ·
        refine ⟨1867409329188902274624071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244939552792601516416047 1867409329188902274624071)
        ·
          refine ⟨2801113993783353411936107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867409329188902274624071 2801113993783353411936107)
          ·
            refine ⟨4201670990675030117904161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801113993783353411936107 4201670990675030117904161)
            ·
              refine ⟨3151253243006272588428121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201670990675030117904161 3151253243006272588428121)
              ·
                refine ⟨2363439932254704441321091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151253243006272588428121 2363439932254704441321091)
                ·
                  refine ⟨3545159898382056661981637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363439932254704441321091 3545159898382056661981637)
                  ·
                    refine ⟨664717480946635624121557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545159898382056661981637 664717480946635624121557)
                    ·
                      rfl

theorem cell22_1941799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1941799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941799 prefixEnd_1941799 := by exact prefixLift 1941799
  have htrace : WordTrace (prefixWord ++ tailWord_1941799) baseStart_1941799 baseEnd_1941799 := by
    simpa [prefixWord, tailWord_1941799, baseEnd_1941799] using wordTrace_append hprefix tailTrace_1941799
  have hstable : (prefixWord ++ tailWord_1941799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941799).length < 2 ^ (prefixWord ++ tailWord_1941799).sum := by decide
  have hdescent : baseEnd_1941799 < baseStart_1941799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941825 : List Nat := [1, 2, 5, 2, 3, 1, 8]
def baseStart_1941825 : Nat := 118140960795 + 1941825 * 2 ^ 59
def prefixEnd_1941825 : Nat := 4983230072969 + 3 ^ 40 * 1941825 * 2
def baseEnd_1941825 : Nat := 24619495602888156406351

theorem tailTrace_1941825 : CollatzResearch.WordTrace tailWord_1941825 prefixEnd_1941825 24619495602888156406351 := by
  unfold tailWord_1941825
  simp only [CollatzResearch.WordTrace]
  refine ⟨70824176190107137152114929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47216117460071424768076619 70824176190107137152114929)
  ·
    refine ⟨53118132142580352864086197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70824176190107137152114929 53118132142580352864086197)
    ·
      refine ⟨4979824888366908081008081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53118132142580352864086197 4979824888366908081008081)
      ·
        refine ⟨3734868666275181060756061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979824888366908081008081 3734868666275181060756061)
        ·
          refine ⟨1400575749853192897783523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3734868666275181060756061 1400575749853192897783523)
          ·
            refine ⟨2100863624779789346675285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400575749853192897783523 2100863624779789346675285)
            ·
              refine ⟨24619495602888156406351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2100863624779789346675285 24619495602888156406351)
              ·
                rfl

theorem cell22_1941825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 8].length) (baseStart_1941825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941825 prefixEnd_1941825 := by exact prefixLift 1941825
  have htrace : WordTrace (prefixWord ++ tailWord_1941825) baseStart_1941825 baseEnd_1941825 := by
    simpa [prefixWord, tailWord_1941825, baseEnd_1941825] using wordTrace_append hprefix tailTrace_1941825
  have hstable : (prefixWord ++ tailWord_1941825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941825).length < 2 ^ (prefixWord ++ tailWord_1941825).sum := by decide
  have hdescent : baseEnd_1941825 < baseStart_1941825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941836 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1941836 : Nat := 118140960795 + 1941836 * 2 ^ 59
def prefixEnd_1941836 : Nat := 4983230072969 + 3 ^ 40 * 1941836 * 2
def baseEnd_1941836 : Nat := 221576715600926620315481

theorem tailTrace_1941836 : CollatzResearch.WordTrace tailWord_1941836 prefixEnd_1941836 221576715600926620315481 := by
  unfold tailWord_1941836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412288696533643015382681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47216384928711524020510241 35412288696533643015382681)
  ·
    refine ⟨26559216522400232261537011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35412288696533643015382681 26559216522400232261537011)
    ·
      refine ⟨39838824783600348392305517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26559216522400232261537011 39838824783600348392305517)
      ·
        refine ⟨14939559293850130647114569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39838824783600348392305517 14939559293850130647114569)
        ·
          refine ⟨11204669470387597985335927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14939559293850130647114569 11204669470387597985335927)
          ·
            refine ⟨16807004205581396978003891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204669470387597985335927 16807004205581396978003891)
            ·
              refine ⟨25210506308372095467005837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16807004205581396978003891 25210506308372095467005837)
              ·
                refine ⟨9453939865639535800127189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25210506308372095467005837 9453939865639535800127189)
                ·
                  refine ⟨221576715600926620315481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9453939865639535800127189 221576715600926620315481)
                  ·
                    rfl

theorem cell22_1941836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1941836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941836 prefixEnd_1941836 := by exact prefixLift 1941836
  have htrace : WordTrace (prefixWord ++ tailWord_1941836) baseStart_1941836 baseEnd_1941836 := by
    simpa [prefixWord, tailWord_1941836, baseEnd_1941836] using wordTrace_append hprefix tailTrace_1941836
  have hstable : (prefixWord ++ tailWord_1941836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941836).length < 2 ^ (prefixWord ++ tailWord_1941836).sum := by decide
  have hdescent : baseEnd_1941836 < baseStart_1941836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941840 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_1941840 : Nat := 118140960795 + 1941840 * 2 ^ 59
def prefixEnd_1941840 : Nat := 4983230072969 + 3 ^ 40 * 1941840 * 2
def baseEnd_1941840 : Nat := 664731516084525183846431

theorem tailTrace_1941840 : CollatzResearch.WordTrace tailWord_1941840 prefixEnd_1941840 664731516084525183846431 := by
  unfold tailWord_1941840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412361642526397356955487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47216482190035196475940649 35412361642526397356955487)
  ·
    refine ⟨53118542463789596035433231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35412361642526397356955487 53118542463789596035433231)
    ·
      refine ⟨79677813695684394053149847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53118542463789596035433231 79677813695684394053149847)
      ·
        refine ⟨119516720543526591079724771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79677813695684394053149847 119516720543526591079724771)
        ·
          refine ⟨179275080815289886619587157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119516720543526591079724771 179275080815289886619587157)
          ·
            refine ⟨2100879853304178358823287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 179275080815289886619587157 2100879853304178358823287)
            ·
              refine ⟨3151319779956267538234931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100879853304178358823287 3151319779956267538234931)
              ·
                refine ⟨4726979669934401307352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151319779956267538234931 4726979669934401307352397)
                ·
                  refine ⟨1772617376225400490257149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4726979669934401307352397 1772617376225400490257149)
                  ·
                    refine ⟨664731516084525183846431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772617376225400490257149 664731516084525183846431)
                    ·
                      rfl

theorem cell22_1941840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_1941840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941840 prefixEnd_1941840 := by exact prefixLift 1941840
  have htrace : WordTrace (prefixWord ++ tailWord_1941840) baseStart_1941840 baseEnd_1941840 := by
    simpa [prefixWord, tailWord_1941840, baseEnd_1941840] using wordTrace_append hprefix tailTrace_1941840
  have hstable : (prefixWord ++ tailWord_1941840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941840).length < 2 ^ (prefixWord ++ tailWord_1941840).sum := by decide
  have hdescent : baseEnd_1941840 < baseStart_1941840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941891 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 1, 3]
def baseStart_1941891 : Nat := 118140960795 + 1941891 * 2 ^ 59
def prefixEnd_1941891 : Nat := 4983230072969 + 3 ^ 40 * 1941891 * 2
def baseEnd_1941891 : Nat := 664748974426778050821275

theorem tailTrace_1941891 : CollatzResearch.WordTrace tailWord_1941891 prefixEnd_1941891 664748974426778050821275 := by
  unfold tailWord_1941891
  simp only [CollatzResearch.WordTrace]
  refine ⟨70826583407868030424017527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47217722271912020282678351 70826583407868030424017527)
  ·
    refine ⟨106239875111802045636026291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70826583407868030424017527 106239875111802045636026291)
    ·
      refine ⟨159359812667703068454039437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106239875111802045636026291 159359812667703068454039437)
      ·
        refine ⟨59759929750388650670264789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159359812667703068454039437 59759929750388650670264789)
        ·
          refine ⟨1400623353524734000084331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59759929750388650670264789 1400623353524734000084331)
          ·
            refine ⟨2100935030287101000126497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400623353524734000084331 2100935030287101000126497)
            ·
              refine ⟨1575701272715325750094873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100935030287101000126497 1575701272715325750094873)
              ·
                refine ⟨1181775954536494312571155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575701272715325750094873 1181775954536494312571155)
                ·
                  refine ⟨1772663931804741468856733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181775954536494312571155 1772663931804741468856733)
                  ·
                    refine ⟨664748974426778050821275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772663931804741468856733 664748974426778050821275)
                    ·
                      rfl

theorem cell22_1941891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 3].length) (baseStart_1941891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941891 prefixEnd_1941891 := by exact prefixLift 1941891
  have htrace : WordTrace (prefixWord ++ tailWord_1941891) baseStart_1941891 baseEnd_1941891 := by
    simpa [prefixWord, tailWord_1941891, baseEnd_1941891] using wordTrace_append hprefix tailTrace_1941891
  have hstable : (prefixWord ++ tailWord_1941891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941891).length < 2 ^ (prefixWord ++ tailWord_1941891).sum := by decide
  have hdescent : baseEnd_1941891 < baseStart_1941891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941913 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1941913 : Nat := 118140960795 + 1941913 * 2 ^ 59
def prefixEnd_1941913 : Nat := 4983230072969 + 3 ^ 40 * 1941913 * 2
def baseEnd_1941913 : Nat := 664756505476377326771207

theorem tailTrace_1941913 : CollatzResearch.WordTrace tailWord_1941913 prefixEnd_1941913 664756505476377326771207 := by
  unfold tailWord_1941913
  simp only [CollatzResearch.WordTrace]
  refine ⟨70827385813788328181318393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47218257209192218787545595 70827385813788328181318393)
  ·
    refine ⟨53120539360341246135988795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70827385813788328181318393 53120539360341246135988795)
    ·
      refine ⟨79680809040511869203983193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53120539360341246135988795 79680809040511869203983193)
      ·
        refine ⟨59760606780383901902987395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79680809040511869203983193 59760606780383901902987395)
        ·
          refine ⟨89640910170575852854481093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59760606780383901902987395 89640910170575852854481093)
          ·
            refine ⟨16807670656982972410215205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89640910170575852854481093 16807670656982972410215205)
            ·
              refine ⟨3151438248184307326915351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16807670656982972410215205 3151438248184307326915351)
              ·
                refine ⟨4727157372276460990373027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151438248184307326915351 4727157372276460990373027)
                ·
                  refine ⟨7090736058414691485559541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727157372276460990373027 7090736058414691485559541)
                  ·
                    refine ⟨664756505476377326771207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7090736058414691485559541 664756505476377326771207)
                    ·
                      rfl

theorem cell22_1941913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1941913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941913 prefixEnd_1941913 := by exact prefixLift 1941913
  have htrace : WordTrace (prefixWord ++ tailWord_1941913) baseStart_1941913 baseEnd_1941913 := by
    simpa [prefixWord, tailWord_1941913, baseEnd_1941913] using wordTrace_append hprefix tailTrace_1941913
  have hstable : (prefixWord ++ tailWord_1941913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941913).length < 2 ^ (prefixWord ++ tailWord_1941913).sum := by decide
  have hdescent : baseEnd_1941913 < baseStart_1941913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941964 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_1941964 : Nat := 118140960795 + 1941964 * 2 ^ 59
def prefixEnd_1941964 : Nat := 4983230072969 + 3 ^ 40 * 1941964 * 2
def baseEnd_1941964 : Nat := 664773963818630193746051

theorem tailTrace_1941964 : CollatzResearch.WordTrace tailWord_1941964 prefixEnd_1941964 664773963818630193746051 := by
  unfold tailWord_1941964
  simp only [CollatzResearch.WordTrace]
  refine ⟨35414622968301781945712473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47219497291069042594283297 35414622968301781945712473)
  ·
    refine ⟨26560967226226336459284355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35414622968301781945712473 26560967226226336459284355)
    ·
      refine ⟨39841450839339504688926533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26560967226226336459284355 39841450839339504688926533)
      ·
        refine ⟨7470272032376157129173725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39841450839339504688926533 7470272032376157129173725)
        ·
          refine ⟨2801352012141058923440147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7470272032376157129173725 2801352012141058923440147)
          ·
            refine ⟨4202028018211588385160221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801352012141058923440147 4202028018211588385160221)
            ·
              refine ⟨1575760506829345644435083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4202028018211588385160221 1575760506829345644435083)
              ·
                refine ⟨2363640760244018466652625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575760506829345644435083 2363640760244018466652625)
                ·
                  refine ⟨1772730570183013849989469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363640760244018466652625 1772730570183013849989469)
                  ·
                    refine ⟨664773963818630193746051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772730570183013849989469 664773963818630193746051)
                    ·
                      rfl

theorem cell22_1941964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_1941964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1941964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1941964 prefixEnd_1941964 := by exact prefixLift 1941964
  have htrace : WordTrace (prefixWord ++ tailWord_1941964) baseStart_1941964 baseEnd_1941964 := by
    simpa [prefixWord, tailWord_1941964, baseEnd_1941964] using wordTrace_append hprefix tailTrace_1941964
  have hstable : (prefixWord ++ tailWord_1941964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941964).length < 2 ^ (prefixWord ++ tailWord_1941964).sum := by decide
  have hdescent : baseEnd_1941964 < baseStart_1941964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942065 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_1942065 : Nat := 118140960795 + 1942065 * 2 ^ 59
def prefixEnd_1942065 : Nat := 4983230072969 + 3 ^ 40 * 1942065 * 2
def baseEnd_1942065 : Nat := 664808538182699596970741

theorem tailTrace_1942065 : CollatzResearch.WordTrace tailWord_1942065 prefixEnd_1942065 664808538182699596970741 := by
  unfold tailWord_1942065
  simp only [CollatzResearch.WordTrace]
  refine ⟨70832929709237658140851649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47221953139491772093901099 70832929709237658140851649)
  ·
    refine ⟨53124697281928243605638737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70832929709237658140851649 53124697281928243605638737)
    ·
      refine ⟨39843522961446182704229053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53124697281928243605638737 39843522961446182704229053)
      ·
        refine ⟨14941321110542318514085895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39843522961446182704229053 14941321110542318514085895)
        ·
          refine ⟨22411981665813477771128843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14941321110542318514085895 22411981665813477771128843)
          ·
            refine ⟨33617972498720216656693265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411981665813477771128843 33617972498720216656693265)
            ·
              refine ⟨25213479374040162492519949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33617972498720216656693265 25213479374040162492519949)
              ·
                refine ⟨9455054765265060934694981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25213479374040162492519949 9455054765265060934694981)
                ·
                  refine ⟨1772822768487198925255309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9455054765265060934694981 1772822768487198925255309)
                  ·
                    refine ⟨664808538182699596970741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772822768487198925255309 664808538182699596970741)
                    ·
                      rfl

theorem cell22_1942065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_1942065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942065 prefixEnd_1942065 := by exact prefixLift 1942065
  have htrace : WordTrace (prefixWord ++ tailWord_1942065) baseStart_1942065 baseEnd_1942065 := by
    simpa [prefixWord, tailWord_1942065, baseEnd_1942065] using wordTrace_append hprefix tailTrace_1942065
  have hstable : (prefixWord ++ tailWord_1942065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942065).length < 2 ^ (prefixWord ++ tailWord_1942065).sum := by decide
  have hdescent : baseEnd_1942065 < baseStart_1942065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942097 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1942097 : Nat := 118140960795 + 1942097 * 2 ^ 59
def prefixEnd_1942097 : Nat := 4983230072969 + 3 ^ 40 * 1942097 * 2
def baseEnd_1942097 : Nat := 664819492436662180170643

theorem tailTrace_1942097 : CollatzResearch.WordTrace tailWord_1942097 prefixEnd_1942097 664819492436662180170643 := by
  unfold tailWord_1942097
  simp only [CollatzResearch.WordTrace]
  refine ⟨70834096845121727606016545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47222731230081151737344363 70834096845121727606016545)
  ·
    refine ⟨53125572633841295704512409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70834096845121727606016545 53125572633841295704512409)
    ·
      refine ⟨39844179475380971778384307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53125572633841295704512409 39844179475380971778384307)
      ·
        refine ⟨59766269213071457667576461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39844179475380971778384307 59766269213071457667576461)
        ·
          refine ⟨22412350954901796625341173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59766269213071457667576461 22412350954901796625341173)
          ·
            refine ⟨2101157902022043433625735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22412350954901796625341173 2101157902022043433625735)
            ·
              refine ⟨3151736853033065150438603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101157902022043433625735 3151736853033065150438603)
              ·
                refine ⟨4727605279549597725657905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151736853033065150438603 4727605279549597725657905)
                ·
                  refine ⟨3545703959662198294243429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727605279549597725657905 3545703959662198294243429)
                  ·
                    refine ⟨664819492436662180170643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545703959662198294243429 664819492436662180170643)
                    ·
                      rfl

theorem cell22_1942097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1942097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942097 prefixEnd_1942097 := by exact prefixLift 1942097
  have htrace : WordTrace (prefixWord ++ tailWord_1942097) baseStart_1942097 baseEnd_1942097 := by
    simpa [prefixWord, tailWord_1942097, baseEnd_1942097] using wordTrace_append hprefix tailTrace_1942097
  have hstable : (prefixWord ++ tailWord_1942097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942097).length < 2 ^ (prefixWord ++ tailWord_1942097).sum := by decide
  have hdescent : baseEnd_1942097 < baseStart_1942097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942140 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_1942140 : Nat := 118140960795 + 1942140 * 2 ^ 59
def prefixEnd_1942140 : Nat := 4983230072969 + 3 ^ 40 * 1942140 * 2
def baseEnd_1942140 : Nat := 221611404071808133781837

theorem tailTrace_1942140 : CollatzResearch.WordTrace tailWord_1942140 prefixEnd_1942140 221611404071808133781837 := by
  unfold tailWord_1942140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35417832591982972974915937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47223776789310630633221249 35417832591982972974915937)
  ·
    refine ⟨26563374443987229731186953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35417832591982972974915937 26563374443987229731186953)
    ·
      refine ⟨19922530832990422298390215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26563374443987229731186953 19922530832990422298390215)
      ·
        refine ⟨29883796249485633447585323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19922530832990422298390215 29883796249485633447585323)
        ·
          refine ⟨44825694374228450171377985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29883796249485633447585323 44825694374228450171377985)
          ·
            refine ⟨33619270780671337628533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44825694374228450171377985 33619270780671337628533489)
            ·
              refine ⟨25214453085503503221400117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33619270780671337628533489 25214453085503503221400117)
              ·
                refine ⟨2363854976765953427006261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25214453085503503221400117 2363854976765953427006261)
                ·
                  refine ⟨221611404071808133781837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2363854976765953427006261 221611404071808133781837)
                  ·
                    rfl

theorem cell22_1942140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_1942140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942140 prefixEnd_1942140 := by exact prefixLift 1942140
  have htrace : WordTrace (prefixWord ++ tailWord_1942140) baseStart_1942140 baseEnd_1942140 := by
    simpa [prefixWord, tailWord_1942140, baseEnd_1942140] using wordTrace_append hprefix tailTrace_1942140
  have hstable : (prefixWord ++ tailWord_1942140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942140).length < 2 ^ (prefixWord ++ tailWord_1942140).sum := by decide
  have hdescent : baseEnd_1942140 < baseStart_1942140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942146 : List Nat := [3, 4, 3, 1, 1, 1, 1, 8]
def baseStart_1942146 : Nat := 118140960795 + 1942146 * 2 ^ 59
def prefixEnd_1942146 : Nat := 4983230072969 + 3 ^ 40 * 1942146 * 2
def baseEnd_1942146 : Nat := 73870696237560265077277

theorem tailTrace_1942146 : CollatzResearch.WordTrace tailWord_1942146 prefixEnd_1942146 73870696237560265077277 := by
  unfold tailWord_1942146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708971005486052243637573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47223922681296139316366861 17708971005486052243637573)
  ·
    refine ⟨3320432063528634795682045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17708971005486052243637573 3320432063528634795682045)
    ·
      refine ⟨1245162023823238048380767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3320432063528634795682045 1245162023823238048380767)
      ·
        refine ⟨1867743035734857072571151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245162023823238048380767 1867743035734857072571151)
        ·
          refine ⟨2801614553602285608856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867743035734857072571151 2801614553602285608856727)
          ·
            refine ⟨4202421830403428413285091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801614553602285608856727 4202421830403428413285091)
            ·
              refine ⟨6303632745605142619927637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202421830403428413285091 6303632745605142619927637)
              ·
                refine ⟨73870696237560265077277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6303632745605142619927637 73870696237560265077277)
                ·
                  rfl

theorem cell22_1942146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_1942146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942146 prefixEnd_1942146 := by exact prefixLift 1942146
  have htrace : WordTrace (prefixWord ++ tailWord_1942146) baseStart_1942146 baseEnd_1942146 := by
    simpa [prefixWord, tailWord_1942146, baseEnd_1942146] using wordTrace_append hprefix tailTrace_1942146
  have hstable : (prefixWord ++ tailWord_1942146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942146).length < 2 ^ (prefixWord ++ tailWord_1942146).sum := by decide
  have hdescent : baseEnd_1942146 < baseStart_1942146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942232 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_1942232 : Nat := 118140960795 + 1942232 * 2 ^ 59
def prefixEnd_1942232 : Nat := 4983230072969 + 3 ^ 40 * 1942232 * 2
def baseEnd_1942232 : Nat := 664865705695566828045229

theorem tailTrace_1942232 : CollatzResearch.WordTrace tailWord_1942232 prefixEnd_1942232 664865705695566828045229 := by
  unfold tailWord_1942232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35419510349816322831090475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47226013799755097108120633 35419510349816322831090475)
  ·
    refine ⟨53129265524724484246635713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35419510349816322831090475 53129265524724484246635713)
    ·
      refine ⟨39846949143543363184976785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53129265524724484246635713 39846949143543363184976785)
      ·
        refine ⟨29885211857657522388732589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39846949143543363184976785 29885211857657522388732589)
        ·
          refine ⟨11206954446621570895774721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29885211857657522388732589 11206954446621570895774721)
          ·
            refine ⟨8405215834966178171831041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11206954446621570895774721 8405215834966178171831041)
            ·
              refine ⟨6303911876224633628873281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405215834966178171831041 6303911876224633628873281)
              ·
                refine ⟨4727933907168475221654961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303911876224633628873281 4727933907168475221654961)
                ·
                  refine ⟨3545950430376356416241221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727933907168475221654961 3545950430376356416241221)
                  ·
                    refine ⟨664865705695566828045229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3545950430376356416241221 664865705695566828045229)
                    ·
                      rfl

theorem cell22_1942232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_1942232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942232 prefixEnd_1942232 := by exact prefixLift 1942232
  have htrace : WordTrace (prefixWord ++ tailWord_1942232) baseStart_1942232 baseEnd_1942232 := by
    simpa [prefixWord, tailWord_1942232, baseEnd_1942232] using wordTrace_append hprefix tailTrace_1942232
  have hstable : (prefixWord ++ tailWord_1942232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942232).length < 2 ^ (prefixWord ++ tailWord_1942232).sum := by decide
  have hdescent : baseEnd_1942232 < baseStart_1942232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942234 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1942234 : Nat := 118140960795 + 1942234 * 2 ^ 59
def prefixEnd_1942234 : Nat := 4983230072969 + 3 ^ 40 * 1942234 * 2
def baseEnd_1942234 : Nat := 664866390336439489495223

theorem tailTrace_1942234 : CollatzResearch.WordTrace tailWord_1942234 prefixEnd_1942234 664866390336439489495223 := by
  unfold tailWord_1942234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709773411406350000938439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47226062430416933335835837 17709773411406350000938439)
  ·
    refine ⟨26564660117109525001407659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17709773411406350000938439 26564660117109525001407659)
    ·
      refine ⟨39846990175664287502111489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26564660117109525001407659 39846990175664287502111489)
      ·
        refine ⟨29885242631748215626583617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39846990175664287502111489 29885242631748215626583617)
        ·
          refine ⟨22413931973811161719937713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29885242631748215626583617 22413931973811161719937713)
          ·
            refine ⟨16810448980358371289953285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22413931973811161719937713 16810448980358371289953285)
            ·
              refine ⟨3151959183817194616866241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16810448980358371289953285 3151959183817194616866241)
              ·
                refine ⟨2363969387862895962649681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151959183817194616866241 2363969387862895962649681)
                ·
                  refine ⟨1772977040897171971987261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363969387862895962649681 1772977040897171971987261)
                  ·
                    refine ⟨664866390336439489495223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1772977040897171971987261 664866390336439489495223)
                    ·
                      rfl

theorem cell22_1942234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1942234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942234 prefixEnd_1942234 := by exact prefixLift 1942234
  have htrace : WordTrace (prefixWord ++ tailWord_1942234) baseStart_1942234 baseEnd_1942234 := by
    simpa [prefixWord, tailWord_1942234, baseEnd_1942234] using wordTrace_append hprefix tailTrace_1942234
  have hstable : (prefixWord ++ tailWord_1942234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942234).length < 2 ^ (prefixWord ++ tailWord_1942234).sum := by decide
  have hdescent : baseEnd_1942234 < baseStart_1942234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942236 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_1942236 : Nat := 118140960795 + 1942236 * 2 ^ 59
def prefixEnd_1942236 : Nat := 4983230072969 + 3 ^ 40 * 1942236 * 2
def baseEnd_1942236 : Nat := 221622358325770716981739

theorem tailTrace_1942236 : CollatzResearch.WordTrace tailWord_1942236 prefixEnd_1942236 221622358325770716981739 := by
  unfold tailWord_1942236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35419583295809077172663281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47226111061078769563551041 35419583295809077172663281)
  ·
    refine ⟨26564687471856807879497461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35419583295809077172663281 26564687471856807879497461)
    ·
      refine ⟨2490439450486575738702887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26564687471856807879497461 2490439450486575738702887)
      ·
        refine ⟨3735659175729863608054331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490439450486575738702887 3735659175729863608054331)
        ·
          refine ⟨5603488763594795412081497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735659175729863608054331 5603488763594795412081497)
          ·
            refine ⟨4202616572696096559061123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5603488763594795412081497 4202616572696096559061123)
            ·
              refine ⟨6303924859044144838591685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202616572696096559061123 6303924859044144838591685)
              ·
                refine ⟨1181985911070777157235941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6303924859044144838591685 1181985911070777157235941)
                ·
                  refine ⟨221622358325770716981739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181985911070777157235941 221622358325770716981739)
                  ·
                    rfl

theorem cell22_1942236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_1942236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942236 prefixEnd_1942236 := by exact prefixLift 1942236
  have htrace : WordTrace (prefixWord ++ tailWord_1942236) baseStart_1942236 baseEnd_1942236 := by
    simpa [prefixWord, tailWord_1942236, baseEnd_1942236] using wordTrace_append hprefix tailTrace_1942236
  have hstable : (prefixWord ++ tailWord_1942236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942236).length < 2 ^ (prefixWord ++ tailWord_1942236).sum := by decide
  have hdescent : baseEnd_1942236 < baseStart_1942236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942275 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 7]
def baseStart_1942275 : Nat := 118140960795 + 1942275 * 2 ^ 59
def prefixEnd_1942275 : Nat := 4983230072969 + 3 ^ 40 * 1942275 * 2
def baseEnd_1942275 : Nat := 221626808491443016406699

theorem tailTrace_1942275 : CollatzResearch.WordTrace tailWord_1942275 prefixEnd_1942275 221626808491443016406699 := by
  unfold tailWord_1942275
  simp only [CollatzResearch.WordTrace]
  refine ⟨70840589038476864005996279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47227059358984576003997519 70840589038476864005996279)
  ·
    refine ⟨106260883557715296008994419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70840589038476864005996279 106260883557715296008994419)
    ·
      refine ⟨159391325336572944013491629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106260883557715296008994419 159391325336572944013491629)
      ·
        refine ⟨59771747001214854005059361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159391325336572944013491629 59771747001214854005059361)
        ·
          refine ⟨44828810250911140503794521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59771747001214854005059361 44828810250911140503794521)
          ·
            refine ⟨33621607688183355377845891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44828810250911140503794521 33621607688183355377845891)
            ·
              refine ⟨50432411532275033066768837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33621607688183355377845891 50432411532275033066768837)
              ·
                refine ⟨9456077162301568700019157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50432411532275033066768837 9456077162301568700019157)
                ·
                  refine ⟨221626808491443016406699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9456077162301568700019157 221626808491443016406699)
                  ·
                    rfl

theorem cell22_1942275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_1942275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942275 prefixEnd_1942275 := by exact prefixLift 1942275
  have htrace : WordTrace (prefixWord ++ tailWord_1942275) baseStart_1942275 baseEnd_1942275 := by
    simpa [prefixWord, tailWord_1942275, baseEnd_1942275] using wordTrace_append hprefix tailTrace_1942275
  have hstable : (prefixWord ++ tailWord_1942275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942275).length < 2 ^ (prefixWord ++ tailWord_1942275).sum := by decide
  have hdescent : baseEnd_1942275 < baseStart_1942275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942309 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 5]
def baseStart_1942309 : Nat := 118140960795 + 1942309 * 2 ^ 59
def prefixEnd_1942309 : Nat := 4983230072969 + 3 ^ 40 * 1942309 * 2
def baseEnd_1942309 : Nat := 221630688123054764623331

theorem tailTrace_1942309 : CollatzResearch.WordTrace tailWord_1942309 prefixEnd_1942309 221630688123054764623331 := by
  unfold tailWord_1942309
  simp only [CollatzResearch.WordTrace]
  refine ⟨70841829120353687812733981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47227886080235791875155987 70841829120353687812733981)
  ·
    refine ⟨26565685920132632929775243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70841829120353687812733981 26565685920132632929775243)
    ·
      refine ⟨39848528880198949394662865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26565685920132632929775243 39848528880198949394662865)
      ·
        refine ⟨29886396660149212045997149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39848528880198949394662865 29886396660149212045997149)
        ·
          refine ⟨11207398747555954517248931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29886396660149212045997149 11207398747555954517248931)
          ·
            refine ⟨16811098121333931775873397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207398747555954517248931 16811098121333931775873397)
            ·
              refine ⟨1576040448875056103988131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16811098121333931775873397 1576040448875056103988131)
              ·
                refine ⟨2364060673312584155982197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576040448875056103988131 2364060673312584155982197)
                ·
                  refine ⟨221630688123054764623331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2364060673312584155982197 221630688123054764623331)
                  ·
                    rfl

theorem cell22_1942309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_1942309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942309 prefixEnd_1942309 := by exact prefixLift 1942309
  have htrace : WordTrace (prefixWord ++ tailWord_1942309) baseStart_1942309 baseEnd_1942309 := by
    simpa [prefixWord, tailWord_1942309, baseEnd_1942309] using wordTrace_append hprefix tailTrace_1942309
  have hstable : (prefixWord ++ tailWord_1942309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942309).length < 2 ^ (prefixWord ++ tailWord_1942309).sum := by decide
  have hdescent : baseEnd_1942309 < baseStart_1942309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942330 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_1942330 : Nat := 118140960795 + 1942330 * 2 ^ 59
def prefixEnd_1942330 : Nat := 4983230072969 + 3 ^ 40 * 1942330 * 2
def baseEnd_1942330 : Nat := 664899253098327239094929

theorem tailTrace_1942330 : CollatzResearch.WordTrace tailWord_1942330 prefixEnd_1942330 664899253098327239094929 := by
  unfold tailWord_1942330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710648763319402099812111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47228396702185072266165629 17710648763319402099812111)
  ·
    refine ⟨26565973144979103149718167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17710648763319402099812111 26565973144979103149718167)
    ·
      refine ⟨39848959717468654724577251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26565973144979103149718167 39848959717468654724577251)
      ·
        refine ⟨59773439576202982086865877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39848959717468654724577251 59773439576202982086865877)
        ·
          refine ⟨1400939990067257392660919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59773439576202982086865877 1400939990067257392660919)
          ·
            refine ⟨2101409985100886088991379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400939990067257392660919 2101409985100886088991379)
            ·
              refine ⟨3152114977651329133487069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101409985100886088991379 3152114977651329133487069)
              ·
                refine ⟨1182043116619248425057651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3152114977651329133487069 1182043116619248425057651)
                ·
                  refine ⟨1773064674928872637586477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182043116619248425057651 1773064674928872637586477)
                  ·
                    refine ⟨664899253098327239094929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773064674928872637586477 664899253098327239094929)
                    ·
                      rfl

theorem cell22_1942330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_1942330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942330 prefixEnd_1942330 := by exact prefixLift 1942330
  have htrace : WordTrace (prefixWord ++ tailWord_1942330) baseStart_1942330 baseEnd_1942330 := by
    simpa [prefixWord, tailWord_1942330, baseEnd_1942330] using wordTrace_append hprefix tailTrace_1942330
  have hstable : (prefixWord ++ tailWord_1942330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942330).length < 2 ^ (prefixWord ++ tailWord_1942330).sum := by decide
  have hdescent : baseEnd_1942330 < baseStart_1942330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942367 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1942367 : Nat := 118140960795 + 1942367 * 2 ^ 59
def prefixEnd_1942367 : Nat := 4983230072969 + 3 ^ 40 * 1942367 * 2
def baseEnd_1942367 : Nat := 664911918954471475919815

theorem tailTrace_1942367 : CollatzResearch.WordTrace tailWord_1942367 prefixEnd_1942367 664911918954471475919815 := by
  unfold tailWord_1942367
  simp only [CollatzResearch.WordTrace]
  refine ⟨70843944554143563718345355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47229296369429042478896903 70843944554143563718345355)
  ·
    refine ⟨106265916831215345577518033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70843944554143563718345355 106265916831215345577518033)
    ·
      refine ⟨79699437623411509183138525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106265916831215345577518033 79699437623411509183138525)
      ·
        refine ⟨29887289108779315943676947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79699437623411509183138525 29887289108779315943676947)
        ·
          refine ⟨44830933663168973915515421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29887289108779315943676947 44830933663168973915515421)
          ·
            refine ⟨16811600123688365218318283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44830933663168973915515421 16811600123688365218318283)
            ·
              refine ⟨25217400185532547827477425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16811600123688365218318283 25217400185532547827477425)
              ·
                refine ⟨18913050139149410870608069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25217400185532547827477425 18913050139149410870608069)
                ·
                  refine ⟨3546196901090514538239013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18913050139149410870608069 3546196901090514538239013)
                  ·
                    refine ⟨664911918954471475919815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546196901090514538239013 664911918954471475919815)
                    ·
                      rfl

theorem cell22_1942367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1942367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942367 prefixEnd_1942367 := by exact prefixLift 1942367
  have htrace : WordTrace (prefixWord ++ tailWord_1942367) baseStart_1942367 baseEnd_1942367 := by
    simpa [prefixWord, tailWord_1942367, baseEnd_1942367] using wordTrace_append hprefix tailTrace_1942367
  have hstable : (prefixWord ++ tailWord_1942367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942367).length < 2 ^ (prefixWord ++ tailWord_1942367).sum := by decide
  have hdescent : baseEnd_1942367 < baseStart_1942367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942412 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1942412 : Nat := 118140960795 + 1942412 * 2 ^ 59
def prefixEnd_1942412 : Nat := 4983230072969 + 3 ^ 40 * 1942412 * 2
def baseEnd_1942412 : Nat := 664927323374106358544677

theorem tailTrace_1942412 : CollatzResearch.WordTrace tailWord_1942412 prefixEnd_1942412 664927323374106358544677 := by
  unfold tailWord_1942412
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422792919490268201866745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47230390559320357602488993 35422792919490268201866745)
  ·
    refine ⟨26567094689617701151400059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35422792919490268201866745 26567094689617701151400059)
    ·
      refine ⟨39850642034426551727100089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26567094689617701151400059 39850642034426551727100089)
      ·
        refine ⟨29887981525819913795325067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39850642034426551727100089 29887981525819913795325067)
        ·
          refine ⟨44831972288729870692987601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29887981525819913795325067 44831972288729870692987601)
          ·
            refine ⟨33623979216547403019740701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44831972288729870692987601 33623979216547403019740701)
            ·
              refine ⟨12608992206205276132402763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33623979216547403019740701 12608992206205276132402763)
              ·
                refine ⟨18913488309307914198604145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608992206205276132402763 18913488309307914198604145)
                ·
                  refine ⟨14185116231980935648953109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18913488309307914198604145 14185116231980935648953109)
                  ·
                    refine ⟨664927323374106358544677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14185116231980935648953109 664927323374106358544677)
                    ·
                      rfl

theorem cell22_1942412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1942412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942412 prefixEnd_1942412 := by exact prefixLift 1942412
  have htrace : WordTrace (prefixWord ++ tailWord_1942412) baseStart_1942412 baseEnd_1942412 := by
    simpa [prefixWord, tailWord_1942412, baseEnd_1942412] using wordTrace_append hprefix tailTrace_1942412
  have hstable : (prefixWord ++ tailWord_1942412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942412).length < 2 ^ (prefixWord ++ tailWord_1942412).sum := by decide
  have hdescent : baseEnd_1942412 < baseStart_1942412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942431 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 3, 3]
def baseStart_1942431 : Nat := 118140960795 + 1942431 * 2 ^ 59
def prefixEnd_1942431 : Nat := 4983230072969 + 3 ^ 40 * 1942431 * 2
def baseEnd_1942431 : Nat := 664933827462396642319619

theorem tailTrace_1942431 : CollatzResearch.WordTrace tailWord_1942431 prefixEnd_1942431 664933827462396642319619 := by
  unfold tailWord_1942431
  simp only [CollatzResearch.WordTrace]
  refine ⟨70846278825911702648675147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47230852550607801765783431 70846278825911702648675147)
  ·
    refine ⟨106269418238867553973012721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70846278825911702648675147 106269418238867553973012721)
    ·
      refine ⟨79702063679150665479759541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106269418238867553973012721 79702063679150665479759541)
      ·
        refine ⟨7472068469920374888727457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79702063679150665479759541 7472068469920374888727457)
        ·
          refine ⟨5604051352440281166545593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472068469920374888727457 5604051352440281166545593)
          ·
            refine ⟨4203038514330210874909195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604051352440281166545593 4203038514330210874909195)
            ·
              refine ⟨6304557771495316312363793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203038514330210874909195 6304557771495316312363793)
              ·
                refine ⟨4728418328621487234272845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304557771495316312363793 4728418328621487234272845)
                ·
                  refine ⟨1773156873233057712852317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4728418328621487234272845 1773156873233057712852317)
                  ·
                    refine ⟨664933827462396642319619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773156873233057712852317 664933827462396642319619)
                    ·
                      rfl

theorem cell22_1942431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_1942431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942431 prefixEnd_1942431 := by exact prefixLift 1942431
  have htrace : WordTrace (prefixWord ++ tailWord_1942431) baseStart_1942431 baseEnd_1942431 := by
    simpa [prefixWord, tailWord_1942431, baseEnd_1942431] using wordTrace_append hprefix tailTrace_1942431
  have hstable : (prefixWord ++ tailWord_1942431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942431).length < 2 ^ (prefixWord ++ tailWord_1942431).sum := by decide
  have hdescent : baseEnd_1942431 < baseStart_1942431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942454 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1942454 : Nat := 118140960795 + 1942454 * 2 ^ 59
def prefixEnd_1942454 : Nat := 4983230072969 + 3 ^ 40 * 1942454 * 2
def baseEnd_1942454 : Nat := 664941700832432248994549

theorem tailTrace_1942454 : CollatzResearch.WordTrace tailWord_1942454 prefixEnd_1942454 664941700832432248994549 := by
  unfold tailWord_1942454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427944856551773598547651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47231411803218918384508277 4427944856551773598547651)
  ·
    refine ⟨6641917284827660397821477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427944856551773598547651 6641917284827660397821477)
    ·
      refine ⟨1245359490905186324591527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6641917284827660397821477 1245359490905186324591527)
      ·
        refine ⟨1868039236357779486887291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245359490905186324591527 1868039236357779486887291)
        ·
          refine ⟨2802058854536669230330937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868039236357779486887291 2802058854536669230330937)
          ·
            refine ⟨2101544140902501922748203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802058854536669230330937 2101544140902501922748203)
            ·
              refine ⟨3152316211353752884122305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101544140902501922748203 3152316211353752884122305)
              ·
                refine ⟨2364237158515314663091729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3152316211353752884122305 2364237158515314663091729)
                ·
                  refine ⟨1773177868886485997318797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364237158515314663091729 1773177868886485997318797)
                  ·
                    refine ⟨664941700832432248994549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773177868886485997318797 664941700832432248994549)
                    ·
                      rfl

theorem cell22_1942454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1942454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942454 prefixEnd_1942454 := by exact prefixLift 1942454
  have htrace : WordTrace (prefixWord ++ tailWord_1942454) baseStart_1942454 baseEnd_1942454 := by
    simpa [prefixWord, tailWord_1942454, baseEnd_1942454] using wordTrace_append hprefix tailTrace_1942454
  have hstable : (prefixWord ++ tailWord_1942454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942454).length < 2 ^ (prefixWord ++ tailWord_1942454).sum := by decide
  have hdescent : baseEnd_1942454 < baseStart_1942454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942489 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 6]
def baseStart_1942489 : Nat := 118140960795 + 1942489 * 2 ^ 59
def prefixEnd_1942489 : Nat := 4983230072969 + 3 ^ 40 * 1942489 * 2
def baseEnd_1942489 : Nat := 221651227349234608123147

theorem tailTrace_1942489 : CollatzResearch.WordTrace tailWord_1942489 prefixEnd_1942489 221651227349234608123147 := by
  unfold tailWord_1942489
  simp only [CollatzResearch.WordTrace]
  refine ⟨70848394259701578554286521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47232262839801052369524347 70848394259701578554286521)
  ·
    refine ⟨53136295694776183915714891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70848394259701578554286521 53136295694776183915714891)
    ·
      refine ⟨79704443542164275873572337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53136295694776183915714891 79704443542164275873572337)
      ·
        refine ⟨59778332656623206905179253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79704443542164275873572337 59778332656623206905179253)
        ·
          refine ⟨5604218686558425647360555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59778332656623206905179253 5604218686558425647360555)
          ·
            refine ⟨8406328029837638471040833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604218686558425647360555 8406328029837638471040833)
            ·
              refine ⟨6304746022378228853280625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406328029837638471040833 6304746022378228853280625)
              ·
                refine ⟨4728559516783671639960469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304746022378228853280625 4728559516783671639960469)
                ·
                  refine ⟨221651227349234608123147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4728559516783671639960469 221651227349234608123147)
                  ·
                    rfl

theorem cell22_1942489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_1942489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942489 prefixEnd_1942489 := by exact prefixLift 1942489
  have htrace : WordTrace (prefixWord ++ tailWord_1942489) baseStart_1942489 baseEnd_1942489 := by
    simpa [prefixWord, tailWord_1942489, baseEnd_1942489] using wordTrace_append hprefix tailTrace_1942489
  have hstable : (prefixWord ++ tailWord_1942489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942489).length < 2 ^ (prefixWord ++ tailWord_1942489).sum := by decide
  have hdescent : baseEnd_1942489 < baseStart_1942489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942504 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1942504 : Nat := 118140960795 + 1942504 * 2 ^ 59
def prefixEnd_1942504 : Nat := 4983230072969 + 3 ^ 40 * 1942504 * 2
def baseEnd_1942504 : Nat := 664958816854248785244395

theorem tailTrace_1942504 : CollatzResearch.WordTrace tailWord_1942504 prefixEnd_1942504 664958816854248785244395 := by
  unfold tailWord_1942504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35424470677323618058041283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47232627569764824077388377 35424470677323618058041283)
  ·
    refine ⟨53136706015985427087061925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35424470677323618058041283 53136706015985427087061925)
    ·
      refine ⟨9963132377997267578824111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53136706015985427087061925 9963132377997267578824111)
      ·
        refine ⟨14944698566995901368236167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9963132377997267578824111 14944698566995901368236167)
        ·
          refine ⟨22417047850493852052354251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14944698566995901368236167 22417047850493852052354251)
          ·
            refine ⟨33625571775740778078531377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22417047850493852052354251 33625571775740778078531377)
            ·
              refine ⟨25219178831805583558898533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33625571775740778078531377 25219178831805583558898533)
              ·
                refine ⟨4728596030963546917293475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25219178831805583558898533 4728596030963546917293475)
                ·
                  refine ⟨7092894046445320375940213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728596030963546917293475 7092894046445320375940213)
                  ·
                    refine ⟨664958816854248785244395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7092894046445320375940213 664958816854248785244395)
                    ·
                      rfl

theorem cell22_1942504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1942504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942504 prefixEnd_1942504 := by exact prefixLift 1942504
  have htrace : WordTrace (prefixWord ++ tailWord_1942504) baseStart_1942504 baseEnd_1942504 := by
    simpa [prefixWord, tailWord_1942504, baseEnd_1942504] using wordTrace_append hprefix tailTrace_1942504
  have hstable : (prefixWord ++ tailWord_1942504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942504).length < 2 ^ (prefixWord ++ tailWord_1942504).sum := by decide
  have hdescent : baseEnd_1942504 < baseStart_1942504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942516 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1942516 : Nat := 118140960795 + 1942516 * 2 ^ 59
def prefixEnd_1942516 : Nat := 4983230072969 + 3 ^ 40 * 1942516 * 2
def baseEnd_1942516 : Nat := 664962924699484753944359

theorem tailTrace_1942516 : CollatzResearch.WordTrace tailWord_1942516 prefixEnd_1942516 664962924699484753944359 := by
  unfold tailWord_1942516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35424689515301881082759701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47232919353735841443679601 35424689515301881082759701)
  ·
    refine ⟨1660532321029775675754361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35424689515301881082759701 1660532321029775675754361)
    ·
      refine ⟨1245399240772331756815771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660532321029775675754361 1245399240772331756815771)
      ·
        refine ⟨1868098861158497635223657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245399240772331756815771 1868098861158497635223657)
        ·
          refine ⟨1401074145868873226417743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868098861158497635223657 1401074145868873226417743)
          ·
            refine ⟨2101611218803309839626615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401074145868873226417743 2101611218803309839626615)
            ·
              refine ⟨3152416828204964759439923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101611218803309839626615 3152416828204964759439923)
              ·
                refine ⟨4728625242307447139159885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152416828204964759439923 4728625242307447139159885)
                ·
                  refine ⟨1773234465865292677184957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4728625242307447139159885 1773234465865292677184957)
                  ·
                    refine ⟨664962924699484753944359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773234465865292677184957 664962924699484753944359)
                    ·
                      rfl

theorem cell22_1942516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1942516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942516 prefixEnd_1942516 := by exact prefixLift 1942516
  have htrace : WordTrace (prefixWord ++ tailWord_1942516) baseStart_1942516 baseEnd_1942516 := by
    simpa [prefixWord, tailWord_1942516, baseEnd_1942516] using wordTrace_append hprefix tailTrace_1942516
  have hstable : (prefixWord ++ tailWord_1942516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942516).length < 2 ^ (prefixWord ++ tailWord_1942516).sum := by decide
  have hdescent : baseEnd_1942516 < baseStart_1942516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942521 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_1942521 : Nat := 118140960795 + 1942521 * 2 ^ 59
def prefixEnd_1942521 : Nat := 4983230072969 + 3 ^ 40 * 1942521 * 2
def baseEnd_1942521 : Nat := 664964636301666407569343

theorem tailTrace_1942521 : CollatzResearch.WordTrace tailWord_1942521 prefixEnd_1942521 664964636301666407569343 := by
  unfold tailWord_1942521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70849561395585648019451417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47233040930390432012967611 70849561395585648019451417)
  ·
    refine ⟨53137171046689236014588563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70849561395585648019451417 53137171046689236014588563)
    ·
      refine ⟨79705756570033854021882845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53137171046689236014588563 79705756570033854021882845)
      ·
        refine ⟨29889658713762695258206067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79705756570033854021882845 29889658713762695258206067)
        ·
          refine ⟨44834488070644042887309101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29889658713762695258206067 44834488070644042887309101)
          ·
            refine ⟨16812933026491516082740913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44834488070644042887309101 16812933026491516082740913)
            ·
              refine ⟨12609699769868637062055685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16812933026491516082740913 12609699769868637062055685)
              ·
                refine ⟨2364318706850369449135441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12609699769868637062055685 2364318706850369449135441)
                ·
                  refine ⟨1773239030137777086851581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364318706850369449135441 1773239030137777086851581)
                  ·
                    refine ⟨664964636301666407569343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773239030137777086851581 664964636301666407569343)
                    ·
                      rfl

theorem cell22_1942521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_1942521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942521 prefixEnd_1942521 := by exact prefixLift 1942521
  have htrace : WordTrace (prefixWord ++ tailWord_1942521) baseStart_1942521 baseEnd_1942521 := by
    simpa [prefixWord, tailWord_1942521, baseEnd_1942521] using wordTrace_append hprefix tailTrace_1942521
  have hstable : (prefixWord ++ tailWord_1942521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942521).length < 2 ^ (prefixWord ++ tailWord_1942521).sum := by decide
  have hdescent : baseEnd_1942521 < baseStart_1942521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942538 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1942538 : Nat := 118140960795 + 1942538 * 2 ^ 59
def prefixEnd_1942538 : Nat := 4983230072969 + 3 ^ 40 * 1942538 * 2
def baseEnd_1942538 : Nat := 664970455749084029894291

theorem tailTrace_1942538 : CollatzResearch.WordTrace tailWord_1942538 prefixEnd_1942538 664970455749084029894291 := by
  unfold tailWord_1942538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17712545359131014980705067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47233454291016039948546845 17712545359131014980705067)
  ·
    refine ⟨26568818038696522471057601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17712545359131014980705067 26568818038696522471057601)
    ·
      refine ⟨19926613529022391853293201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26568818038696522471057601 19926613529022391853293201)
      ·
        refine ⟨14944960146766793889969901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19926613529022391853293201 14944960146766793889969901)
        ·
          refine ⟨5604360055037547708738713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14944960146766793889969901 5604360055037547708738713)
          ·
            refine ⟨4203270041278160781554035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604360055037547708738713 4203270041278160781554035)
            ·
              refine ⟨6304905061917241172331053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203270041278160781554035 6304905061917241172331053)
              ·
                refine ⟨2364339398218965439624145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6304905061917241172331053 2364339398218965439624145)
                ·
                  refine ⟨1773254548664224079718109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364339398218965439624145 1773254548664224079718109)
                  ·
                    refine ⟨664970455749084029894291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773254548664224079718109 664970455749084029894291)
                    ·
                      rfl

theorem cell22_1942538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1942538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942538 prefixEnd_1942538 := by exact prefixLift 1942538
  have htrace : WordTrace (prefixWord ++ tailWord_1942538) baseStart_1942538 baseEnd_1942538 := by
    simpa [prefixWord, tailWord_1942538, baseEnd_1942538] using wordTrace_append hprefix tailTrace_1942538
  have hstable : (prefixWord ++ tailWord_1942538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942538).length < 2 ^ (prefixWord ++ tailWord_1942538).sum := by decide
  have hdescent : baseEnd_1942538 < baseStart_1942538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942624 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_1942624 : Nat := 118140960795 + 1942624 * 2 ^ 59
def prefixEnd_1942624 : Nat := 4983230072969 + 3 ^ 40 * 1942624 * 2
def baseEnd_1942624 : Nat := 221666631768869490748009

theorem tailTrace_1942624 : CollatzResearch.WordTrace tailWord_1942624 prefixEnd_1942624 221666631768869490748009 := by
  unfold tailWord_1942624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35426659057106248305225463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47235545409474997740300617 35426659057106248305225463)
  ·
    refine ⟨53139988585659372457838195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35426659057106248305225463 53139988585659372457838195)
    ·
      refine ⟨79709982878489058686757293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53139988585659372457838195 79709982878489058686757293)
      ·
        refine ⟨29891243579433397007533985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79709982878489058686757293 29891243579433397007533985)
        ·
          refine ⟨22418432684575047755650489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29891243579433397007533985 22418432684575047755650489)
          ·
            refine ⟨16813824513431285816737867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22418432684575047755650489 16813824513431285816737867)
            ·
              refine ⟨25220736770146928725106801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16813824513431285816737867 25220736770146928725106801)
              ·
                refine ⟨18915552577610196543830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25220736770146928725106801 18915552577610196543830101)
                ·
                  refine ⟨221666631768869490748009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18915552577610196543830101 221666631768869490748009)
                  ·
                    rfl

theorem cell22_1942624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_1942624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942624 prefixEnd_1942624 := by exact prefixLift 1942624
  have htrace : WordTrace (prefixWord ++ tailWord_1942624) baseStart_1942624 baseEnd_1942624 := by
    simpa [prefixWord, tailWord_1942624, baseEnd_1942624] using wordTrace_append hprefix tailTrace_1942624
  have hstable : (prefixWord ++ tailWord_1942624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942624).length < 2 ^ (prefixWord ++ tailWord_1942624).sum := by decide
  have hdescent : baseEnd_1942624 < baseStart_1942624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942656 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_1942656 : Nat := 118140960795 + 1942656 * 2 ^ 59
def prefixEnd_1942656 : Nat := 4983230072969 + 3 ^ 40 * 1942656 * 2
def baseEnd_1942656 : Nat := 665010849560571055443929

theorem tailTrace_1942656 : CollatzResearch.WordTrace tailWord_1942656 prefixEnd_1942656 665010849560571055443929 := by
  unfold tailWord_1942656
  simp only [CollatzResearch.WordTrace]
  refine ⟨35427242625048283037807911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47236323500064377383743881 35427242625048283037807911)
  ·
    refine ⟨53140863937572424556711867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35427242625048283037807911 53140863937572424556711867)
    ·
      refine ⟨79711295906358636835067801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53140863937572424556711867 79711295906358636835067801)
      ·
        refine ⟨59783471929768977626300851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79711295906358636835067801 59783471929768977626300851)
        ·
          refine ⟨89675207894653466439451277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59783471929768977626300851 89675207894653466439451277)
          ·
            refine ⟨33628202960495049914794229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89675207894653466439451277 33628202960495049914794229)
            ·
              refine ⟨3152644027546410929511959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33628202960495049914794229 3152644027546410929511959)
              ·
                refine ⟨4728966041319616394267939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152644027546410929511959 4728966041319616394267939)
                ·
                  refine ⟨7093449061979424591401909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728966041319616394267939 7093449061979424591401909)
                  ·
                    refine ⟨665010849560571055443929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7093449061979424591401909 665010849560571055443929)
                    ·
                      rfl

theorem cell22_1942656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_1942656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942656 prefixEnd_1942656 := by exact prefixLift 1942656
  have htrace : WordTrace (prefixWord ++ tailWord_1942656) baseStart_1942656 baseEnd_1942656 := by
    simpa [prefixWord, tailWord_1942656, baseEnd_1942656] using wordTrace_append hprefix tailTrace_1942656
  have hstable : (prefixWord ++ tailWord_1942656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942656).length < 2 ^ (prefixWord ++ tailWord_1942656).sum := by decide
  have hdescent : baseEnd_1942656 < baseStart_1942656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942746 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1942746 : Nat := 118140960795 + 1942746 * 2 ^ 59
def prefixEnd_1942746 : Nat := 4983230072969 + 3 ^ 40 * 1942746 * 2
def baseEnd_1942746 : Nat := 665041658399840820693653

theorem tailTrace_1942746 : CollatzResearch.WordTrace tailWord_1942746 prefixEnd_1942746 665041658399840820693653 := by
  unfold tailWord_1942746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714441954942627861598023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47238511879847007630928061 17714441954942627861598023)
  ·
    refine ⟨26571662932413941792397035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17714441954942627861598023 26571662932413941792397035)
    ·
      refine ⟨39857494398620912688595553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26571662932413941792397035 39857494398620912688595553)
      ·
        refine ⟨29893120798965684516446665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39857494398620912688595553 29893120798965684516446665)
        ·
          refine ⟨22419840599224263387334999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29893120798965684516446665 22419840599224263387334999)
          ·
            refine ⟨33629760898836395081002499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22419840599224263387334999 33629760898836395081002499)
            ·
              refine ⟨50444641348254592621503749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33629760898836395081002499 50444641348254592621503749)
              ·
                refine ⟨9458370252797736116531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50444641348254592621503749 9458370252797736116531953)
                ·
                  refine ⟨7093777689598302087398965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9458370252797736116531953 7093777689598302087398965)
                  ·
                    refine ⟨665041658399840820693653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7093777689598302087398965 665041658399840820693653)
                    ·
                      rfl

theorem cell22_1942746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1942746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942746 prefixEnd_1942746 := by exact prefixLift 1942746
  have htrace : WordTrace (prefixWord ++ tailWord_1942746) baseStart_1942746 baseEnd_1942746 := by
    simpa [prefixWord, tailWord_1942746, baseEnd_1942746] using wordTrace_append hprefix tailTrace_1942746
  have hstable : (prefixWord ++ tailWord_1942746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942746).length < 2 ^ (prefixWord ++ tailWord_1942746).sum := by decide
  have hdescent : baseEnd_1942746 < baseStart_1942746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942752 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_1942752 : Nat := 118140960795 + 1942752 * 2 ^ 59
def prefixEnd_1942752 : Nat := 4983230072969 + 3 ^ 40 * 1942752 * 2
def baseEnd_1942752 : Nat := 665043712322458805043635

theorem tailTrace_1942752 : CollatzResearch.WordTrace tailWord_1942752 prefixEnd_1942752 665043712322458805043635 := by
  unfold tailWord_1942752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428993328874387235555255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47238657771832516314073673 35428993328874387235555255)
  ·
    refine ⟨53143489993311580853332883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35428993328874387235555255 53143489993311580853332883)
    ·
      refine ⟨79715234989967371279999325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53143489993311580853332883 79715234989967371279999325)
      ·
        refine ⟨29893213121237764229999747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79715234989967371279999325 29893213121237764229999747)
        ·
          refine ⟨44839819681856646344999621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29893213121237764229999747 44839819681856646344999621)
          ·
            refine ⟨8407466190348121189687429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44839819681856646344999621 8407466190348121189687429)
            ·
              refine ⟨1576399910690272723066393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8407466190348121189687429 1576399910690272723066393)
              ·
                refine ⟨1182299933017704542299795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576399910690272723066393 1182299933017704542299795)
                ·
                  refine ⟨1773449899526556813449693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182299933017704542299795 1773449899526556813449693)
                  ·
                    refine ⟨665043712322458805043635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1773449899526556813449693 665043712322458805043635)
                    ·
                      rfl

theorem cell22_1942752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_1942752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942752 prefixEnd_1942752 := by exact prefixLift 1942752
  have htrace : WordTrace (prefixWord ++ tailWord_1942752) baseStart_1942752 baseEnd_1942752 := by
    simpa [prefixWord, tailWord_1942752, baseEnd_1942752] using wordTrace_append hprefix tailTrace_1942752
  have hstable : (prefixWord ++ tailWord_1942752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942752).length < 2 ^ (prefixWord ++ tailWord_1942752).sum := by decide
  have hdescent : baseEnd_1942752 < baseStart_1942752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942778 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1942778 : Nat := 118140960795 + 1942778 * 2 ^ 59
def prefixEnd_1942778 : Nat := 4983230072969 + 3 ^ 40 * 1942778 * 2
def baseEnd_1942778 : Nat := 665052612653803403893555

theorem tailTrace_1942778 : CollatzResearch.WordTrace tailWord_1942778 prefixEnd_1942778 665052612653803403893555 := by
  unfold tailWord_1942778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714733738913645227889247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47239289970436387274371325 17714733738913645227889247)
  ·
    refine ⟨26572100608370467841833871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17714733738913645227889247 26572100608370467841833871)
    ·
      refine ⟨39858150912555701762750807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26572100608370467841833871 39858150912555701762750807)
      ·
        refine ⟨59787226368833552644126211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39858150912555701762750807 59787226368833552644126211)
        ·
          refine ⟨89680839553250328966189317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59787226368833552644126211 89680839553250328966189317)
          ·
            refine ⟨16815157416234436681160497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89680839553250328966189317 16815157416234436681160497)
            ·
              refine ⟨12611368062175827510870373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16815157416234436681160497 12611368062175827510870373)
              ·
                refine ⟨2364631511657967658288195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12611368062175827510870373 2364631511657967658288195)
                ·
                  refine ⟨3546947267486951487432293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364631511657967658288195 3546947267486951487432293)
                  ·
                    refine ⟨665052612653803403893555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3546947267486951487432293 665052612653803403893555)
                    ·
                      rfl

theorem cell22_1942778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1942778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1942778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1942778 prefixEnd_1942778 := by exact prefixLift 1942778
  have htrace : WordTrace (prefixWord ++ tailWord_1942778) baseStart_1942778 baseEnd_1942778 := by
    simpa [prefixWord, tailWord_1942778, baseEnd_1942778] using wordTrace_append hprefix tailTrace_1942778
  have hstable : (prefixWord ++ tailWord_1942778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942778).length < 2 ^ (prefixWord ++ tailWord_1942778).sum := by decide
  have hdescent : baseEnd_1942778 < baseStart_1942778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
